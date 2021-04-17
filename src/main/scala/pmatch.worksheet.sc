// A pattern matching compiler

type ID = String

// We abstract the body of each clause as a call E(x1,...,xk)
// In a full compiler, this would be an arbitrary piece of code
case class Code(name:String, vars:List[Var])

// A pattern is either a variable or a constructor
// We could extend this, e.g. with guards
class Pat
case class Var(name:ID) extends Pat
case class Constr(name:String, elems:List[Pat]) extends Pat

// Our pattern matching construct is a list of clauses
// A clause consists of bound variables that will be matched against patterns
// This is different than an ordinary match like in ML, where we match multiple patterns against one value
// Our match conceptually looks like this:
//   match
//   | x = Plus(Mul(a,b),c), y = Mul(d,e)    =>  body1
//   | x = Plus(c,Mul(a,b)), z = Plus(d,e)   =>  body1
//   | ...
// Where x,y,z are bound variables that we match against patterns.
// An ML-like match such as:
//   match x with
//   | Mul(Add(a,b),Add(c,d)) => body1
//   | Mul(c,Add(a,b)) => body2
//   | else => body3
// Can be translated to:
//   match
//   | x = Mul(Add(a,b),Add(c,d)) => body1
//   | x = Mul(c,Add(a,b)) => body2
//   | else => body3
// This format makes it significantly simpler to compile, because during the compilation process, a match
// on a single variable turns into a match on multiple variables. For example, if we branch on x, we get:
//   match
//   | x = Mul(y,z) =>
//        match
//        | y = Add(a,b), z = Add(c,d) => body1
//        | c = y, z = Add(a,b) => body2
//   | else => body3
// As you can see, compilation of a match where each clause pattern matches against only a single variable,
// turns into a nested match where we may match against multiple variables.
// The alternative would be to match against a tuple, but using multiple variables is better, because
// it gives us more flexibility: we can simplify equations like c = y, which means that it's no longer
// the case that all clauses match agaist the same set of variables. That is, we turn the inner match above into:
//        match
//        | y = Add(a,b), z = Add(c,d) => body1
//        | z = Add(a,b) => body2[c := y]
// Tuples on the other hand tend to accumulate a lot of unnecessary matches against variables, and also require
// an extra step in the final codegen.
case class Clause(pats: Map[String, Pat], body: Code)
type Match = List[Clause]

// We compile pattern matching to case trees
// A node in a case tree is either a Test, which pattern matches a variable against a single constructor
// Or it is the final node Run, which runs some code (coming from the body of a clause)
abstract class CaseTree {
  def pp() : Unit
}
case class Test(x:ID, constr:String, elems:List[ID], yes:CaseTree, no:CaseTree) extends CaseTree {
  def pp() = {
    val args = elems.mkString(",")
    prindent(s"test($constr($args) = $x):")
    indent { yes.pp }
    no.pp()
  }
}
case class Run(code:Code) extends CaseTree {
  def pp() = {
    val args = code.vars.map(v => v.name).mkString(",")
    prindent(s"${code.name}($args)")
  }
}

var indentLevel = 0
def indent(f : () => Unit) = {
  indentLevel += 1
  f()
  indentLevel -= 1
}
def prindent(s:String) = {
  println(("  " * indentLevel) + s)
}

var k = 0
def fresh() : String = {
  k += 1
  return s"x$k"
}

// This is the main function that builds a case tree for a pattern matching problem
def genMatch(clauses : List[Clause]) : CaseTree = {
  if(clauses.isEmpty) assert(false, "Non-exhaustive pattern")
  val clauses2 = clauses.map(substVarEqs)
  val Clause(pats,bod) = clauses2.head  // We always try to determine if the first clause matches first, to avoid doing unnecessary work
  if(pats.isEmpty) return Run(bod)
  val branchVar = branchingHeuristic(pats, clauses2)
  // Now we branch on branchVar by testing against the constructor in pats
  // We generate the new clauses in the yes and no branch:
  //   The yes branch will contain all clauses that have the same constructor for that var + clauses that don't match on that var at all
  //   The no branch will contain all clauses that have a different constructor for that var + clause that don't match on that var at all
  // We see that clauses that don't match on that var are duplicated. So we might want to choose our branching heuristic to minimize this
  val Constr(constrname, elems) = pats(branchVar) // We know that the pattern must be a constructor at this point, because all vars have been subtituted
  var yes = collection.mutable.ListBuffer[Clause]()
  var no = collection.mutable.ListBuffer[Clause]()
  val vars = elems.map(x => fresh())
  for(Clause(pats,bod) <- clauses2){
    if(pats.contains(branchVar)){
      val Constr(constrname2, elems2) = pats(branchVar)
      if(constrname == constrname2){
        assert(elems.length == elems2.length, s"Constructors with inconsistent sizes: $constrname, ${elems.length} ${elems2.length}")
        var newpats = pats - branchVar
        for((vr,pat) <- vars.zip(elems2)){
          newpats += (vr -> pat)
        }
        yes += Clause(newpats, bod)
      }else{
        no += Clause(pats,bod)
      }
    }else{
      yes += Clause(pats,bod)
      no += Clause(pats,bod)
    }
  }
  return Test(branchVar, constrname, vars, genMatch(yes.toList), genMatch(no.toList))
}

// This takes a clause with plain variable matches such as (c = x) and substitutes them
def substVarEqs(clause: Clause): Clause = {
  val substitution = new collection.mutable.HashMap[String, String]()
  val patterns = new collection.mutable.HashMap[String, Pat]()
  for((v,p) <- clause.pats) p match {
    case Var(v2) => substitution(v2) = v
    case _ => patterns(v) = p
  }
  val body = Code(clause.body.name, clause.body.vars.map(v => Var(substitution.getOrElse(v.name, v.name))))
  return Clause(patterns.toMap, body)
}

// Heuristically select a variable to branch on
// We want to do that in such a way as to generate a the best final case tree
// It's not entirely clear what is best: smallest total size, or maybe a bigger case tree can sometimes be more efficient to execute
// Due to the hash consing it is hard to predict which case tree will actually be smallest
// One solution might be to try all possible branchings, and choose the best case tree using some cost metric
// Note sure if that's worth it, since the case trees are already quite good with a simple heuristic: the one that locally causes the least duplication
var heuristic = "good"
def branchingHeuristic(pats: Map[String, Pat], clauses: List[Clause]): String =
  if(heuristic == "good") pats.keys.maxBy(v => clauses.count({case Clause(ps,bod) => ps.contains(v)}))
  else if(heuristic == "bad") pats.keys.minBy(v => clauses.count({case Clause(ps,bod) => ps.contains(v)}))
  else if(heuristic == "none") pats.keys.head
  else assert(false, s"Bad heuristic: $heuristic")


// Example pattern match
val x = Var("x")
val y = Var("y")
val z = Var("z")
val zero = Constr("Zero", List())
def suc(a: Pat) = Constr("Suc", List(a))
def add(a: Pat, b: Pat) = Constr("Add", List(a, b))
def mul(a: Pat, b: Pat) = Constr("Mul", List(a, b))
def pow(a: Pat, b: Pat) = Constr("Pow", List(a, b))

val clauses = List(
  add(zero,zero) -> Code("Z",List()),
  add(zero, x) -> Code("A", List(x)),
  add(x,zero) -> Code("B", List(x)),
  mul(zero,x) -> Code("C", List(x)),
  mul(x,zero) -> Code("D", List(x)),
  add(suc(x), y) -> Code("E", List(x,y)),
  add(x, suc(y)) -> Code("F", List(x,y)),
  mul(suc(x), y) -> Code("G", List(x,y)),
  mul(x, suc(y)) -> Code("H", List(x,y)),
  mul(add(x, y), z) -> Code("I", List(x,y,z)),
  mul(z, add(x, y)) -> Code("J", List(x,y,z)),
  mul(mul(x, y), z) -> Code("K", List(x,y,z)),
  pow(x, suc(y)) -> Code("L", List(x,y)),
  pow(x, zero) -> Code("M", List(x)),
  suc(add(zero,zero)) -> Code("Q1",List()),
  suc(add(x,y)) -> Code("Q2",List(x,y)),
  x -> Code("N", List(x))
)

val exampleMatch : Match = clauses.map((pat,bod) => Clause(Map("it" -> pat), bod)).toList

val result = genMatch(exampleMatch)
result.pp()

// Output:
//   (heuristics make no difference for this example)
//
// test(it = Add(x1,x2)):
//   test(x1 = Zero()):
//     test(x2 = Zero()):
//       Z()
//     A(x2)
//   test(x2 = Zero()):
//     B(x1)
//   test(x1 = Suc(x3)):
//     E(x3,x2)
//   test(x2 = Suc(x4)):
//     F(x1,x4)
//   N(it)
// test(it = Mul(x5,x6)):
//   test(x5 = Zero()):
//     C(x6)
//   test(x6 = Zero()):
//     D(x5)
//   test(x5 = Suc(x7)):
//     G(x7,x6)
//   test(x6 = Suc(x8)):
//     H(x5,x8)
//   test(x5 = Add(x9,x10)):
//     I(x9,x10,x6)
//   test(x6 = Add(x11,x12)):
//     J(x11,x12,x5)
//   test(x5 = Mul(x13,x14)):
//     K(x13,x14,x6)
//   N(it)
// test(it = Pow(x15,x16)):
//   test(x16 = Suc(x17)):
//     L(x15,x17)
//   test(x16 = Zero()):
//     M(x15)
//   N(it)
// test(it = Suc(x18)):
//   test(x18 = Add(x19,x20)):
//     test(x19 = Zero()):
//       test(x20 = Zero()):
//         Q1()
//       Q2(x19,x20)
//     Q2(x19,x20)
//   N(it)
// N(it)


// Example from: Compiling Pattern Matching to Good Decision Trees, Luc Maranget
// -----------------------------------------------------------------------------
//
// let rec run a s e c = match a,s,c with
// | _,_,Ldi i::c -> 1
// | _,_,Push::c -> 2
// | Int n2,Val (Int n1)::s,IOp op::c -> 3
// | Int 0,_,Test (c2,_)::c -> 4
// | Int _,_,Test (_,c3)::c -> 5
// | _,_,Extend::c -> 6
// | _,_,Search k::c -> 7
// | _,_,Pushenv::c -> 8
// | _,Env e::s,Popenv::c -> 9
// | _,_,Mkclos cc::c -> 10
// | _,_,Mkclosrec cc::c -> 11
// | Clo (cc,ce),Val v::s,Apply::c -> 12
// | a,(Code c::Env e::s),[] -> 13
// | a,[],[] -> 14

val nil = Constr("nil",List())
def cons(a:Pat,b:Pat) = Constr("cons", List(a,b))
def int(a:Pat) = Constr("int", List(a))
def vall(a:Pat) = Constr("val", List(a))
def test(a:Pat,b:Pat) = Constr("test", List(a,b))
val i = Var("i")
val c = Var("c")
val e = Var("e")
val a = Var("a")
val cc = Var("cc")
val op = Var("op")

k=0
val clauses2 = List(
  Map("c" -> Constr("Ldi",List(cons(i,c)))),
  Map("c" -> Constr("Push",List(c))),
  Map("a" -> int(Var("n2")), "s" -> vall(int(Var("n1"))), "c" -> Constr("iop",List(op,c))),
  Map()
).map(x => Clause(x,Code(fresh(),List())))

val result2 = genMatch(clauses2)
result2.pp()


val clauses3 = List(
  add(add(x,x),zero) -> Code("A",List()),
  add(mul(x,x),zero) -> Code("B",List()),
  add(x,pow(x,x)) -> Code("C",List()),
  add(x,mul(x,x)) -> Code("F",List()),
  x -> Code("Z", List(x))
)

val exampleMatch3 : Match = clauses3.map((pat,bod) => Clause(Map("it" -> pat), bod)).toList

heuristic = "good"
val result3 = genMatch(exampleMatch3)
result3.pp()

heuristic = "bad"
val result4 = genMatch(exampleMatch3)
result4.pp()



// Thoughts:
// - Most real pattern matches are relatively simple; they don't have any tricky cases that lead to duplication
// - Pretty much any reasonable algorithm will do well on those
// - Thus which pattern matching algorithm you use probably doesn't matter much
// - Sharing can be done as a post pass that generically shares CFG nodes
//      This is fine, because there seems to be little danger of code explosion, so trying to generate shared trees seems to be a waste of effort
// - Sharing further makes the choice of algorithm less relevant:
//      In the example above, sharing compresses the case tree from the bad heuristic to be pretty much equivalent to the good heuristic
//      It's actually difficult to come up with an example where the simple "good" heuristic produces suboptimal code when you have a sharing post-pass
// - It might be important to not be forced to check all constructors of a data type in an n-way branch
// - But maybe n-way branches should be done if possible, because they might have more efficient codegen (e.g. jump table)
// - We do want to use the types to eliminate dead cases, and to eagerly test/assert cases when only one constructor is still possible
// - It might actually be feasible to enumerate all possible pattern matching trees, if we always branch on a var with a constructor in the first clause, because those aren't that many choices