---
title: First-Class Refinement Types<br/>for Scala 3
author: "[Matt Bovel](mailto:matthieu@bovel.net), EPFL<br/>co-supervised by Viktor Kunčak ([Stainless](https://github.com/epfl-lara/stainless)) and Martin Odersky ([Scala](https://github.com/scala/scala3/)) <br/>work done in collaboration with Quentin Bernet and Valentin Schneeberger"
---

## <span class="chapter">Refinement types</span>

<div class="text">

Refinement types are types qualified with logical predicates.

<div class="fragment">

For example, $$\{ x: \text{Int} \mid x > 0 \}$$ denotes the type of all integers `x` such that `x > 0`.

</div>

<div class="fragment">

Implemented in many languages: [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), [Boolean refinement types in F\*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types), [Subset types in Dafny](https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types), etc.

</div>


<div class="fragment">

Prior art in Scala: [SMT-based checking of predicate-qualified types for Scala](https://dl.acm.org/doi/10.1145/2998392.2998398) (Schmid and Kunčak, Scala Symposium 2016), [Refined](https://github.com/fthomas), [Iron](https://github.com/Iltotore/iron).

</div>

</div> <!-- .text -->

## <span class="chapter">Outline</span>

<div class="columns">
<div class="column wide-lists" style="flex: 2.2;">

We present a work-in-progress implementation of refinement types in Scala 3, with focus on:

<ul>
<li class="fragment"><strong>First-class integration:</strong> implemented in the Scala compiler directly, not as a plugin or a separate tool.</li>
<li class="fragment"><strong>Typing:</strong> imprecise types by default, recover refinements when needed.</li>
<li class="fragment"><strong>Runtime checks:</strong> pattern matching and sugar.</li>
<li class="fragment"><strong>Solver:</strong> lightweight custom solver for subtyping.</li>
<li class="fragment"><strong>Mechanization:</strong> are we sound yet?</li>
</ul>

</div>

<div class="column">

<figure style="text-align: center">
<img src="images/qualified_type.png" alt="qualified types" style="width: 50%">
<figcaption><em>Un type qualifié</em>, by Marina Granados Castro</figcaption>
</figure>

</div> <!-- .column -->
</div> <!-- .columns -->


## <span class="chapter">Syntax</span>

Consider the type of non-empty lists:

$$\{ l: \text{List[A]} \mid l.\text{nonEmpty} \}$$

<div class="fragment">

In Scala, we use `with` instead of `|` because the latter is already used for union types:

```scala
type NonEmptyList[A] = { l: List[A] with l.nonEmpty }
```

- `l`: binder
- `List[A]`: parent type
- `l.nonEmpty`: qualifier (predicate)

</div >

<div class="notes">

A refinement type defines a subset of values. Here `l` is a binder, `List[A]` is the parent type, and `l.nonEmpty` is the predicate or qualifier. This reads "all List[A] values l such that l is non-empty". We call them logically qualified types in Scala to distinguish from structural refinement types, which refine members like `val` and `def`.

</div>

## <span class="chapter">Syntax:</span> Shorthand

When a binder already exists, such as in:

```scala
def zip[A, B](xs: List[A], ys: {ys: List[B] with ys.size == xs.size})
```

<div class="fragment">

We can omit it:

```scala
def zip[A, B](xs: List[A], ys: List[B] with ys.size == xs.size)
```

</div>

<div class="fragment">

The second version is desugared to the first.

</div>

<div class="notes">

When the value already has a name, like a parameter or val, you can skip the binder. The name is reused in the predicate.

</div>

## <span class="chapter">Syntax:</span> Example sized List API

```scala
def zip[A, B](xs: List[A], ys: List[B] with ys.size == xs.size):
  {l: List[(A, B)] with l.size == xs.size}
```

```scala {.fragment}
def concat[T](xs: List[T], ys: List[T]):
  {res: List[T] with res.size == xs.size + ys.size}
```

```scala {.fragment}
val xs: List[Int] = ...
val ys: List[Int] = ...
zip(concat(xs, ys), concat(ys, xs))
zip(concat(xs, ys), concat(xs, xs)) // error
```

## <span class="chapter">First-class</span>

Liquid Haskell is a plugin that runs after type checking.

```haskell
{-@ x :: {v:Int | v mod 2 == 0 } @-}
let x = 42 :: Int in ...
```

<div class="fragment">

In contrast, our implementation is directly integrated into the Scala 3 compiler:

```scala
val x: Int with (x % 2 == 0) = 42
```

</div>

<div class="fragment">

Refinement type subtyping is checked during type checking, not as a separate phase. Early prototypes did this as a separate phase, with more drawbacks than benefits.

<small>See also [Usability Barriers for Liquid Types](https://dl.acm.org/doi/10.1145/3729327) (Gamboa, Reese, Fonseca and Aldrich, PLDI 2025).</small>

</div>

## <span class="chapter">First-class:</span> Error messages

Predicates are type-checked like other Scala expressions:

```scala
def f[A](l: List[A] with l.notEmpty) = () // error
```

```text
-- [E008] Not Found Error: tests/neg-custom-args/qualified-types/predicate_error.scala:1:27 ----------------------------
1 |def f[A](l: List[A] with l.notEmpty) = () // error
  |                         ^^^^^^^^^^
  |                         value notEmpty is not a member of List[A]
  |                         - did you mean l.nonEmpty?
```

## <span class="chapter">First-class:</span> Error messages and inference

Same inference and error reporting as for other Scala types:

```scala
def g[T](f: T => Unit, x: T) = f(x)
g((x: PosInt) => x * 2, -2) // error
```

```text
-- [E007] Type Mismatch Error: tests/neg-custom-args/qualified-types/infer.scala:2:29 ------------------------
2 |  g((x: PosInt) => x * 2, -2) // error
  |                          ^^
  |                          Found:    (-2 : Int)
  |                          Required: {v: Int with v > 0}
```

## <span class="chapter">First-class:</span> Overload resolution

Consider the following two overloads of `min`:

```scala
/** Minimum of a list. O(n) */
def min(l: List[Int]): Int = l.min

/** Minimum of a sorted list. O(1) */
def min(l: List[Int] with l.isSorted): Int = l.head
```

<div class="fragment">

The second, more efficient overload is called if the list is known to be sorted:

```scala
val l2: List[Int] with l2.isSorted = l.sorted
min(l2) // calls second overload
```

</div>

## <span class="chapter">Typing</span>

For backward compatibility and performance reasons, refinement types are not inferred from terms by default. The wider type is inferred instead:

```scala
val x: /* Int */ = 42
```

<div class="fragment">

Why not type `x` as `{v: Int with v == 42}` directly?

</div>

<div class="fragment">

Because it would:

1. **Not be backward compatible:** overload resolution and implicit search return different results for a type vs. a more precise subtype.
2. **Hurt UX:** users would be flooded with complex types.
3. **Hurt performance:** big types slow down type checking.

</div>

## <span class="chapter">Typing</span>: Selfification

However, when a refinement type is expected, the compiler can _selfify_ the typed expression: that is, to give `e: T` the refinement type `x: T with x == e`:

```scala
val x: {v: Int with v == 42} = 42
```

<div class="fragment">

As a typing rule:

$$
\frac{\Gamma \vDash a : A \qquad \text{firstorder}(A)}{\Gamma \vDash a : \lbrace  x : A \mid x == a \rbrace }
\text{(T-Self)}
$$

</div>

<div class="fragment">

Selfification is standard in other refinement type systems. Typing based on the expected type is standard in Scala. We also do so for singleton types or union types.

</div>

## <span class="chapter">Typing</span>: Local unfolding

The system can also recover precise selfified types from local definitions:

```scala
val v1: Int = readInt()
val v2: Int = v1
val v3: Int with (v3 == v1) = v2
```

<div class="fragment">

Conceptually done by remembering definitions in a “fact context”:

$$
\frac{\Gamma \vDash a : A \qquad \Gamma, x : A, \lbrace x == a \rbrace \vDash b : B \qquad \text{firstorder}(A) }{\Gamma \vDash \texttt{let}\ x : A = a\ \texttt{in}\ b : \text{avoid}(B, x)}
\text{(T-LetEq)}
$$

</div>

<div class="fragment">

Similar rule in [System FR as Foundations for Stainless](https://doi.org/10.1145/3360592) (Hamza, Voirol and Kunčak, OOPSLA 2019).

</div>


## <span class="chapter">Runtime checks</span>

When static checking fails, a refinement type can be checked at runtime using pattern matching:

```scala
val idRegex = "^[a-zA-Z_][a-zA-Z0-9_]*$"
type ID = {s: String with s.matches(idRegex)}
```

<div class="fragment">

```scala
"a2e7-e89b" match
    case id: ID =>
        id: ID // matched, id has type ID
    case id     =>
        // default case, did not match
```

</div>

<div class="notes">

When the compiler can't verify a predicate statically, you can use runtime checks. Pattern matching checks the predicate at runtime.

</div>

## <span class="chapter">Runtime checks:</span> `.runtimeChecked`

You can also use `.runtimeChecked` ([SIP-57](https://docs.scala-lang.org/sips/replace-nonsensical-unchecked-annotation.html)) when you expect the check to always pass:

```scala
val id: ID = "a2e7-e89b".runtimeChecked
```

<div class="fragment">

Desugars to:

```scala
val id: ID =
  if ("a2e7-e89b".matches(idRegex)) "a2e7-e89b".asInstanceOf[ID]
  else throw new IllegalArgumentException()
```

</div>

<div class="fragment" style="font-size: 0.8em;">

Note: like with other types, you can also use `.asInstanceOf[ID]` directly to skip the check altogether.

</div>

## <span class="chapter">Example:</span> Bound-checked merge sort

Specify a type for non-negative integers (`Pos`) and a safe division function:

```scala
type Pos = {x: Int with x >= 0}

def safeDiv(x: Pos, y: Pos with y > 1): {res: Pos with res < x} =
  (x / y).runtimeChecked
```

Define an opaque type for bound-checked sequences:

```scala
opaque type SafeSeq[T] = Seq[T]

object SafeSeq:
  def fromSeq[T](seq: Seq[T]): SafeSeq[T] = seq
  def apply[T](elems: T*): SafeSeq[T] = fromSeq(elems)
```

## <span class="chapter">Example:</span> Bound-checked merge sort (2)

Add some methods to `SafeSeq`:

```scala
extension [T](a: SafeSeq[T])
  def len: Pos = a.length.runtimeChecked
  def apply(i: Pos with i < a.len): T =  a(i)
  def ++(that: SafeSeq[T]): SafeSeq[T] = a ++ that
  def splitAt(i: Pos with i < a.len): (SafeSeq[T], SafeSeq[T]) =
    a.splitAt(i)
```

These methods are only defined for non-empty sequences:

```scala
extension [T](a: SafeSeq[T] with a.len > 0)
  def head: T = a.head
  def tail: SafeSeq[T] = a.tail
```

## <span class="chapter">Example:</span> Bound-checked merge sort (3)

We can match on non-empty sequences, ensuring `head` and `tail` are safe to use:

```scala
def merge[T: Ordering as ord](left: SafeSeq[T], right: SafeSeq[T]): SafeSeq[T] =
  (left, right) match
    case (l: SafeSeq[T] with l.len > 0, r: SafeSeq[T] with r.len > 0) =>
      if ord.lt(l.head, r.head) then
        SafeSeq(l.head) ++ merge(l.tail, r)
      else
        SafeSeq(r.head) ++ merge(l, r.tail)
    case (l, r) =>
      if l.len == 0 then r else l
```

<div class="fragment">

This would be simplified with flow-sensitive typing.

</div>

## <span class="chapter">Example:</span> Bound-checked merge sort (4)

`middle` is known to be less than `len`, so `splitAt` is safe to use:

```scala
def mergeSort[T: Ordering](list: SafeSeq[T]): SafeSeq[T] =
  val len = list.len
  val middle = safeDiv(len, 2)
  if middle == 0 then
    list
  else
    val (left, right) = list.splitAt(middle)
    merge(mergeSort(left), mergeSort(right))
```

## <span class="chapter">Subtyping</span>

How does the compiler check `{x: T with p(x)} <: {y: S with q(y)}`?

1. Check `T <: S`
2. Check `p(x)` implies `q(x)` for all `x`

<div class="fragment">

A solver is needed to check logical implication (2.).

</div>

<div class="fragment">

We developed a lightweight custom solver that combines several techniques:

</div>

<ul>

<li class="fragment">constant folding,</li>
<li class="fragment">normalization,</li>
<li class="fragment">unfolding,</li>
<li class="fragment">equality reasoning.</li>

</ul>

<div class="notes">

To check if one refinement type is a subtype of another, the compiler checks if the parent types are related, and if the first predicate implies the second. Our implementation uses a lightweight custom solver that combines several techniques.

</div>

## <span class="chapter">Future work:</span> Flow-sensitive typing

Works with pattern matching:

```scala
x match
  case x: Int with x > 0 =>
    x: {v: Int with v > 0}
```

<div class="fragment">

Could also work with `if` conditions:

```scala
if x > 0 then
  x: {v: Int with v > 0}
```

</div>

## <span class="chapter">Future work:</span> External checks

Our solver is lightweight 👍 but incomplete 👎.

<div class="fragment">

In particular, it cannot handle ordering relations yet, for example it cannot prove:

```scala
{v: Int with v > 2} <: {v: Int with v > 0}
```

</div>

<div class="fragment">

For this and for more complex predicates, we could integrate with an external SMT solver like [Z3](https://microsoft.github.io/z3guide/docs/logic/intro/), [CVC5](https://cvc5.github.io/), or [Princess](https://philipp.ruemmer.org/princess.shtml) for explicit checks only:

```scala
x: {v: Int with v > 0} // checked by the type checker
x.runtimeChecked: {v: Int with v > 0} // checked at runtime
x.externallyChecked: {v: Int with v > 0} // checked by an external tool
x.asInstanceOf[{v: Int with v > 0}] // unchecked
```

</div>

## <span class="chapter">Mechanization</span>

Syntax of the language formalized so far:

$$
\begin{aligned}
A, B &::= X \mid  \texttt{Unit} \mid \texttt{Bool} \mid \Pi x: A.\ B \mid \forall X.\ A \mid \lbrace  x : A \mid b \rbrace \mid A \lor B \mid A \land B \\
a, b, f &::= \texttt{unit} \mid \texttt{true} \mid \texttt{false} \mid x \mid \lambda x: A.\ b \mid \Lambda X.\ b \mid f\ a \mid f[A] \\
         &\quad \mid \texttt{let}\ x : A = b\ \texttt{in}\ a \mid a == b \mid \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2
\end{aligned}
$$

<div class="fragment">

Mechanization done in Rocq, using a definitional interpreter, semantic types, and Autosubst (for de Bruijn indices). Does not yet include the implication solver.

<small>See [Mechanizing Refinement Types](https://doi.org/10.1145/3632912) (Borkowski, Vazou and Jhala, POPL 2024), [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3093333.3009866) (Amin and Tiark Rompf, POPL 2017), [A Logical Approach to Type Soundness](https://doi.org/10.1145/3676954) (Timany, Krebbers, Dreyer and Birkedal, Journal of the ACM 2024), [Autosubst: Reasoning with de Bruijn Terms and Parallel Substitutions](https://doi.org/10.1007/978-3-319-22102-1_24) (Schäfer, Tebbi and Smolka, ITP 2015).</small>

</div>


## <span class="chapter">Mechanization</span>: Interpretation

A semantic type is a predicate on values. The interpretation $⟦ A ⟧_{\delta}^{\rho}$ maps a syntactic type $A$ to a semantic type, given a type variable environment $\delta$ and a value environment $\rho$:

$$
\begin{aligned}
\cdots\\
⟦ \texttt{Bool} ⟧_{\delta}^{\rho} &= \lambda v.\ v = \texttt{true} \lor v = \texttt{false} \\
\cdots\\
⟦ \lbrace  x : A \mid p \rbrace  ⟧_{\delta}^{\rho} &= \lambda v.\ ⟦ A ⟧_{\delta}^{\rho}(v) \land \rho, x \mapsto v \vdash p \Downarrow \texttt{true} \\
\cdots\\
\end{aligned}
$$

## <span class="chapter">Mechanization</span>: Typing

The rule for let-bindings that stores equalities in the fact context:

$$
\frac{\Gamma \vDash a : A \qquad \text{firstorder}(A) \qquad \Gamma, x : A, \lbrace x == a \rbrace \vDash b : B}{\Gamma \vDash \texttt{let}\ x : A = a\ \texttt{in}\ b : \text{avoid}(B, x)}
\text{(T-LetEq)}
$$

The rule for selfification:

$$
\frac{\Gamma \vDash a : A \qquad \text{firstorder}(A)}{\Gamma \vDash a : \lbrace  x : A \mid x == a \rbrace }
\text{(T-Self)}
$$

The rule for `if` expressions:

$$
\frac{\Gamma \vDash a : \texttt{Bool} \qquad \Gamma, \lbrace a == \texttt{true} \rbrace \vDash b_1 : B_1 \qquad \Gamma, \lbrace a == \texttt{false} \rbrace \vDash b_2 : B_2}{\Gamma \vDash \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2 : B_1 \lor B_2}
\text{(T-If)}
$$

## <span class="chapter">Conclusion</span>

<div class="columns">

<div class="column wide-lists" style="flex: 3.6;">

- **Syntax:** `{x: T with p(x)}`, can omit binder,
- **First-class:** integrates with Scala UX and features (overloading, extension methods, givens, etc.),
- **Typing:** imprecise types by default, can recover refinements using *selfification* and local unfolding,
- **Runtime checks:** pattern matching, `.runtimeChecked`,
- **Subtyping:** normalization, local unfolding, equality reasoning, compatibility with other types,
- **Future work:** flow-sensitive typing, external checks,
- **Mechanization:** System F with refinement types and more, using a definitional interpreter and semantic types.

</div>

<div class="column">

<figure style="text-align: center">
<img src="images/qualified_type.png" alt="qualified types" style="width: 80%">
<figcaption><em>Un type qualifié</em>, by Marina Granados Castro</figcaption>
</figure>

</div> <!-- .column -->
</div> <!-- .columns -->


## <span class="chapter">Backup:</span> Predicate restrictions

<div class="fragment">

```scala
var x = 3
val y: Int with y == 3 = x // ⛔️ x is mutable
```

</div>

<div class="fragment">

```scala
class Box(val value: Int)
val b: Box with b == Box(3) = Box(3) // ⛔️ Box has equality by reference
```

</div>

<div class="fragment">

The predicate language is restricted to a fragment of Scala consisting of constants, stable identifiers, field selections over `val` fields, pure term applications, type applications, and constructors of case classes without initializers.

</div>

<div class="fragment">

Purity of functions is currently not enforced. Should it be?

</div>

## <span class="chapter">Backup:</span> LH Usability Barriers

From [“Usability Barriers for Liquid Types”](https://dl.acm.org/doi/10.1145/3729327) [1]:

- 4.2 Unclear Divide between Haskell and LiquidHaskell:
  - <small>“comments are usually seen as just optional information in the code and not something that is directly used by the compiler”</small>
  - <small>“It's sort of like you're doing two things at once because you're implementing in Haskell. But you're also talking to GHC, but you're also talking to LiquidHaskell.”</small>
- 4.7 Unhelpful Error Messages
  - <small>“[...] error messages produced from typing errors inside the predicates, seemed indistinguishable from those produced by verification errors.”</small>
- 4.8 Limited IDE Support 
  - <small>“[user] tried to use the function <code>length</code>, but since it was not imported, it was impossible to use in this case.”</small>

<small>[1] Catarina Gamboa, Abigail Reese, Alcides Fonseca, and Jonathan Aldrich. 2025. Usability Barriers for Liquid Types. Proc. ACM Program. Lang. 9, PLDI, Article 224 (June 2025), 26 pages. <a href="https://dl.acm.org/doi/10.1145/3729327">doi:10.1145/3729327</a></small>

## <span class="chapter">Backup:</span> `List.collect`

Scala type parameters are _erased_ at runtime, so we cannot match on a `List[T]`.

<div class="fragment">

However, we can use `.collect` to filter and convert a list:

```scala
type Pos = { v: Int with v >= 0 }

val xs = List(-1,2,-2,1)
xs.collect { case x: Pos => x } : List[Pos]
```

</div>

## <span class="chapter">Backup:</span> Specify using assertions 😕

<div class="columns">
<div class="column">

We can use assertions:

```scala
def zip[A, B](
  xs: List[A],
  ys: List[B]
) : List[(A, B)] = {
  require(xs.size == ys.size)
  ...
}.ensuring(_.size == xs.size)
```

</div>
<div class="column fragment">

Limitations:

- _Runtime overhead_: checked at runtime, not compile time,
- _No static guarantees_: only checked for specific inputs,
- _Not part of the API_: not visible in function type,
- _Hard to compose_: cannot be passed as type argument.

</div> <!-- .column -->

</div> <!-- .columns -->

<div class="notes">

We can use assertions, but they have limitations. The check happens at runtime, so there's overhead. The compiler can't verify the precondition is always satisfied. The precondition is not visible in the function type. And assertions don't compose well—imagine passing a list of values that all satisfy some property.

</div>

## <span class="chapter">Backup:</span> Specify using dependent types 😕

<div class="columns">
<div class="column">

Can we use path-dependent types?

```scala
def zip[A, B](
  xs: List[A],
  ys: List[B] {
    val size: xs.size.type
  }
): List[(A, B)] {
  val size: xs.size.type
} = ...
```

</div>
<div class="column fragment">

Limitations:

- _Limited reasoning_: only fields, literals and constant folding,
- _Not inferred_: need manual type annotations, or not typable at all,
- _Different languages_: term-level vs type-level.

</div> <!-- .column -->

</div> <!-- .columns -->

## <span class="chapter">Future work:</span> term-parameterized types

```scala
extension [T](list: List[T])
  def get(index: Int with index >= 0 && index < list.size): T = ...
```

<div class="fragment">

To modularize the “range” concept, we could introduce term-parameterized types:

```scala
type Range(from: Int, to: Int) = {v: Int with v >= from && v < to}
extension [T](list: List[T])
  def get(index: Range(0, list.size)): T = ...
```

</div>


## <span class="chapter">Future work:</span> Flow-sensitive typing (2)

This would be required for reasoning with refinement types inside cases:

<div style="font-size: 0.7em;">

```scala
enum MyList[+T]:
  case Cons(head: T, tail: MyList[T])
  case Nil

def myLength(xs: MyList[Int]): Int =
  xs match
    case MyList.Nil =>
      // Add assumption xs == MyList.Nil
      0
    case MyList.Cons(_, xs1) =>
      // Add assumption xs == MyList.Cons(?, xs1)
      1 + myLength(xs1)
```

</div>

## <span class="chapter">Subtyping:</span> Constant folding

```scala
{v: Int with v == 1 + 1}     <: {v: Int with v == 2}
```

## <span class="chapter">Subtyping:</span> Normalization

Arithmetic expressions are normalized using standard algebraic properties, for example commutativity of addition:

```scala
{v: Int with v == x + 1}     <: {v: Int with v == 1 + x}
```

<div class="fragment">

```scala
{v: Int with v == y + x}     <: {v: Int with v == x + y}
```

</div>

<div class="fragment">

Or grouping operands with the same constant factor in sums of products:

```scala
{v: Int with v == x + 3 * y} <: {v: Int with v == 2 * y + (x + y)}
```

</div>

## <span class="chapter">Subtyping:</span> Local unfolding

As mentioned, refinement types are not inferred from terms by default. However, the solver can unfold definitions of local `val` (only), even when they have an imprecise type:

```scala
val x: Int = ...
val y: Int = x + 1

{v: Int with v == y} =:= {v: Int with v == x + 1}
```

## <span class="chapter">Subtyping:</span> Equality reasoning

Transitivity of equality:

```scala
{v: Int with v == a && a == b} <: {v: Int with v == b}
```

<div class="fragment">

Congruence of equality:

```scala
{v: Int with a == b}           <: {v: Int with f(a) == f(b)}
```

</div>

<div class="fragment">

This is implemented using an E-Graph-like data structure.

</div>

## <span class="chapter">Subtyping:</span> With other Scala types

Literal types are subtypes of singleton refinement types:

```scala
3 <: {v: Int with v == 3}
```

<div class="fragment">

We plan to support subtyping with other Scala types in the future.

</div>
