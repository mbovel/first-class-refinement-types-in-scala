---
title: First-class Refinement Types<br/>in Scala
author: "<u>Matt Bovel</u>, Viktor Kunčak and Martin Odersky"
---

## Introduction

<div class="columns">

<div class="column">

Refinement types are types qualified with logical predicates. For example,

$$\{ x: \text{Int} \mid x > 0 \}$$

denotes the type of all integers `x` such that `x > 0`.

<div class="fragment">

Implemented in many languages: [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), [Boolean refinement types in F\*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types), [Subset types in Dafny](https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types), etc.

</div>

</div>

<div class="column">

<div class="fragment">

This talk presents:

</div>

<div class="fragment">

1. A prototype **implementation** of refinement types in the Scala 3 compiler as _first-class_ types (§2, §4).

</div>

<div class="fragment">

2. A core **calculus** proven sound in Rocq by semantic typing, where both programs and predicates may diverge.

</div>

</div>

</div>

# <small>Part 1</small><br/>Implementation

## Syntax (§2.1)

<div class="columns">

<div class="column">

**Long form**, mirroring set-builder notation:

```scala
type NonEmpty[A] =
  {l: List[A] with l.nonEmpty}
```

<div class="fragment">

**Short form**, reusing a name already in scope:

```scala
val x: (Int with x % 2 == 0) = 42
// desugars to:
val x: {v: Int with v % 2 == 0} = 42
```

</div>

</div>

<div class="column">

```scala {.fragment}
def zip[A, B](
  xs: List[A],
  ys: List[B] with ys.size == xs.size
): {zs: List[(A, B)] with zs.size == xs.size}
```

```scala {.fragment}
def concat[T](
  xs: List[T],
  ys: List[T]
): {zs: List[T] with zs.size ==
                       xs.size + ys.size}
```

```scala {.fragment}
val xs: List[Int] = …; val ys: List[Int] = …
zip(concat(xs, ys), concat(ys, xs))
zip(concat(xs, ys), concat(xs, xs)) // error
```

</div>

</div>

<div class="notes">

- `with` was a deprecated keyword in Scala 3, so it was free to reuse; `|` was already taken by union types.
- `_` and `this` were considered as implicit binders and rejected: repeated `_` denotes distinct parameters, and `this` already means something else.
- Predicates reuse Scala's **expression** syntax: two new grammar productions, no new term language.
- The base type is an `InfixType`, which excludes complex forms such as unparenthesized match types.

</div>

## Why _first-class_? (§1)

<div class="columns">

<div class="column">

Liquid Haskell is a plugin that runs **after** type checking. The type of `x` is declared twice:

```haskell
{-@ x :: {v:Int | v mod 2 == 0} @-}
let x = 42 :: Int in ...
```

<div class="fragment">

“It's sort of like you're doing two things at once […] you're also talking to GHC, but you're also talking to LiquidHaskell.”
<small>– [Usability Barriers for Liquid Types](https://dl.acm.org/doi/10.1145/3729327) (Gamboa et al., PLDI 2025)</small>

</div>

<div class="fragment">

Instead, we implement refinement as ordinary Scala types, participating in subtyping, inference, overloading and pattern matching.

</div>

</div>

<div class="column">

<div class="fragment">

```scala
// Example: Bounded polymorphism
type Even = {v: Int with v % 2 == 0}
def maximum[T: Ordering, U <: T]
  (xs: List[U]): U = xs.reduce(max)
def example1: Even =
  maximum(List(2, 4, 6))
```

</div>

<div class="fragment">

```scala
// Example: Overload resolution
def min(l: List[Int] with l.isSorted) =
  l.head // O(1)
def min(l: List[Int]) = l.min // O(n)

def ex2(l: List[Int] with l.isSorted) =
  min(l) // calls the first overload
```

</div>

</div>

</div>

<div class="notes">

- Schmid and Kunčak's Scala prototype was “largely independent of Scala's own type checker”, so refinements could **not** be inferred as type arguments, and needed a separate qualifier inference algorithm that proved hard to scale.
- Honest history: our early prototypes also ran as a separate phase. More drawbacks than benefits.
- In `maximum`, `List(2, 4, 6)` is typed `List[2 | 4 | 6]`; inference instantiates `T := Int` (whose `Ordering` does the comparisons) and `U := 2 | 4 | 6`, and the result checks against `Even` since each literal satisfies the predicate. This is the case that motivated abstract refinements.
- Dafny and F\* also treat refinements as first-class, but were designed around verification from the ground up; ours is the first integration into a pre-existing language where subtyping is central and pervasive.

</div>

## Mixed-precision type inference (§2.4)

<div class="columns">

<div class="column">

Refinement types are **not** inferred from terms by default; the wider type is:

```scala
val x = 42 // Int, not {v: Int with v == 42}
```

<div class="fragment">

Why not always infer the precise type?

</div>

<div class="fragment">

1. **Backward compatibility:** implicit and overload resolution depend on inferred types; a more precise type changes which instances are found.
2. **Performance:** bigger types, slower comparisons.
3. **Usability:** inferring most precise types everywhere would be unreadable.

</div>

</div>

<div class="column">

<div class="fragment">

Instead, precision is recovered **on demand**, by a standard mechanism called _selfification_, triggerd by the bidirectional type-inference algorithm:

</div>

<div class="fragment">

```scala
val x: (Int with x == 42) = 42 // selfified
```

</div>

</div>

</div>

## Run-time checks (§2.5)

<div class="columns">

<div class="column">

**Pattern matching** branches on whether the predicate holds at run time:

```scala
type ID = {s: String with s.matches(idRegex)}

"a2e7-e89b" match
  case id: ID => ... // holds, id has type ID
  case _      => ... // does not hold
```

</div>

<div class="column">

<div class="fragment">

**Checked casts.** `.runtimeChecked` ([SIP-57](https://docs.scala-lang.org/sips/replace-nonsensical-unchecked-annotation.html)), when you expect the check to pass:

```scala
val id: ID = "a2e7-e89b".runtimeChecked
```

</div>

<div class="fragment">

```scala
// desugars to:
val id: ID =
  if ("a2e7-e89b".matches(idRegex))
    "a2e7-e89b".asInstanceOf[ID]
  else throw new IllegalArgumentException()
```

</div>

</div>

</div>

<div class="notes">

- The JVM erases type parameters, so `List[ID]` cannot be matched directly, but `xs.collect { case x: ID => x }` works.
- Both work only for first-order predicates: higher-order values cannot be checked eagerly, which sidesteps blame assignment for now.

</div>

## Solver (§4.3)

<div class="columns">

<div class="column">

How does the compiler check `{x: T with p(x)} <: {y: S with q(y)}`?

1. Check `T <: S`
2. Check `p(x)` implies `q(x)` for all `x`

<div class="fragment">

Existing implementation lowers the problem to an SMT solver.

</div>

<div class="fragment">

Due to publishing and performance concerns, we instead implemented our own **lightweight e-graph-based solver**.

</div>

</div>

<div class="column">

Domain-specific rewrites during canonicalization:

```scala
{v: Int with v == x + 3 * y}
  <: {v: Int with v == 2 * y + (x + y)}
```

```scala {.fragment}
{v: Int with v == a && a == b}
  <: {v: Int with v == b}
{v: Int with a == b}
  <: {v: Int with f(a) == f(b)}
```
</div>

</div>

<div class="notes">

- Strictly stronger than substitution alone; intentionally weaker than equality saturation: one representative per class, so only one form is explored.

</div>

## Evaluation (§4.4)

<div class="columns">

<div class="column">

**Compilation overhead**, against each system's own unchecked baseline:

| System | Overhead |
|---|---|
| First-class (ours) | **0–12%** |
| Schmid and Kunčak | 20–38% |
| Stainless | ≥ 56% |

<div class="fragment">

**When the feature is unused**, the full Dotty CI passes unchanged: the compiler itself (≈200 000 LoC), ≈10 000 tests, a 50-project community build. At most 4% slowdown on the official benchmark suite.

</div>


</div>

<div class="column">

<div class="fragment">

**Expressiveness.** Because refinements are types, we get type-argument inference. We also compile unmodified Scala, so adoption is incremental.

</div>

<div class="fragment">

Conversely, both alternatives have stronger solvers: SMT-backed and complete for linear integer arithmetic, ADTs and equality.

</div>

</div>

</div>

# <small>Part 2</small><br />Metatheory

## Language (§3.1)

<div class="columns">

<div class="column">

Essentially System $F_{<:>}$ with refinements, dependent functions and pairs, sums, unions, intersections and equi-recursive types:

$$
\begin{aligned}
A, B ::=\ & X \mid \texttt{Unit} \mid \texttt{True} \mid \texttt{False} \mid \texttt{Int32} \mid \top \mid \bot \\
 &\mid \Pi x{:}A.\, B \mid \forall (X {:>} L {<:} U).\, A \mid \Sigma x{:}A.\, B \\
 &\mid A + B \mid \lbrace x : A \mid p \rbrace \mid A \lor B \mid A \land B \\
 &\mid \mu X.\, A
\end{aligned}
$$

<div class="fragment">

$$
\begin{aligned}
a, b, f, p ::=\ & c \mid x \mid \lambda x{:}A.\, b \mid f\; a \mid f\,[A] \\
 &\mid \Lambda (X {:>} L {<:} U).\, b \mid \textsf{let}\; x{:}A = a \;\textsf{in}\; b \\
 &\mid (a_1, a_2) \mid \textsf{inl}[A]\, a \mid \textsf{inr}[A]\, a \mid \textsf{match} \ldots \\
 &\mid a \;\mathit{op}\; b \mid \textsf{if}\; a \;\textsf{then}\; b_1 \;\textsf{else}\; b_2 \mid \textsf{loop}(a)\; x.\, b
\end{aligned}
$$

</div>

</div>

<div class="column">



<div class="fragment">

**Loops.** $\textsf{loop}(a)\; x.\, b$ is a limited recursion that suffices to model loops and tail recursion. The body returns $\textsf{inl}$ to continue, $\textsf{inr}$ to exit.

</div>


<div class="fragment">

**Contribution**. To our knowledge, this is the first mechanized soundness proof combining refinements with $\lor$/$\land$, bounded polymorphism (both bounds), and positive equi-recursive types.

</div>

</div>

</div>

<div class="notes">

- `True` and `False` are singletons rather than one `Bool`: then $v \in \lbrace x : A \mid p \rbrace$ is exactly “$v \in A$ and $p \in \mathcal{E}\llbracket \texttt{True} \rrbracket$”. `Bool` is recovered as `True` $\lor$ `False`.

</div>

## Definitional Interpreter (§3.2)

Operational semantic is defined using a **fuel-bounded definitional interpreter**:

```coq
Fixpoint eval (fuel: nat) (env: list Value) (t: Term) : option (option Value) :=
  match fuel with
  | 0 => None              (* timeout *)
  | S fuel' =>
    match t with
    | tabs _ b =>
        Some (Some (vabs env b))
    | tapp f a =>
        match eval fuel' env f with
        | Some (Some (vabs envf b)) =>
          … eval fuel' (va :: envf) b
        | None => None       (* timeout *)
        | _ => Some None     (* stuck *)
    …
```

## Interpretation (§3.3)

<div class="columns">

<div class="column">

A *semantic type* is a predicate $\textsf{Value} \to \textsf{Prop}$.

<div class="fragment">

The _value interpretation_ $\mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}$ maps a syntactic type to a semantic type, given a semantic type context $\delta$ and a value environement $\rho$.

</div>

$$
\begin{aligned}
\mathcal{V}\llbracket \Pi x{:}A.\, B \rrbracket_{\delta}^{\rho}(v) \triangleq\ & \exists \rho_f, b.\; v = \langle \rho_f, \lambda x.\, b \rangle\ \land \\
  & \forall v_a.\; \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v_a) \implies \\
  &\quad \mathcal{E}\llbracket B \rrbracket_{\delta}^{\rho_f[x \mapsto v_a]}(b)
\end{aligned}
$$

<div class="fragment">

$$\mathcal{V}\llbracket \lbrace x : A \mid p \rbrace \rrbracket_{\delta}^{\rho}(v) \triangleq \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v) \land \mathcal{E}\llbracket \texttt{True} \rrbracket_{\delta}^{\rho[x \mapsto v]}(p)$$

</div>

<div class="fragment">

$$\mathcal{V}\llbracket \mu X.\, A \rrbracket_{\delta}^{\rho}(v) \triangleq \forall n.\; F^n(v)$$

$$F^0(v) = \top,\quad F^{n+1}(v) = \mathcal{V}\llbracket A \rrbracket_{\delta[X \mapsto F^n]}^{\rho}(v)$$

</div>

</div>

<div class="column">

The term interpretation lifts it to terms. This is where **partial correctness** lives:

$$
\begin{aligned}
\mathcal{E}\llbracket A \rrbracket_{\delta}^{\rho}(a) \triangleq\ & \forall n, r.\; \texttt{eval}\; n\; \rho\; a = \texttt{Some}\; r \implies \\
 &\quad \exists v.\; r = \texttt{Some}\; v \land \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v)
\end{aligned}
$$

<div class="fragment">

“**If** evaluation terminates, it produces a value, not a stuck state, and that value is in $\mathcal{V}\llbracket A \rrbracket$.” Vacuously true for diverging terms.

</div>

<div class="fragment">

Well-formedness ties the assignments to the context:

$$
\begin{aligned}
\mathrm{wf}(\delta, \Gamma, \rho) \triangleq\ & \forall (x : A) \in \Gamma.\; \mathcal{V}\llbracket A \rrbracket(\rho(x)) \\
 \land\ & \forall (X {:>} L {<:} U) \in \Gamma. \\
 &\quad \mathcal{V}\llbracket L \rrbracket \subseteq \delta(X) \subseteq \mathcal{V}\llbracket U \rrbracket \\
 \land\ & \forall (a_1 \sim a_2) \in \Gamma.\; \exists v, n_1, n_2. \\
 &\quad \texttt{eval}\; n_1\; \rho\; a_1 = \texttt{eval}\; n_2\; \rho\; a_2 \\
 &\quad\quad = \texttt{Some}\,(\texttt{Some}\; v)
\end{aligned}
$$

</div>

</div>

</div>

<div class="notes">

- Step-index-**free**: the $\forall n$ is inside the definition, so no external step counter is threaded through.

</div>

## Typing (§3.4)

<div class="columns">

<div class="column">

Semantic typing is **defined**, not derived: it quantifies over every well-formed environment:

$$\Gamma \vDash a : A \triangleq \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \mathcal{E}\llbracket A \rrbracket_{\delta}^{\rho}(a)$$

<div class="fragment">

So the usual typing rules are not definitions but **lemmas**: each of the 20 rules is proven individually, and any derivation built from them inherits safety. This is the fundamental theorem of the logical relation.

</div>

<div class="fragment">

A syntactic judgment $\Gamma \vdash a : A$ mirrors the rules, with:

**Theorem (Adequacy).** If $\Gamma \vdash a : A$ then $\Gamma \vDash a : A$.

</div>

<div class="fragment">

</div>

</div>

<div class="column">

$$\frac{\Gamma \vDash a : A \qquad \Gamma, x : A, x \sim a \vDash b : B}{\Gamma \vDash \textsf{let}\; x{:}A = a \;\textsf{in}\; b : \textsf{avoid}(B, x)}\;\text{(T-Let)}$$

<div class="fragment">

$$\frac{\Gamma \vDash a : A \qquad \textsf{firstorder}(A)}{\Gamma \vDash a : \lbrace x : A \mid x \mathbin{\texttt{==}} a \rbrace}\;\text{(T-Self)}$$

</div>

<div class="fragment">

$$\frac{\Gamma \vDash a : A \qquad \Gamma, x : A \vDash b : A + B}{\Gamma \vDash \textsf{loop}(a)\; x.\, b : B}\;\text{(T-Loop)}$$

</div>

<div class="fragment">

</div>

</div>

</div>

<div class="notes">

- No preservation, no progress, no canonical-forms lemma.
- $\textsf{firstorder}$ excludes closures and polymorphic values: no run-time equality.
- Recursion **without** typing a self-reference, which is what would normally force step-indexed reasoning for a fixpoint combinator.
- $\textsf{avoid}(B, x)$ removes a variable going out of scope, guided by polarity: a predicate mentioning $x$ becomes `true` positively, `false` negatively.

</div>

## Subtyping (§3.5)

<div class="columns">

<div class="column">

Subtyping is semantic inclusion, again quantified over all well-formed environments:

$$\Gamma \vDash A <: B \triangleq \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho} \subseteq \mathcal{V}\llbracket B \rrbracket_{\delta}^{\rho}$$

<div class="fragment">

Every value satisfying $A$ also satisfies $B$. The 20 subtyping rules are, again, lemmas.

</div>

<div class="fragment">

$$\Gamma \vDash \lbrace x : A \mid p \rbrace <: A \;\text{(S-RefineBase)}$$

$$\frac{\Gamma \vDash A <: B \qquad \Gamma, x : A \vDash p_1 \Rightarrow p_2}{\Gamma \vDash \lbrace x : A \mid p_1 \rbrace <: \lbrace x : B \mid p_2 \rbrace}\;\text{(S-Refine)}$$

</div>

</div>

<div class="column">

Recursive types are **equi**-recursive: no fold/unfold terms, just subtyping.

$$\frac{\textsf{spos}(X, A)}{\Gamma \vDash \mu X.\, A <: A[X \mapsto \mu X.\, A]}\;\text{(S-Mu-Unfold)}$$

$$\frac{\textsf{spos}(X, A)}{\Gamma \vDash A[X \mapsto \mu X.\, A] <: \mu X.\, A}\;\text{(S-Mu-Fold)}$$

<div class="fragment">

Together they give $\mu X.\, A \cong A[X \mapsto \mu X.\, A]$, proven by showing the two interpretations coincide. That is the ingredient that replaces step indexing.

</div>

<div class="fragment">

**Strict positivity** buys that: $X$ never occurs left of an arrow or in a $\forall$ bound. Two sharper edges:

- under a **union**, $X$ must be entirely absent;
- under a **nested** $\mu Y.\, B$, we need $\textsf{spos}(Y, B)$ *and* $X \notin B$.

</div>

</div>

</div>

<div class="notes">

- The single case added to Dotty's type comparer: check $<: A$, delegate the predicate to the solver.

</div>

## Semantic implication and termination (§2.3, §3.3)

<div class="columns">

<div class="column">

Predicates are ordinary pure terms, so they **may diverge**. $\lbrace x : A \mid p \rbrace$ holds when $p$ evaluates to `true` *whenever it terminates*, exactly like a run-time assertion, which only fails if the check returns `false`.

<div class="fragment">

Termination is confined to **one** judgment, used only by <span class="smallcaps">S-Refine</span>:

$$
\begin{aligned}
\Gamma \vDash p_1 \Rightarrow p_2 \triangleq\ & \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \\
 &\quad \mathcal{E}\llbracket \texttt{True} \rrbracket(p_1) \implies \mathcal{E}\llbracket \texttt{True} \rrbracket(p_2)
\end{aligned}
$$

</div>

<div class="fragment">

No typing rule mentions termination, so soundness needs **no termination assumption**, unlike System FR (total correctness), Liquid Haskell (reflected functions), F\* and Dafny (specification-level computation).

</div>

</div>

<div class="column">

Some entailments need nothing:

**Lemma (And-True).** $\Gamma \vDash (t \mathbin{\texttt{\&\&}} \texttt{true}) \Rightarrow t$.

<div class="fragment">

Others genuinely do:

**Lemma (And-False).** $t$ terminates $\implies \Gamma \vDash (t \mathbin{\texttt{\&\&}} \texttt{false}) \Rightarrow \texttt{false}$.

</div>

<div class="fragment">

Alarming? No: a diverging predicate is indistinguishable from `true`, not from `false`, and `true` proves nothing:

**Lemma.** $\Gamma \vDash \lbrace x : A \mid \textsf{diverge} \rbrace \mathrel{<:>} \lbrace x : A \mid \texttt{true} \rbrace \mathrel{<:>} A$, and no *terminating* term has type $\lbrace x : A \mid \texttt{false} \rbrace$.

</div>

</div>

</div>

<div class="notes">

- Necessary: $\neg\,(\varnothing \vDash (\textsf{diverge} \mathbin{\texttt{\&\&}} \texttt{false}) \Rightarrow \texttt{false})$.

</div>

## Future work

<div class="columns">

<div class="column">

**Implementation**

- **Flow-sensitive typing.** Works for patterns today; `if` conditions should narrow too:

```scala
if x > 0 then x: {v: Int with v > 0}
```

- **External checks** for what our lightweight solver cannot do. For example, it cannot yet prove `{v: Int with v > 2} <: {v: Int with v > 0}`:

```scala
x.externallyChecked: {v: Int with v > 0}
```

- **Term-parameterized types**, to modularize predicates:

```scala
type Range(from: Int, to: Int) = {v: Int with v >= from && v < to}
```

</div>

<div class="column">

**Theory**

- **Enforcing purity.** Today a function called in a predicate is *assumed* pure; an impure one is a silent logical error. Capture checking tracks exactly this, and separation checking would make invalidating facts on writes sound.

- **A syntactic proof system for entailment.** We leave implication purely semantic; the solver's normalization rules are not yet verified against it.

- **A termination checker**, needed only for the termination-sensitive entailment rules, never systematically for every function in a predicate.

- **Classes and objects**, absent from the core calculus.

</div>

</div>

## Summary

<div class="columns">

<div class="column">

Refinement types can be **first-class types** in a mainstream language.

- **Design:** refinements are ordinary Scala types, so subtyping, inference, bounded polymorphism, overloading and pattern matching work by construction.

- **Partial correctness:** predicates may diverge; a diverging predicate is vacuous, and soundness needs no termination assumption.

- **Metatheory:** the first mechanized proof combining refinements with unions, intersections, bounded polymorphism with both bounds, and positive equi-recursive types.

- **Implementation:** ≈2 500 lines in Dotty, a ≈600-line e-graph solver, 0–12% overhead, Dotty CI green.

</div>

<div class="column">

**Try it.** Published on Maven, usable from any SBT project:

```scala
scalaOrganization := "ch.epfl.lara"
scalaVersion := "3.10.0-RC1-bin-...-NIGHTLY"
scalacOptions ++= Seq(
  "-language:experimental.qualifiedTypes")
```

```scala {.fragment}
type Even = {v: Int with v % 2 == 0}
val x: Even = 42
```

<div class="fragment">

**Artifact:** Rocq mechanization, the Dotty extension, and the JMH benchmark suites.

<small><https://github.com/mbovel/first-class-refinement-types-in-scala></small>

</div>

<div class="fragment">

Thank you. Questions welcome.

</div>

</div>

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

