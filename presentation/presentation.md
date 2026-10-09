---
title: First-class Refinement Types<br/>in Scala
author: "<u>Matt Bovel</u>, Viktor Kunčak and Martin Odersky<br/>EPFL <small>(Swiss Federal Institute of Technology in Lausanne, Switzerland)</small>"
---

## Introduction

<div class="columns">

<div class="column">

Slides and paper:

<img src="./qr-code.svg" style="margin: -4.25%; width: 108.5%;" />
<small><a href="https://matt.bovel.net/scala-refinement-types/">matt.bovel.net/scala-refinement-types/</a></small>

</div>

<div class="column">

<div class="fragment">

A *refinement type* is a type refined with a predicate.

</div>

<div class="fragment">

For example,

$$\{ x: \text{Int} \mid x > 0 \}$$

denotes the type of integers `x` such that `x > 0`.

</div>

<div class="fragment">

In other languages: [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), [Boolean refinement types in F\*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types), [Subset types in Dafny](https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types), etc.

</div>

</div>

<div class="column">

<div class="fragment">

This talk presents:

1. A **prototype implementation** of refinement types in Scala 3 as _first-class_ types (§2, §4).

</div>

<div class="fragment">

2. A core **calculus** proven sound in Rocq for a pure subset of Scala; System $F_{<:>}$ with refinements, dependent functions and positive equi-recursive types, under a partial correctness semantics (§3).

</div>

</div>

</div>

# <small>Part 1</small><br/>Implementation

<div class="notes">

Let's start with the implementation.

</div>

## Syntax (§2.1)

<div class="columns">

<div class="column">

**Long form**, mirroring the set-builder notation:

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

<div class="fragment">

<small>Surveyed and implemented by Quentin Bernet for his Master thesis.</small>

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
```

</div>

</div>

## Why _first-class_? (§1)

<div class="columns">

<div class="column">

1. It's easier for us.
2. It's probably easier for users. <small>See [Usability Barriers for Liquid Types](https://dl.acm.org/doi/10.1145/3729327) (Gamboa et al., PLDI 2025)</small>
3. It's more expressive: refinement tyes are ordinary Scala types, participating in inference, **overload resolution** (1), **subtyping** (2), etc.

<div class="fragment">


```scala
// Example 1: Overload resolution
def min(l: List[Int] with l.isSorted) =
  l.head // O(1)

def min(l: List[Int]) =
  l.min // O(n)

def ex1(l: List[Int] with l.isSorted) =
  min(l) // calls the first overload
```

</div>

</div>

<div class="column">

<div class="fragment">

<p style="margin-bottom: -1em"><small>Inspired by [Abstract Refinement Types](https://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf) (Vazou et al., ESOP 2013).</small></p>

```scala
// Example 2: Bounded polymorphism
given Ord[Int] = ...

type Even = {v: Int with v % 2 == 0}

def ex2: Even =
  maximum(List(2, 4, 6))
```

</div>

<div class="fragment">

```scala
def maximum[T: Ord, U <: T](xs: List[U]): U =
  xs.reduce(max)
```


</div>

</div>

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

1. **Backward compatibility:** implicit and overload resolution depend on inferred types; a more precise type changes which instances are found.
2. **Performance:** bigger types, slower comparisons.
3. **Usability:** inferring most precise types everywhere would be unreadable.

</div>

</div>

<div class="column">

<div class="fragment">

Instead, precision is recovered **on demand**, by a standard mechanism called _selfification_, triggered by the bidirectional type-inference algorithm:

```scala
val x: (Int with x == 42) = 42 // selfified
```

</div>

</div>

</div>


## Solver (§4.3)

<div class="columns">

<div class="column">

How does the compiler check `{x: T with p(x)} <: {x: T with q(x)}`?


<div class="fragment">

Need to check that `p(x)` implies `q(x)` for all `x: T`.

</div>

<div class="fragment">

Existing implementations lower to SMT.

</div>

<div class="fragment">

Due to packaging and performance concerns, we instead implemented our own **lightweight e-graph-based solver**.

</div>

</div>

<div class="column">

<div class="fragment">

```scala
{v: Int with v == a && a == b}
  <: {v: Int with v == b}
{v: Int with a == b}
  <: {v: Int with f(a) == f(b)}
```

</div>

<div class="fragment">

And domain-specific normalizations such as:

```scala
{v: Int with v == x + 3 * y}
  <: {v: Int with v == 2 * y + (x + y)}
```

Also beta-reduction, ADT selections reductions and limited reasoning on LIA inequalities.
</div>

</div>

</div>

<div class="notes">

- Strictly stronger than substitution alone; intentionally weaker than equality saturation: one representative per class, so only one form is explored.

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
</div>
</div>

## Evaluation (§4.4)

<div class="columns">

<div class="column">

**Compilation overhead**, against each system's own unchecked baseline:

| System | Overhead |
|---|---|
| First-class (ours) | **0–13%** |
| Schmid and Kunčak | 20–41% |
| Stainless | ≥ 53% |

<div class="fragment">

**When the feature is unused**, the full Dotty CI passes unchanged: the compiler itself (≈200 000 LoC),<br/>≈10 000 tests, a 50-project community build.

≤ 4% slowdown on the official benchmark suite.

</div>


</div>

<div class="column">



</div>

</div>

# <small>Part 2</small><br />Metatheory

## Language (§3.1)

<div class="columns">

<div class="column math-left">

Essentially System $F_{<:>}$ with refinements, dependent functions and pairs, sums, unions, intersections and equi-recursive types:

$$
\begin{aligned}
A, B ::=\ & X \mid \texttt{Unit} \mid \texttt{True} \mid \texttt{False} \mid \texttt{Int32} \mid \top \mid \bot \\
 &\mid \Pi x{:}A.\, B \mid \forall (X {:>} L {<:} U).\, A \mid \Sigma x{:}A.\, B \\
 &\mid A + B \mid \lbrace x : A \mid p \rbrace \mid A \lor B \mid A \land B \\
 &\mid \mu X.\, A
\end{aligned}
$$

</div>

<div class="column">


<div class="fragment math-left">

$$
\begin{aligned}
a, b, f, p ::=\ & c \mid x \mid \lambda x{:}A.\, b \mid f\; a \mid f\,[A] \\
 &\mid \Lambda (X {:>} L {<:} U).\, b \mid \textsf{let}\; x{:}A = a \;\textsf{in}\; b \\
 &\mid (a_1, a_2) \mid \textsf{inl}[A]\, a \mid \textsf{inr}[A]\, a \mid \textsf{match} \ldots \\
 &\mid a \;\mathit{op}\; b \mid \textsf{if}\; a \;\textsf{then}\; b_1 \;\textsf{else}\; b_2 \mid \textsf{loop}(a)\; x.\, b
\end{aligned}
$$

</div>

<div class="fragment">

$\textsf{loop}(a)\; x.\, b$ suffices to model loops and tail recursion. The body returns $\textsf{inl}$ to continue, $\textsf{inr}$ to exit.

</div>

<div class="fragment math-left">

Values are a separate category:

$$
\begin{aligned}
v ::=\ & c \mid (v_1, v_2) \mid \textsf{inl}(v) \mid \textsf{inr}(v) \mid \langle \rho, \lambda x.\, b \rangle \mid \langle \rho, \Lambda X.\, b \rangle
\end{aligned}
$$

</div>

</div>

</div>

<div class="notes">

- `True` and `False` are singletons rather than one `Bool`: then $v \in \lbrace x : A \mid p \rbrace$ is exactly “$v \in A$ and $p \in \mathcal{E}\llbracket \texttt{True} \rrbracket$”. `Bool` is recovered as `True` $\lor$ `False`.

</div>

## Definitional Interpreter (§3.2)

Operational semantic is defined using a **fuel-bounded definitional interpreter**:

<p style="margin-top: 0"><small>Inspired by [Type soundness proofs with definitional interpreters](https://dl.acm.org/doi/10.1145/3093333.3009866) (Amin et al., POPL 2017).</small></p>

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

The **value interpretation** $\mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v)$ defines what it means for a value $v$ to satisfy a type $A$, given a semantic type context $\delta$ and a value environement $\rho$. <small>See [A Logical Approach to Type Soundness](https://dl.acm.org/doi/10.1145/3676954) (Timany et al., JACM 2024).</small>


<div class="fragment">

$\mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}$ is a **semantic type** (`Value -> Prop`).

</div>

<div class="fragment">

The **term interpretation** $\mathcal{E}\llbracket A \rrbracket_{\delta}^{\rho}(t)$ lifts it to terms:


$$
\begin{aligned}
\mathcal{E}\llbracket A \rrbracket_{\delta}^{\rho}(t) \triangleq\ & \forall n, r.\; \texttt{eval}\; n\; \rho\; t = \texttt{Some}\; r \implies \\
 &\quad \exists v.\; r = \texttt{Some}\; v \land \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v)
\end{aligned}
$$

“**If** evaluation terminates, it produces a value, and that value is in $\mathcal{V}\llbracket A \rrbracket$.” Vacuously true for diverging terms; this is _partial correctness_.

</div>

</div>

<div class="column">

<div class="fragment">

Value interpretation of **refinement types**:

$$\mathcal{V}\llbracket \lbrace x : A \mid p \rbrace \rrbracket_{\delta}^{\rho}(v) \triangleq \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v) \land \mathcal{E}\llbracket \texttt{True} \rrbracket_{\delta}^{\rho[x \mapsto v]}(p)$$

</div>

</div>

</div>

<div class="notes">

- The cyclic definition in other clothing: $\mathcal{V}\llbracket \mu X.\, A \rrbracket \triangleq \mathcal{V}\llbracket A[X \mapsto \mu X.\, A] \rrbracket$. The unfolding is not a structural subterm of $\mu X.\, A$, so Rocq rejects the fixpoint. Only the binding of $X$ changes in the nested occurrence.
- Strict positivity makes $F$ monotone, so the approximations decrease from $\top$ and reach the greatest fixpoint at $\omega$. Fold and unfold are then lemmas, not definitions.
- Step-index-**free**: the $\forall n$ is inside the definition, so no external step counter is threaded through. The index counts unfoldings of the recursive type, not evaluation steps.

</div>

## Typing (§3.4)

<div class="columns">

<div class="column">

Semantic typing is **defined**:

$$\Gamma \vDash a : A \triangleq \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \mathcal{E}\llbracket A \rrbracket_{\delta}^{\rho}(a)$$

<div class="fragment">

The typing rules are not declared, they are **lemmas**.

</div>

<div class="fragment">

A context $\Gamma$ is made of:

1. Term bindings: $x : A$
2. Type variable bindings: $X >: A <: B$
3. Equality facts: $s \sim t$

</div>

</div>

<div class="column">

<div class="fragment">

Rule for let-bindings:

$$\frac{\Gamma \vDash a : A \qquad \Gamma, x : A, x \sim a \vDash b : B}{\Gamma \vDash \textsf{let}\; x{:}A = a \;\textsf{in}\; b : \textsf{avoid}(B, x)}\;\text{(T-Let)}$$

</div>

<div class="fragment">

Selfification rule:

$$\frac{\Gamma \vDash a : A \qquad \textsf{firstorder}(A)}{\Gamma \vDash a : \lbrace x : A \mid x \mathbin{\texttt{==}} a \rbrace}\;\text{(T-Self)}$$

</div>

</div>

</div>

<div class="notes">

- No preservation, no progress, no canonical-forms lemma.
- $\textsf{firstorder}$ excludes closures and polymorphic values: no run-time equality.
- $\textsf{avoid}(B, x)$ removes a variable going out of scope, guided by polarity: a predicate mentioning $x$ becomes `true` positively, `false` negatively.

</div>

## Subtyping (§3.5)

<div class="columns">

<div class="column">

Subtyping is semantic inclusion:

$$\Gamma \vDash A <: B \triangleq \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho} \subseteq \mathcal{V}\llbracket B \rrbracket_{\delta}^{\rho}$$

<div class="fragment">

Every value satisfying $A$ also satisfies $B$.

</div>

</div>

<div class="column">

<div class="fragment">

Recursive types are equi-recursive:

$$\frac{\textsf{spos}(X, A)}{\Gamma \vDash \mu X.\, A <: A[X \mapsto \mu X.\, A]}\;\text{(S-Mu-Unfold)}$$

$$\frac{\textsf{spos}(X, A)}{\Gamma \vDash A[X \mapsto \mu X.\, A] <: \mu X.\, A}\;\text{(S-Mu-Fold)}$$

</div>

<div class="fragment">

Together they give $\mu X.\, A <:> A[X \mapsto \mu X.\, A]$, provided $X$ occurs only **strictly positively** in $A$.

</div>

</div>

</div>

<div class="notes">

- The single case added to Dotty's type comparer: check $<: A$, delegate the predicate to the solver.

</div>

## Refinements Subtyping and Semantic Implication (§3.5)

<div class="columns">

<div class="column">

Last but not the least, rules for refinement types:

$$\Gamma \vDash \lbrace x : A \mid p \rbrace <: A \;\text{(S-RefineBase)}$$

<div class="fragment">

Subtyping between refinements is semantic implication, a.k.a. entailment:

$$\frac{\Gamma \vDash A <: B \qquad \Gamma, x : A \vDash p_1 \Rightarrow p_2}{\Gamma \vDash \lbrace x : A \mid p_1 \rbrace <: \lbrace x : B \mid p_2 \rbrace}\;\text{(S-Refine)}$$

</div>

</div>

<div class="column">

<div class="fragment">

A refinement $\lbrace x : A \mid p \rbrace$ holds when $p$ evaluates to `true` *whenever it terminates*. Implication reads both predicates that way:

</div>

<div class="fragment">

$$
\begin{aligned}
\Gamma \vDash p_1 \Rightarrow p_2 \triangleq\ & \forall \delta, \rho.\; \mathrm{wf}(\delta, \Gamma, \rho) \implies \\
 &\quad \mathcal{E}\llbracket \texttt{True} \rrbracket(p_1) \implies \mathcal{E}\llbracket \texttt{True} \rrbracket(p_2)
\end{aligned}
$$

</div>


<div class="fragment">

**Lemma:**

$$\Gamma \vDash \lbrace x : A \mid \textsf{diverge} \rbrace \mathrel{<:>} \lbrace x : A \mid \texttt{true} \rbrace \mathrel{<:>} A$$

</div>

</div>

</div>

# Wrap-up

## Future work

<div class="columns">

<div class="column">

Implementation:

- **Better Solver** for what our lightweight solver cannot do.

- **A termination checker**, needed only for the termination-sensitive entailment rules, never systematically for every function in a predicate.

- **Term-parameterized types**, to modularize predicates:

```scala
    type Range(from: Int, to: Int) =
      {v: Int with v >= from && v < to}
```

</div>

<div class="column">

Theory:

- **Rules for semantic implication.** We leave implication purely semantic; the solver's normalization rules are not yet verified against it.

- **Enforcing purity.** Today a function called in a predicate is *assumed* pure. Capture and separation checking can ensure that predicates are pure.

- **Classes and objects**, absent from the presented core calculus.

</div>

</div>

## Conclusion

<div class="columns">

<div class="column" style="flex: 1.5;">

We showed:

1. A **prototype implementation** of refinement types in Scala 3 as _first-class_ types; normal Scala types that participate in subtyping, inference, overloads resolution and pattern matching.

2. A core **calculus** proven sound in Rocq by semantic typing. It includes refinements, dependent functions and pairs, sums, unions, intersections and equi-recursive positive types, and allows predicates to diverge.

</div>

<div class="column" style="margin-left: 1.2em;">

Slides and paper:

<div style="width: 100%;">
<img src="./qr-code.svg" style="margin: -4.25%; width: 108.5%;" />
<small><a href="https://matt.bovel.net/scala-refinement-types/">matt.bovel.net/scala-refinement-types/</a></small>
</div>

</div>

<div class="column" style="flex: 0 0 auto;">

<figure style="text-align: center; margin: -1.2em 0 0 0;">
<img src="./refined_type.png" style="height: 450px; width: auto;" />
<figcaption><small><em>Un type raffiné</em>,<br/>by Marina Granados Castro</small></figcaption>
</figure>

</div>

</div>

# Bonus slides

## Backup: LH Usability Barriers

From [“Usability Barriers for Liquid Types”](https://dl.acm.org/doi/10.1145/3729327) [1]:

- 4.2 Unclear Divide between Haskell and LiquidHaskell:
  - <small>“comments are usually seen as just optional information in the code and not something that is directly used by the compiler”</small>
  - <small>“It's sort of like you're doing two things at once because you're implementing in Haskell. But you're also talking to GHC, but you're also talking to LiquidHaskell.”</small>
- 4.7 Unhelpful Error Messages
  - <small>“[...] error messages produced from typing errors inside the predicates, seemed indistinguishable from those produced by verification errors.”</small>
- 4.8 Limited IDE Support 
  - <small>“[user] tried to use the function <code>length</code>, but since it was not imported, it was impossible to use in this case.”</small>

<small>[1] Catarina Gamboa, Abigail Reese, Alcides Fonseca, and Jonathan Aldrich. 2025. Usability Barriers for Liquid Types. Proc. ACM Program. Lang. 9, PLDI, Article 224 (June 2025), 26 pages. <a href="https://dl.acm.org/doi/10.1145/3729327">doi:10.1145/3729327</a></small>


## Backup: `List.collect`

Scala type parameters are _erased_ at runtime, so we cannot match on a `List[T]`.

<div class="fragment">

However, we can use `.collect` to filter and convert a list:

```scala
type Pos = { v: Int with v >= 0 }

val xs = List(-1,2,-2,1)
xs.collect { case x: Pos => x } : List[Pos]
```

</div>


## Backup: Value interpretation (more)

<div class="fragment">

Value interpretation of **function types**:

$$
\begin{aligned}
\mathcal{V}\llbracket \Pi x{:}A.\, B \rrbracket_{\delta}^{\rho}(v) \triangleq\ & \exists \rho_f, b.\; v = \langle \rho_f, \lambda x.\, b \rangle\ \land \\
  & \forall v_a.\; \mathcal{V}\llbracket A \rrbracket_{\delta}^{\rho}(v_a) \implies \mathcal{E}\llbracket B \rrbracket_{\delta}^{\rho_f[x \mapsto v_a]}(b)
\end{aligned}
$$

</div>


<div class="fragment">

Value interpretation of **recursive types**?

$$\textcolor{red}{\mathcal{V}\llbracket \mu X.\, A \rrbracket_{\delta}^{\rho}(v) \triangleq \mathcal{V}\llbracket A \rrbracket_{\delta[X \mapsto \mathcal{V}\llbracket \mu X.\, A \rrbracket_{\delta}^{\rho}]}^{\rho}(v)}$$

</div>

<div class="fragment">

$$\mathcal{V}\llbracket \mu X.\, A \rrbracket_{\delta}^{\rho}(v) \triangleq \forall n.\; F^n(v)$$

$$F^0(v) = \top,\quad F^{n+1}(v) = \mathcal{V}\llbracket A \rrbracket_{\delta[X \mapsto F^n]}^{\rho}(v)$$

</div>
