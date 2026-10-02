---
title: First-class Refinement Types<br/>in Scala
author: "<u>Matt Bovel</u>, Viktor Kunčak and Martin Odersky"
---

## Introduction

<div class="columns">

<div class="column">

Refinement types are types qualified with logical predicates.

<div class="fragment">

For example,

$$\{ x: \text{Int} \mid x > 0 \}$$

denotes the type of all integers `x` such that `x > 0`.

</div>

<div class="fragment">

Implemented in many languages: [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), [Boolean refinement types in F\*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types), [Subset types in Dafny](https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types), etc.

</div>


<div class="fragment">

Prior art in Scala: [SMT-based checking of predicate-qualified types for Scala](https://dl.acm.org/doi/10.1145/2998392.2998398) (Schmid and Kunčak, Scala Symposium 2016), [Refined](https://github.com/fthomas), [Iron](https://github.com/Iltotore/iron).

</div>

</div>

<div class="column">

<div class="fragment">

We present:

</div>

<div class="fragment">

1. **Implementation**: a prototype implementation of refinement implementation the Scala compiler, as a _first-class_ feature,

</div>

<div class="fragment">

2. **Metatheory**: a companion type system proven sound using semantic types / logical relations.

</div>

</div>

</div>

# <small>Part 1</small><br/>Implementation

<!-- TODO: Center vertically -->

## Syntax (§2.1)

<div class="columns">

<div class="column">

- `with` keyword. Show pos type alias example.

- Show short form syntax.

</div>

<div class="column">

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

</div>

</div>


## Why _first-class_? (§1)

- Existing systems have split layers. Liquid haskell is a plugin (Cite usability study). In dafny, two languages.

- LH double declaration, our one-liner.

- Honnest history: we actually began with an implementation in a separate phase, but it we hurt.

- Show examples from paper (bounded polymorphism, overload resolution)

## Mixed-precision type inference (§2.4)

## Run-time checks (§2.5)

## Solver (§4.3)

## Evaluation (§4.4)

# <small>Part 2</small><br />Metatheory

## Language (§3.1)

- Essentially System F with refinement, dependent functions, products, sums, intersetion, unions and bounded polymorphism.

- Loops.

- Recursive types, positivity restriction.

## Definitional Interpreter (§3.2)

## Interpretation (§3.3)

- Value interpretation description (relation on values env, semantic context, value, not step-indexed)

- Term interpretation. Instead of defining down arrow, use `eval` directly.

- Partial correctness.

- Show definitions for `True`, functions, universal types, and refinement types.

## Typing (§3.4)

- What is a context (relation on values env, semantic context, types context).

- Show definition. Rules are then lemmas.

- Show rules T-Let, T-Self, T-Loop

## Subtyping (§3.5)

- Show definition. Rules are then lemmas.

- Show S-Mu-*, S-Refine

## Semantic implication and termination (§2.3, §3.3)

- Definition of semantic implication.

- Look, no notion of termination, partial correctness.

- Few insights about non termination (from 2.3)

## Future work

## Summary
