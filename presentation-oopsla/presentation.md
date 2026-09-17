---
title: Semantics of<br/>Recursive Types
author: "CS-642 project presentation<br/>Matt Bovel"
---

## Recursive types

<div class="columns">

<div class="column" style="flex: 1">

<div class="fragment">

This Scala definition is recursive:
```scala
enum List[A]:
  case Nil()
  case Cons(head: A, tail: List[A])
```

</div>

<div class="fragment">

Syntax of STLC + recursive types:

$$
\begin{aligned}
  \text{Terms} &\quad t ::= x \mid \lambda x. t \mid t_1 \; t_2 \\
  \text{Types} &\quad T ::= T_1 \to T_2 \; \, {\color{#a626a4} \bf \mid  X \mid \mu X. T}
\end{aligned}
$$

</div>

<div class="fragment">

Additionally using unit, disjoint sum and pair types, we can define:

$$
\text{List[A]} \triangleq \mu X. \, Unit + (A, X)
$$

</div>

</div>

<div class="column" style="flex: 1">



<div class="fragment">

A recursive type can be unfolded:

$$
\begin{aligned}
\mu X. \, & Unit + (A, X) \\
\equiv \; & Unit + (A, \mu X. \, Unit + (A, X)) \\
\equiv \; & Unit + (A, Unit + (A, \mu X. \, Unit + (A, X))) \\
\end{aligned}
$$

</div>

<div class="fragment">

We want a typing rule to unfold:

$$
\frac{\Gamma \vdash t : \mu X. T}{\Gamma \vdash t : T[X \mapsto \mu X. T]}
$$

</div>

<div class="fragment">

And one to fold:

$$
\frac{\Gamma \vdash t : T[X \mapsto \mu X. T]}{\Gamma \vdash t : \mu X. T}
$$

</div>

</div>

</div>


## Syntax & Definitional interpreter

<div class="columns">

<div class="column">


```coq {.small}
Inductive Term : Type :=
  | tbool : bool -> Term
  | tvar : nat -> Term
  | tabs : Ty -> Term -> Term
  | tapp : Term -> Term -> Term.

Inductive Ty : Type :=
  | TBool : Ty
  | TFun : Ty -> Ty -> Ty.
```

- We use de Bruijn indices for bindings
- Terms and values are separate
- Types don't have runtime semantics
- Lambdas capture their environment

</div>

<div class="column">

```coq {.small}
Inductive Value : Type :=
  | vbool : bool -> Value
  | vabs  : (list Value) -> Term -> Value.
  
Fixpoint eval_wrong (env: list Value) (t: Term) : option Value :=
  match t with
  | tbool b => Some (vbool b)
  | tvar i => nth_error env i
  | tabs _ b => Some (vabs env b)
  | tapp f a =>
      match (eval_wrong env f) with
      | Some (vabs envf b) =>
          match (eval_wrong env a) with
          | None => None
          | Some va => eval_wrong (va::envf) b
          end
      | _ => None
      end
  end.
```

</div>

</div>

## Definitional interpreter <small>(termination)</small>


We bound depth of recursive calls to ensure termination by adding a fuel parameter.  
We return a layered option type:  `None` means timeout, `Some None` means a runtime error.

<div style="font-size: 0.9em;">

```coq
Fixpoint eval (fuel: nat) (env: list Value) (t: Term) : option (option Value) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match t with
    …
    | tapp f a =>
        match (eval fuel' env f) with
        | None => None
        | Some (Some (vabs envf b)) =>
            match (eval fuel' env a) with
            | None => None
            | Some None => Some None
            | Some (Some va) => eval fuel' (va::envf) b
            end
        | _ => Some None
    …
```

</div>

## Definitional interpreter <small>(reference)</small>

<img src="./amin.png" class="paper"/>

## Semantic Types

<div class="columns">

<div class="column" style="flex: 1 1 0">

<div class="fragment">

The _value interpretation_ defines what it means for a value to have a syntactic type:

<div style="font-size: 0.9em;">

```coq
Fixpoint interp (T: Ty) (v: Value) : Prop :=
  match T with
  | TBool => exists b, v = vbool b
  | TFun A B =>
      exists env body, v = vabs env body
      /\ forall arg, interp A arg ->
           tinterp (arg::env) body (interp B)
  end.
```

</div>

</div> <!-- end fragment -->


<div class="fragment">

The _term interpretation_ defines what it means for a _term_ to have a _semantic type_:


```coq {.small}
Definition tinterp (env: list Value) (t: Term)
                   (T: Value -> Prop) : Prop :=
  exists v fuel,
    eval fuel env t = Some (Some v) /\ T v.
```

</div> <!-- end fragment -->


</div>

<div class="column" style="flex: 1 1 0">

<div class="fragment">

The _semantic typing judgement_ is defined as:

```coq {.small}
Definition sem_typed (tenv: list Ty) (t: Term)
                     (T: Ty) : Prop :=
  forall env, Forall2 interp tenv env ->
    tinterp env t (interp T).
```

</div><!-- end fragment -->


<div class="fragment">

It allows us to _prove_ typing rules:

```coq {.small}
Lemma sem_typed_app: forall tenv f a A B,
  sem_typed tenv f (TFun A B) ->
  sem_typed tenv a A ->
  sem_typed tenv (tapp f a) B.
Proof.
  …
Qed.
```

$$
\frac{
    \Gamma \vDash f : A \to B \qquad \Gamma \vDash a : A
}{
    \Gamma \vDash f \; a : B
}
$$



</div><!-- end fragment -->

</div><!-- end column -->

</div><!-- end columns -->


## Semantic Types <small>(reference)</small>

<img src="./timany.png" class="paper"/>

## Interpretation of recursive types


<div class="columns">

<div class="column" style="flex: 1 1 0">

<div class="fragment">

Recursive types have a body, and an implicit de Bruijn binder. `TVar i` refers to `i`-th bound type.

```coq {.small}
Inductive Ty : Type :=
  …
  | TVar : nat -> Ty
  | TMu : Ty -> Ty.
```

</div>

<div class="fragment">

Remember, we want $\mu X. T \equiv T[X \mapsto \mu X. T]$.

</div>


<div class="fragment">

Tentative `interp` using substitution:

```coq {.small}
Fixpoint interp_wrong (T: Ty) (v: Value) : Prop :=
  match T with
  …
  | TVar i => False
  | TMu B => interp (subst_ty 0 (TMu B) B)
  end.
```

</div>

</div>

<div class="column" style="flex: 1 1 0">

<div class="fragment">
We need _step-indexing_ to break the circularity.

</div>

```coq {.small .fragment}
Equations? interp (T: Ty) (k: nat)
                  (v: Value) : Prop
  by wf (k, ty_size T)
    (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
  …
  interp (TMu B) 0 v := True;
  interp (TMu B) (S k') v :=
    interp (subst_ty 0 (TMu B) B) k' v.
```

<div class="fragment">

Semantic typing quantifies over all steps:

```coq {.small}
Definition sem_typed (tenv: TyEnv) (t: Term)
                     (T: Ty) : Prop :=
  forall env k,
    Forall2 (fun T v => interp T k v) tenv env ->
    tinterp env t (fun v => interp T k v).
```

</div>

</div>

</div>

## Later types

<div class="columns">

<div class="column" style="flex: 1 1 0">

<div class="fragment">

Remember, we want $\mu X. T \equiv T[X \mapsto \mu X. T]$.

</div>

<div class="fragment">

But the well-founded version of `interp` gives us only $\llbracket \mu X. T \rrbracket^k \equiv \llbracket T[X \mapsto\mu X. T] \rrbracket^{k-1}$.

</div>

<div class="fragment">

We define a _later_ type $\triangleright \, T$ to mean "$T$ but one step later", so we have: $\mu X. T \equiv \triangleright \, T[X \mapsto\mu X. T]$.

</div>

<div class="fragment">

Interpretation of "later":

```coq {.small}
interp (TLater T') 0 v := True;
interp (TLater T') (S k') v := interp T' k' v;
```

</div>

</div>

<div class="column" style="flex: 1 1 0">

<div class="fragment">

We can then prove the following typing rules for recursive types:

$$
\frac{
    \Gamma \vDash t : \triangleright \, T[X \mapsto \mu X. T]
}{
    \Gamma \vDash t : \mu X. T
}
\qquad
\frac{
    \Gamma \vDash t : \mu X. T
}{
    \Gamma \vDash t : \triangleright \, T[X \mapsto \mu X. T]
}
$$

</div>

<div class="fragment">

Can we get rid of these spooky triangles?

</div>

</div>

</div>

## Downward closure

<div class="columns">

<div class="column" style="flex: 1 1 0">

<div class="fragment">

We can avoid the later type in the folding rule if we require that semantic types are _downward closed_:

$$T^{k} \subseteq T^{k'} \text{ for all } k' \le k$$

where $S \subseteq T$ means $\forall v, S \, v \implies T \, v$.

</div>


<div class="fragment">

This is not true with our definition, due to function types contravariance.

</div>

<div class="fragment">

Downward-close `interp` by quantifying over smaller steps in the interpretation of function types:

```coq {.small}
interp (TFun A B) k v :=
  exists env body, v = vabs env body
  /\ forall j (Hj: j <= k) arg, interp A j arg ->
       tinterp (arg::env) body (interp B j);
```

</div>

</div>

<div class="column" style="flex: 1 1 0">

<div class="fragment">

Thanks to downward closure of `interp`, we can now have $\llbracket \mu X. T \rrbracket^k \subseteq \llbracket T[X \mapsto\mu X. T] \rrbracket^k$, so we can get rid of the later type in the folding rule:

$$
\frac{
    \Gamma \vDash t : T[X \mapsto \mu X. T]
}{
    \Gamma \vDash t : \mu X. T
}
\qquad
\frac{
    \Gamma \vDash t : \mu X. T
}{
    \Gamma \vDash t : \triangleright \, T[X \mapsto \mu X. T]
}
$$

</div>

<div class="fragment">

Later types in the wild: <img src="giarrusso.png" class="paper" style="width: 60%;"/> <small><em>Scala step-by-step: soundness for DOT with step-indexed logical relations in Iris</em><br/>Paolo G. Giarrusso, Léo Stefanesco, Amin Timany, Lars Birkedal, and Robbert Krebbers</small>

</div>

</div>

</div>

## Indexed judgements


<div class="columns">

<div class="column" style="flex: 1">

<div class="fragment">

Instead of using later types, can we move steps from the interpretation to the typing judgement?

</div>

<div class="fragment">

$$
\frac{
    \Gamma \vDash_k t : \mu X. T
}{
    \Gamma \vDash_{k-1} t : \, T[X \mapsto \mu X. T]
}
$$

</div>

<div class="fragment">

```coq {.small}
Definition sem_typed (tenv: TyEnv) (n: nat)
                     (t: Term) (T: Ty) : Prop :=
  forall env k, n < k ->
    Forall2 (fun T v => interp T k v) tenv env ->
    tinterp env t (fun v => interp T (k - n) v).
```

</div>

<div class="fragment">

It makes sense:

```coq {.small}
Lemma sem_typed_distribute: forall env tenv n e T,
  sem_typed tenv n e T ->
  (forall k,
     Forall2 (fun T v => interp T k v) tenv env) ->
  tinterp env e (fun v => forall j, interp T j v).
```

</div>
</div>

<div class="column" style="flex: 1">

<div class="fragment">

For the application rule to go through, we also need to allow a gap inside the function interpretation:

```coq {.small}
Inductive Ty : Type :=
  …
  | TFun : nat -> Ty -> Ty -> Ty
  …
```

```coq {.small}
interp (TFun g A B) k v :=
  exists env body, v = vabs env body
  /\ forall j (Hjlo: g < j) (Hjhi: j <= k) arg,
       interp A j arg ->
       tinterp (arg::env) body (interp B (j - g));
```

</div>

<div class="fragment">

So we still have noise in the syntax,  
_and_ now also in the typing rules:

$$
\frac{
    \Gamma \vDash_{i} f : A \to_j B \qquad \Gamma \vDash_{k} a : A
}{
    \Gamma \vDash_{i + j + k} f \; a : B
}
$$

</div>

</div>

</div>

## Existential gaps

<div class="fragment">

Can we existentially quantify over the gaps?

</div>

<div class="fragment">

No.

</div>

<div class="fragment">

More in the report.

</div>


## Science to the rescue


<img src="./science2.png" class="paper" style="position: absolute; right: -2%; top: 5%; width: 20%;"/>

<img src="./science.png" class="paper"/>



## Insight 1. Global steps

In the definitional interpreter, count global evaluation steps instead of depth of recursive calls (🥲).

```coq {.small}
Equations? eval_sig (fuel: nat) (env: ValueEnv) (t: Term) :
  option ({fuel' : nat | fuel' < fuel} * option Value) by wf fuel lt :=
eval_sig 0 _ _ := None;
…
eval_sig (S fuel) env (tapp f a) with eval_sig fuel env f => {
  | None => None;
  | Some (exist _ fuel1 _, None) => Some (exist _ fuel1 _, None);
  | Some (exist _ fuel1 _, Some (vbool _)) => Some (exist _ fuel1 _, None);
  | Some (exist _ fuel1 _, Some (vabs envf body)) with eval_sig fuel1 env a => {
    | None => None;
    | Some (exist _ fuel2 _, None) => Some (exist _ fuel2 _, None);
    | Some (exist _ fuel2 _, Some va) with eval_sig fuel2 (va::envf) body => {
      | None => None;
      | Some (exist _ fuel3 _, r) => Some (exist _ fuel3 _, r)
    }
  }
}.
```

## Insight 2. Make steps arithmetic work

<div class="columns">

<div class="column" style="flex: 1 1 0">

1. Tie type steps to evaluation steps.
1. Decrease steps in the interpretation of _all_ types<br/>_but_ recursive types.
1. Interp recursive types as function power.

```coq {.small .fragment}
Definition SemTy : Type := nat -> Value -> Prop.

Definition tinterp (env: list Value) (k: nat)
                   (t: Term) (T: SemTy) : Prop :=
  forall k' r, eval k env t = Some (k', r) ->
    exists v, r = Some v /\ T k' v.

Fixpoint fun_pow {A: Type} (k: nat)
                 (f: A -> A) (z: A) : A :=
  match k with
  | 0 => z
  | S k => f (fun_pow k f z)
  end
```


</div>

<div class="column" style="flex: 1 1 0">

```coq {.small .fragment}
Definition mu_F (F: SemTy -> SemTy) : SemTy :=
  fun k v => fun_pow (S k) F Bot k v.

Fixpoint interp (tenv: list SemTy) (T: Ty)
                (k: nat) (v: Value) : Prop :=
  match T with
  | TVar i =>
      match nth_error tenv i with
      | Some A => A k v
      | None => False
      end
  | TBool => exists b, v = vbool b
  | TFun A B =>
      exists env body, v = vabs env body /\
        forall j (Hj: j < k) arg,
          interp tenv A j arg ->
          tinterp (arg::env) j body (interp tenv B)
  | TMu B =>
    mu_F (fun Self => interp (Self :: tenv) B) k v
  end.
```

</div>

</div>

## Insight 3. Contractive magic

<div class="columns">

<div class="column" style="flex: 1 1 0">

<div class="fragment">

<img src="./science5.png" class="paper" style="width: 80%; margin-top: 0;"/>

```coq {.small}
Definition approx (k: nat) (F: SemTy): SemTy :=
  fun j v => j < k /\ F j v.
```

</div>

<div class="fragment">

<img src="./science6.png" class="paper" style="width: 80%; margin-top: 0;"/>

```coq {.small}
Definition wf (F: SemTy -> SemTy) : Prop :=
  forall k Z,
    approx (S k) (F Z)
    = approx (S k) (F (approx k Z)).
```

</div>

</div>

<div class="column" style="flex: 1 1 0">


<div class="fragment">

<img src="./science9.png" class="paper" style="width: 85%; margin-top: 0;"/>

</div>

<div class="fragment">

```coq {.small}
Lemma F_well_founded: forall tenv B,
  contractive_at 0 B ->
  wf (fun X => interp (X :: tenv) B).
```

</div>

<div class="fragment">

```coq {.small}
Fixpoint contractive_at (n: nat) (T: Ty) : Prop :=
  match T with
  | TVar i => i <> n
  | TBool => True
  | TFun _ _ => True
  | TMu B => contractive_at (S n) B
  end.
```

Means the binder only occurs under other types.  
$\mu X. X$ is not contractive, but $\mu X. X \to X$ is.

</div>

</div>

</div>

## Insight 3. Contractive magic (continued)

<div class="fragment">

This allows us to prove the following rule:

$$
\frac{
    \Gamma \vDash t : T[X \mapsto \mu X. T] \qquad X \text{ contractive in } T
}{
    \Gamma \vDash t : \mu X. T
}\qquad \frac{
    \Gamma \vDash t : \mu X. T \qquad X \text{ contractive in } T
}{
    \Gamma \vDash t : T[X \mapsto \mu X. T]
}
$$

</div>

<div class="fragment">

Maybe we can have the contractiveness condition by construction.

```scala
enum List[A]:
  case Nil()
  case Cons(head: A, tail: List[A]) // okay
```

```scala
type A = A // not okay
```

</div>


## Conclusion

We mechanized soundness of 3 different semantics for recursive types:

1. Depth-bounded + later types
1. Depth-bounded + indexed judgements
1. Global steps + contractiveness

This allowed us to better understand the tradeoffs between these approaches.

Approach 3. seems better than what I previously had (positivity restriction).

We also investigated the existential gap approach, and found it doesn't work.

Equations is a bit annoying to work with.
