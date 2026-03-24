# Refinement Types

A work-in-progress mechanization of refinement types in [Rocq](https://rocq-prover.org/), using semantic types and a definitional interpreter.

## Syntax

The syntax of terms and types extends System F with booleans, machine integers, dependent function types, dependent pairs (sigma types), and refinement types.

Values are distinct from terms: term lambdas can have free variables, while value closures capture their environment as a list of values.

```math
\begin{aligned}
c &::=  \texttt{unit} \mid \texttt{true} \mid \texttt{false} \mid \ldots \mid \texttt{-1} \mid \texttt{0} \mid \texttt{1} \mid \ldots \\
A, B &::= X \mid  \texttt{Unit} \mid \texttt{Bool} \mid \texttt{Int32} \mid \top \mid \bot \mid \Pi x: A.\ B \mid \forall (X >: L <: U).\ A \mid \Sigma x: A.\ B \mid A + B \mid \lbrace  x : A \mid b \rbrace \mid A \lor B \mid A \land B \mid \mu X.\ A \\
a, b, f &::= c \mid x \mid \lambda x: A.\ b \mid \Lambda (X >: L <: U).\ b \mid f\ a \mid f[A] \mid \texttt{let}\ x : A = b\ \texttt{in}\ a \mid (a_1, a_2) \mid \texttt{match}\ a\ \texttt{with}\ (x, y) \Rightarrow b \mid \texttt{inl}[B]\ a \mid \texttt{inr}[A]\ a \mid \texttt{match}\ a\ \texttt{with}\ \texttt{inl}(x) \Rightarrow b_l \mid \texttt{inr}(y) \Rightarrow b_r \mid a\ \mathit{op}\ b \mid \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2 \mid \texttt{diverge} \mid \texttt{loop}\ a\ b \\
\mathit{op} &::= \texttt{==} \mid \texttt{!=} \mid \texttt{<} \mid \texttt{<=} \mid \texttt{>=} \mid \texttt{>} \mid \texttt{\&\&} \mid \texttt{||} \mid \texttt{+} \mid \texttt{-} \mid \texttt{*} \mid \texttt{/} \mid \texttt{\%} \\
v &::= c \mid (v_1, v_2) \mid \texttt{inl}(v) \mid \texttt{inr}(v) \mid \langle \rho, \lambda x.\ b \rangle \mid \langle \rho, \Lambda (X >: L <: U).\ b  \rangle \\
\rho &::= \varnothing \mid \rho, x \mapsto v
\end{aligned}
```

A value environment $\rho$ maps variables to values. Closures $\langle \rho, \lambda x.\ b \rangle$ and $\langle \rho, \Lambda (X >: L <: U).\ b \rangle$ capture the environment at the point of their creation.

[`Syntax.v`](Syntax.v) defines `Ty` (types), `Term` (terms), and `Value` (values). Bindings use de Bruijn indices.

## Operational semantics

The big-step evaluation relation $\rho \vdash a \Downarrow v$ relates a value environment $\rho$ and a term $a$ to its result value $v$.

```math
\frac{}{\rho \vdash c \Downarrow c}
\qquad
\frac{x \mapsto v \in \rho}{\rho \vdash x \Downarrow v}
```

```math
\frac{}{\rho \vdash \lambda x.\ b \Downarrow \langle \rho, \lambda x.\ b \rangle}
\qquad
\frac{}{\rho \vdash \Lambda (X >: L <: U).\ b \Downarrow \langle \rho, \Lambda (X >: L <: U).\ b \rangle}
```

```math
\frac{\rho \vdash f \Downarrow \langle \rho_f, \lambda x.\ b \rangle \qquad \rho \vdash a \Downarrow v_a \qquad \rho_f, x \mapsto v_a \vdash b \Downarrow v}{\rho \vdash f\ a \Downarrow v}
```

```math
\frac{\rho \vdash f \Downarrow \langle \rho_f, \Lambda (X >: L <: U).\ b \rangle \qquad \rho_f \vdash b \Downarrow v}{\rho \vdash f[A] \Downarrow v}
```

```math
\frac{\rho \vdash a \Downarrow v_a \qquad \rho, x \mapsto v_a \vdash b \Downarrow v}{\rho \vdash \texttt{let}\ x : A = a\ \texttt{in}\ b \Downarrow v}
```

```math
\frac{\rho \vdash a_1 \Downarrow v_1 \qquad \rho \vdash a_2 \Downarrow v_2}{\rho \vdash (a_1, a_2) \Downarrow (v_1, v_2)}
\qquad
\frac{\rho \vdash a \Downarrow (v_1, v_2) \qquad \rho, x \mapsto v_1, y \mapsto v_2 \vdash b \Downarrow v}{\rho \vdash \texttt{match}\ a\ \texttt{with}\ (x, y) \Rightarrow b \Downarrow v}
```

```math
\frac{\rho \vdash a \Downarrow v_a \qquad \rho \vdash b \Downarrow v_b \qquad \delta(\mathit{op}, v_a, v_b) = r}{\rho \vdash a\ \mathit{op}\ b \Downarrow r}
```

```math
\frac{\rho \vdash a \Downarrow \texttt{true} \qquad \rho \vdash b_1 \Downarrow v}{\rho \vdash \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2 \Downarrow v}
\qquad
\frac{\rho \vdash a \Downarrow \texttt{false} \qquad \rho \vdash b_2 \Downarrow v}{\rho \vdash \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2 \Downarrow v}
```

```math
\frac{\rho \vdash a \Downarrow v}{\rho \vdash \texttt{inl}[B]\ a \Downarrow \texttt{inl}(v)}
\qquad
\frac{\rho \vdash a \Downarrow v}{\rho \vdash \texttt{inr}[A]\ a \Downarrow \texttt{inr}(v)}
```

```math
\frac{\rho \vdash a \Downarrow \texttt{inl}(v) \qquad \rho, x \mapsto v \vdash b_l \Downarrow w}{\rho \vdash \texttt{match}\ a\ \texttt{with}\ \texttt{inl}(x) \Rightarrow b_l \mid \texttt{inr}(y) \Rightarrow b_r \Downarrow w}
\qquad
\frac{\rho \vdash a \Downarrow \texttt{inr}(v) \qquad \rho, y \mapsto v \vdash b_r \Downarrow w}{\rho \vdash \texttt{match}\ a\ \texttt{with}\ \texttt{inl}(x) \Rightarrow b_l \mid \texttt{inr}(y) \Rightarrow b_r \Downarrow w}
```

```math
\frac{\rho \vdash a \Downarrow v_0 \qquad \rho, x \mapsto v_0 \vdash b \Downarrow \texttt{inr}(v)}{\rho \vdash \texttt{loop}\ a\ b \Downarrow v}
\qquad
\frac{\rho \vdash a \Downarrow v_0 \qquad \rho, x \mapsto v_0 \vdash b \Downarrow \texttt{inl}(v_1) \qquad \rho \vdash \texttt{loop}\ v_1\ b \Downarrow v}{\rho \vdash \texttt{loop}\ a\ b \Downarrow v}
```

The $\texttt{diverge}$ term has no evaluation rule: it always loops and never produces a value.

where $\delta$ evaluates binary operations on values: equality and inequality on all first-order values, ordering comparisons on naturals and integers, logical operations on booleans, and arithmetic ($+$, $-$, $\times$, $/$, $\%$) on naturals and integers. Comparison and logical operations return a boolean; arithmetic operations return a value of the same numeric type as the operands. Int32 arithmetic uses signed 32-bit wrapping semantics (results are mapped to $[-2^{31}, 2^{31})$).

[`Eval.v`](Eval.v) defines the corresponding fuel-based definitional interpreter. It returns `option (option Value)`: `None` for timeout, `Some None` for runtime error, `Some (Some v)` for successful evaluation. Loop iteration is handled by a separate `run_loop` function that takes a step function and iterates: `inr(v)` signals loop exit (returning `v`), `inl(v)` signals continue (recurring with `v`).

## Type interpretation

A semantic type is a predicate on values. The interpretation $⟦ A ⟧_{\delta}^{\rho}$ maps a syntactic type $A$ to a semantic type, given a type variable environment $\delta$ (mapping type variables to semantic types) and a value environment $\rho$.

```math
\begin{aligned}
⟦ X ⟧_{\delta}^{\rho}(v) &= \delta(X) \\
⟦ \texttt{Unit} ⟧_{\delta}^{\rho}(v) &= v = \texttt{unit} \\
⟦ \texttt{Bool} ⟧_{\delta}^{\rho}(v) &= v = \texttt{true} \lor v = \texttt{false} \\
⟦ \texttt{Int32} ⟧_{\delta}^{\rho}(v) &= \exists z.\ v = z \\
⟦ \Pi x: A.\ B ⟧_{\delta}^{\rho}(v) &= \exists \rho_f, b.\ v = \langle \rho_f, \lambda x.\ b \rangle \land \forall v_a.\ ⟦ A ⟧_{\delta}^{\rho}(v_a) \implies \forall v'. \left( \rho_f, x \mapsto v_a \vdash b \Downarrow v' \implies ⟦ B ⟧_{\delta}^{\rho, x \mapsto v_a}(v') \right) \\
⟦ \forall (X >: L <: U).\ B ⟧_{\delta}^{\rho}(v) &= \exists \rho_f, b.\ v = \langle \rho_f, \Lambda (X >: L <: U).\ b \rangle \land \forall A.\ ⟦ L ⟧_{\delta}^{\rho} \subseteq A \implies A \subseteq ⟦ U ⟧_{\delta}^{\rho} \implies \forall v'. \left( \rho_f \vdash b \Downarrow v' \implies ⟦ B ⟧_{\delta, X \mapsto A}^{\rho}(v') \right) \\
⟦ \Sigma x: A.\ B ⟧_{\delta}^{\rho}(v) &= \exists v_1, v_2.\ v = (v_1, v_2) \land ⟦ A ⟧_{\delta}^{\rho}(v_1) \land ⟦ B ⟧_{\delta}^{\rho, x \mapsto v_1}(v_2) \\
⟦ A + B ⟧_{\delta}^{\rho}(v) &= (\exists w.\ v = \texttt{inl}(w) \land ⟦ A ⟧_{\delta}^{\rho}(w)) \lor (\exists w.\ v = \texttt{inr}(w) \land ⟦ B ⟧_{\delta}^{\rho}(w)) \\
⟦ \lbrace  x : A \mid p \rbrace  ⟧_{\delta}^{\rho}(v) &= ⟦ A ⟧_{\delta}^{\rho}(v) \land \left(\forall w.\ \rho, x \mapsto v \vdash p \Downarrow w \implies w = \texttt{true}\right) \\
⟦ A \lor B ⟧_{\delta}^{\rho}(v) &= ⟦ A ⟧_{\delta}^{\rho}(v) \lor ⟦ B ⟧_{\delta}^{\rho}(v) \\
⟦ A \land B ⟧_{\delta}^{\rho}(v) &= ⟦ A ⟧_{\delta}^{\rho}(v) \land ⟦ B ⟧_{\delta}^{\rho}(v) \\
⟦ \mu X.\ A ⟧_{\delta}^{\rho}(v) &= \forall n.\ \mu_n(\lambda S.\ ⟦ A ⟧_{\delta, X \mapsto S}^{\rho})(v) \\
⟦ \top ⟧_{\delta}^{\rho}(v) &= \top \\
⟦ \bot ⟧_{\delta}^{\rho}(v) &= \bot
\end{aligned}
```

where the step-indexed approximation $\mu_n(F)$ is defined by:

```math
\begin{aligned}
\mu_0(F)(v) &= \top \\
\mu_{n+1}(F)(v) &= F(\mu_n(F))(v)
\end{aligned}
```

[`Interp.v`](Interp.v) defines an `interp` function implementing this interpretation, `interp_mu` for the step-indexed recursive type approximation, and `term_has_semtype` for the partial-correctness typing judgment used in function/universal types and refinements.

## Semantic typing

A typing context $\Gamma$ contains type bindings $x : A$, type variable bounds $L <: X <: U$, and equality facts $a_1 \sim a_2$:

```math
\begin{aligned}
\Gamma &::= \varnothing \\
       &\mid \Gamma, x : A \\
       &\mid \Gamma, L <: X <: U \\
       &\mid \Gamma, a_1 \sim a_2
\end{aligned}
```

A value environment $\rho$ is well-formed with respect to $\Gamma$ under $\delta$, written $\text{wf}(\delta, \Gamma, \rho)$, when for each type binding $x : A$ in $\Gamma$, we have $⟦ A ⟧_{\delta}^{\rho}(\rho(x))$; for each type variable bound $L <: X <: U$ in $\Gamma$, we have $⟦ L ⟧ \subseteq \delta(X) \subseteq ⟦ U ⟧$; and for each fact $a_1 \sim a_2$, the two terms evaluate to the same value (each in its own scoped environment suffix).

A term $a$ has semantic type $A$ under context $\Gamma$, written $\Gamma \vDash a : A$, if for all well-formed environments, whenever the evaluation of $a$ terminates, the result satisfies $A$ (partial correctness):

```math
\Gamma \vDash a : A \iff \forall \delta, \rho.\ \text{wf}(\delta, \Gamma, \rho) \implies \forall v.\ \rho \vdash a \Downarrow v \implies ⟦ A ⟧_{\delta}^{\rho}(v)
```

The following typing rules are proven sound with respect to this semantic typing judgment:

```math
\frac{}{\Gamma \vDash \texttt{unit} : \texttt{Unit}}
\qquad
\frac{}{\Gamma \vDash \texttt{true} : \texttt{Bool}}
\qquad
\frac{}{\Gamma \vDash \texttt{false} : \texttt{Bool}}
\qquad
\frac{}{\Gamma \vDash z : \texttt{Int32}}
\qquad
\frac{}{\Gamma \vDash \texttt{diverge} : \bot}
```

```math
\frac{x: A \in \Gamma}{\Gamma \vDash x : A}
```

```math
\frac{\Gamma, x : A \vDash b : B}{\Gamma \vDash \lambda x: A.\ b : \Pi x: A.\ B}
\qquad
\frac{\Gamma \vDash f : \Pi x: A.\ B \qquad \Gamma \vDash y : A}{\Gamma \vDash f\ y : B[x \mapsto y]}
```

```math
\frac{\Gamma, L <: X <: U \vDash b : B}{\Gamma \vDash \Lambda (X >: L <: U).\ b : \forall (X >: L <: U).\ B}
\qquad
\frac{\Gamma \vDash f : \forall (X >: L <: U).\ B \qquad \Gamma \vDash L <: A \qquad \Gamma \vDash A <: U}{\Gamma \vDash f[A] : B[X \mapsto A]}
```

```math
\frac{\Gamma \vDash a : A \qquad \Gamma, x : A, x \sim a \vDash b : B}{\Gamma \vDash \texttt{let}\ x : A = a\ \texttt{in}\ b : \text{avoid}(B, x)}
\text{(T-Let)}
```

```math
\frac{\Gamma \vDash y : A \qquad \Gamma \vDash a_2 : B}{\Gamma \vDash (y, a_2) : \Sigma x: A.\ B[y \mapsto x]}
\text{(T-Pair)}
```

```math
\frac{\Gamma \vDash a : \Sigma x: A.\ B \qquad \Gamma, x : A, y : B \vDash b : C}{\Gamma \vDash \texttt{match}\ a\ \texttt{with}\ (x, y) \Rightarrow b : \text{avoid}(\text{avoid}(C, y), x)}
\text{(T-MatchPair)}
```

```math
\frac{\Gamma \vDash a : A \qquad \Gamma \vDash b : A \qquad \text{compat}(\mathit{op}, A)}{\Gamma \vDash a\ \mathit{op}\ b : \text{result}(\mathit{op}, A)}
\text{(T-BinOp)}
```

where $\text{compat}(\mathit{op}, A)$ holds when: $A$ is first-order for `==`/`!=`; $A$ is `Int32` (or a refinement thereof) for `<`/`<=`/`>=`/`>`/`+`/`-`/`*`/`/`/`%`; and $A$ is `Bool` for `&&`/`||`. Refinement types inherit compatibility from their base type. The result type $\text{result}(\mathit{op}, A)$ is `Bool` for comparison and logical operations, and $\text{base}(A)$ (i.e., $A$ with refinements stripped) for arithmetic operations.

```math
\frac{\Gamma \vDash a : \texttt{Bool} \qquad \Gamma, a \sim \texttt{true} \vDash b_1 : B_1 \qquad \Gamma, a \sim \texttt{false} \vDash b_2 : B_2}{\Gamma \vDash \texttt{if}\ a\ \texttt{then}\ b_1\ \texttt{else}\ b_2 : B_1 \lor B_2}
\text{(T-If)}
```

```math
\frac{\Gamma \vDash a : A}{\Gamma \vDash \texttt{inl}[B]\ a : A + B}
\text{(T-Inl)}
\qquad
\frac{\Gamma \vDash a : B}{\Gamma \vDash \texttt{inr}[A]\ a : A + B}
\text{(T-Inr)}
```

```math
\frac{\Gamma \vDash a : A_1 + A_2 \qquad \Gamma, x : A_1, a = \texttt{inl}(x) \vDash b_1 : B_1 \qquad \Gamma, x : A_2, a = \texttt{inr}(x) \vDash b_2 : B_2}{\Gamma \vDash \texttt{match}\ a\ \texttt{with}\ \texttt{inl}(x) \Rightarrow b_1 \mid \texttt{inr}(x) \Rightarrow b_2 : \text{avoid}(B_1, x) \mid \text{avoid}(B_2, x)}
\text{(T-MatchSum)}
```

```math
\frac{\Gamma \vDash a : A \qquad \Gamma, x : A \vDash b : A + B}{\Gamma \vDash \texttt{loop}\ a\ b : B}
\text{(T-Loop)}
```

```math
\frac{\Gamma \vDash a : A \qquad \text{firstorder}(A)}{\Gamma \vDash a : \lbrace  x : A \mid x == a \rbrace }
\text{(T-Self)}
```

```math
\frac{\Gamma \vDash a : A \qquad \Gamma \vDash A <: B}{\Gamma \vDash a : B}
\text{(T-Sub)}
```

where $\text{spos}(X, A)$ holds when type variable $X$ appears only in strictly positive positions in $A$ (never to the left of a function arrow); $\text{avoid}(B, x)$ removes occurrences of term variable $x$ from $B$ by approximating refinement predicates (with $\texttt{true}$ or $\texttt{false}$ depending on polarity) and approximating ill-formed recursive types to $\top$ or $\bot$; and $\text{firstorder}(A)$ holds when $A$ is $\texttt{Unit}$, $\texttt{Bool}$, $\texttt{Int32}$, or a refinement $\lbrace x : B \mid p \rbrace$ of a first-order type $B$.

[`SemanticTyping.v`](SemanticTyping.v) defines `sem_typed` for the semantic typing judgment and proves lemmas corresponding to each of the above typing rules.

## Semantic subtyping

A type $A$ is a semantic subtype of $B$ under context $\Gamma$, written $\Gamma \vDash A <: B$, if for all well-formed environments:

```math
\Gamma \vDash A <: B \iff \forall \delta, \rho.\ \text{wf}(\delta, \Gamma, \rho) \implies \forall v.\ ⟦ A ⟧_{\delta}^{\rho}(v) \implies ⟦ B ⟧_{\delta}^{\rho}(v)
```

The following subtyping rules are proven sound with respect to this semantic subtyping judgment:

```math
\frac{}{\Gamma \vDash A <: A}
\text{(S-Refl)}
\qquad
\frac{\Gamma \vDash A <: B \qquad \Gamma \vDash B <: C}{\Gamma \vDash A <: C}
\text{(S-Trans)}
```

```math
\frac{\Gamma \vDash B_1 <: A_1 \qquad \Gamma, x : A_1 \vDash A_2 <: B_2}{\Gamma \vDash \Pi x: A_1.\ A_2 <: \Pi x: B_1.\ B_2}
\text{(S-Fun)}
\qquad
\frac{\Gamma \vDash L_1 <: L_2 \qquad \Gamma \vDash U_2 <: U_1 \qquad \Gamma, L_2 <: X <: U_2 \vDash A <: B}{\Gamma \vDash \forall (X >: L_1 <: U_1).\ A <: \forall (X >: L_2 <: U_2).\ B}
\text{(S-Forall)}
```

```math
\frac{\Gamma \vDash A_1 <: B_1 \qquad \Gamma, x : A_1 \vDash A_2 <: B_2}{\Gamma \vDash \Sigma x: A_1.\ A_2 <: \Sigma x: B_1.\ B_2}
\text{(S-Sigma)}
```

```math
\frac{}{\Gamma \vDash A <: A \lor B}
\text{(S-OrL)}
\qquad
\frac{}{\Gamma \vDash B <: A \lor B}
\text{(S-OrR)}
\qquad
\frac{\Gamma \vDash A <: C \qquad \Gamma \vDash B <: C}{\Gamma \vDash A \lor B <: C}
\text{(S-Or)}
```

```math
\frac{}{\Gamma \vDash A \land B <: A}
\text{(S-AndL)}
\qquad
\frac{}{\Gamma \vDash A \land B <: B}
\text{(S-AndR)}
\qquad
\frac{\Gamma \vDash C <: A \qquad \Gamma \vDash C <: B}{\Gamma \vDash C <: A \land B}
\text{(S-And)}
```

```math
\frac{}{\Gamma \vDash \lbrace x : A \mid p \rbrace <: A}
\text{(S-RefineBase)}
```

```math
\frac{\Gamma \vDash A <: B \qquad \Gamma, x : A \vDash p_1 \Rightarrow p_2}{\Gamma \vDash \lbrace x : A \mid p_1 \rbrace <: \lbrace x : B \mid p_2 \rbrace}
\text{(S-Refine)}
```

```math
\frac{}{\Gamma \vDash A <: \top}
\text{(S-Top)}
\qquad
\frac{}{\Gamma \vDash \bot <: A}
\text{(S-Bot)}
```

```math
\frac{L <: X <: U \in \Gamma}{\Gamma \vDash L <: X}
\text{(S-TVar-Lower)}
\qquad
\frac{L <: X <: U \in \Gamma}{\Gamma \vDash X <: U}
\text{(S-TVar-Upper)}
```

```math
\frac{\text{spos}(X, A)}{\Gamma \vDash \mu X.\ A <: A[X \mapsto \mu X.\ A]}
\text{(S-Mu-Unfold)}
\qquad
\frac{\text{spos}(X, A)}{\Gamma \vDash A[X \mapsto \mu X.\ A] <: \mu X.\ A}
\text{(S-Mu-Fold)}
```

[`SemanticSubtyping.v`](SemanticSubtyping.v) defines `sem_subtype` for the semantic subtyping judgment and proves lemmas corresponding to each of the above subtyping rules.

## Semantic implication

A term $p_1$ semantically implies $p_2$ under context $\Gamma$, written $\Gamma \vDash p_1 \Rightarrow p_2$, if for all well-formed environments, $p_1$ evaluating to true implies $p_2$ evaluates to true:

```math
\Gamma \vDash p_1 \Rightarrow p_2 \iff \forall \delta, \rho.\ \text{wf}(\delta, \Gamma, \rho) \implies \rho \vdash p_1 \Downarrow \texttt{true} \implies \rho \vdash p_2 \Downarrow \texttt{true}
```

[`SemanticImplies.v`](SemanticImplies.v) defines `sem_implies` for this judgment.

## Next steps

- [x] Add `unit`
- [x] Equality (needed for next steps)
- [x] Let-bindings
- [x] Selfification
- [x] Let typing rule with equality witness
- [x] If-then-else
- [x] Subtyping
- [x] Union and intersection types
- [x] Loops
- [x] Recursive types (positive equi-recursive with subtyping)
- [x] Products (sigma types)
- [x] Sum types
- [x] Partial correctness (universal form for `term_has_semtype`)

## Build

```bash
rocq makefile -f _CoqProject -o Makefile
make
```

## References

- [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3093333.3009866)  
  Nada Amin and Tiark Rompf, POPL 2017

- [A Logical Approach to Type Soundness](https://doi.org/10.1145/3676954)  
  Amin Timany, Robbert Krebbers, Derek Dreyer, and Lars Birkedal, Journal of the ACM 2024

- [System FR](https://doi.org/10.1145/3360592)  
  Jad Hamza, Nicolas Voirol, and Viktor Kunčak, OOPSLA 2019

- [Mechanizing Refinement Types](https://doi.org/10.1145/3632912)  
  Michael H. Borkowski, Niki Vazou, and Ranjit Jhala, POPL 2024
