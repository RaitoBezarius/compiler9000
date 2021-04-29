import Lean

inductive LambdaTerm where
| num (val : Nat)
| app (fn: LambdaTerm) (arg: LambdaTerm)
| lambda (body: LambdaTerm)

-- Q1.2
def allFreeVariablesBoundBy (n: Nat) (t: LambdaTerm): Prop :=
  aux n t 0
where
  aux n t depth : Prop := match t with
| LambdaTerm.num (val := m) => m <= n ∨ m <= depth
| LambdaTerm.app (fn := fn) (arg := arg) => aux n fn depth ∧ aux n arg depth
| LambdaTerm.lambda (body := fn) => aux n fn (depth + 1)
theorem allFreeVariablesBoundBy.auxRec (t: LambdaTerm): ∀ n d: Nat, (allFreeVariablesBoundBy.aux n t d -> allFreeVariablesBoundBy.aux (Nat.succ n) t d) := sorry

macro "C[" n:term "](" t:term ")" : term => `(allFreeVariablesBoundBy $n $t)
def isClosedTerm (t: LambdaTerm): Prop := C[0](t)

theorem isClosedTerm.FVBoundness (t: LambdaTerm) (h: isClosedTerm t): ∀ n: Nat, C[n](t) := by
intro n
induction n with
| zero => assumption
| succ m ih => match t with
    | LambdaTerm.num (val := p) => cases ih with
      | inl h =>
        apply Or.inl
        apply Nat.leOfLt (Nat.lt_succ_of_le _)
        assumption -- p ≤ m, therefore p ≤ m + 1.
      | inr h => apply Or.inr; assumption -- p ≤ 0, therefore p ≤ 0.
    | LambdaTerm.app (fn := fn) (arg := arg) => apply And.intro ; exact allFreeVariablesBoundBy.auxRec _ _ _ ih.1 ; exact allFreeVariablesBoundBy.auxRec _ _ _ ih.2
    | LambdaTerm.lambda (body := fn) => admit -- λ ⋅ body

-- Q1.3
def substitute (t: LambdaTerm) (index: Nat) (expr: LambdaTerm): LambdaTerm := sorry
theorem closedTermSubstitutedEqClosedTerm (t: LambdaTerm) (h: isClosedTerm t) (index: Nat) (expr: LambdaTerm): substitute t index expr = t := sorry

-- Q1.4
def batchSubstitute (t: LambdaTerm) (startIndex: Nat) (exprs: List LambdaTerm): LambdaTerm := sorry
-- theorem isClosedTerm.batchSubstitution (t: )
-- case 0: t[] = t
-- case 1: allFreeVariablesBoundBy i t → batchSubstitute t i [u] = t
-- case 2: forall k ≥ 1, allFreeVariablesBoundBy i u_k, batchSubstitute t i [ u_0 … u_n] = substitute i u_0 (batchSubstitute t (i + 1) [ u_1 … u_n ])