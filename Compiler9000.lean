import Lean

inductive LambdaTerm where
| num (val : Nat)
| app (fn: LambdaTerm) (arg: LambdaTerm)
| lambda (body: LambdaTerm)

-- Q1.2
def allFreeVariablesBoundBy : Nat -> LambdaTerm -> Bool
| (n: Nat), LambdaTerm.num (val := m) => m <= n
| (n: Nat), LambdaTerm.app (fn := fn) (arg := arg) => allFreeVariablesBoundBy n fn && allFreeVariablesBoundBy n arg
| (n: Nat), LambdaTerm.lambda (body := t) => allFreeVariablesBoundBy n t

def isClosedTerm (t: LambdaTerm): Prop := sorry
theorem isClosedTermOfFreeVariablesBoundness (n: Nat) (t: LambdaTerm) (h: allFreeVariablesBoundBy n t): isClosedTerm t := sorry

-- Q1.3
def substitute (t: LambdaTerm) (index: Nat) (expr: LambdaTerm): LambdaTerm := sorry
theorem closedTermSubstitutedEqClosedTerm (t: LambdaTerm) (h: isClosedTerm t) (index: Nat) (expr: LambdaTerm): substitute t index expr = t := sorry

-- Q1.4
def batchSubstitute (t: LambdaTerm) (startIndex: Nat) (exprs: List LambdaTerm): LambdaTerm := sorry
-- theorem isClosedTerm.batchSubstitution (t: )
-- case 0: t[] = t
-- case 1: allFreeVariablesBoundBy i t → batchSubstitute t i [u] = t
-- case 2: forall k ≥ 1, allFreeVariablesBoundBy i u_k, batchSubstitute t i [ u_0 … u_n] = substitute i u_0 (batchSubstitute t (i + 1) [ u_1 … u_n ])