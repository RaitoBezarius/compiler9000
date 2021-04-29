import Lean

inductive LambdaTerm where
| var (val : Nat)
| app (fn: LambdaTerm) (arg: LambdaTerm)
| lambda (body: LambdaTerm)

-- Q1.2
def allFreeVariablesBoundBy (n: Nat) (t: LambdaTerm): Prop :=
  aux n t 0
where
  aux n t depth : Prop := match t with
| LambdaTerm.var (val := m) => m < n + depth
| LambdaTerm.app (fn := fn) (arg := arg) => aux n fn depth ∧ aux n arg depth
| LambdaTerm.lambda (body := fn) => aux n fn (depth + 1)

theorem allFreeVariablesBoundBy.auxRec (t: LambdaTerm): ∀ n d: Nat, (allFreeVariablesBoundBy.aux n t d -> allFreeVariablesBoundBy.aux (n + 1) t d) :=
fun n d hn => by induction t generalizing d with
| var m => admit -- todo kek
| app fn arg h_fn h_arg => exact ⟨ h_fn _ hn.1, h_arg _ hn.2 ⟩
| lambda body h_body => exact h_body _ hn

macro "C[" n:term "](" t:term ")" : term => `(allFreeVariablesBoundBy $n $t)
def isClosedTerm (t: LambdaTerm): Prop := C[0](t)

theorem isClosedTerm.FVBoundness (t: LambdaTerm) (h: isClosedTerm t): ∀ n: Nat, C[n](t) :=
fun n => by induction n with
| zero => assumption
| succ m ih => match t with
    | LambdaTerm.var (val := p) => exact allFreeVariablesBoundBy.auxRec _ _ _ ih
    | LambdaTerm.app (fn := fn) (arg := arg) => exact ⟨ allFreeVariablesBoundBy.auxRec _ _ _ ih.1, allFreeVariablesBoundBy.auxRec _ _ _ ih.2 ⟩
    | LambdaTerm.lambda (body := fn) => exact allFreeVariablesBoundBy.auxRec _ _ _ ih

-- Q1.3
def substitute (t: LambdaTerm) (index: Nat) (expr: LambdaTerm): LambdaTerm := 
  aux index t 0
where
  aux i t depth : LambdaTerm := match t with
  | LambdaTerm.var (val := m) => if i + depth = m then expr else t
  | LambdaTerm.app fn arg => LambdaTerm.app (aux i fn depth) (aux i arg depth)
  | LambdaTerm.lambda body => LambdaTerm.lambda (aux i body (depth + 1))

theorem Nat.neOfLt {n m: Nat} (h: n < m): n ≠ m := sorry

theorem substitute.idOnClosed (depth: Nat) (t: LambdaTerm) (ht: C[depth](t)) (index: Nat) (expr: LambdaTerm) (hexpr: isClosedTerm expr): substitute.aux t index expr depth = t :=
by induction t with
  -- ht: m < depth (en fait m < depth + 0)
  -- On a depth ≤ depth + index
  -- On obtient m ≠ depth + index
| var m => have p: index + depth ≠ m := sorry; admit
| app fn arg h_fn h_arg => admit
| lambda body h_body => admit

-- Q1.4
def batchSubstitute (t: LambdaTerm) (startIndex: Nat) (exprs: List LambdaTerm): LambdaTerm := sorry
-- theorem isClosedTerm.batchSubstitution (t: )
-- case 0: t[] = t
-- case 1: allFreeVariablesBoundBy i t → batchSubstitute t i [u] = t
-- case 2: forall k ≥ 1, allFreeVariablesBoundBy i u_k, batchSubstitute t i [ u_0 … u_n] = substitute i u_0 (batchSubstitute t (i + 1) [ u_1 … u_n ])