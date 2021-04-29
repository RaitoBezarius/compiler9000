import Lean
open Classical

-- For Core / standard library?
theorem Nat.neOfLt {n m: Nat} (h: n < m): n ≠ m :=
by
intro heq
rw heq at h
exact Nat.ltIrrefl _ h
theorem Nat.ltAddRight {n m k: Nat} (h: n < m): n < m + k := sorry
theorem Nat.ltAddLeft {n m k: Nat} (h: n < m): n < k + m := sorry

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
| var m => apply Nat.ltTrans hn (Nat.addLtAddRight (Nat.lt.base _) _)
| app fn arg h_fn h_arg => exact ⟨ h_fn _ hn.1, h_arg _ hn.2 ⟩
| lambda body h_body => exact h_body _ hn

theorem allFreeVariablesBoundBy.auxRec₂ {t: LambdaTerm}: ∀ {n d: Nat}, (allFreeVariablesBoundBy.aux (n + 1) t d <-> allFreeVariablesBoundBy.aux n t (d + 1)) :=
by intro n d; induction t generalizing d with
| var v =>
  simp [aux]
  rw [Nat.add_assoc, Nat.add_comm 1 d]
  exact Iff.rfl
| app fn arg h_fn h_arg =>
  simp [aux]
  exact Iff.intro
    (fun H => ⟨ h_fn.1 H.1, h_arg.1 H.2 ⟩)
    (fun H => ⟨ h_fn.2 H.1, h_arg.2 H.2 ⟩)
| lambda body h_body =>
  simp [aux]
  exact Iff.intro
    (fun H => (@h_body (d + 1)).1 H)
    (fun H => (@h_body (d + 1)).2 H)

theorem allFreeVariablesBoundBy.lambda {t: LambdaTerm}: ∀ {n: Nat}, allFreeVariablesBoundBy n (LambdaTerm.lambda t) -> allFreeVariablesBoundBy (n + 1) t :=
by intro n hn; exact allFreeVariablesBoundBy.auxRec₂.2 hn


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

theorem substitute.idOnClosed (depth: Nat) (t: LambdaTerm) (ht: C[depth](t)) (index: Nat) (expr: LambdaTerm) (hexpr: isClosedTerm expr): substitute.aux expr index t depth = t :=
by induction t generalizing depth with
| var m => simp [allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux] at ht; have p: index + depth ≠ m := (Nat.neOfLt $ Nat.ltAddLeft ht).symm; simp [aux, p];
| app fn arg h_fn h_arg => simp [aux, h_fn depth (ht.1), h_arg depth (ht.2)]
| lambda body h_body => simp [aux, h_body (depth + 1) (allFreeVariablesBoundBy.lambda ht)]

-- Q1.4
def batchSubstitute (t: LambdaTerm) (startIndex: Nat) (exprs: List LambdaTerm): LambdaTerm := sorry
-- theorem isClosedTerm.batchSubstitution (t: )
-- case 0: t[] = t
-- case 1: allFreeVariablesBoundBy i t → batchSubstitute t i [u] = t
-- case 2: forall k ≥ 1, allFreeVariablesBoundBy i u_k, batchSubstitute t i [ u_0 … u_n] = substitute i u_0 (batchSubstitute t (i + 1) [ u_1 … u_n ])