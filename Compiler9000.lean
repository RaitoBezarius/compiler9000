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
deriving Inhabited

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
  simp only [aux]
  rw [Nat.add_assoc, Nat.add_comm 1 d]
  exact Iff.rfl
| app fn arg h_fn h_arg =>
  exact Iff.intro
    (fun H => ⟨ h_fn.1 H.1, h_arg.1 H.2 ⟩)
    (fun H => ⟨ h_fn.2 H.1, h_arg.2 H.2 ⟩)
| lambda body h_body =>
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
| var m => have neg: index + depth ≠ m := (Nat.neOfLt $ Nat.ltAddLeft ht).symm; simp [aux, neg];
| app fn arg h_fn h_arg => simp [aux, h_fn depth (ht.1), h_arg depth (ht.2)]
| lambda body h_body => simp [aux, h_body (depth + 1) (allFreeVariablesBoundBy.lambda ht)]

-- Q1.4
def batchSubstitute (t: LambdaTerm) (startIndex: Nat) (exprs: List LambdaTerm): LambdaTerm := sorry
-- theorem isClosedTerm.batchSubstitution (t: )
-- case 0: t[] = t
-- case 1: allFreeVariablesBoundBy i t → batchSubstitute t i [u] = t
-- case 2: forall k ≥ 1, allFreeVariablesBoundBy i u_k, batchSubstitute t i [ u_0 … u_n] = substitute i u_0 (batchSubstitute t (i + 1) [ u_1 … u_n ])


-- Part 2
-- Q2.1
inductive SmallStepBetaReduction: LambdaTerm -> LambdaTerm -> Prop :=
| Eval : ∀ (u v: LambdaTerm), SmallStepBetaReduction (LambdaTerm.app (LambdaTerm.lambda u) v) (substitute t 0 u)
| LeftContext : ∀ (u v t: LambdaTerm), SmallStepBetaReduction t u -> SmallStepBetaReduction (LambdaTerm.app t v) (LambdaTerm.app u v)
| RightContext : ∀ (t u v : LambdaTerm), SmallStepBetaReduction t u -> SmallStepBetaReduction (LambdaTerm.app v t) (LambdaTerm.app v u)
| LambdaContext : ∀ (t u : LambdaTerm), SmallStepBetaReduction t u -> SmallStepBetaReduction (LambdaTerm.lambda t) (LambdaTerm.lambda u)

-- Q2.2
inductive BetaReduction: LambdaTerm -> LambdaTerm -> Prop :=
| Rfl (u: LambdaTerm): BetaReduction u u
| Trans (t u v: LambdaTerm): SmallStepBetaReduction t u -> BetaReduction u v -> BetaReduction t v

-- Q2.3
theorem BetaReduction.subterms.reduceAux1 (t u v: LambdaTerm):
  BetaReduction t u -> BetaReduction (LambdaTerm.app t v) (LambdaTerm.app u v) :=
fun h_red => by induction h_red with
| Rfl => exact BetaReduction.Rfl _
| Trans w x y h_smallstep h_step₁ h_step₂ =>
  -- TODO(Ryan): golf me.
  apply BetaReduction.Trans (LambdaTerm.app w v) (LambdaTerm.app x v)
  apply SmallStepBetaReduction.LeftContext
  assumption
  assumption


theorem BetaReduction.subterms.reduceAux2 (t u v: LambdaTerm):
  BetaReduction t u -> BetaReduction (LambdaTerm.app v t) (LambdaTerm.app v u) :=
fun h_red => by induction h_red with
| Rfl => exact BetaReduction.Rfl _
| Trans w x y h_smallstep h_step₁ h_step₂ =>
  -- TODO(Ryan): golf me.
  apply BetaReduction.Trans (LambdaTerm.app v w) (LambdaTerm.app v x)
  apply SmallStepBetaReduction.RightContext
  assumption
  assumption

theorem BetaReduction.subterms.reduceAux3 (t u: LambdaTerm):
  BetaReduction t u -> BetaReduction (LambdaTerm.lambda t) (LambdaTerm.lambda u) := 
fun h_red => by induction h_red with
| Rfl => exact BetaReduction.Rfl _
| Trans w x y h_smallstep h_step₁ h_step₂ =>
  -- TODO(Ryan): golf me.
  apply BetaReduction.Trans (LambdaTerm.lambda w) (LambdaTerm.lambda x)
  apply SmallStepBetaReduction.LambdaContext
  assumption; assumption

-- Part 3
-- Q3.2
inductive KrivineInstruction
| Access (n: Nat)
| Grab (next: KrivineInstruction)
| Push (next: KrivineInstruction) (continuation: KrivineInstruction)

inductive KrivineClosure
| pair (i: KrivineInstruction) (e: List KrivineClosure)

def KrivineEnv := List KrivineClosure
def KrivineStack := List KrivineClosure

-- TODO(Ryan): maybe, merge these two definitions?

structure KrivineState where
  code: KrivineInstruction
  env: KrivineEnv
  stack: KrivineStack

-- Q3.3
def evalKrivineMachine (state: KrivineState): Option KrivineState :=
match state.code, state.env, state.stack with
| KrivineInstruction.Access 0, (KrivineClosure.pair code recEnv :: closures), stack => some $ KrivineState.mk code recEnv stack
| KrivineInstruction.Access n, (KrivineClosure.pair code recEnv :: closures), stack => some $ KrivineState.mk (KrivineInstruction.Access (n - 1)) closures stack
| KrivineInstruction.Push c' c, env, stack => some $ KrivineState.mk c env (KrivineClosure.pair c' env :: stack)
| KrivineInstruction.Grab code, closures, (KrivineClosure.pair c₀ e₀ :: stack) => some $ KrivineState.mk code (KrivineClosure.pair c₀ e₀ :: closures) stack
| _, _, _ => none

-- Part 4
-- Q4.1
def compile_instr: LambdaTerm -> KrivineInstruction
| LambdaTerm.lambda t => KrivineInstruction.Grab (compile_instr t)
| LambdaTerm.app t u => KrivineInstruction.Push (compile_instr u) (compile_instr t)
| LambdaTerm.var n => KrivineInstruction.Access n

def compile : LambdaTerm -> KrivineState :=
fun t => KrivineState.mk (compile_instr t) [] []

-- Part 5

-- Q5.1
def compile.leftInv: KrivineInstruction -> LambdaTerm
| KrivineInstruction.Access n => LambdaTerm.var n
| KrivineInstruction.Push c' c => LambdaTerm.app (leftInv c) (leftInv c')
| KrivineInstruction.Grab c => LambdaTerm.lambda (leftInv c)

-- Q5.2
def compile.idOfLeftInv (t: LambdaTerm): compile.leftInv (compile_instr t) = t :=
by induction t with
| var n => rfl
| app fn arg h_fn h_arg => simp [compile.leftInv, h_fn, h_arg]
| lambda t ht => simp [compile.leftInv, ht]


def KrivineEnv.inv_rel: List KrivineEnv -> List KrivineEnv -> Prop := sorry
def KrivineEnv.inv_wf (x: List KrivineEnv): Acc inv_rel x := sorry

def List.max: List Nat → Nat
| [] => 0
| x :: q => Nat.max x (max q)

-- TODO: make sense of this.
/-def KrivineClosure.depth: KrivineClosure -> Nat
| KrivineClosure.pair _ e => 1 + List.max (List.map depth e)

def KrivineEnv.correct: KrivineEnv -> Prop
| [] => true
| KrivineClosure.pair c₀ e₀ :: closures => C[List.length e₀](compile.leftInv c₀) ∧ (correct e₀) ∧ (correct closures)

set_option codegen false in
@[implementedBy KrivineEnv.correctUnsafe]
def KrivineEnv.correct (lenv: List KrivineEnv): Prop :=
WellFounded.fixF (fun e correct => match e with
  | [] => true
  | KrivineEnv.Item c₀ e₀ :: env => C[List.length e₀](compile.left_inv c₀) ∧ (correct e₀ (sorry)) ∧ (correct env (sorry))
) lenv (inv_wf lenv)


def KrivineStack.correct: List KrivineStack -> Prop
| [] => true
| KrivineStack.Item c₀ e₀ :: stack => C[List.length stack](compile.left_inv c₀) && (KrivineEnv.correctUnsafe e₀) && (correct stack)

def KrivineState.correct (state: KrivineState): Prop :=
C[List.length state.env](compile.left_inv state.code) ∧ (KrivineEnv.correct state.env) ∧ (KrivineStack.correct state.stack)


def compile.inv.env: List KrivineEnv -> List LambdaTerm
| [] => []
| (KrivineEnv.Item code recEnv) :: e => (left_inv code) :: env e
-/
-- compose closures
--def compile.tau: KrivineState -> LambdaTerm
--| c, e, s => LambdaTerm.app (batchSubstitute (inv c) 0 (inv.env e)) (tau )

-- Q5.3
--theorem transitionCorrectness (state₀: KrivineState) (state₁: KrivineState)
--  (hTransition: evalKrivineMachine state₀ = state₁): KrivineState.correct state₀ -> KrivineState.correct state₁ := sorry

-- Q5.4
-- require the good definition of tau.
-- theorem simulationCorrectness (state₀: KrivineState) (state₁: KrivineState):
-- (evalKrivineMachine state₀ = state₁) -> KrivineState.correct state₀ -> SmallStepBetaReduction (compile.left_inv state₀) (compile.left_inv state₁) := sorry

-- Q5.5
-- theorem 