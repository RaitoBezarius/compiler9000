import Lean
open Classical

-- For Core / standard library?
theorem Nat.neOfLt {n m: Nat} (h: n < m): n ≠ m :=
by
intro heq;
rw [heq] at h
exact Nat.ltIrrefl _ h

theorem Nat.ltAddLeft {n m k: Nat} (h: n < m): n < k + m :=
by induction k with
    | zero => exact show n < 0 + m from (Nat.zero_add m).symm ▸ h
    | succ k h => exact succ_add k m ▸ leStep h
theorem Nat.ltAddRight {n m k: Nat} (h: n < m): n < m + k :=
  Nat.add_comm k m ▸ Nat.ltAddLeft h

theorem Nat.ltSuccMaxLeft {a b: Nat}: a < Nat.succ (Nat.max a b) := sorry
theorem Nat.ltSuccMaxRight {a b: Nat}: b < Nat.succ (Nat.max a b) := sorry
theorem Nat.succMaxEqMaxSucc {a b: Nat}: Nat.succ (Nat.max a b) = Nat.max (Nat.succ a) (Nat.succ b) := sorry

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

theorem boundedByFollowing (m : Nat) (h : C[n](t)) : C[n + m](t) :=
by induction m with
| zero => assumption
| succ m ih => match t with
    | LambdaTerm.var (val := p) => exact allFreeVariablesBoundBy.auxRec _ _ _ ih
    | LambdaTerm.app (fn := fn) (arg := arg) => exact ⟨ allFreeVariablesBoundBy.auxRec _ _ _ ih.1, allFreeVariablesBoundBy.auxRec _ _ _ ih.2 ⟩
    | LambdaTerm.lambda (body := fn) => exact allFreeVariablesBoundBy.auxRec _ _ _ ih

theorem boundByGreater (greater : n ≤ m) (h : C[n](t)) : C[m](t) :=
by match Nat.le.dest greater with
| ⟨ w, hw ⟩ =>
  rw [← hw]
  exact boundedByFollowing w h

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
def batchSubstitute (t : LambdaTerm) (index: Nat) (exprs : List LambdaTerm) : LambdaTerm :=
  aux t 0
where
  find (l : List (Nat × LambdaTerm)) depth m : LambdaTerm :=
    match l with
      | [] => LambdaTerm.var m
      | (i, expr) :: tail => if i + depth = m then expr else find tail depth m
  aux t depth : LambdaTerm := match t with
    | LambdaTerm.var (val := m) => find (List.enumFrom index exprs) depth m
    | LambdaTerm.app fn arg => LambdaTerm.app (aux fn depth) (aux arg depth)
    | LambdaTerm.lambda body => LambdaTerm.lambda (aux body (depth + 1))

macro t:term "[" i:term "←" l:term "]" : term => `(batchSubstitute $t $i $l)

theorem batchSubstituteFindSwap (index depth : Nat) (exprs : List LambdaTerm) :
  batchSubstitute.find (List.enumFrom index exprs) (depth + 1) m =
  batchSubstitute.find (List.enumFrom (index + 1) exprs) depth m :=
by induction exprs generalizing index with
  | nil => simp [batchSubstitute.find]
  | cons e t h =>
    have this : index + 1 + depth = index + (depth + 1) :=
    by rw [Nat.add_assoc, Nat.add_comm 1 depth]
    simp [batchSubstitute.find, this, h (index + 1)]

theorem batchSubstituteSwap (t : LambdaTerm) (l : List LambdaTerm) (i : Nat) (depth : Nat) :
  batchSubstitute.aux i l t (depth + 1) = batchSubstitute.aux (i + 1) l t depth :=
by induction t generalizing depth with
  | var m =>
    simp [batchSubstitute.aux, batchSubstituteFindSwap]
  | app fn arg h_fn h_arg => simp [batchSubstitute.aux, h_fn, h_arg]
  | lambda body h_body => simp [batchSubstitute.aux, h_body]

theorem substEmpty (t : LambdaTerm) {i : Nat} (depth : Nat) :
  t[i ← []] = t :=
by induction t generalizing i with
| var m => simp [batchSubstitute, batchSubstitute.aux, batchSubstitute.find]
| app fn arg h_fn h_arg =>
  simp only [batchSubstitute] at h_fn
  simp only [batchSubstitute] at h_arg
  simp [batchSubstitute, batchSubstitute.aux, h_fn, h_arg]
| lambda body h_body =>
  simp only [batchSubstitute] at h_body
  simp only [batchSubstitute, batchSubstitute.aux]
  rw [batchSubstituteSwap body [] i 0, h_body]

theorem substMinorized (h : C[i](t)) (l : List LambdaTerm) : t[i ← l] = t :=
by induction t generalizing i with
| var m =>
  simp [batchSubstitute, batchSubstitute.aux]
  suffices p : ∀ j, i ≤ j → batchSubstitute.find (List.enumFrom j l) 0 m = LambdaTerm.var m
  from p i (Nat.leRefl i)
  induction l with
  | nil =>
    intro j h'
    simp [batchSubstitute.find]
  | cons hd tl tl_h =>
    intro j h'
    simp [batchSubstitute.find]
    have p : j ≠ m := Nat.ltOfLtOfLe h h' |> Nat.neOfLt |> Ne.symm
    simp [p, tl_h (j + 1) (Nat.leStep h')]
| app fn arg h_fn h_arg =>
  simp only [batchSubstitute] at h_fn
  simp only [batchSubstitute] at h_arg
  simp [batchSubstitute, batchSubstitute.aux, h_fn h.1, h_arg h.2]
| lambda body h_body =>
  have p := h_body (allFreeVariablesBoundBy.auxRec₂.2 h)
  simp only [batchSubstitute] at p
  rw [← batchSubstituteSwap body l i 0] at p
  simp [batchSubstitute, batchSubstitute.aux, p]

theorem batchSubstituteFindLower (h : m < i) :
  batchSubstitute.find (List.enumFrom i l) 0 m = LambdaTerm.var m :=
by induction l generalizing i with
| nil => simp [batchSubstitute.find]
| cons hd tl h_tl =>
  simp only [Nat.add_zero, batchSubstitute.find, ifNeg $ Ne.symm $ Nat.neOfLt h]
  exact h_tl $ Nat.ltTrans h $ Nat.ltSuccSelf i

structure BoundedTerm (i : Nat) where
  t : LambdaTerm
  p : C[i](t)

theorem batchSubstituteFindMinorized (l : List (BoundedTerm i)) (i_le_j : i ≤ j) (depth m : Nat) :
  (λ result => result = LambdaTerm.var m ∨ C[i](result)) $
  batchSubstitute.find (List.enumFrom j (List.map (λ x => x.t) l)) depth m :=
by induction l generalizing j with
| nil => simp [batchSubstitute.find]
| cons hd tl h_tl =>
  simp only [batchSubstitute.find]
  byCases h : j + depth = m
  focus
    simp only [ifPos h]
    exact Or.inr hd.p
  focus
    simp only [ifNeg h]
    exact h_tl $ Nat.leTrans i_le_j $ Nat.leSucc j

theorem substRotate (t : LambdaTerm) {i : Nat} (hd : BoundedTerm i) (tl : List (BoundedTerm i)) :
  t[i ← hd.t :: List.map (λ x => x.t) tl] =
  t[(i + 1) ← List.map (λ x => x.t) tl][i ← [hd.t]] :=
by
  suffices p : ∀ j : Nat, i ≤ j →
    t[j ← hd.t :: List.map (λ x => x.t) tl] =
    t[(j + 1) ← List.map (λ x => x.t) tl][j ← [hd.t]]
  by exact p i (Nat.leRefl i)
  induction t with
  | var m =>
    intro j h
    simp only [batchSubstitute, batchSubstitute.aux, batchSubstitute.find, Nat.add_zero]
    byCases h₁ : m ≤ j
    focus
      rw [batchSubstituteFindLower (show m < j + 1 from Nat.ltOfLeOfLt h₁ $ Nat.ltSuccSelf j)]
      byCases h₂ : m = j
      simp [batchSubstitute.aux, batchSubstitute.find, h₂]
      simp [batchSubstitute.aux, batchSubstitute.find, Ne.symm h₂]
    focus
      have j_ne_m : j ≠ m := λ h' => h₁ $ Nat.leOfEq h'.symm
      have p := batchSubstituteFindMinorized tl (Nat.leTrans h $ Nat.leSucc j) 0 m
      simp at p
      cases p with
      | inl h => simp [h, batchSubstitute.aux, batchSubstitute.find, j_ne_m]
      | inr h' =>
        have p' : C[j](_) := boundByGreater h h'
        have p'' := substMinorized p' [hd.t]
        simp only [ifNeg j_ne_m]
        simp only [batchSubstitute] at p''
        rw [p'']
  | app fn arg h_fn h_arg =>
    intro j h
    simp [batchSubstitute] at h_fn
    simp [batchSubstitute] at h_arg
    simp [batchSubstitute, batchSubstitute.aux, h_fn j h, h_arg j h]
  | lambda body h_body =>
    intro j h
    simp only [batchSubstitute] at h_body
    simp only [batchSubstitute, batchSubstitute.aux, batchSubstituteSwap]
    rw [h_body (j + 1) (Nat.leTrans h $ Nat.leSucc j)]

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
  stack: KrivineEnv

instance : Inhabited KrivineState where
  default := { code := KrivineInstruction.Access 0, env := [], stack := [] }

-- Q3.3
@[reducible]
def evalKrivineMachine (state: KrivineState): Option KrivineState :=
match state.code, state.env, state.stack with
| KrivineInstruction.Access 0, (KrivineClosure.pair code recEnv :: closures), stack =>
  some $ KrivineState.mk code recEnv stack
| KrivineInstruction.Access n, (KrivineClosure.pair code recEnv :: closures), stack =>
  some $ KrivineState.mk (KrivineInstruction.Access (n - 1)) closures stack
| KrivineInstruction.Push c' c, env, stack =>
  some $ KrivineState.mk c env (KrivineClosure.pair c' env :: stack)
| KrivineInstruction.Grab code, closures, (KrivineClosure.pair c₀ e₀ :: stack) =>
  some $ KrivineState.mk code (KrivineClosure.pair c₀ e₀ :: closures) stack
| _, _, _ =>
  none

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

def compile.leftInv.env: KrivineEnv -> List LambdaTerm
| [] => []
| (KrivineClosure.pair code recEnv) :: e => (leftInv code) :: env e

-- def compile.undo: KrivineState -> LambdaTerm
-- | state =>
-- LambdaTerm.app
-- (batchSubstitute (leftInv state.code) 0 (leftInv.env state.env))

-- Q5.2
def compile.idOfLeftInv (t: LambdaTerm): compile.leftInv (compile_instr t) = t :=
by induction t with
| var n => rfl
| app fn arg h_fn h_arg => simp [compile.leftInv, h_fn, h_arg]
| lambda t ht => simp [compile.leftInv, ht]

def List.max: List Nat → Nat
| [] => 0
| x :: q => Nat.max x (max q)

partial def KrivineClosure.depthUnsafe: KrivineClosure -> Nat
| KrivineClosure.pair i env => List.max (List.map depthUnsafe env) + 1

set_option codegen false in
@[implementedBy KrivineClosure.depthUnsafe]
def KrivineClosure.depth: KrivineClosure -> Nat :=
fun closure => by induction closure with
| pair i env depth_env => exact depth_env
| nil => exact 0
| cons head tail head_depth tail_depth => exact Nat.max (head_depth + 1) (tail_depth + 1)

theorem KrivineClosure.depth.cons (c: KrivineInstruction) (a: KrivineClosure) (q: List KrivineClosure):
depth (pair c (a :: q)) = Nat.max (depth a + 1) (depth (pair c q) + 1) := rfl

def KrivineClosure.depth.spec: ∀ (c: KrivineInstruction) (x: KrivineClosure) (e: List KrivineClosure),
  depth x < depth (KrivineClosure.pair c (x :: e)) :=
fun c x e => by
simp [KrivineClosure.depth.cons]
exact Nat.ltSuccMaxLeft

namespace KrivineEnv
def depth: KrivineEnv -> Nat
| [] => 0
| closure :: closures => Nat.max (KrivineClosure.depth closure + 1) (depth closures + 1)

theorem depth_of_kcDepth (c: KrivineInstruction) (x: KrivineEnv): KrivineClosure.depth (KrivineClosure.pair c x) = depth x :=
by induction x with
| nil => simp [depth, KrivineClosure.depth]
| cons a q hq => simp [depth, KrivineClosure.depth.cons, hq]

theorem depth_spec₁: ∀ (c: KrivineInstruction) (x: KrivineEnv) (q: KrivineEnv),
  measure depth q (KrivineClosure.pair c x :: q) :=
fun c x q => by
  simp only [measure, InvImage, depth]
  rw [← Nat.succMaxEqMaxSucc]
  exact Nat.ltSuccMaxRight

theorem depth_spec₂: ∀ (c: KrivineInstruction) (x: KrivineEnv) (q: KrivineEnv),
  measure depth x (KrivineClosure.pair c x :: q) :=
fun c x q => by
  simp only [measure, InvImage, depth, depth_of_kcDepth]
  exact Nat.ltSuccMaxLeft


def depth_rel: KrivineEnv -> KrivineEnv -> Prop := measure depth
def depth_wf: WellFounded (measure depth) := measureWf depth

def correctF: (e: KrivineEnv) -> ((y : KrivineEnv) → measure depth y e → Prop) -> Prop :=
fun e correct => match e with
| [] => true
| KrivineClosure.pair c₀ e₀ :: env =>
  have e = KrivineClosure.pair c₀ e₀ :: env := by admit
  C[List.length e₀](compile.leftInv c₀)
  ∧ (correct e₀ (by rw [this]; exact depth_spec₂ _ _ _))
  ∧ (correct env (by rw [this]; exact depth_spec₁ _ _ _))

def correct: KrivineEnv -> Prop :=
WellFounded.fix depth_wf correctF

def correct.spec:
  ∀ (x: KrivineEnv), WellFounded.fix depth_wf correctF x = correctF x (fun y correct => WellFounded.fix depth_wf correctF y)
  := WellFounded.fixEq depth_wf correctF

end KrivineEnv

def KrivineState.correct (state: KrivineState): Prop :=
  C[List.length state.env](compile.leftInv state.code)
  ∧ (KrivineEnv.correct state.env)
  ∧ (KrivineEnv.correct state.stack)

-- Q5.3
theorem evalKrivineMachine.correctStateSpec (state: KrivineState) (hcorrect: KrivineState.correct state): (evalKrivineMachine state).isSome := sorry
@[reducible]
def evalKrivineMachine.getCorrectState (state: KrivineState) (hcorrect: KrivineState.correct state): KrivineState := (evalKrivineMachine state).get!

theorem correctness.code.aux₁ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv)
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): C[List.length env](compile.leftInv code) :=
by
simp [KrivineEnv.correct] at h
rw [KrivineEnv.correct.spec] at h
exact h.1

theorem correctness.code.aux₂ (n: Nat):
  C[Nat.succ n](compile.leftInv $ KrivineInstruction.Access (Nat.succ n)) -> C[Nat.succ n](compile.leftInv $ KrivineInstruction.Access n) :=
by
intro h; simp [compile.leftInv, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux, Nat.lt.base]

theorem correctness.env.aux₁ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv)
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): KrivineEnv.correct env :=
by
simp only [KrivineEnv.correct] at h; rw [KrivineEnv.correct.spec] at h
exact h.2.1

theorem correctness.env.aux₂ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv)
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): KrivineEnv.correct tail :=
by
simp only [KrivineEnv.correct] at h; rw [KrivineEnv.correct.spec] at h
exact h.2.2

theorem correctness.env.aux₃ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv) (h_code: C[List.length env](compile.leftInv code))
  (h_head: KrivineEnv.correct env) (h_tail: KrivineEnv.correct tail): KrivineEnv.correct (KrivineClosure.pair code env :: tail) :=
by
simp only [KrivineEnv.correct]; rw [KrivineEnv.correct.spec]
exact ⟨ h_code, ⟨ h_head, h_tail ⟩ ⟩

theorem transitionCorrectness (state: KrivineState) (hcorrect: KrivineState.correct state):
  KrivineState.correct (evalKrivineMachine.getCorrectState state hcorrect) :=
by
have (evalKrivineMachine state).isSome := evalKrivineMachine.correctStateSpec state hcorrect
simp [KrivineState.correct, evalKrivineMachine.getCorrectState]
match state.code, state.env, state.stack with
| KrivineInstruction.Access 0, (KrivineClosure.pair code recEnv :: closures), stack => exact sorry
| KrivineInstruction.Access n, (KrivineClosure.pair code recEnv :: closures), stack => exact sorry
| KrivineInstruction.Push c' c, env, stack => exact sorry
| KrivineInstruction.Grab code, closures, (KrivineClosure.pair c₀ e₀ :: stack) => exact sorry
| _, _, _ => exact sorry


-- require the good definition of tau.
-- theorem simulationCorrectness (state₀: KrivineState) (state₁: KrivineState):
-- (evalKrivineMachine state₀ = state₁) -> KrivineState.correct state₀ -> SmallStepBetaReduction (compile.left_inv state₀) (compile.left_inv state₁) := sorry

-- Q5.5
-- theorem
