import Lean
open Classical

-- For Core / standard library?
def List.forall (p : α → Prop) := List.foldr (λ a b => p a ∧ b) True

theorem List.forallCons (hd : α) (tl : List α) : List.forall p (hd :: tl) ↔ p hd ∧ List.forall p tl :=
by simp [List.forall, List.foldr]

theorem Option.someOfNotNone {T: Type} (x: Option T): x ≠ none <-> ∃ t: T, x = some t :=
by
apply Iff.intro
intro notNone
match x with
| some u => exact ⟨u, by rfl⟩
| none => exact absurd notNone (by simp)
intro hsome
rw [hsome.2]
exact Option.noConfusion

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

theorem Nat.ltMaxLeft {a b c: Nat}: a < b -> a < Nat.max b c :=
fun hab => by
simp only [Nat.max]
byCases hbc: b ≤ c
rw [ifPos hbc]; exact Nat.ltOfLtOfLe hab hbc
rw [ifNeg hbc]; exact hab

theorem Nat.ltMaxRight {a b c: Nat}: a < c -> a < Nat.max b c :=
fun hac => by
simp only [Nat.max]
byCases hbc: b ≤ c
rw [ifPos hbc]; exact hac
rw [ifNeg hbc]; exact Nat.ltTrans hac (Nat.gtOfNotLe hbc)

theorem Nat.succMaxEqMaxSucc {a b: Nat}: Nat.succ (Nat.max a b) = Nat.max (Nat.succ a) (Nat.succ b) :=
by
  simp [Nat.max];
  byCases hab: a ≤ b
  focus
    byCases hsucc: succ a ≤ succ b
    rw [ifPos hab, ifPos hsucc]
    rw [ifNeg hsucc, ifNeg <| show ¬ a ≤ b from λ h => hsucc <| succLeSucc h]
  focus
    byCases hsucc: succ a ≤ succ b
    rw [ifPos hsucc, ifPos <| leOfSuccLeSucc hsucc]
    rw [ifNeg hab, ifNeg hsucc]

theorem Nat.ltSuccMaxLeft {a b: Nat}: a < Nat.succ (Nat.max a b) :=
by rw [succMaxEqMaxSucc]; exact ltMaxLeft (lt.base _)
theorem Nat.ltSuccMaxRight {a b: Nat}: b < Nat.succ (Nat.max a b) :=
by rw [succMaxEqMaxSucc]; exact ltMaxRight (lt.base _)

theorem List.lengthMap (f : α → β) (l : List α) : List.length (List.map f l) = List.length l :=
by induction l with
| nil => simp [length, lengthAux]
| cons hd tl h_tl => simp [map, length_cons, h_tl]

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

theorem batchSubstituteFindPop (index m : Nat) {depth : Nat} (exprs : List LambdaTerm)
  (h₁ : m < index + exprs.length) (h₂ : index + depth ≤ m) :
  batchSubstitute.find (List.enumFrom (index + 1) exprs) depth (m + 1) =
  batchSubstitute.find (List.enumFrom index exprs) depth m :=
by induction exprs generalizing index with
| nil =>
  simp only [List.length_nil, Nat.add_zero] at h₁
  have p : m < index + depth := Nat.ltAddRight h₁
  have p' := Nat.ltOfLtOfLe p h₂
  exact absurd p' <| Nat.ltIrrefl m
| cons hd tl h_tl =>
  simp [batchSubstitute.find]
  byCases h' : (index + depth = m)
  focus
    have h'' : index + 1 + depth = m + 1 by rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, h']
    simp [ifPos h', ifPos h'']
  focus
    have h'' : index + 1 + depth ≠ m + 1 by
      rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      intro h₀
      simp [Nat.add_one] at h₀
      apply Nat.noConfusion h₀
      exact (λ h : index + depth = m => h' h)
    simp [ifNeg h', ifNeg h'']
    apply h_tl (index + 1)
    focus
      simp only [List.length_cons, (Nat.add_one _).symm,
        Nat.add_comm (List.length _) 1, (Nat.add_assoc _ _ _).symm] at h₁
      exact h₁
    focus
      apply Nat.leOfLtSucc
      rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc]
      apply Nat.succLeSucc
      exact Nat.succLeOfLt <| Nat.ltOfLeOfNe h₂ h'

theorem batchSubstituteSwap (t : LambdaTerm) (l : List LambdaTerm) (i : Nat) (depth : Nat) :
  batchSubstitute.aux i l t (depth + 1) = batchSubstitute.aux (i + 1) l t depth :=
by induction t generalizing depth with
  | var m =>
    simp [batchSubstitute.aux, batchSubstituteFindSwap]
  | app fn arg h_fn h_arg => simp [batchSubstitute.aux, h_fn, h_arg]
  | lambda body h_body => simp [batchSubstitute.aux, h_body]

theorem substEmpty (t : LambdaTerm) {i : Nat} :
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

theorem batchSubstituteFindMinorized (l : List LambdaTerm)
  (h_l : List.forall (λ t => C[i](t)) l) (i_le_j : i ≤ j) (depth m : Nat) :
  (λ result => result = LambdaTerm.var m ∨ C[i](result)) $
  batchSubstitute.find (List.enumFrom j l) depth m :=
by induction l generalizing j with
| nil => simp [batchSubstitute.find]
| cons hd tl h_tl =>
  simp only [batchSubstitute.find]
  simp only [List.forall, List.foldr] at h_l
  byCases h : j + depth = m
  focus
    simp only [ifPos h]
    exact Or.inr h_l.1
  focus
    simp only [ifNeg h]
    exact h_tl h_l.2 $ Nat.leTrans i_le_j $ Nat.leSucc j

theorem substRotate (t : LambdaTerm) {i : Nat} {hd : LambdaTerm} {tl : List LambdaTerm}
  (h_hd : C[i](hd)) (h_tl : List.forall (λ t => C[i](t)) tl) :
  t[i ← hd :: tl] = t[(i + 1) ← tl][i ← [hd]] :=
by
  suffices p : ∀ j : Nat, i ≤ j → t[j ← hd :: tl] = t[(j + 1) ← tl][j ← [hd]]
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
      have p := batchSubstituteFindMinorized tl h_tl (Nat.leTrans h $ Nat.leSucc j) 0 m
      simp at p
      cases p with
      | inl h => simp [h, batchSubstitute.aux, batchSubstitute.find, j_ne_m]
      | inr h' =>
        have p' : C[j](_) := boundByGreater h h'
        have p'' := substMinorized p' [hd]
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

-- Another useful lemma
theorem substAllByClosed {l : List LambdaTerm} {t : LambdaTerm}
  (h₁ : C[List.length l](t)) (h₂ : List.forall (λ t => C[0](t)) l) : C[0](t[0 ← l]) :=
by
  suffices p : ∀ {t i}, C[List.length l + i](t) →
    C[i](t[i ← l])
  by
    apply p
    rw [Nat.add_zero]
    exact h₁
  intro t
  induction t with
  | var m =>
    intro i h
    simp only [allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux] at h
    simp only [batchSubstitute, batchSubstitute.aux]
    suffices p :
      ∀ l j, (List.forall (λ t => C[0](t)) l) →
      (m < List.length l + j + i) →
      C[0](batchSubstitute.find (List.enumFrom (j + i) l) 0 m) ∨
      (batchSubstitute.find (List.enumFrom (j + i) l) 0 m = LambdaTerm.var m ∧ m < j + i)
    from match p l 0 h₂ h with
    | Or.inl p => boundByGreater (Nat.zeroLe i) (Nat.zero_add i ▸ p)
    | Or.inr p => by
      simp [Nat.add_zero] at p
      rw [p.1];
      exact p.2
    intro l j hl h
    induction l generalizing j with
    | nil =>
      apply Or.inr
      simp [List.enumFrom, batchSubstitute.find]
      simp [List.length_nil] at h
      exact h
    | cons hd tl h_tl =>
      simp [List.forall, List.foldr] at hl
      simp [List.length_cons, (Nat.add_one _).symm] at h
      rw [Nat.add_assoc _ 1 j] at h
      have p := h_tl (1 + j) hl.2 h
      byCases hm : m < j + i
      focus simp [batchSubstituteFindLower hm, hm]
      focus
        byCases hm' : j + i = m
        focus simp [List.enumFrom, batchSubstitute.find, hm', hl.1]
        focus match p with
        | Or.inl p =>
          apply Or.inl
          simp [List.enumFrom, batchSubstitute.find, hm']
          exact (show j + i + 1 = 1 + j + i by rw [Nat.add_comm, Nat.add_assoc]) ▸ p
        | Or.inr p =>
          exact absurd p.2 (show ¬ m < 1 + j + i from λ h => by
            rw [Nat.add_assoc, Nat.add_comm, Nat.add_one] at h
            match Nat.eqOrLtOfLe (Nat.leOfLtSucc h) with
            | Or.inl h => exact hm' h.symm
            | Or.inr h => exact hm h)
  | app fn arg h_fn h_arg =>
    intro i h
    simp [allFreeVariablesBoundBy, batchSubstitute] at h_fn
    simp [allFreeVariablesBoundBy, batchSubstitute] at h_arg
    simp [allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux, h_fn h.1, h_arg h.2]
  | lambda body h_body =>
    intro i h
    simp [allFreeVariablesBoundBy, batchSubstitute] at h_body
    simp [allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux]
    have p := allFreeVariablesBoundBy.lambda h
    simp [allFreeVariablesBoundBy] at p
    simp [batchSubstituteSwap]
    apply allFreeVariablesBoundBy.auxRec₂.1
    exact h_body p

-- Part 2
-- Q2.1
inductive SmallStepBetaReduction: LambdaTerm -> LambdaTerm -> Prop :=
| Eval : ∀ (u v: LambdaTerm), SmallStepBetaReduction (LambdaTerm.app (LambdaTerm.lambda u) v) (u[0 ← [v]])
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
-- @[reducible]
def evalKrivineMachine (state: KrivineState): Option KrivineState :=
match state.code, state.env, state.stack with
| KrivineInstruction.Access 0, (KrivineClosure.pair code recEnv :: closures), stack =>
  some $ KrivineState.mk code recEnv stack
| KrivineInstruction.Access (Nat.succ n), (KrivineClosure.pair code recEnv :: closures), stack =>
  some $ KrivineState.mk (KrivineInstruction.Access n) closures stack
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
def undoInstruction : KrivineInstruction → LambdaTerm
| KrivineInstruction.Access n => LambdaTerm.var n
| KrivineInstruction.Push c' c => LambdaTerm.app (undoInstruction c) (undoInstruction c')
| KrivineInstruction.Grab c => LambdaTerm.lambda (undoInstruction c)

set_option codegen false in
def undoClosure : KrivineClosure → LambdaTerm := KrivineClosure.rec
  (λ inst env env_undone => (undoInstruction inst)[0 ← env_undone])
  []
  (λ hd tl hd_undone tl_undone => hd_undone :: tl_undone)

/-def a : List KrivineClosure → LambdaTerm := KrivineClosure.rec_1
  (λ inst env env_undone => (undoInstruction inst)[0 ← env_undone])
  []
  (λ hd tl hd_undone tl_undone => hd_undone :: tl_undone)-/

set_option codegen false in
def undo (s : KrivineState) : LambdaTerm := List.foldl
  (λ f arg => LambdaTerm.app f $ undoClosure arg)
  ((undoInstruction s.code)[0 ← List.map undoClosure s.env])
  s.stack

theorem undoClosureSpec :
  undoClosure (KrivineClosure.pair i e) = (undoInstruction i)[0 ← List.map undoClosure e] :=
by
  simp [undoClosure]
  apply show ∀ {x y}, x = y → (undoInstruction i)[0 ← x] = (undoInstruction i)[0 ← y] from λ h => by rw [h]
  induction e with
  | nil => simp
  | cons hd tl h_tl =>
    simp [List.map]
    rw [h_tl]

-- Q5.2
def compile.idOfLeftInv (t: LambdaTerm): undoInstruction (compile_instr t) = t :=
by induction t with
| var n => rfl
| app fn arg h_fn h_arg => simp [undoInstruction, h_fn, h_arg]
| lambda t ht => simp [undoInstruction, ht]

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
fun e correct => match (generalizing := true) e with
| [] => true
| KrivineClosure.pair c₀ e₀ :: env =>
  C[List.length e₀](undoInstruction c₀)
  ∧ (correct e₀ (depth_spec₂ _ _ _))
  ∧ (correct env (depth_spec₁ _ _ _))

def correct: KrivineEnv -> Prop :=
WellFounded.fix depth_wf correctF

def correct.spec:
  ∀ (x: KrivineEnv), WellFounded.fix depth_wf correctF x = correctF x (fun y correct => WellFounded.fix depth_wf correctF y)
  := WellFounded.fixEq depth_wf correctF


theorem lateralInduction {motive : KrivineEnv → Sort}
  (env : KrivineEnv)
  (nil : motive [])
  (cons : ∀ code env tail, motive env → motive tail →
    motive (KrivineClosure.pair code env :: tail)) : motive env :=
by
  apply WellFounded.fix depth_wf
  intros x h_acc
  match x with
  | [] => exact nil
  | KrivineClosure.pair code env :: tail =>
    exact cons _ _ _ (h_acc _ $ depth_spec₂ _ _ _) (h_acc _ $ depth_spec₁ _ _ _)

end KrivineEnv

def KrivineState.correct (state: KrivineState): Prop :=
  C[List.length state.env](undoInstruction state.code)
  ∧ (KrivineEnv.correct state.env)
  ∧ (KrivineEnv.correct state.stack)

-- Q5.3
theorem Classical.dne {p: Prop}: ¬¬p -> p :=
fun hnnp => match (em p) with
| Or.inl hp => hp
| Or.inr hnp => absurd hnp hnnp

theorem evalKrivineMachine.isTransitionOfCorrect (state: KrivineState) (hcorrect: KrivineState.correct state)
  (h_grab: (∃ c: KrivineInstruction, state.code = KrivineInstruction.Grab c) -> (List.length state.stack) ≥ 1):
  (evalKrivineMachine state) ≠ none :=
byContradiction (fun hcontra =>
  by
  simp at hcontra
  have evalKrivineMachine state = none from Classical.dne hcontra
  match state with
  | KrivineState.mk code env stack =>
    match code with
    | KrivineInstruction.Access 0 =>
      match env, stack with
      | (KrivineClosure.pair code recEnv :: closures), stack =>
        simp [evalKrivineMachine] at this
    | KrivineInstruction.Access (Nat.succ n) =>
      match env, stack with
      | (KrivineClosure.pair code recEnv :: closures), stack =>
        simp [evalKrivineMachine] at this
    | KrivineInstruction.Push c' c =>
      match env, stack with
      | env, stack =>
        simp [evalKrivineMachine] at this
    | KrivineInstruction.Grab code =>
      match env, stack with
      | closures, (KrivineClosure.pair c₀ e₀ :: stack) =>
        simp [evalKrivineMachine] at this
      | env, [] =>
        simp only [List.length] at h_grab
        exact h_grab ⟨ code, by rfl ⟩
)

theorem correctness.code.aux₁ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv)
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): C[List.length env](undoInstruction code) :=
by
simp [KrivineEnv.correct] at h
rw [KrivineEnv.correct.spec] at h
exact h.1

theorem correctness.code.aux₂ (m n: Nat):
  C[Nat.succ m](undoInstruction $ KrivineInstruction.Access (Nat.succ n)) -> C[m](undoInstruction $ KrivineInstruction.Access n) :=
by
intro h; simp [undoInstruction, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux, Nat.lt.base]; simp [undoInstruction, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux] at h; exact h

theorem correctness.code.aux₃ {c c': KrivineInstruction} {n: Nat}:
  C[n](undoInstruction $ KrivineInstruction.Push c c') -> C[n](undoInstruction c') ∧ C[n](undoInstruction c) :=
by
simp [undoInstruction, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux]
exact (fun a => a)

theorem correctness.code.aux₄ {c: KrivineInstruction}:
  C[n](undoInstruction $ KrivineInstruction.Grab c) -> C[Nat.succ n](undoInstruction c) :=
by
simp [undoInstruction, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux]
exact (fun H => by apply (allFreeVariablesBoundBy.auxRec₂).2; exact H)

theorem correctness.env.aux₁ (code: KrivineInstruction) (env: KrivineEnv)
  (tail: KrivineEnv)
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): KrivineEnv.correct env :=
by
simp only [KrivineEnv.correct] at h; rw [KrivineEnv.correct.spec] at h
exact h.2.1

theorem correctness.env.aux₂ {code: KrivineInstruction} {env: KrivineEnv}
  {tail: KrivineEnv}
  (h: KrivineEnv.correct (KrivineClosure.pair code env :: tail)): KrivineEnv.correct tail :=
by
simp only [KrivineEnv.correct] at h; rw [KrivineEnv.correct.spec] at h
exact h.2.2

theorem correctness.env.aux₃ {code: KrivineInstruction} {env: KrivineEnv}
  {tail: KrivineEnv} (h_code: C[List.length env](undoInstruction code))
  (h_head: KrivineEnv.correct env) (h_tail: KrivineEnv.correct tail): KrivineEnv.correct (KrivineClosure.pair code env :: tail) :=
by
simp only [KrivineEnv.correct]; rw [KrivineEnv.correct.spec]
exact ⟨ h_code, ⟨ h_head, h_tail ⟩ ⟩

theorem transitionCorrectness (state: KrivineState) (hcorrect: KrivineState.correct state)
  (h_istransition: evalKrivineMachine state ≠ none):
  KrivineState.correct $ (evalKrivineMachine state).get! :=
by
simp [KrivineState.correct]
match state with
| KrivineState.mk code env stack =>
  match code with
  | KrivineInstruction.Access 0 =>
    match env, stack with
    | (KrivineClosure.pair code recEnv :: closures), stack =>
      simp [KrivineState.correct] at hcorrect
      have evalKrivineMachine { code := KrivineInstruction.Access 0, env := KrivineClosure.pair code recEnv :: closures, stack := stack } = some { code := code, env := recEnv, stack := stack} from by rfl
      simp [this, Option.get!]
      exact ⟨ (correctness.code.aux₁ _ _ closures hcorrect.2.1), ⟨ (correctness.env.aux₁ code recEnv closures hcorrect.2.1), hcorrect.2.2 ⟩ ⟩
  | KrivineInstruction.Access (Nat.succ n) =>
    match env, stack with
    | (KrivineClosure.pair code recEnv :: closures), stack =>
      simp [KrivineState.correct] at hcorrect
      simp [evalKrivineMachine, Option.get!]
      exact ⟨ (correctness.code.aux₂ _ _ hcorrect.1), ⟨ correctness.env.aux₂ hcorrect.2.1, hcorrect.2.2 ⟩ ⟩
  | KrivineInstruction.Push c' c =>
    match env, stack with
    | env, stack =>
      simp [KrivineState.correct] at hcorrect
      simp [evalKrivineMachine, Option.get!]
      have allFreeVariablesBoundBy (List.length env) (undoInstruction c') from (correctness.code.aux₃ hcorrect.1).2
      exact ⟨ (correctness.code.aux₃ hcorrect.1).1, ⟨ hcorrect.2.1, correctness.env.aux₃ this hcorrect.2.1 hcorrect.2.2⟩⟩
  | KrivineInstruction.Grab code =>
    match env, stack with
    | closures, (KrivineClosure.pair c₀ e₀ :: stack) =>
      simp [KrivineState.correct] at hcorrect
      simp [evalKrivineMachine, Option.get!]
      have h₁: allFreeVariablesBoundBy (List.length e₀) (undoInstruction c₀) from correctness.code.aux₁ _ _ _ hcorrect.2.2
      have h₂: KrivineEnv.correct e₀ from correctness.env.aux₁ _ _ _ hcorrect.2.2
      exact ⟨ correctness.code.aux₄ hcorrect.1, ⟨ correctness.env.aux₃ h₁ h₂ hcorrect.2.1, correctness.env.aux₂ hcorrect.2.2 ⟩ ⟩
    | env, [] =>
      simp [KrivineState.correct] at hcorrect
      simp [evalKrivineMachine, Option.get!]
      have evalKrivineMachine { code := KrivineInstruction.Grab code, env := env, stack := [] } = none from by rfl
      exact absurd this h_istransition


-- Q5.4

theorem lemma₀ : SmallStepBetaReduction u v →
  SmallStepBetaReduction
    (List.foldl (λ f arg => LambdaTerm.app f (undoClosure arg)) u l)
    (List.foldl (λ f arg => LambdaTerm.app f (undoClosure arg)) v l) :=
by induction l generalizing u v with
| nil =>
  simp [List.foldl]
  exact λ h => h
| cons hd tl tl_h =>
  intro h
  apply tl_h
  simp [List.foldl]
  exact SmallStepBetaReduction.LeftContext _ _ _ h

theorem lemma₁ (h₁ : C[0](u)) (h₂ : List.forall (λ t => C[0](t)) l) :
  SmallStepBetaReduction (LambdaTerm.app (LambdaTerm.lambda (t[1 ← l])) u) (t[0 ← u :: l]) :=
by
  rw [substRotate t h₁ h₂]
  apply SmallStepBetaReduction.Eval

theorem closedOfCorrect {env : KrivineEnv} (correct : KrivineEnv.correct env) :
  List.forall (λ t => C[0](t)) (List.map undoClosure env) :=
by induction env using KrivineEnv.lateralInduction with
| nil => simp [List.map, List.forall, List.foldr]
| cons code env tail h_env h_tail =>
  simp [List.map, List.forallCons, h_tail <| correctness.env.aux₂ correct]
  simp [undoClosureSpec]
  exact substAllByClosed
    (by
      rw [List.lengthMap undoClosure env]
      exact correctness.code.aux₁ code env tail correct)
    (h_env <| correctness.env.aux₁ _ _ _ correct)

theorem simulationCorrectness (state₀ : KrivineState) (state₁ : KrivineState)
 (eval : evalKrivineMachine state₀ = state₁) (correct : KrivineState.correct state₀) :
 SmallStepBetaReduction (undo state₀) (undo state₁) ∨ undo state₀ = undo state₁ :=
by match state₀ with
| KrivineState.mk code state stack =>
  induction code with
  | Access n => match state with
    | [] =>
      cases n with
      | zero => simp [evalKrivineMachine] at eval
      | succ n => simp [evalKrivineMachine] at eval
    | KrivineClosure.pair code recEnv :: closures =>
      apply Or.inr
      cases n with
      | zero =>
        simp [evalKrivineMachine] at eval
        apply Option.noConfusion eval
        intro eval
        rw [← eval]
        simp [undo, undoInstruction, batchSubstitute, batchSubstitute.aux, List.enumFrom, batchSubstitute.find]
        rw [undoClosureSpec]
        rfl
      | succ n =>
        simp [evalKrivineMachine] at eval
        apply Option.noConfusion eval
        intro eval
        rw [← eval]
        simp [undo, undoInstruction, batchSubstitute, batchSubstitute.aux, List.enumFrom, batchSubstitute.find]
        suffices p : batchSubstitute.find (List.enumFrom 1 (List.map undoClosure closures)) 0 (Nat.succ n) =
          batchSubstitute.find (List.enumFrom 0 (List.map undoClosure closures)) 0 n
        by rw [p]
        apply batchSubstituteFindPop
        focus
          have p := correct.1
          simp [List.length_cons, undoInstruction, allFreeVariablesBoundBy, allFreeVariablesBoundBy.aux] at p
          rw [List.lengthMap, Nat.zero_add]
          apply Nat.lt_of_succ_lt_succ
          exact p
        focus
          exact Nat.zeroLe n
  | Push c' c c'_h c_h =>
    simp [evalKrivineMachine] at eval
    apply Option.noConfusion eval
    intro eval
    rw [← eval]
    simp [undo, undoInstruction, batchSubstitute, batchSubstitute.aux, undoClosureSpec, List.foldl]
  | Grab c c_h =>
    apply Or.inl
    match stack with
    | [] => simp [evalKrivineMachine] at eval
    | KrivineClosure.pair code recEnv :: closures =>
      simp [evalKrivineMachine] at eval
      apply Option.noConfusion eval
      intro eval
      rw [← eval]
      simp [undo, undoInstruction, batchSubstitute, batchSubstitute.aux,
        undoClosureSpec, List.foldl, List.map]
      simp [KrivineState.correct] at correct
      apply lemma₀
      simp [batchSubstituteSwap]
      have p₁ := substAllByClosed
        (by
          rw [List.lengthMap undoClosure recEnv]
          exact correctness.code.aux₁ _ _ _ correct.2.2)
        (closedOfCorrect <| correctness.env.aux₁ _ _ _ correct.2.2)
      apply lemma₁ p₁ (closedOfCorrect correct.2.1)

-- Q5.5
inductive EvalTC: KrivineState -> KrivineState -> Prop :=
| Rfl (u: KrivineState): EvalTC u u
| Trans (t u v: KrivineState): evalKrivineMachine t = u -> EvalTC u v -> EvalTC t v

theorem simulationCorrectnessTC (u v : KrivineState) (h : EvalTC u v) (correct : KrivineState.correct u) :
  BetaReduction (undo u) (undo v) :=
by induction h with
| Rfl u => apply BetaReduction.Rfl
| Trans t u v t_h a a_h =>
  have p := simulationCorrectness t u t_h correct
  have u_correct := transitionCorrectness t correct (by simp [t_h])
  rw [t_h] at u_correct
  match p with
  | Or.inl p =>
    exact BetaReduction.Trans (undo t) (undo u) (undo v) p (a_h u_correct)
  | Or.inr p =>
    rw [p]
    exact a_h u_correct
