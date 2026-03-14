import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Classical

/-! ## Preorder'

A total preorder over candidates `α`, representing an individual's preference ranking.
-/
variable {α : Type}

/-- A total preorder: reflexive, transitive, total, and antisymmetric. -/
structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a

/-- Strict preference: `a` is strictly preferred to `b` iff `a ≤ b` but not `b ≤ a`. -/
def Preorder'.lt (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a

lemma Preorder'.lt_asymm (p : Preorder' α) (a b : α) :
    p.lt a b → ¬ p.lt b a := by
  intro ⟨hab, hnba⟩ ⟨hba, _⟩
  exact hnba hba

@[simp]
lemma Preorder'.not_lt {α : Type} (p : Preorder' α) (a b : α) :
    ¬ p.lt a b ↔ p.le b a := by
  unfold Preorder'.lt
  constructor
  . intro h; push_neg at h
    rcases p.total a b with hab | hba
    . exact h hab
    . exact hba
  . intro hba; push_neg; intro _; exact hba

lemma Preorder'.lt_trans (p : Preorder' α) {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h
      exact h1.2 (p.trans _ _ _ h2.1 h)

/-- The three possible outcomes when comparing two elements under a total preorder. -/
inductive Cmp (p : Preorder' α) (a b : α) : Type
  | Indiff (h₁ : p.le a b) (h₂ : p.le b a) : Cmp p a b
  | LT     (h  : p.le a b) (hn : ¬p.le b a) : Cmp p a b
  | GT     (hn : ¬p.le a b) (h  : p.le b a)  : Cmp p a b

noncomputable def Preorder'.cmp (p : Preorder' α) (a b : α) : Cmp p a b :=
  if hab : p.le a b then
    if hba : p.le b a then Cmp.Indiff hab hba
    else Cmp.LT hab hba
  else Cmp.GT hab (p.total a b |>.resolve_left hab)


/-! ## Social Welfare Function

Core definitions for Arrow's theorem: profiles, SWFs, and the three key properties.
-/
variable {N : ℕ}

/-- A preference profile assigns each voter `i ∈ Fin N` their preference ordering. -/
def Profile (α : Type) (N : ℕ) := Fin N → Preorder' α

/-- A Social Welfare Function aggregates individual preferences into a social ordering. -/
def SWF (α : Type) (N : ℕ) := (Fin N → Preorder' α) → Preorder' α

-- Notation: `a ≻[R p] b` means society (under SWF `R`) strictly prefers `a` over `b` in profile `p`
notation a " ≻[" R p "] " b => Preorder'.lt (R p) b a
notation a " ≽[" R p "] " b => Preorder'.le (R p) b a
notation a " ≻[" R p "] " b "≻ " c =>
  Preorder'.lt (R p) b a ∧ Preorder'.lt (R p) b c
notation a " ≽[" R p "] " b "≻ " c =>
  Preorder'.le (R p) b a ∧ Preorder'.lt (R p) b c

-- Notation: `a ≻[p] b` means voter with preference `p` strictly prefers `a` over `b`
notation a " ≻[" p  "] " b => Preorder'.lt p b a
notation a " ≽[" p  "] " b => Preorder'.le p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c
notation a " ≽[" p  "] " b "≻ " c => (a ≽[p] b) ∧ b ≻[p] c

/-- Voter `k` is a dictator for the pair `(a, b)` if whenever `k` prefers `a` over `b`,
    society also prefers `a` over `b`. -/
def Dictates (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b

/-- Two profiles agree on `(a, b)` if every voter ranks `a` vs `b` the same way in both. -/
def AgreeOn {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)

/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society. -/
def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α),
    (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b

/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
def AIIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≽[R p] b) ↔ a ≽[R q] b) ∧ ((b ≽[R p] a) ↔ b ≽[R q] a)

lemma strict_aiia {R: SWF α N}
  {p q: Profile α N} {a b: α}
  (hagree: AgreeOn p q a b)(hAIIA: AIIA R):
  (a ≻[R p] b) ↔ a ≻[R q] b := by
  have := hAIIA _ _ _ _ hagree
  simp [Preorder'.lt, this.1, this.2]

/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs. -/
def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)

/-! ## Preference Construction

We construct concrete preference orderings to build test profiles for the proof.
Given three alternatives, `prefer a₀ a₁ a₂ tie` ranks them with optional ties:
- `Tie.Not`: a₀ > a₁ > a₂
- `Tie.Top`: a₀ ~ a₁ > a₂
- `Tie.Bot`: a₀ > a₁ ~ a₂
-/
variable [LinearOrder α]

/-- Where ties occur in a 3-element preference ranking -/
inductive Tie
  | Not  -- No ties: a₀ > a₁ > a₂
  | Top  -- Top two tied: a₀ ~ a₁ > a₂
  | Bot  -- Bottom two tied: a₀ > a₁ ~ a₂

/-- Construct a preference ordering with optional ties:
    - `Tie.Not`: a₀ > a₁ > a₂ (strict ranking)
    - `Tie.Top`: a₀ ~ a₁ > a₂ (top two tied)
    - `Tie.Bot`: a₀ > a₁ ~ a₂ (bottom two tied)
    Uses the ambient `LinearOrder` as a tiebreaker for elements outside `{a₀, a₁, a₂}`. -/
def prefer (a₀ _a₁ a₂ : α) (tie : Tie) (h02 : a₀ ≠ a₂) : Preorder' α where
  le x y := match tie with
    | .Not =>
      if x = a₂ then True              -- a₂ is bottom
      else if y = a₀ then True         -- a₀ is top
      else if x = a₀ then y = a₀       -- only a₀ ≤ a₀
      else if y = a₂ then x = a₂       -- only a₂ ≥ a₂
      else x ≤ y                        -- fallback to LinearOrder
    | .Top =>
      if y = a₂ then x = a₂           -- only a₂ ≥ a₂ (a₂ is bottom)
      else if x = a₂ then True        -- a₂ ≤ everything else
      else True                        -- a₀ ~ a₁: both directions
    | .Bot =>
      if x = a₀ then y = a₀           -- only a₀ ≤ a₀ (a₀ is top)
      else if y = a₀ then True        -- everything else ≤ a₀
      else True                        -- a₁ ~ a₂: both directions
  refl := by intro x; cases tie <;> simp
  trans := by
    intro a b c ha hb
    cases tie <;> simp only at ha hb ⊢
    · split_ifs with haa2 hca0 haa0 hca2 <;> simp_all
      by_cases hba0: b = a₀
      · simp_all
      · simp_all; exact le_trans ha.2 hb
    · split_ifs at ha hb ⊢; exact ha
    · split_ifs at ha hb ⊢; exact hb
  total := by
    intro a b
    cases tie
    · split_ifs <;> simp_all [le_total a b]
    · simp only; by_cases hxa : a = a₂ <;> by_cases hya : b = a₂ <;> simp_all
    · simp only; by_cases hxa : a = a₀ <;> by_cases hya : b = a₀ <;> simp_all

/-! ### Lemmas for Tie.Not (strict ranking a₀ > a₁ > a₂) -/

/-- In `prefer a₀ a₁ a₂ .Not`, we have `a₀ > a₁`. -/
lemma prefer_lt_01 (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).lt a₁ a₀ := by
  simp [Preorder'.lt, prefer, h02, Ne.symm h01]

lemma prefer_le_01 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).le a₁ a₀ := by simp [prefer]

lemma prefer_lt_12 (a₀ a₁ a₂ : α) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).lt a₂ a₁ := by
  simp [Preorder'.lt, prefer, h12, Ne.symm h02]

lemma prefer_le_12 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).le a₂ a₁ := by simp [prefer]

lemma prefer_lt_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).lt a₂ a₀ := by
  simp [Preorder'.lt, prefer, h02, Ne.symm h02]

lemma prefer_le_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Not h02).le a₂ a₀ := by simp [prefer]

/-! ### Lemmas for Tie.Top (a₀ ~ a₁ > a₂) -/

/-- In `prefer a₀ a₁ a₂ .Top`, we have a₀ > a₂ -/
lemma prefer_top_lt_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Top h02).lt a₂ a₀ := by
  simp [Preorder'.lt, prefer, h02]

/-- In `prefer a₀ a₁ a₂ .Top`, we have a₁ > a₂ -/
lemma prefer_top_lt_12 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Top h02).lt a₂ a₁ := by
  simp [Preorder'.lt, prefer, h12]

/-- In `prefer a₀ a₁ a₂ .Top`, a₀ and a₁ are indifferent: a₀ ≤ a₁ -/
lemma prefer_top_le_01 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Top h02).le a₀ a₁ := by
  simp [prefer, h02, h12]

/-- In `prefer a₀ a₁ a₂ .Top`, a₀ and a₁ are indifferent: a₁ ≤ a₀ -/
lemma prefer_top_le_10 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂):
    (prefer a₀ a₁ a₂ .Top h02).le a₁ a₀ := by
  simp [prefer, h02]

lemma prefer_top_le_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Top h02).le a₂ a₀ := by simp [prefer]

lemma prefer_top_le_12 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Top h02).le a₂ a₁ := by simp [prefer]

/-! ### Lemmas for Tie.Bot (a₀ > a₁ ~ a₂) -/

/-- In `prefer a₀ a₁ a₂ .Bot`, we have a₀ > a₁ -/
lemma prefer_bot_lt_01 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h01 : a₀ ≠ a₁) :
    (prefer a₀ a₁ a₂ .Bot h02).lt a₁ a₀ := by
  simp [Preorder'.lt, prefer, Ne.symm h01]

/-- In `prefer a₀ a₁ a₂ .Bot`, we have a₀ > a₂ -/
lemma prefer_bot_lt_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Bot h02).lt a₂ a₀ := by
  simp [Preorder'.lt, prefer, Ne.symm h02]

/-- In `prefer a₀ a₁ a₂ .Bot`, a₁ and a₂ are indifferent: a₁ ≤ a₂ -/
lemma prefer_bot_le_12 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h01 : a₀ ≠ a₁) :
    (prefer a₀ a₁ a₂ .Bot h02).le a₁ a₂ := by
  simp [prefer, Ne.symm h02, Ne.symm h01]

/-- In `prefer a₀ a₁ a₂ .Bot`, a₁ and a₂ are indifferent: a₂ ≤ a₁ -/
lemma prefer_bot_le_21 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h01 : a₀ ≠ a₁) :
    (prefer a₀ a₁ a₂ .Bot h02).le a₂ a₁ := by
  simp [prefer, Ne.symm h01, Ne.symm h02]

lemma prefer_bot_le_01 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) (h01 : a₀ ≠ a₁) :
    (prefer a₀ a₁ a₂ .Bot h02).le a₁ a₀ := by simp [prefer, Ne.symm h01]

lemma prefer_bot_le_02 (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ .Bot h02).le a₂ a₀ := by simp [prefer, Ne.symm h02]

/-! ## Pivotal Voter

The key construction: we find the "pivotal voter" who flips society's preference.
Starting from a profile where everyone prefers `b ≻ a`, we flip voters one by one
to prefer `a ≻ b`. By unanimity, society eventually flips too. The first voter
whose flip changes society's preference is the pivotal voter.
-/
variable [NeZero N] {R : SWF α N}

/-- A family of profiles indexed by `k ∈ Fin (N+1)`:
    voters `0..k-1` prefer `b ≻ a`, voters `k..N-1` prefer `a ≻ b`. -/
def canonicalSwap (a b : α) (hab : a ≠ b) : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      then prefer b b a .Not (Ne.symm hab)  -- b on top
      else prefer a b b .Not hab            -- a on top

/-- `flipping R a b hab k` holds iff society prefers `b ≻ a` when voters `0..k` prefer `b ≻ a`. -/
def flipping (R : SWF α N) (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => ¬ a ≻[R ((canonicalSwap a b hab) k.succ)] b

/-- By unanimity, a flip must occur: when all voters prefer `b ≻ a`, so does society. -/
lemma flip_exists (R : SWF α N) (a b : α) (hab : a ≠ b) (hu : Unanimity R):
    ∃ k, flipping R a b hab k := by
  use (0:Fin N).rev
  unfold flipping canonicalSwap
  have: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  simp [Nat.sub_add_cancel this]
  have: b ≻[R (fun i => prefer b b a .Not (Ne.symm hab) )] a := by
    apply hu; intro i; simp [prefer_lt_02 b _ a (Ne.symm hab)]
  exact this.1

/-- The pivotal voter for `(a, b)`: the minimum `k` where society flips from `a ≻ b` to `b ≻ a`. -/
noncomputable def pivoter (a b : α) (hab : a ≠ b) (hu : Unanimity R) : Fin N :=
  Fin.find (flipping R a b hab) (flip_exists R a b hab hu)

/-- Before the pivotal voter, society still prefers `a ≻ b`. -/
lemma no_flip (a b : α) {hab : a ≠ b} (i : Fin N) {hu: Unanimity R}:
    i < pivoter a b hab hu → a ≻[R (canonicalSwap a b hab i.succ)] b := by
  intro hilt
  have h := Fin.find_min (flip_exists R a b hab hu) hilt
  unfold flipping at h; push_neg at h; exact h

/-- At the pivotal voter, society flips to `b ≻ a`. -/
lemma flipped (a b : α) {hab : a ≠ b} {hu: Unanimity R}:
    b ≽[R (canonicalSwap a b hab (pivoter a b hab hu).succ)] a := by
  exact (Preorder'.not_lt _ _ _).mp (Fin.find_spec (flip_exists R a b hab hu))

/-- The pivotal voter for `(a, b)` dictates the pair `(b, c)`. -/
lemma nab_pivotal_bc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : Dictates R (pivoter a b hab hu) b c := by
  let n_ab := pivoter a b hab hu

  -- Magic profile 1
  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  let mg1: Profile α N := fun i: Fin N =>
    if i < n_ab.val
      then prefer b c a .Not (Ne.symm hab)
      else prefer a b c .Not hac
  -- soc prefer a > b > c
  have habc: a ≻[R mg1] b ≻ c  := by
    constructor
    -- a > b by def of n_ab
    . by_cases hn : n_ab = 0
      . -- Case n_ab = 0: All voters prefer a > b, use unanimity
        have h : ∀ i : Fin N, a ≻[mg1 i] b := by
          intro i; simp [mg1, hn]
          exact prefer_lt_01 a b c hab hac
        exact hu _ _ _ h
      . -- Case n_ab ≠ 0: Use no_flip
        let k := n_ab - 1
        have hk_succ : k.val + 1 = n_ab.val := by
          simp only [k, Fin.val_sub_one_of_ne_zero hn]
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hn))
        have hk : k.val < n_ab := by omega
        have hp : AgreeOn mg1 (canonicalSwap a b hab k.succ) a b := by
          intro i; simp only [mg1, canonicalSwap]
          by_cases hi : i.val < n_ab.val <;> simp [hk_succ, hi]
          . constructor
            . rw[← not_iff_not]
              simp only [(prefer_lt_02 b c a (Ne.symm hab)).2, (prefer_lt_02 b b a (Ne.symm hab)).2]
            . simp only [prefer_le_02 b c a (Ne.symm hab), prefer_le_02 b b a (Ne.symm hab)]
          . constructor
            . simp only [prefer_le_01 a b c hac, prefer_le_01 a b b hab]
            . rw[← not_iff_not]
              simp only [(prefer_lt_01 a b c hab hac).2, (prefer_lt_01 a b b hab hab).2]

        apply (strict_aiia hp hAIIA).mpr
        exact no_flip a b k hk
    -- b > c by unanimity
    . have h: ∀ i: Fin N, b ≻[mg1 i] c := by
        intro i; unfold mg1; split_ifs
        . exact prefer_lt_01 b c a hbc (Ne.symm hab)
        . exact prefer_lt_12 a b c hbc hac
      exact hu _ _ _ h
  intro pp h

  -- Magic profile 2: match arbitrary profile `pp` on (b,c)
  -- For i < n_ab: (b ~ c) > a, or b > c > a, or c > b > a (matching pp)
  -- For i = n_ab: b > a > c
  -- For i > n_ab: a > (b ~ c), or a > b > c, or a > c > b (matching pp)
  -- result: socPrefer b ≥ a > c
  let mg2 : Profile α N := fun i: Fin N =>
    if i < n_ab
      then match (pp i).cmp b c with
        | .LT _ _ => prefer c b a .Not (Ne.symm hac)
        | .GT _ _ => prefer b c a .Not (Ne.symm hab)
        | .Indiff _ _ => prefer b c a .Top (Ne.symm hab)  -- b ~ c > a
      else
        if i = n_ab then prefer b a c .Not hbc
        else match (pp i).cmp b c with
        | .LT _ _ => prefer a c b .Not hab
        | .GT _ _ => prefer a b c .Not hac
        | .Indiff _ _ => prefer a b c .Bot hac  -- a > b ~ c

  have h_agree: AgreeOn pp mg2 b c := by
    unfold AgreeOn mg2; intro i
    split_ifs with hiltnab hieqnab
    . constructor -- i < n_ab
      . cases (pp i).cmp b c with
        | LT _ hn=> rw[← not_iff_not]; simp [hn, (prefer_lt_01 c b a (Ne.symm hbc) (Ne.symm hac)).2]
        | GT _ h => simp only [h, prefer_le_01 b c a (Ne.symm hab)]
        | Indiff _ h2 => simp only [h2, prefer_top_le_10 b c a (Ne.symm hab)]
      . cases (pp i).cmp b c with
        | LT h _=> simp [h, (prefer_lt_01 c b a (Ne.symm hbc) (Ne.symm hac)).1]
        | GT hn _ => rw[← not_iff_not]; simp [hn, (prefer_lt_01 b c a hbc (Ne.symm hab)).2]
        | Indiff h1 _ => simp only [h1, prefer_top_le_01 b c a (Ne.symm hab) (Ne.symm hac)]
    . -- i = n_ab
      subst i n_ab; constructor
      . simp only [h.1, prefer_le_02 b a c hbc]
      . rw[← not_iff_not]; simp [h.2, (prefer_lt_02 b a c hbc).2]
    . constructor -- i > n_ab
      . cases (pp i).cmp b c with
        | LT _ hn => rw[← not_iff_not]; simp [hn, (prefer_lt_12 a c b (Ne.symm hbc) hab).2]
        | GT _ h => simp only [h, prefer_le_12 a b c hac]
        | Indiff _ h2 => simp only [h2, prefer_bot_le_21 a b c hac hab]
      . cases (pp i).cmp b c with
        | LT h _=> simp [h, prefer_le_12 a c b hab]
        | GT hn _ => rw[← not_iff_not]; simp [hn, (prefer_lt_12 a b c hbc hac).2]
        | Indiff h1 _ => simp only [h1, prefer_bot_le_12 a b c hac hab]

  have hbac: b ≽[R mg2] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn mg2 (canonicalSwap a b hab n_ab.succ) b a := by
        unfold AgreeOn canonicalSwap mg2; intro i;
        by_cases hi: i < n_ab
        . have :i.val < n_ab +1 := by omega
          simp [hi, this]
          constructor
          . simp only [prefer_le_02 b b a (Ne.symm hab)]
            cases (pp i).cmp b c with
            | LT _ _ => simp only [prefer_le_12 c b a (Ne.symm hac)]
            | GT _ _ => simp only [prefer_le_02 b c a (Ne.symm hab)]
            | Indiff _ _ => simp only [prefer_top_le_02 b c a (Ne.symm hab)]
          . rw[← not_iff_not]
            simp [(prefer_lt_02 b b a (Ne.symm hab)).2]
            cases (pp i).cmp b c with
            | LT _ _ => simp [(prefer_lt_12 c b a (Ne.symm hab) (Ne.symm hac)).2]
            | GT _ _ => simp [(prefer_lt_02 b c a (Ne.symm hab)).2]
            | Indiff _ _ => simp [(prefer_top_lt_02 b c a (Ne.symm hab)).2]
        . by_cases hi2: i = n_ab
          . simp [hi2, prefer_le_01 b a c hbc, prefer_le_02 b b a (Ne.symm hab)]
            rw[← not_iff_not]
            simp [(prefer_lt_01 b a c (Ne.symm hab) hbc).2, (prefer_lt_02 b b a (Ne.symm hab)).2]
          . have :¬ (i.val < n_ab +1 ):= by omega
            simp [hi, hi2, this]
            constructor
            . rw[← not_iff_not]
              simp [(prefer_lt_02 a b b hab).2]
              cases (pp i).cmp b c with
              | LT _ _ => simp [(prefer_lt_02 a c b hab).2]
              | GT _ _ => simp [(prefer_lt_01 a b c hab hac).2]
              | Indiff _ _ => simp [(prefer_bot_lt_01 a b c hac hab).2]
            . simp only [(prefer_lt_02 a b b hab).1]
              cases (pp i).cmp b c with
              | LT _ _ => simp [(prefer_lt_02 a c b hab).1]
              | GT _ _ => simp [(prefer_lt_01 a b c hab hac).1]
              | Indiff _ _ => simp [(prefer_bot_lt_01 a b c hac hab).1]
      apply (hAIIA _ _ _ _ h_agree_ba).1.mpr
      exact flipped a b
    -- By AIIA
    . have h_agree_ac: AgreeOn mg2 mg1 a c := by
        unfold AgreeOn mg2 mg1; intro i; simp; split_ifs
        . constructor
          . rw[← not_iff_not]
            simp [(prefer_lt_12 b c a (Ne.symm hac) (Ne.symm hab)).2]
            cases (pp i).cmp b c with
            | LT _ _ => simp [(prefer_lt_02 c b a (Ne.symm hac)).2]
            | GT _ _ => simp [(prefer_lt_12 b c a (Ne.symm hac) (Ne.symm hab)).2]
            | Indiff _ _ => simp [(prefer_top_lt_12 b c a (Ne.symm hab) (Ne.symm hac)).2]
          . simp [prefer_le_12 b c a (Ne.symm hab)]
            cases (pp i).cmp b c with
            | LT _ _ => simp [prefer_le_02 c b a (Ne.symm hac)]
            | GT _ _ => simp [prefer_le_12 b c a (Ne.symm hab)]
            | Indiff _ _ => simp [prefer_top_le_12 b c a (Ne.symm hab)]
        . constructor
          . simp only [prefer_le_12 b a c hbc, prefer_le_02 a b c hac]
          . rw[← not_iff_not]
            simp [(prefer_lt_12 b a c hac hbc).2, (prefer_lt_02 a b c hac).2]
        . constructor
          . simp only [prefer_le_02 a b c hac]
            cases (pp i).cmp b c with
            | LT _ _ => simp [prefer_le_01 a c b hab]
            | GT _ _ => simp [prefer_le_02 a b c hac]
            | Indiff _ _ => simp [prefer_bot_le_02 a b c hac]
          . rw[← not_iff_not]
            simp [(prefer_lt_02 a b c hac).2]
            cases (pp i).cmp b c with
            | LT _ _ => simp [(prefer_lt_01 a c b hac hab).2]
            | GT _ _ => simp [(prefer_lt_02 a b c hac).2]
            | Indiff _ _ => simp [(prefer_bot_lt_02 a b c hac).2]
      exact (strict_aiia h_agree_ac hAIIA).mpr ((R mg1).lt_trans habc.2 habc.1)

  -- transitivity from b ≽ a ≻ c
  have hRmg2bc : b ≻[R mg2] c := by
    simp [Preorder'.lt]
    constructor
    . exact (R mg2).trans c a b hbac.2.1 hbac.1
    . intro h
      have := (R mg2).trans a b c hbac.1 h
      exact absurd this hbac.2.2
  exact (strict_aiia h_agree hAIIA).mpr hRmg2bc

/-- The pivotal voter for `(a, b)` comes no later than the one for `(b, c)`. -/
lemma nab_le_nbc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : pivoter a b hab hu ≤ pivoter b c hbc hu := by
  by_contra h; push_neg at h;
  let cs := canonicalSwap b c hbc (pivoter b c hbc hu).succ
  have h_pref : b ≻[cs (pivoter a b hab hu)] c := by
    simp only [cs, canonicalSwap]
    split_ifs with hh
    . simp at hh; omega
    . exact prefer_lt_02 b _ c hbc
  exact absurd
    (nab_pivotal_bc a b c hab hac hbc hu hAIIA cs h_pref) -- n_ab still dictates b over c
    ((Preorder'.not_lt _ _ _).mpr (flipped b c))          -- but n_bc flipped, so society should prefer c over b

/-- The pivotal voter for `(c, b)` comes no later than the one for `(a, b)`. -/
lemma ncb_le_nab (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R):
    pivoter c b (Ne.symm hbc) hu ≤ pivoter a b hab hu := by
  by_contra h; push_neg at h
  let n_ab := pivoter a b hab hu
  let n_cb := pivoter c b (Ne.symm hbc) hu
  let cs := canonicalSwap c b (Ne.symm hbc) n_ab.succ
  have: b ≻[cs n_ab] c := by simp [cs, canonicalSwap, prefer_lt_02 b _ c hbc]
  exact absurd
    (nab_pivotal_bc a b c hab hac hbc hu hAIIA cs this) -- n_ab prefer b over c, so is society
    (Preorder'.lt_asymm _ _ _ (no_flip c b n_ab h))     -- n_ab before pivoter, so b c shouldn't flip

/-- Combining the above: `pivoter (c, b) ≤ pivoter (b, c)`. -/
lemma nbc_le_ncb (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : pivoter c b (Ne.symm hbc) hu ≤ pivoter b c hbc hu :=
  le_trans (ncb_le_nab a b c hab hac hbc hu hAIIA) (nab_le_nbc a b c hab hac hbc hu hAIIA)

/-- All pivotal voters for pairs in `{a, b, c}` are the same:
    `pivoter (b, c) = pivoter (c, b) = pivoter (a, b)`. -/
lemma n_ab_pivotal_bc_cb (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R):
    (pivoter b c hbc hu) = (pivoter c b (Ne.symm hbc) hu) ∧
    (pivoter c b (Ne.symm hbc) hu) = pivoter a b hab hu := by

  let n_ab := pivoter a b hab hu
  let n_bc := pivoter b c hbc hu
  let n_cb := pivoter c b (Ne.symm hbc) hu
  -- n_bc ≥ n_ab
  have h_nab_le_nbc: n_ab ≤ n_bc := nab_le_nbc a b c hab hac hbc hu hAIIA

  -- n_cb ≤ n_ab
  have h_ncb_le_nab: n_cb ≤ n_ab := ncb_le_nab a b c hab hac hbc hu hAIIA

  have h_ncb_le_nbc: n_cb ≤ n_bc := nbc_le_ncb a b c hab hac hbc hu hAIIA
  -- n_bc ≥ n_ab ≥ n_cb
  -- n_cb ≥ n_bc
  -- As b and c are distinct and arbitrary, n_bc ≤ n_cb also holds
  have h_nbc_le_ncb: n_bc ≤ n_cb := nbc_le_ncb a c b hac hab (Ne.symm hbc) hu hAIIA

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb: n_bc = n_cb := le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_ncb_eq_nab: n_cb = n_ab := by
    have h_nab_le_n_cb: n_ab ≤ n_cb := le_trans h_nab_le_nbc h_nbc_le_ncb
    exact le_antisymm h_ncb_le_nab h_nab_le_n_cb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

/-- The pivotal voter for any pair `(a, b)` dictates *every* pair `(x, y)`. -/
lemma n_ab_dictate_xy (a b c x y: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
    (hu: Unanimity R) (hAIIA: AIIA R):
    Dictates R (pivoter a b hab hu) x y := by
  -- Collect pivotal voter equalities for {a,b,c}
  obtain ⟨h_nbc_eq_ncb, h_ncb_eq_nab⟩ := n_ab_pivotal_bc_cb a b c hab hac hbc hu hAIIA
  obtain ⟨h_nab_eq_nba, h_nba_eq_nca⟩ := n_ab_pivotal_bc_cb c a b (Ne.symm hac) (Ne.symm hbc) hab hu hAIIA
  obtain ⟨_, h_nbc_eq_nac⟩ := n_ab_pivotal_bc_cb a c b hac hab (Ne.symm hbc) hu hAIIA
  by_cases hxa : x = a; subst x
  . by_cases hyb : y = b; subst y
    . simpa [← h_nba_eq_nca, ← h_nab_eq_nba] using nab_pivotal_bc c a b (Ne.symm hac) (Ne.symm hbc) hab hu hAIIA
    . by_cases hyc : y = c; subst y
      . simpa [← h_nab_eq_nba] using nab_pivotal_bc b a c (Ne.symm hab) hbc hac hu hAIIA
      . simpa [← h_nab_eq_nba] using nab_pivotal_bc b a y (Ne.symm hab) (Ne.symm hyb) hxy hu hAIIA
  . by_cases hxb : x = b; subst x
    . by_cases hya : y = a; subst y
      . simpa [h_ncb_eq_nab] using nab_pivotal_bc c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) hu hAIIA
      . by_cases hyc : y = c; subst y
        . exact nab_pivotal_bc a b c hab hac hbc hu hAIIA
        . exact nab_pivotal_bc a b y hab (Ne.symm hya) hxy hu hAIIA
    . by_cases hxc : x = c; subst x
      . by_cases hya : y = a; subst y
        . simpa [h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc b c a hbc (Ne.symm hab) (Ne.symm hac) hu hAIIA
        . by_cases hyb : y = b; subst y
          . simpa [← h_nbc_eq_nac, h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc a c b hac hab (Ne.symm hbc) hu hAIIA
          . simpa [h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc b c y hbc (Ne.symm hyb) hxy hu hAIIA
      . -- x ∉ {a,b,c}
        obtain ⟨h_nbx_eq_nxb, h_nxb_eq_nab⟩ := n_ab_pivotal_bc_cb a b x hab (Ne.symm hxa) (Ne.symm hxb) hu hAIIA
        obtain ⟨_, h_nbx_eq_nax⟩ := n_ab_pivotal_bc_cb a x b (Ne.symm hxa) hab hxb hu hAIIA
        by_cases hya : y = a; subst y
        . simpa [h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc b x a (Ne.symm hxb) (Ne.symm hab) hxa hu hAIIA
        . by_cases hyb : y = b; subst y
          . simpa [← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc a x b (Ne.symm hxa) hab hxb hu hAIIA
          . by_cases hyc : y = c; subst y
            . simpa [← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc a x c (Ne.symm hxa) hac hxc hu hAIIA
            . simpa [h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc b x y (Ne.symm hxb) (Ne.symm hyb) hxy hu hAIIA

/-- **Arrow's Impossibility Theorem**: No SWF with ≥3 alternatives and ≥1 voters
    can satisfy Unanimity, IIA, and Non-Dictatorship simultaneously. -/
theorem Impossibility [Fintype α] (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N, (Unanimity R) ∧ (AIIA R) ∧ (NonDictatorship R) := by
  by_contra ⟨ R, ⟨ hu, hAIIA, hNonDictactor ⟩⟩
  apply hNonDictactor
  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha
  use pivoter a b hab hu
  intro x y hxy
  exact n_ab_dictate_xy a b c x y hab hac hbc hxy hu hAIIA
