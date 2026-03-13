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

lemma Preorder'.le_of_lt {α : Type} (p : Preorder' α) (a b : α) :
    p.lt a b → p.le a b := by
    intro h
    exact h.1

lemma Preorder'.lt_trans (p : Preorder' α) {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h
      exact h1.2 (p.trans _ _ _ h2.1 h)

/-- For a total preorder with distinct elements: ¬(a > b) implies b ≥ a -/
lemma Preorder'.le_of_not_lt (p : Preorder' α) (a b : α) :
    ¬ p.lt a b → p.le b a := by
  rw [Preorder'.not_lt]
  exact id

/-- Two elements are indifferent if both a ≤ b and b ≤ a -/
def Preorder'.indiff (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ p.le b a

/-- Indifference means neither is strictly preferred -/
lemma Preorder'.indiff_iff_not_lt (p : Preorder' α) (a b : α) :
    p.indiff a b ↔ (¬ p.lt a b ∧ ¬ p.lt b a) := by
  unfold Preorder'.indiff Preorder'.lt
  constructor
  · intro ⟨hab, hba⟩
    exact ⟨fun ⟨_, h⟩ => h hba, fun ⟨_, h⟩ => h hab⟩
  · intro ⟨hnab, hnba⟩
    push_neg at hnab hnba
    -- hnab : p.le a b → p.le b a
    -- hnba : p.le b a → p.le a b
    constructor
    · rcases p.total a b with h | h
      · exact h
      · exact hnba h
    · rcases p.total b a with h | h
      · exact h
      · exact hnab h

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

def AgreeStronglyOn {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≻[p i] b) ↔ a ≻[q i] b) ∧ ((b ≻[p i] a) ↔ b ≻[q i] a)

lemma agree_strongly_is_agree {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) :
    AgreeStronglyOn p q a b → AgreeOn p q a b := by
  intro h i
  have h2 := h i
  simp only [← Preorder'.not_lt, not_iff_not]
  exact ⟨h2.2, h2.1⟩

/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society. -/
def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α),
    (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b

/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
def AIIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≻[R p] b) ↔ a ≻[R q] b)

/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs. -/
def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)

/-! ## Preference Construction

We construct concrete preference orderings to build test profiles for the proof.
Given three alternatives, `prefer a₀ a₁ a₂` ranks them as `a₀ ≻ a₁ ≻ a₂`.
-/
variable [LinearOrder α]

/-- Construct a preference ordering `a₀ ≻ a₁ ≻ a₂`, using the ambient `LinearOrder`
    as a tiebreaker for elements outside `{a₀, a₁, a₂}`. -/
def prefer (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) : Preorder' α where
  le x y :=
    if x = a₂ then True              -- a₂ is bottom
    else if y = a₀ then True         -- a₀ is top
    else if x = a₀ then y = a₀       -- only a₀ ≤ a₀
    else if y = a₂ then x = a₂       -- only a₂ ≥ a₂
    else x ≤ y                        -- fallback to LinearOrder
  refl := by intro x; simp
  trans := by
    intro a b c ha hb; split_ifs with haa2 hca0 haa0 hca2 <;> simp_all
    by_cases hba0: b = a₀
    . simp_all
    . simp_all; exact le_trans ha.2 hb
  total := by intro a b; split_ifs <;> simp_all [le_total a b]

/-- In `prefer a₀ a₁ a₂`, we have `a₀ ≻ a₁`. -/
lemma pick_lt_01 (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).lt a₁ a₀ := by
  simp [Preorder'.lt, prefer]
  exact ⟨h02, Ne.symm h01⟩

lemma pick_le_01 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).le a₁ a₀ := by simp [prefer]

lemma pick_lt_12 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).lt a₂ a₁ := by
  simp [Preorder'.lt, prefer]
  split_ifs with ha10
  . exact absurd (Eq.symm ha10) h01
  . exact ⟨ h12, Ne.symm h02, h12 ⟩

lemma pick_le_12 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).le a₂ a₁ := by simp [prefer]

lemma pick_lt_02 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).lt a₂ a₀ := by
  simp [Preorder'.lt, prefer]
  exact ⟨h02, Ne.symm h02⟩

lemma pick_le_02 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (prefer a₀ a₁ a₂ h02).le a₂ a₀ := by simp [prefer]

/-! ## Preference with Ties

A preference ordering where two alternatives are tied (indifferent).
-/

/-- Position of the singleton (non-tied) element -/
inductive SingletonPosition | Top | Bottom

/-- `prefer_with_tie a b c pos` creates a preference where b and c are tied:
    - If pos = Top: a > (b ~ c)
    - If pos = Bottom: (b ~ c) > a -/
def prefer_with_tie (a b c : α) (pos : SingletonPosition) (hab : a ≠ b) : Preorder' α where
  le x y := match pos with
    | .Top =>
      if x = a then y = a           -- only a ≤ a (a is top)
      else if y = a then True       -- everything else ≤ a
      else True                     -- b ~ c: both b ≤ c and c ≤ b
    | .Bottom =>
      if y = a then x = a           -- only a ≥ a (a is bottom)
      else if x = a then True       -- a ≤ everything else
      else True                     -- b ~ c: both directions
  refl := by intro x; cases pos <;> simp
  trans := by
    intro x y z hxy hyz
    cases pos <;> simp only at hxy hyz ⊢
    · split_ifs at hxy hyz ⊢ <;> simp_all
    · split_ifs at hxy hyz ⊢ <;> simp_all
  total := by
    intro x y; cases pos
    · simp only; by_cases hxa : x = a <;> by_cases hya : y = a <;> simp_all
    · simp only; by_cases hxa : x = a <;> by_cases hya : y = a <;> simp_all

/-- In `prefer_with_tie a b c .Top`, we have a > b -/
lemma prefer_with_tie_top_lt_ab (a b c : α) (hab : a ≠ b) :
    (prefer_with_tie a b c .Top hab).lt b a := by
  simp only [Preorder'.lt, prefer_with_tie]
  constructor
  · simp [Ne.symm hab]
  · simp [Ne.symm hab]

/-- In `prefer_with_tie a b c .Top`, we have a > c -/
lemma prefer_with_tie_top_lt_ac (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    (prefer_with_tie a b c .Top hab).lt c a := by
  simp only [Preorder'.lt, prefer_with_tie]
  constructor
  · simp [Ne.symm hac]
  · simp [Ne.symm hac]

/-- In `prefer_with_tie a b c .Top`, b and c are indifferent: b ≤ c -/
lemma prefer_with_tie_top_le_bc (a b c : α) (hab : a ≠ b) :
    (prefer_with_tie a b c .Top hab).le b c := by
  simp only [prefer_with_tie]
  simp [Ne.symm hab]

/-- In `prefer_with_tie a b c .Top`, b and c are indifferent: c ≤ b -/
lemma prefer_with_tie_top_le_cb (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    (prefer_with_tie a b c .Top hab).le c b := by
  simp only [prefer_with_tie]
  simp [Ne.symm hac]

/-- In `prefer_with_tie a b c .Top`, b and c are indifferent (not b > c) -/
lemma prefer_with_tie_top_not_lt_bc (a b c : α) (hab : a ≠ b) :
    ¬(prefer_with_tie a b c .Top hab).lt c b := by
  simp only [Preorder'.lt, prefer_with_tie, not_and, not_not]
  intro _; simp [Ne.symm hab]

/-- In `prefer_with_tie a b c .Top`, b and c are indifferent (not c > b) -/
lemma prefer_with_tie_top_not_lt_cb (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    ¬(prefer_with_tie a b c .Top hab).lt b c := by
  simp only [Preorder'.lt, prefer_with_tie, not_and, not_not]
  intro _; simp [Ne.symm hac]

/-- In `prefer_with_tie a b c .Bottom`, b > a -/
lemma prefer_with_tie_bottom_lt_ba (a b c : α) (hab : a ≠ b) :
    (prefer_with_tie a b c .Bottom hab).lt a b := by
  simp only [Preorder'.lt, prefer_with_tie]
  constructor
  · simp [Ne.symm hab]
  · exact Ne.symm hab

/-- In `prefer_with_tie a b c .Bottom`, c > a -/
lemma prefer_with_tie_bottom_lt_ca (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    (prefer_with_tie a b c .Bottom hab).lt a c := by
  simp only [Preorder'.lt, prefer_with_tie]
  constructor
  · simp [Ne.symm hac]
  · exact Ne.symm hac

/-- In `prefer_with_tie a b c .Bottom`, b and c are indifferent: b ≤ c -/
lemma prefer_with_tie_bottom_le_bc (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    (prefer_with_tie a b c .Bottom hab).le b c := by
  simp only [prefer_with_tie]
  simp [Ne.symm hac]

/-- In `prefer_with_tie a b c .Bottom`, b and c are indifferent: c ≤ b -/
lemma prefer_with_tie_bottom_le_cb (a b c : α) (hab : a ≠ b) :
    (prefer_with_tie a b c .Bottom hab).le c b := by
  simp only [prefer_with_tie]
  simp [Ne.symm hab]

/-- In `prefer_with_tie a b c .Bottom`, b and c are indifferent (not b > c) -/
lemma prefer_with_tie_bottom_not_lt_bc (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    ¬(prefer_with_tie a b c .Bottom hab).lt c b := by
  simp only [Preorder'.lt, prefer_with_tie, not_and, not_not]
  intro _; simp [Ne.symm hab, Ne.symm hac]

/-- In `prefer_with_tie a b c .Bottom`, b and c are indifferent (not c > b) -/
lemma prefer_with_tie_bottom_not_lt_cb (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    ¬(prefer_with_tie a b c .Bottom hab).lt b c := by
  simp only [Preorder'.lt, prefer_with_tie, not_and, not_not]
  intro _
  simp [Ne.symm hab, Ne.symm hac]

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
      then prefer b b a (Ne.symm hab)  -- b on top
      else prefer a b b hab            -- a on top

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
  have: b ≻[R (fun i => prefer b b a (Ne.symm hab) )] a := by
    apply hu; intro i; simp [pick_lt_02 b _ a (Ne.symm hab)]
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
      then prefer b c a (Ne.symm hab)
      else prefer a b c hac
  -- soc prefer a > b > c
  have habc: a ≻[R mg1] b ≻ c  := by
    constructor
    -- a > b by def of n_ab
    . by_cases hn : n_ab = 0
      . -- Case n_ab = 0: All voters prefer a > b, use unanimity
        have h : ∀ i : Fin N, a ≻[mg1 i] b := by
          intro i; simp [mg1, hn]
          exact pick_lt_01 a b c hab hac
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
              simp only [(pick_lt_02 b c a (Ne.symm hab)).2, (pick_lt_02 b b a (Ne.symm hab)).2]
            . simp only [pick_le_02 b c a (Ne.symm hab), pick_le_02 b b a (Ne.symm hab)]
          . constructor
            . simp only [pick_le_01 a b c hac, pick_le_01 a b b hab]
            . rw[← not_iff_not]
              simp only [(pick_lt_01 a b c hab hac).2, (pick_lt_01 a b b hab hab).2]
        apply (hAIIA _ _ _ _ hp).mpr
        exact no_flip a b k hk
    -- b > c by unanimity
    . have h: ∀ i: Fin N, b ≻[mg1 i] c := by
        intro i; unfold mg1; split_ifs
        . exact pick_lt_01 b c a hbc (Ne.symm hab)
        . exact pick_lt_12 a b c hab hbc hac
      exact hu _ _ _ h
  intro pp h

  -- Magic profile 2: match arbitrary profile `pp` on (b,c)
  -- For i < n_ab: (b ~ c) > a, or b > c > a, or c > b > a (matching pp)
  -- For i = n_ab: b > a > c
  -- For i > n_ab: a > (b ~ c), or a > b > c, or a > c > b (matching pp)
  -- result: socPrefer b ≥ a > c
  let mg2 : Profile α N := fun i: Fin N =>
    if i < n_ab
      then
        if b ≻[pp i] c then prefer b c a (Ne.symm hab)
        else if c ≻[pp i] b then prefer c b a (Ne.symm hac)
        else prefer_with_tie a b c .Bottom hab  -- b ~ c, a at bottom
      else
        if i = n_ab
        then prefer b a c hbc
        else if b ≻[pp i] c then prefer a b c hac
        else if c ≻[pp i] b then prefer a c b hab
        else prefer_with_tie a b c .Top hab  -- b ~ c, a at top

  have h_agree: AgreeOn pp mg2 b c := by
    -- AgreeOn means: for all i, (b ≽[pp i] c ↔ b ≽[mg2 i] c) ∧ (c ≽[pp i] b ↔ c ≽[mg2 i] b)
    -- mg2 matches pp on (b,c) by construction:
    -- - when b ≻[pp] c: mg2 uses prefer with b > c
    -- - when c ≻[pp] b: mg2 uses prefer with c > b
    -- - when indifferent: mg2 uses prefer_with_tie with b ~ c
    unfold AgreeOn mg2; intro i
    by_cases hinab : i < n_ab
    · simp only [hinab, ↓reduceIte]
      by_cases hppibc : b ≻[pp i] c
      · simp only [hppibc, ↓reduceIte]
        -- mg2 i = prefer b c a, so b > c in mg2
        -- pp has b > c, so b ≽ c and ¬(c ≽ b) match
        constructor <;> simp only [pick_le_01, pick_le_12, prefer] <;> sorry
      · by_cases hppicb : c ≻[pp i] b
        · simp only [hppibc, hppicb, ↓reduceIte]
          -- mg2 i = prefer c b a, so c > b in mg2
          constructor <;> simp only [pick_le_01, pick_le_12, prefer] <;> sorry
        · simp only [hppibc, hppicb, ↓reduceIte]
          -- mg2 i = prefer_with_tie a b c .Bottom, so b ~ c in mg2
          constructor <;> simp only [prefer_with_tie] <;> sorry
    · simp only [hinab, ↓reduceIte]
      by_cases hieqnab : i = n_ab
      · simp only [hieqnab, ↓reduceIte]
        -- mg2 n_ab = prefer b a c, and we know b ≻[pp n_ab] c from h
        constructor <;> simp only [pick_le_01, pick_le_12, prefer] <;> sorry
      · simp only [hieqnab, ↓reduceIte]
        by_cases hppibc : b ≻[pp i] c
        · simp only [hppibc, ↓reduceIte]
          -- mg2 i = prefer a b c, so b > c in mg2
          constructor <;> simp only [pick_le_12, pick_le_02, prefer] <;> sorry
        · by_cases hppicb : c ≻[pp i] b
          · simp only [hppibc, hppicb, ↓reduceIte]
            -- mg2 i = prefer a c b, so c > b in mg2
            constructor <;> simp only [pick_le_12, pick_le_02, prefer] <;> sorry
          · simp only [hppibc, hppicb, ↓reduceIte]
            -- mg2 i = prefer_with_tie a b c .Top, so b ~ c in mg2
            constructor <;> simp only [prefer_with_tie] <;> sorry

  have hbac: b ≽[R mg2] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn mg2 (canonicalSwap a b hab n_ab.succ) b a := by
        unfold AgreeOn canonicalSwap; intro i; split_ifs with h
        . simp only [pick_lt_02 b b a (Ne.symm hab)]; unfold mg2; simp at h
          split_ifs with hinab hppibc hieqnab hppibc
          . simp only [pick_lt_02 b c a (Ne.symm hab)]
          . simp only [pick_lt_12 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)]
          . simp only [pick_lt_01 b a c (Ne.symm hab) hbc]
          . omega
          . omega
        . unfold mg2; simp at h
          have : ¬(i < n_ab) := by omega
          rw [Preorder'.lt_iff _ _ _ hab]
          simp only [pick_lt_02 a b b hab]
          split_ifs
          . omega
          . simp only [pick_lt_01 a b c hab hac]
          . simp only [pick_lt_02 a c b hab]
      apply (hAIIA _ _ _ _ h_agree_ba).mpr
      exact flipped a b
    -- By AIIA
    . have h_agree_ac: AgreeOn mg1 mg2 a c := by
        unfold AgreeOn mg2 mg1; intro i; simp
        split_ifs with hinab hppibc hieqnab hppibc
        . rfl
        . rw [Preorder'.lt_iff _ _ _ (Ne.symm hac)]
          simp only [pick_lt_02 c b a (Ne.symm hac), pick_lt_12 b c a hbc (Ne.symm hac)]
        . simp only [pick_lt_12 b a c (Ne.symm hab) hac hbc, pick_lt_02 a b c hac]
        . simp only [pick_lt_02 a b c hac]
        . simp [pick_lt_01 a c b hac hab, pick_lt_02 a b c hac]
      exact (hAIIA _ _ _ _ h_agree_ac).mp ((R mg1).lt_trans habc.2 habc.1)
  exact (hAIIA _ _ _ _ h_agree).mpr ((R mg2).lt_trans hbac.2 hbac.1)

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
    . exact pick_lt_02 b _ c hbc
  exact absurd
    (nab_pivotal_bc a b c hab hac hbc hu hAIIA cs h_pref) -- n_ab still dictates b over c
    (Preorder'.lt_asymm _ _ _ (flipped b c))              -- but n_bc flipped, so society should prefer c over b

/-- The pivotal voter for `(c, b)` comes no later than the one for `(a, b)`. -/
lemma ncb_le_nab (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R):
    pivoter c b (Ne.symm hbc) hu ≤ pivoter a b hab hu := by
  by_contra h; push_neg at h
  let n_ab := pivoter a b hab hu
  let n_cb := pivoter c b (Ne.symm hbc) hu
  let cs := canonicalSwap c b (Ne.symm hbc) n_ab.succ
  have: b ≻[cs n_ab] c := by simp [cs, canonicalSwap, pick_lt_02 b _ c hbc]
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
