import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Classical

/-! ## Preorder'

A total preorder over candidates `α`, representing an individual's preference ranking.
-/
variable {α : Type}

/-- A total preorder: reflexive, transitive, and total. -/
structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a

/-- Strict preference: `a` is strictly preferred to `b` iff `a ≤ b` but not `b ≤ a`. -/
@[simp]
def Preorder'.lt (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a

-- Notation: `a ≻[p] b` means voter with preference `p` strictly prefers `a` over `b`
notation a " ≻[" p  "] " b => Preorder'.lt p b a
notation a " ≽[" p  "] " b => Preorder'.le p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c
notation a " ≽[" p  "] " b "≻ " c => (a ≽[p] b) ∧ b ≻[p] c

lemma Preorder'.lt_asymm {p : Preorder' α} {a b : α} :
    p.lt a b → ¬ p.lt b a := by intro ⟨_, hnba⟩ ⟨hba, _⟩; exact hnba hba

lemma Preorder'.not_lt {α : Type} {p : Preorder' α} {a b : α} :
    ¬ p.lt a b ↔ p.le b a := by simp [Preorder'.lt, p.total]

lemma Preorder'.lt_trans {p : Preorder' α} {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h; exact h1.2 (p.trans _ _ _ h2.1 h)

lemma Preorder'.lt_of_lt_of_le {p : Preorder' α} {a b c : α}
    (hab : p.lt a b) (hbc : p.le b c) : p.lt a c := by
    simp [Preorder'.lt] at hab ⊢; constructor
    . exact p.trans _ _ _ hab.1 hbc
    . intro h; exact absurd (p.trans _ _ _ hbc h) hab.2

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
def SWF (α : Type) (N : ℕ) := Profile α N → Preorder' α

/-- Voter `k` is a dictator for the pair `(a, b)` if whenever `k` prefers `a` over `b`,
    society also prefers `a` over `b`. -/
def Dictates (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b

/-- Two profiles agree on `(a, b)` if every voter ranks `a` vs `b` the same way in both. -/
@[simp]
def AgreeOn (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)

/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society. -/
def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α), (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b

/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
def AIIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≽[R p] b) ↔ a ≽[R q] b) ∧ ((b ≽[R p] a) ↔ b ≽[R q] a)

/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs. -/
def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)

/-! ## Preference Construction

We construct concrete preference orderings to build test profiles for the proof.
Given three alternatives, `prefer a₀ a₁ a₂ tie` ranks them with optional ties.
-/

/-- Where ties occur in a 3-element preference ranking -/
inductive Tie | Not | Top | Bot

/-- Construct a preference ordering with optional ties:
    - `Tie.Not`: a₀ > a₁ > a₂ (strict ranking)
    - `Tie.Top`: a₀ ~ a₁ > a₂ (top two tied)
    - `Tie.Bot`: a₀ > a₁ ~ a₂ (bottom two tied) -/
def prefer (a₀ _a₁ a₂ : α) (tie : Tie) (h02 : a₀ ≠ a₂) : Preorder' α where
  le x y := match tie with
    | .Not =>
      if x = a₂ then True              -- a₂ is bottom
      else if y = a₀ then True         -- a₀ is top
      else if x = a₀ then y = a₀       -- only a₀ ≤ a₀
      else if y = a₂ then x = a₂       -- only a₂ ≥ a₂
      else True
    | .Top =>
      if y = a₂ then x = a₂           -- only a₂ ≥ a₂ (a₂ is bottom)
      else if x = a₂ then True        -- a₂ ≤ everything else
      else True                        -- a₀ ~ a₁: both directions
    | .Bot =>
      if x = a₀ then y = a₀           -- only a₀ ≤ a₀ (a₀ is top)
      else if y = a₀ then True        -- everything else ≤ a₀
      else True                        -- a₁ ~ a₂: both directions
  refl := by intro x; cases tie <;> simp
  trans := by intro a b c ha hb; split <;> split_ifs <;> simp_all
  total := by intro a b; split <;> by_cases a = a₂ <;> by_cases b = a₀ <;> simp_all

lemma prefer_expand
  (top mid bot: α)(tie: Tie := Tie.Not)(htb: top ≠ bot)
  :let p:= prefer top mid bot tie htb
  (top ≽[p] mid) ∧ (mid ≽[p] bot) ∧ (top ≽[p] bot) ∧ (¬ bot ≽[p] top) ∧
  (
    match tie with
    | .Not => (top ≠ mid → ¬ mid ≽[p] top) ∧ (mid ≠ bot → ¬ bot ≽[p] mid)
    | .Top => mid ≠ bot → ((mid ≽[p] top) ∧ ¬ bot ≽[p] mid)
    | .Bot => top ≠ mid → ((¬ mid ≽[p] top) ∧ bot ≽[p] mid)
  )
  := by
  intro p; unfold p prefer; simp; refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals split <;> try simp_all [Ne.symm htb] <;> intro h <;> exact Ne.symm h

/-! ## Pivotal Voter

The key construction: we find the "pivotal voter" who flips society's preference.
Starting from a profile where everyone prefers `b ≻ a`, we flip voters one by one
to prefer `a ≻ b`. By unanimity, society eventually flips too. The first voter
whose flip changes society's preference is the pivotal voter.
-/
variable [NeZero N] {R : SWF α N}

/-- A family of profiles indexed by `k ∈ Fin (N+1)`:
    voters `0..k-1` prefer `b ≻ a`, voters `k..N-1` prefer `a ≻ b`. -/
@[simp]
def canonicalSwap (a b : α) (hab : a ≠ b) : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      -- `prefer` takes 3 items, we duplicate middle as a workaround
      then prefer b b a .Not (Ne.symm hab)  -- b on top
      else prefer a b b .Not hab            -- a on top

/-- `flipping R a b hab k` holds iff society prefers `b ≻ a` when voters `0..k` prefer `b ≻ a`. -/
def flipping (R : SWF α N) (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => ¬ a ≻[R (canonicalSwap a b hab k.succ)] b

/-- By unanimity, a flip must occur: when all voters prefer `b ≻ a`, so does society. -/
lemma flip_exists (R : SWF α N) (a b : α) (hab : a ≠ b) (hu : Unanimity R):
    ∃ k, flipping R a b hab k := by
  use (0:Fin N).rev
  unfold flipping canonicalSwap
  have: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  simp [Nat.sub_add_cancel this]
  have : b ≻[R (fun i => prefer b b a .Not (Ne.symm hab) )] a := by
    apply hu; intro _; simp [prefer_expand b b a]
  intro _; exact this.1

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
  exact Fin.find_spec (flip_exists R a b hab hu) |> Preorder'.not_lt.mp

/-- The pivotal voter for `(a, b)` dictates the pair `(b, c)`. -/
lemma nab_dictate_bc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : Dictates R (pivoter a b hab hu) b c := by
  let n_ab := pivoter a b hab hu
  have hba := Ne.symm hab; have hca := Ne.symm hac; have hcb := Ne.symm hbc

  -- Magic profile 1
  -- 0 ... k-1 prefer b ≻ c ≻ a
  -- k ... N-1 prefer a ≻ b ≻ c
  -- Result: Society prefers a ≻ b ≻ c
  let mg1: Profile α N := fun i: Fin N =>
    if i < n_ab.val
      then prefer b c a .Not hba
      else prefer a b c .Not hac

  have habc: a ≻[R mg1] b ≻ c  := by
    constructor
    -- a ≻ b by definition of n_ab
    -- note that voter is `Fin N` but the family of profiles is `Fin N+1`.
    -- The profile zero is not handled in `flipping` related functions.
    . by_cases hn : n_ab = 0
      . -- Case n_ab = 0: All voters prefer a > b, use unanimity
        have h : ∀ i : Fin N, a ≻[mg1 i] b := by
          intro _; simp [mg1, hn, prefer_expand a b c, hab]
        exact hu _ _ _ h
      . -- Case n_ab ≠ 0: Use no_flip
        let k := n_ab - 1
        have hk_succ : k.val + 1 = n_ab.val := by
          simp only [k, Fin.val_sub_one_of_ne_zero hn]
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hn))
        have hk : k.val < n_ab := by omega
        have hp : AgreeOn mg1 (canonicalSwap a b hab k.succ) a b := by
          intro i; unfold mg1
          by_cases hi : i.val < n_ab.val <;> simp [hk_succ, hi]
          . simp [prefer_expand b b a, prefer_expand b c a]
          . simp [prefer_expand a b b, prefer_expand a b c, hab]

        simp [hAIIA _ _ _ _ hp]
        exact no_flip a b k hk
    -- b ≻ c by unanimity
    . have h: ∀ i: Fin N, b ≻[mg1 i] c := by
        intro _; unfold mg1; split_ifs
        all_goals simp [prefer_expand b c a, prefer_expand a b c, hbc]
      exact hu _ _ _ h
  intro pp h_pp_bc
  -- `pp` has arbitrary preference on (b,c), except n_ab

  -- Magic profile 2: match `pp` on (b,c)
  -- For i < n_ab: (b ? c) ≻ a (matching pp)
  -- For i = n_ab: b ≻ a ≻ c
  -- For i > n_ab: a ≻ (b ? c) (matching pp)
  -- Result: Society prefers b ≽ a ≻ c
  let mg2 : Profile α N := fun i: Fin N =>
    if i < n_ab
      then match (pp i).cmp b c with
        | .LT     _ _ => prefer c b a .Not hca
        | .GT     _ _ => prefer b c a .Not hba
        | .Indiff _ _ => prefer b c a .Top hba  -- b ~ c ≻ a
      else
        if i = n_ab then prefer b a c .Not hbc
        else match (pp i).cmp b c with
        | .LT     _ _ => prefer a c b .Not hab
        | .GT     _ _ => prefer a b c .Not hac
        | .Indiff _ _ => prefer a b c .Bot hac  -- a ≻ b ~ c

  have h_agree: AgreeOn pp mg2 b c := by
    simp [mg2]; intro i; split_ifs
    . -- i < n_ab
      cases (pp i).cmp b c with
      | LT     h  hn => simp [ h, hn, prefer_expand c b a, hcb]
      | GT     hn h  => simp [ h, hn, prefer_expand b c a, hbc]
      | Indiff h1 h2 => simp [h1, h2, prefer_expand b c a .Top hba, hca]
    . -- i = n_ab
      subst i n_ab; simp [h_pp_bc.1, h_pp_bc.2, prefer_expand b a c .Not hbc]
    . -- i > n_ab
      cases (pp i).cmp b c with
      | LT     h  hn => simp [ h, hn, prefer_expand a c b, hcb]
      | GT     hn h  => simp [ h, hn, prefer_expand a b c, hbc]
      | Indiff h1 h2 => simp [h1, h2, prefer_expand a b c .Bot hac, hab]

  have hbac: b ≽[R mg2] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn mg2 (canonicalSwap a b hab n_ab.succ) b a := by
        unfold mg2; intro i;
        by_cases hi: i < n_ab
        . have :i.val < n_ab +1 := by omega
          simp [hi, this, prefer_expand b b a]
          split
          . simp [prefer_expand c b a, hba]
          . simp [prefer_expand b c a]
          . simp [prefer_expand b c a .Top hba]
        . by_cases hi2: i = n_ab
          . simp [hi2, prefer_expand b b a, prefer_expand b a c, hba]
          . have :¬ (i.val < n_ab +1 ):= by omega
            simp [hi, hi2, this, prefer_expand a b b]
            split
            . simp [prefer_expand a c b]
            . simp [prefer_expand a b c, hab]
            . simp [prefer_expand a b c .Bot hac, hab]
      simp only [hAIIA _ _ _ _ h_agree_ba]
      exact flipped a b
    -- By AIIA
    . have h_agree_ac: AgreeOn mg2 mg1 a c := by
        simp [mg2, mg1]; intro i; split_ifs
        . -- i < n_ab
          simp [prefer_expand b c a, hca]
          split
          . simp [prefer_expand c b a]
          . simp [prefer_expand b c a, hca]
          . simp [prefer_expand b c a .Top hba, hca]
        . -- i = n_ab
          simp [prefer_expand a b c, prefer_expand b a c, hac]
        . -- i > n_ab
          simp [prefer_expand a b c]
          split
          . simp [prefer_expand a c b, hac]
          . simp [prefer_expand a b c]
          . simp [prefer_expand a b c .Bot hac]
      simp [hAIIA _ _ _ _ h_agree_ac]
      exact (R mg1).lt_trans habc.2 habc.1

  simp [hAIIA _ _ _ _ h_agree]
  -- transitivity from b ≽ a ≻ c
  show b ≻[R mg2] c
  exact (R mg2).lt_of_lt_of_le hbac.2 hbac.1

/-- The pivotal voter for `(a, b)` comes no later than the one for `(b, c)`. -/
lemma nab_le_nbc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : pivoter a b hab hu ≤ pivoter b c hbc hu := by
  by_contra h; push_neg at h;
  let cs := canonicalSwap b c hbc (pivoter b c hbc hu).succ
  have h_pref : b ≻[cs (pivoter a b hab hu)] c := by
    simp [cs]; split_ifs with hh <;> simp_all [prefer_expand b c c]; omega
  exact absurd
    (nab_dictate_bc a b c hab hac hbc hu hAIIA cs h_pref) -- n_ab still dictates b over c
    (flipped b c |> Preorder'.not_lt.mpr)                 -- but n_bc flipped, so society should prefer c over b

/-- The pivotal voter for `(c, b)` comes no later than the one for `(a, b)`. -/
lemma ncb_le_nab (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R):
    pivoter c b (Ne.symm hbc) hu ≤ pivoter a b hab hu := by
  by_contra h; push_neg at h
  let n_ab := pivoter a b hab hu
  let cs := canonicalSwap c b (Ne.symm hbc) n_ab.succ
  have: b ≻[cs n_ab] c := by simp [cs, prefer_expand b b c]
  exact absurd
    (nab_dictate_bc a b c hab hac hbc hu hAIIA cs this) -- n_ab prefer b over c, so is society
    (no_flip c b n_ab h |> Preorder'.lt_asymm)          -- n_ab before pivoter, so b c shouldn't flip

/-- Combining the above: `pivoter (c, b) ≤ pivoter (b, c)`. -/
lemma ncb_le_nbc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R)
    : pivoter c b (Ne.symm hbc) hu ≤ pivoter b c hbc hu :=
  le_trans (ncb_le_nab a b c hab hac hbc hu hAIIA) (nab_le_nbc a b c hab hac hbc hu hAIIA)

/-- All pivotal voters for pairs in `{a, b, c}` are the same:
    `pivoter (b, c) = pivoter (c, b) = pivoter (a, b)`. -/
lemma nab_eq_nbc_ncb (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hAIIA: AIIA R):
    (pivoter b c hbc hu) = (pivoter c b (Ne.symm hbc) hu) ∧
    (pivoter c b (Ne.symm hbc) hu) = pivoter a b hab hu := by

  have h_nab_le_nbc := nab_le_nbc a b c hab hac hbc hu hAIIA
  have h_ncb_le_nab := ncb_le_nab a b c hab hac hbc hu hAIIA
  have h_ncb_le_nbc := ncb_le_nbc a b c hab hac hbc hu hAIIA

  -- As b and c are distinct and arbitrary, n_bc ≤ n_cb also holds
  have h_nbc_le_ncb := ncb_le_nbc a c b hac hab (Ne.symm hbc) hu hAIIA

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb := le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_nab_le_ncb := le_trans h_nab_le_nbc h_nbc_le_ncb
  have h_ncb_eq_nab := le_antisymm h_ncb_le_nab h_nab_le_ncb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

/-- The pivotal voter for any pair `(a, b)` dictates *every* pair `(x, y)`. -/
lemma n_ab_dictate_xy (a b c x y: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
    (hu: Unanimity R) (hAIIA: AIIA R):
    Dictates R (pivoter a b hab hu) x y := by
  -- prepare bridging equalities: n_ab = n_bc = n_cb
  have := nab_eq_nbc_ncb a b c hab hac hbc hu hAIIA
  by_cases hxb: x ≠ b <;> by_cases hxc: x ≠ c <;> by_cases hyc: y ≠ c <;> simp_all <;> try subst x y
  -- x ∉ {b, c}, y ≠ c, bridging from n_cx = n_bc = n_ab
  . have := nab_dictate_bc c x y (Ne.symm hxc) (Ne.symm hyc) hxy hu hAIIA
    have := nab_eq_nbc_ncb b c x hbc (Ne.symm hxb) (Ne.symm hxc) hu hAIIA
    simp_all
  -- x ∉ {b, c}, y = c, bridging from n_bx = n_cb = n_ab
  . have := nab_dictate_bc b x c (Ne.symm hxb) hbc hxc hu hAIIA
    have := nab_eq_nbc_ncb c b x (Ne.symm hbc) (Ne.symm hxc) (Ne.symm hxb) hu hAIIA
    simp_all
  -- x = c, y ≠ c
  . by_cases hyb: y ≠ b
    -- n_bc = n_ab
    . have := nab_dictate_bc b c y hbc (Ne.symm hyb) (Ne.symm hyc) hu hAIIA
      simp_all
    -- n_ac = n_cb = n_ab
    . have := nab_dictate_bc a c b hac hab (Ne.symm hbc) hu hAIIA
      have := nab_eq_nbc_ncb a c b hac hab (Ne.symm hbc) hu hAIIA
      simp_all
  -- x = b, y ≠ c, n_cb = n_ab
  . have := nab_dictate_bc c b y (Ne.symm hbc) (Ne.symm hyc) hxy hu hAIIA
    simp_all
  -- x = b, y = c
  . exact nab_dictate_bc a b c hab hac hbc hu hAIIA

/-- **Arrow's Impossibility Theorem**: No SWF with ≥3 alternatives and ≥1 voters
    can satisfy Unanimity, IIA, and Non-Dictatorship simultaneously. -/
theorem Impossibility [Fintype α] (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N, (Unanimity R) ∧ (AIIA R) ∧ (NonDictatorship R) := by
  by_contra ⟨ R, ⟨ hu, hAIIA, hNonDictator ⟩⟩
  apply hNonDictator
  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha
  use pivoter a b hab hu
  intro x y hxy
  exact n_ab_dictate_xy a b c x y hab hac hbc hxy hu hAIIA
