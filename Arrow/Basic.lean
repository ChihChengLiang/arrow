import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

open Classical in
noncomputable section

variable (α: Type) [Fintype α] [DecidableEq α] -- α is the type of alternatives
variable (N: ℕ ) -- N is the number of voters
variable (ha: Fintype.card α ≥ 3)

structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a
  antisymm : ∀ a b, le a b → le b a → a = b

def Preorder'.lt {α : Type} (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a

lemma Preorder'.lt_asymm {α : Type} (p : Preorder' α) (a b : α) :
    p.lt a b → ¬ p.lt b a := by
  intro ⟨hab, hnba⟩ ⟨hba, _⟩
  exact hnba hba

lemma Preorder'.lt_irrefl {α : Type} (p : Preorder' α) (a : α) :
    ¬ p.lt a a := by
  intro ⟨h, hn⟩
  exact hn h

lemma Preorder'.lt_of_not_lt {α : Type} (p : Preorder' α) (a b : α)
    (hab : a ≠ b) (h : ¬ p.lt b a) : p.lt a b := by
  unfold Preorder'.lt at *
  push_neg at h
  rcases p.total a b with hab' | hba'
  · constructor
    · exact hab'
    · intro hba
      exact hab (p.antisymm a b hab' hba)
  · constructor
    · exact h hba'
    · intro hba
      exact hab (p.antisymm a b (h hba') hba)

lemma Preorder'.lt_trans  {α : Type} (p : Preorder' α) {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h
      exact h1.2 (p.trans _ _ _ h2.1 h)

-- Map individual i to their preferences
def PreferenceProfile (α : Type) (N : ℕ) :=
  Fin N → Preorder' α

def SocialWelfareFunction (α : Type) (N : ℕ) :=
  (Fin N → Preorder' α) → Preorder' α

-- profile generating function. Useful for building profile with a pivotal voter
abbrev profileGen: Type := Fin (N+1) →  PreferenceProfile α N

-- society prefers a over b in profile p
abbrev socPrefers {α : Type} {N : ℕ}
    (R : SocialWelfareFunction α N) (p : PreferenceProfile α N) (a b : α) : Prop :=
  (R p).lt b a  -- b is below a, meaning a is preferred

abbrev socWeakPrefers {α : Type} {N : ℕ}
    (R : SocialWelfareFunction α N) (p : PreferenceProfile α N) (a b : α) : Prop :=
  (R p).le b a  -- b is below a, meaning a is preferred

-- voter prefers a over b
abbrev voterPrefers {α : Type} (p : Preorder' α) (a b : α) : Prop :=
  p.lt b a  -- b is below a, meaning a is preferred

-- In society R, voter k dictate just ab
def dictate_ab {α : Type} {N : ℕ} (R : SocialWelfareFunction α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: PreferenceProfile α N ), voterPrefers (p k) a b → socPrefers R p a b

-- all voters in both profile p and q prefer a over b
def sameCol {α : Type} {N : ℕ}
    (p q : PreferenceProfile α N) (a b : α) : Prop :=
  ∀ i, voterPrefers (p i) a b ↔ voterPrefers (q i) a b  -- voter i prefers a over b in p iff in q

-- if everyone like `a` over `b`, so is society
def unanimity (R : SocialWelfareFunction α N) : Prop :=
  ∀ (p: PreferenceProfile α N) (a b: α),
    (∀ i: Fin N, voterPrefers (p i) a b) → socPrefers R p a b

-- (AIIA: Arrow's Independence of Irrelevant Alternatives)
-- If each individual's preferences over `a` and `b` are the same in profile `p` and profile `q`,
-- then SocialWelfareFunction(p) and SocialWelfareFunction(q) rank the two alternatives the same
def AIIA (R : SocialWelfareFunction α N) : Prop :=
  ∀ (p q: PreferenceProfile α N) (a b: α),
    sameCol p q a b → (socPrefers R p a b ↔ socPrefers R q a b)

def NonDictactorship (R : SocialWelfareFunction α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), dictate_ab R i a b)

-- Everyone starts with a > b, then one by one from left b > a
def swappingProfileAB
  {α : Type} (N:ℕ) (k: Fin N)
  (a b :α) :=
  {
    p: PreferenceProfile α N | ∀ (i: Fin N),
    (i < k ↔ voterPrefers (p i) b a) ∧ (k ≤ i ↔ voterPrefers (p i) a b)
  }

lemma flip_exists (P : Fin (N+1) → Prop) (h0 : ¬ P 0) (hN : P (Fin.last N)) :
    ∃ k : Fin N, ¬ P k.castSucc ∧ P k.succ := by
  induction N with
  | zero =>
    -- Fin.last 0 = 0, so hN and h0 contradict
    simp [Fin.last] at hN h0
    exact absurd hN h0
  | succ n ih =>
    -- either P flips somewhere in 0..n, or it flips at n→n+1
    by_cases h : P (Fin.last n).castSucc
    · -- P is true before the end, recurse on smaller range
      let P' : Fin (n+1) → Prop := fun k => P k.castSucc
      have h0' : ¬ P' 0 := by
        simp [P']
        exact h0
      by_cases h : P' (Fin.last n)
      . -- P' flips somewhere in 0..n, use ih
        have hk := ih P' h0' h
        simp [P'] at hk
        obtain ⟨ k, hk2⟩ := hk
        exact ⟨k.castSucc, hk2⟩
      . -- P' is false at Fin.last n, so flip happens at last step
        simp [P'] at h
        use Fin.last n
        constructor
        exact h
        exact hN
    · -- P flips at the last step
      use Fin.last n
      constructor
      exact h
      exact hN

def swapping_k
  {α : Type} {N:ℕ} (p q: PreferenceProfile α N) (k: Fin (N+1))
  : PreferenceProfile α N :=
  fun i: Fin N => if i < k.val then p i else q i

def swapping_k2
  {α : Type} {N:ℕ} (r s t: PreferenceProfile α N) (k: Fin (N+1))
  : PreferenceProfile α N :=
  fun i: Fin N =>
    if i < k.val
    then r i
    else if i = k.val
      then s i
      else t i


def preorderFromRanking {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α)
    (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) : Preorder' α where
  le x y :=
    -- first handle the 6 ordered pairs among a₀, a₁, a₂
    if x = a₂ then True              -- a₂ is bottom, below everything
    else if y = a₀ then True         -- a₀ is top, everything is below it
    else if x = a₀ then y = a₀      -- a₀ only ≤ itself
    else if y = a₂ then x = a₂      -- a₂ only ≥ itself
    -- now x, y ∉ {a₀, a₂} handled, only a₁ vs others remain
    else x ≤ y                        -- fallback to LinearOrder
  refl := by
    intro x
    simp
  trans := by
    intro a b c ha hb
    split_ifs with haa2 hca0 haa0 hca2
    . split_ifs at hb with hba2 hba0 hca2
      . split_ifs at ha with hba0
        . rw[hba0] at hba2
          exact absurd hba2 h02
        . rw[ha] at hba2
          exact absurd hba2 h02
      . exact hb
      . split_ifs at ha
        rw[ha] at hb
        exact absurd hb h02
      . split_ifs at ha
        exact absurd ha hba0
    . split_ifs at ha with hba0 hba2
      . split_ifs at hb with hba2
        . rw[hba0] at hba2
          exact absurd hba2 h02
        . rw[hb] at hca2
          exact absurd hca2 h02
      . exact ha
      . split_ifs at hb
        . exact absurd hb hba2
    . split_ifs at ha with hba0 hba2
      . split_ifs at hb with hba2
        . rw[hba0] at hba2
          exact absurd hba2 h02
        . exact absurd hb hca0
      . exact absurd ha haa2
      . split_ifs at hb
        exact le_trans ha hb
  total := by
    intro a b
    split_ifs with haa2 hba2 haa0 hba0 hba0 hba2 haa0 haa0 hba2 hba2
    tauto
    tauto
    tauto
    tauto
    tauto
    tauto
    tauto
    tauto
    tauto
    tauto
    exact le_total a b
  antisymm := by
    intro a b ha hb
    split_ifs at ha with haa2 hba0 haa0 hba2
    . split_ifs at hb with hba2 haa0 hba0
      . rw [haa2, hba2]
      . rw[haa0] at haa2; exact absurd haa2 h02
      . exact absurd hb haa0
      . rw[hb, haa2]
    . split_ifs at hb with hba2 haa0
      . rw[hba0 ] at hba2; exact absurd hba2 h02
      . rw[hba0, haa0]
      .  exact absurd hb haa0
    . rw[ha, haa0]
    . rw[ha , hba2]
    . split_ifs at hb
      exact le_antisymm ha hb

lemma preorderFromRanking_lt_01 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (preorderFromRanking a₀ a₁ a₂ h01 h12 h02).lt a₁ a₀ := by
  simp [Preorder'.lt, preorderFromRanking]
  exact ⟨h02, Ne.symm h01⟩

lemma preorderFromRanking_lt_12 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (preorderFromRanking a₀ a₁ a₂ h01 h12 h02).lt a₂ a₁ := by
  simp [Preorder'.lt, preorderFromRanking]
  split_ifs with ha10
  . exact absurd (Eq.symm ha10) h01
  . exact ⟨ h12, Ne.symm h02, h12 ⟩


lemma preorderFromRanking_lt_02 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (preorderFromRanking a₀ a₁ a₂ h01 h12 h02).lt a₂ a₀ := by
  simp [Preorder'.lt, preorderFromRanking]
  exact ⟨h02, Ne.symm h02⟩

-- if a property holds at 0 and not at N (or vice versa),
-- there must be a first index where it flips
lemma swapping_exists_pivotal
  {α : Type}
  {N:ℕ}
  (a b : α)
  (hab : a ≠ b)
  {R: SocialWelfareFunction α N}
  (p q: PreferenceProfile α N)
  (hp: ∀ i: Fin N, voterPrefers (p i) b a)
  (hq: ∀ i: Fin N, voterPrefers (q i) a b)
  (hunanimity: unanimity _ _ R)
  :
    ∃ k : Fin N, socPrefers R (swapping_k p q k.castSucc) a b ∧ socPrefers R (swapping_k p q k.succ) b a := by

  have h_flipping : socPrefers R (swapping_k p q 0) a b  ∧ socPrefers R (swapping_k p q (Fin.last N)) b a := by
    have h0: swapping_k p q 0 = q := by unfold swapping_k; simp
    have hN: swapping_k p q (Fin.last N) = p := by unfold swapping_k; simp
    rw [h0, hN]
    apply hunanimity at hq
    apply hunanimity at hp
    exact ⟨hq , hp⟩

  obtain ⟨ hStart, hEnd ⟩ := h_flipping
  let P := fun k => socPrefers R (swapping_k p q k) b a
  have hp0: ¬ P 0 := by
    simp [P]
    apply  Preorder'.lt_asymm at hStart
    exact hStart
  have hpN: P (Fin.last N) := by
    simp [P]
    exact hEnd
  have hh: ∃ k : Fin N, ¬ P k.castSucc ∧ P k.succ := by
    exact flip_exists N P hp0 hpN
  obtain ⟨ k, ⟨ hleft, hright ⟩ ⟩ := hh
  simp [P] at hleft hright
  use k
  constructor
  exact Preorder'.lt_of_not_lt _ b a (Ne.symm hab) hleft
  exact hright

lemma nab_pivotal_bc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  {R: SocialWelfareFunction α N}
  (p q t: PreferenceProfile α N)
  (hp: ∀ i: Fin N, voterPrefers (p i) b c ∧ voterPrefers (p i) c a)
  (hq: ∀ i: Fin N, voterPrefers (q i) a b ∧ voterPrefers (q i) b c)
  (ht: ∀ i: Fin N, voterPrefers (t i) b a ∧ voterPrefers (t i) a c)
  (hunanimity: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  :
  ∃ n_ab: Fin N, ∀ pp: PreferenceProfile α N,
    voterPrefers (pp n_ab) b c → socPrefers R pp b c := by
  have hpba: ∀ i: Fin N, voterPrefers (p i) b a := by intro i; exact (p i).lt_trans (hp i).2 (hp i).1
  have hqab: ∀ i: Fin N, voterPrefers (q i) a b := by intro i; exact (hq i).1
  obtain ⟨n_ab, h_nab_pivot_p ⟩ := swapping_exists_pivotal a b hab p q hpba hqab hunanimity

  -- soc prefer a > b > c
  have habc:
    socPrefers R (swapping_k p q n_ab.castSucc) a b ∧
    socPrefers R (swapping_k p q n_ab.castSucc) b c  := by
    constructor
    -- a > b by def of n_ab
    . exact h_nab_pivot_p.1
    -- b > c by def of n_ab
    . have h: ∀ i: Fin N, voterPrefers (swapping_k p q n_ab.castSucc i) b c := by
        intro i
        unfold swapping_k
        split_ifs
        . exact (hp i).1
        . exact (hq i).2
      apply hunanimity at h
      exact h

  use n_ab
  intro pp h

  let rr : PreferenceProfile α N := fun i: Fin N =>
    if i < n_ab
      then
        if  voterPrefers (pp i) b c
          then preorderFromRanking b c a hbc (Ne.symm hac) (Ne.symm hab)
          else preorderFromRanking c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
      else
        if i = n_ab
        then preorderFromRanking b a c (Ne.symm hab) hac hbc
        else if  voterPrefers (pp i) b c
          then preorderFromRanking a b c hab hbc hac
          else preorderFromRanking a c b hac (Ne.symm hbc) hab

  have hSameCol: sameCol pp rr b c := by
    unfold sameCol
    intro i
    unfold rr
    split_ifs with hi hppibc hieqnab hppibc
    . simp [preorderFromRanking_lt_01 b c a hbc (Ne.symm hac) (Ne.symm hab)]
      exact hppibc
    . rw [← not_iff_not]
      constructor
      . intro
        unfold voterPrefers
        apply  Preorder'.lt_asymm
        simp [preorderFromRanking_lt_01 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)]
      . intro
        exact hppibc
    . simp [preorderFromRanking_lt_02 b a c (Ne.symm hab) hac hbc]
      rw [hieqnab]
      exact h
    . simp [preorderFromRanking_lt_12 a b c hab hbc hac]; exact hppibc
    . rw [← not_iff_not]
      constructor
      . intro
        unfold voterPrefers
        apply  Preorder'.lt_asymm
        simp [preorderFromRanking_lt_12 a c b hac (Ne.symm hbc) hab]
      . intro
        exact hppibc

  have hbac:
    socPrefers R rr b a ∧
    socPrefers R rr a c := by
    constructor
    . exact h_nab_pivot_p.2
    . have hsoc_swp_ac: socPrefers R (swapping_k p q n_ab.castSucc) a c :=
        (R (swapping_k p q n_ab.castSucc)).lt_trans habc.2 habc.1
      have hSameCol_ac: sameCol (swapping_k p q n_ab.castSucc) rr a c := by
        unfold sameCol rr swapping_k
        intro i
        simp at *
        split_ifs with hinab hppibc hieqnab hppibc
        . rw [← not_iff_not]
          constructor
          . intro h; apply Preorder'.lt_asymm
            exact preorderFromRanking_lt_12 b c a hbc (Ne.symm hac) (Ne.symm hab)
          . intro h; apply Preorder'.lt_asymm
            exact (hp i).2
        . rw [← not_iff_not]
          constructor
          . intro h; apply Preorder'.lt_asymm
            exact preorderFromRanking_lt_02 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
          . intro h; apply Preorder'.lt_asymm
            exact (hp i).2
        . simp [preorderFromRanking_lt_12 b a c (Ne.symm hab) hac hbc]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [preorderFromRanking_lt_02 a b c hab hbc hac]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [preorderFromRanking_lt_01 a c b hac (Ne.symm hbc) hab]
          exact (q i).lt_trans (hq i).2 (hq i).1

      have hSoc_rr_ac := by apply hAIIA at hSameCol_ac; exact hSameCol_ac
      exact hSoc_rr_ac.mp hsoc_swp_ac

  have hrr_bc := (R rr).lt_trans hbac.2 hbac.1
  have hSocPrefer := by apply hAIIA at hSameCol; exact hSameCol
  exact hSocPrefer.mpr hrr_bc

theorem Impossibility
    {α : Type} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SocialWelfareFunction α N,
    (unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictactorship _ _ R) := by
  by_contra h
  obtain ⟨ R, ⟨ hunanimity, hAIIA, hNonDictactor ⟩⟩ := h
  apply hNonDictactor
  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha

  -- let p
  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  let P' := {p: PreferenceProfile α N | ∀ i : Fin N, voterPrefers (p i) b c ∧ voterPrefers (p i) c a}
  let Q' := {q: PreferenceProfile α N | ∀ i : Fin N, voterPrefers (q i) a b ∧ voterPrefers (q i) b c}


  let p: profileGen α N :=
    fun k =>
      fun i =>
        if i.val < k.val
          then preorderFromRanking b c a hbc (Ne.symm hac) (Ne.symm hab)
          else preorderFromRanking a b c hab hbc hac
  have hpflipping: isFlipping R p a b := by
    simp only [isFlipping]
    constructor
    -- k = 0
    . apply hunanimity
      intro i
      simp only [p]
      have hi0: ¬ (i.val < 0) := Nat.not_lt_zero _
      simp
      exact preorderFromRanking_lt_01 a b c hab hbc hac
    -- k = N
    . apply hunanimity
      intro i
      simp only [p]
      have : ((i.castSucc).val < (Fin.last N).val) := by
        simp [Fin.castSucc, Fin.last]
      simp
      exact preorderFromRanking_lt_02 b c a hbc (Ne.symm hac) (Ne.symm hab)

  obtain ⟨n_ab, h_nab_pivot_p ⟩ := exists_pivotal a b hab N p hpflipping

  have habc: socPrefers R (p n_ab.castSucc) a b ∧ socPrefers R (p n_ab.castSucc) b c := by
    constructor
    -- by definiion of n_ab pivoting
    . rw[isPivotal] at h_nab_pivot_p
      exact h_nab_pivot_p.1
    -- by hunanimity
    . have hp: (∀ i: Fin N, voterPrefers (p n_ab.castSucc i) b c) := by
        intro i
        simp only [p]
        split_ifs with h
        . exact preorderFromRanking_lt_01 b c a hbc (Ne.symm hac) (Ne.symm hab)
        . exact preorderFromRanking_lt_12 a b c hab hbc hac
      apply hunanimity at hp
      exact hp

  -- i j k
  -- a b c

  -- let q
  -- 0...k-1 prefer b > a ∧ c > a
  -- k prefer b > a > c
  -- k+1 ... N prefer a > b ∧ c < a
  -- result: socPrefer b ≥ a > c

  -- let's see if we can ignore the square issue
  let q: profileGen α N :=
    fun k =>
      fun i =>
        if i.val < k.val
          then preorderFromRanking b c a hbc (Ne.symm hac) (Ne.symm hab)
          else if i.val = k.val
            then preorderFromRanking b a c (Ne.symm hab) hac hbc
            else preorderFromRanking a b c hab hbc hac

  -- For just a and b, q happens to be the situation p flip the social outcome.
  -- AIIA guarentee n_ab is pivotal in q too.
  -- But we don't have to show n_ab is pivotal, which requires wrangling with n_ab - 1 and troubles of Fin N.
  -- We only interest in showing n_ab flip q's outcome part.
  have hSocPreferQba: socPrefers R (q n_ab.castSucc) b a := by
    have hSameCol: sameCol (p n_ab.succ) (q n_ab.castSucc) b a := by
      simp only [sameCol]
      intro i
      simp only [p, q]
      by_cases hh: i.val < n_ab.castSucc.val
      . have hhh: i.val < n_ab.succ.val := by exact Nat.lt_succ_of_lt hh
        simp only [hhh, if_true]
        simp only [hh, if_true]
      . by_cases hhh: i.val = n_ab.castSucc.val
        . have hhhh: ¬ (i.val < n_ab.castSucc.val) := by omega
          simp only [hhhh, if_false]
          have hhhhh: (i.val < n_ab.succ.val) := by
            rw[hhh]
            exact Fin.castSucc_lt_succ
          simp only [hhhhh, if_true]
          simp only [hhh, if_true]
          rw[voterPrefers, voterPrefers]
          simp [preorderFromRanking_lt_01 b a c (Ne.symm hab) hac hbc]
          simp [preorderFromRanking_lt_02 b c a hbc (Ne.symm hac) (Ne.symm hab)]
        . have hhhh: i.val ≥ n_ab.succ.val := by
            push_neg at hh
            push_neg at hhh
            have h1 : n_ab.castSucc.val < i.val := Nat.lt_of_le_of_ne hh (Ne.symm hhh)
            exact Nat.succ_le_of_lt h1
          have hhhh: ¬(i.val < n_ab.succ.val) := by omega
          simp only [hhhh, if_false]
          simp only [hh, if_false]
          simp only [hhh, if_false]
    apply hAIIA at hSameCol
    exact hSameCol.mp h_nab_pivot_p.2

  -- society of p prefer a over c, because of transit preference from a b and b c.
  -- q has same preference of a and c with p. AIIA makes sure society of q prefers a over c too
  have hSocPreferQac: socPrefers R (q n_ab.castSucc) a c := by
    have hSameCol: sameCol (p n_ab.castSucc) (q n_ab.castSucc) a c := by
      simp only [sameCol]
      intro i
      simp only [p, q]
      by_cases hh: i.val < n_ab.castSucc.val
      . simp only [hh, if_true]
      . simp only [hh, if_false]
        by_cases hhh: i.val = n_ab.castSucc.val
        . simp only [hhh, if_true]
          simp [preorderFromRanking_lt_02 a b c hab hbc hac]
          simp [preorderFromRanking_lt_12 b a c (Ne.symm hab) hac hbc]
        . simp only [hhh, if_false]
    have hSocPreferPac: socPrefers R (p n_ab.castSucc) a c := by
      obtain ⟨ hab, hbc ⟩ := habc
      exact (R (p n_ab.castSucc)).lt_trans hbc hab
    apply hAIIA at hSameCol
    exact hSameCol.mp hSocPreferPac

  let pbc : profileGen α N  :=
    fun k =>
      fun i =>
        if i.val < k.val
          then preorderFromRanking a b c hab hbc hac  -- a > b > c
          else preorderFromRanking c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac) -- c > b > a


  let pbcProfile: PreferenceProfile α N := pbc n_ab.castSucc

  -- focusing on b c
  -- by AIIA with p q
  -- n_ab dictate b c (*)
  -- have h_n_ab_dictacte_bc:
  --   voterPrefers ((p n_ab.castSucc) n_ab) b c → socPrefers R (p n_ab.castSucc) b c  := by sorry

  have h_star : socPrefers R pbcProfile b c := by
    -- AIIA from ξ (q n_ab.castSucc): the {b,c} columns match
    have hSameCol : sameCol (q n_ab.castSucc) pbcProfile b c := by
      intro i
      simp [q]
      -- voters < n_ab: both have b > c ✓
      -- voters ≥ n_ab: both have c > b ✓
      sorry
    have hSocPreferQbc : socPrefers R (q n_ab.castSucc) b c := by
      exact (R (q n_ab.castSucc)).lt_trans hSocPreferQac hSocPreferQba
    exact (hAIIA _ _ _ _ hSameCol).mp hSocPreferQbc

  have hpbcflipping : isFlipping R pbc c b := by
    constructor
    · -- at k=0, all voters prefer c > b, so society prefers c > b
      apply hunanimity
      intro i
      simp [pbc]
      -- i.val < 0 is false, so all use preorderFromRanking a b c
      -- need: voterPrefers (preorderFromRanking a b c) b c
      exact preorderFromRanking_lt_01 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
    · -- at k=N, all voters prefer b > c, so society prefers b > c
      apply hunanimity
      intro i
      simp [pbc]
      -- i.val < N always, so all use preorderFromRanking c b a
      exact preorderFromRanking_lt_12 a b c hab hbc hac


  obtain ⟨n_bc, h_nbc_pivot⟩ := exists_pivotal c b (Ne.symm hbc) N pbc hpbcflipping

  -- n_bc ≥ n_ab
  have h_nab_le_nbc : n_ab ≤ n_bc := by
    by_contra h
    push_neg at h
    -- h : n_bc < n_ab, meaning at castSucc of n_bc, society still prefers b > c
    -- but h_nbc_pivot.1 says society prefers c > b at castSucc of n_bc
    have : socPrefers R (pbc n_bc.castSucc) c b := h_nbc_pivot.1
    -- h_star says socPrefers R (pbc n_ab.castSucc) b c
    -- but pbc n_bc.castSucc and pbc n_ab.castSucc have same {b,c} column
    -- when n_bc < n_ab, because the split point is earlier
    have hSameCol : sameCol (pbc n_bc.castSucc) (pbc n_ab.castSucc) b c := by
      intro i
      simp [pbc]
      by_cases hh: i < n_bc
      . have hhh: i < n_ab := by omega
        simp only [hh, hhh]
      . sorry

    have := (hAIIA _ _ _ _ hSameCol).mp h_star
    exact absurd this (Preorder'.lt_asymm _ _ _ this)



  -- n_cb ≤ n_ab
  let n_cb: Fin N := sorry
  have h_ncb_le_nab: n_cb ≤ n_ab := by sorry
  -- n_bc ≥ n_ab ≥ n_cb
  -- n_cb ≥ n_bc
  have h_nbc_le_ncb: n_bc ≤ n_cb := by sorry

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb: n_bc = n_cb := by
    have h_ncb_le_nbc: n_cb ≤ n_bc := by exact le_trans h_ncb_le_nab h_nab_le_nbc
    exact le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_ncb_eq_nab: n_cb = n_ab := by
    have h_nab_le_n_cb: n_ab ≤ n_cb := by exact le_trans h_nab_le_nbc h_nbc_le_ncb
    exact le_antisymm h_ncb_le_nab h_nab_le_n_cb

  -- n_bc = n_cb = n_ab can be extended to n_ts

  -- but (*) requires n_ab holds dictatorship over all ordered pairs of alternatives
  sorry
