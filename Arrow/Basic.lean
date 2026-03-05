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
    ∃ k : Fin N, (∀ i ≤ k, ¬ P i.castSucc) ∧ P k.succ := by
  -- Define Q on natural numbers: Q m = P m for m ≤ N
  let Q : ℕ → Prop := fun m => ∃ (h : m < N + 1), P ⟨m, h⟩
  have hQ_dec : DecidablePred Q := by
    intro m
    by_cases hm : m < N + 1
    · exact decidable_of_iff (P ⟨m, hm⟩) ⟨fun hp => ⟨hm, hp⟩, fun ⟨_, hp⟩ => hp⟩
    · exact isFalse (fun ⟨h, _⟩ => hm h)
  -- Q is true at N (since P (Fin.last N))
  have hQN : Q N := ⟨Nat.lt_succ_self N, by convert hN⟩
  -- There exists some m where Q m
  have hex : ∃ m, Q m := ⟨N, hQN⟩
  -- Find the minimum m where Q m
  let m := @Nat.find Q hQ_dec hex
  have hQm : Q m := @Nat.find_spec Q hQ_dec hex
  have hm_min : ∀ k < m, ¬ Q k := fun k hk => @Nat.find_min Q hQ_dec hex k hk
  -- m > 0 since Q 0 = P 0 is false
  have hm_pos : 0 < m := by
    by_contra hm0
    push_neg at hm0
    have hm_eq : m = 0 := Nat.le_zero.mp hm0
    rw [hm_eq] at hQm
    obtain ⟨_, hP0⟩ := hQm
    have : (⟨0, Nat.zero_lt_succ N⟩ : Fin (N+1)) = 0 := rfl
    rw [this] at hP0
    exact h0 hP0
  -- m ≤ N since Q m implies m < N + 1
  have hm_le_N : m ≤ N := by
    obtain ⟨hlt, _⟩ := hQm
    omega
  -- m - 1 < N
  have hm_pred_lt : m - 1 < N := by omega
  -- Define k as the predecessor of m
  let k : Fin N := ⟨m - 1, hm_pred_lt⟩
  use k
  constructor
  · -- ∀ i ≤ k, ¬ P i.castSucc
    intro i hi
    have hi_val : i.val ≤ m - 1 := by simp only [Fin.le_def] at hi; exact hi
    have hi_lt_m : i.val < m := by omega
    have hnotQ : ¬ Q i.val := hm_min i.val hi_lt_m
    simp only [Q, not_exists] at hnotQ
    have hi_lt : i.val < N + 1 := Nat.lt_of_lt_of_le i.isLt (Nat.le_succ N)
    intro hPi
    apply hnotQ hi_lt
    have : i.castSucc = ⟨i.val, hi_lt⟩ := by simp [Fin.ext_iff]
    rw [← this]
    exact hPi
  · -- P k.succ
    obtain ⟨hm_lt, hPm⟩ := hQm
    have hk_succ_val : k.succ.val = m := by simp only [k, Fin.val_succ]; omega
    convert hPm using 1
    simp only [Fin.ext_iff, hk_succ_val]

def swapping_k
  {α : Type} {N:ℕ} (p q: PreferenceProfile α N) (k: Fin (N+1))
  : PreferenceProfile α N :=
  fun i: Fin N => if i < k.val then p i else q i

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
    ∃ k : Fin N,
    (∀ i ≤ k, socPrefers R (swapping_k p q i.castSucc) a b) ∧
    socPrefers R (swapping_k p q k.succ) b a := by

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
  have hh: ∃ k : Fin N, (∀ i ≤ k, ¬ P i.castSucc) ∧ P k.succ := by
    exact flip_exists N P hp0 hpN
  obtain ⟨ k, ⟨ hleft, hright ⟩ ⟩ := hh
  simp [P] at hleft hright
  use k
  constructor
  · intro i hi
    exact Preorder'.lt_of_not_lt _ b a (Ne.symm hab) (hleft i hi)
  · exact hright

lemma nab_pivotal_bc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  {R: SocialWelfareFunction α N}
  (hunanimity: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  :
  ∃ n_ab: Fin N, ∀ pp: PreferenceProfile α N,
    voterPrefers (pp n_ab) b c → socPrefers R pp b c := by
  let p: PreferenceProfile α N := fun i => preorderFromRanking b c a hbc (Ne.symm hac) (Ne.symm hab)
  let q: PreferenceProfile α N := fun i => preorderFromRanking a b c hab hbc hac

  have hp: ∀ i: Fin N, voterPrefers (p i) b c ∧ voterPrefers (p i) c a := by
    intro i; constructor
    . exact preorderFromRanking_lt_01 b c a hbc (Ne.symm hac) (Ne.symm hab)
    . exact preorderFromRanking_lt_12 b c a hbc (Ne.symm hac) (Ne.symm hab)
  have hq: ∀ i: Fin N, voterPrefers (q i) a b ∧ voterPrefers (q i) b c := by
    intro i; constructor
    . exact preorderFromRanking_lt_01 a b c hab hbc hac
    . exact preorderFromRanking_lt_12 a b c hab hbc hac

  have hpba: ∀ i: Fin N, voterPrefers (p i) b a := by intro i; exact (p i).lt_trans (hp i).2 (hp i).1
  have hqab: ∀ i: Fin N, voterPrefers (q i) a b := by intro i; exact (hq i).1
  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  obtain ⟨n_ab, h_nab_pivot_p ⟩ := swapping_exists_pivotal a b hab p q hpba hqab hunanimity

  -- soc prefer a > b > c
  have habc:
    socPrefers R (swapping_k p q n_ab.castSucc) a b ∧
    socPrefers R (swapping_k p q n_ab.castSucc) b c  := by
    constructor
    -- a > b by def of n_ab
    . exact h_nab_pivot_p.1 n_ab (le_refl n_ab)
    -- b > c by unanimity
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

  -- let rr
  -- 0...k-1 prefer b > a ∧ c > a
  -- k prefer b > a > c
  -- k+1 ... N prefer a > b ∧ c < a
  -- result: socPrefer b ≥ a > c
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
    -- By AIIA on nab pivoting defintion
    . have hSameCol_ba: sameCol (swapping_k p q n_ab.succ) rr b a := by
        unfold sameCol swapping_k
        intro i
        split_ifs with h
        . simp [(p i).lt_trans (hp i).2 (hp i).1]
          unfold rr
          simp at *
          have h2: ¬(i > n_ab) := by omega
          split_ifs with hinab hppibc hieqnab hppibc
          . exact preorderFromRanking_lt_02 b c a hbc (Ne.symm hac) (Ne.symm hab)
          . exact preorderFromRanking_lt_12 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
          . exact preorderFromRanking_lt_01 b a c (Ne.symm hab) hac hbc
          . omega
          . omega
        . rw [← not_iff_not]
          constructor
          . intro h; apply Preorder'.lt_asymm
            unfold rr
            simp at *
            have h2: ¬(i < n_ab) := by omega
            split_ifs
            . omega
            . exact preorderFromRanking_lt_01 a b c hab hbc hac
            . exact preorderFromRanking_lt_02 a c b hac (Ne.symm hbc) hab
          . intro h; apply Preorder'.lt_asymm; exact (hq i).1
      have hSocPrefer_rr_ba := by apply hAIIA at hSameCol_ba; exact hSameCol_ba;
      exact hSocPrefer_rr_ba.mp h_nab_pivot_p.2
    -- By AIIA
    . have hsoc_swp_ac: socPrefers R (swapping_k p q n_ab.castSucc) a c :=
        (R (swapping_k p q n_ab.castSucc)).lt_trans habc.2 habc.1
      have hSameCol_ac: sameCol (swapping_k p q n_ab.castSucc) rr a c := by
        unfold sameCol rr swapping_k
        intro i
        simp at *
        split_ifs with hinab hppibc hieqnab hppibc
        . rw [← not_iff_not]
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

lemma nab_le_nbc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  {R: SocialWelfareFunction α N}
  (b c: α)
  (n_ab n_bc: Fin N)
  (p q: PreferenceProfile α N)
  (hq: ∀ i: Fin N, voterPrefers (q i) b c)
  (h_nab_dictate_bc: ∀ (pp : PreferenceProfile α N), voterPrefers (pp n_ab) b c → socPrefers R pp b c)
  (h_nbc_pivot : (∀ i ≤ n_bc, socPrefers R (swapping_k p q i.castSucc) b c) ∧ socPrefers R (swapping_k p q n_bc.succ) c b)
  : n_ab ≤ n_bc  := by
  -- need to use the h_nbc_pivot to show that n_bc must be latter than n_ab.
  -- if n_bc flipped, but not the dictacterous n_ab, then the result is still b > c.
  by_contra h
  push_neg at h
  let pp := (swapping_k p q n_bc.succ)
  have h3 :  voterPrefers (pp n_ab) b c:= by
    unfold pp swapping_k
    split_ifs with hh
    . simp at *; omega
    . exact hq n_ab
  have h4 := h_nab_dictate_bc pp h3
  have h5 := by apply Preorder'.lt_asymm at h4; exact h4
  exact absurd  h_nbc_pivot.2 h5

lemma ncb_le_nab
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  {R: SocialWelfareFunction α N}
  (b c: α)
  (n_ab n_cb: Fin N)
  (p q: PreferenceProfile α N)
  (hq: ∀ i: Fin N, voterPrefers (q i) b c)
  (h_nab_dictate_bc: ∀ (pp : PreferenceProfile α N), voterPrefers (pp n_ab) b c → socPrefers R pp b c)
  (h_ncb_pivot : (∀ i ≤ n_cb, socPrefers R (swapping_k q p i.castSucc) c b) ∧ socPrefers R (swapping_k q p n_cb.succ) b c)
  : n_cb ≤ n_ab := by
  -- the society ranking of c > b should flip no later than n_ab does it.
  by_contra h
  push_neg at h
  -- profile at n_cb column
  let pp := (swapping_k q p n_cb.castSucc)
  -- We haven't reached pivotal voter n_cb, society supposed to rank c > b
  have h1: socPrefers R pp c b := by
    have h10: n_ab ≤  n_cb := by omega
    exact h_ncb_pivot.1 n_cb (le_refl n_cb)
  -- But n_ab already flipped to b > c, the dictactorial position should flip society ranking already
  have h2: socPrefers R pp b c := by
    have h20:  voterPrefers (pp n_ab) b c := by
      unfold pp swapping_k
      simp
      split_ifs
      . exact hq n_ab
      . exact hq n_ab
    exact h_nab_dictate_bc pp h20
  have h3 := by apply Preorder'.lt_asymm at h2; exact h2
  exact absurd h1 h3

lemma nbc_le_ncb
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  {R: SocialWelfareFunction α N}
  (b c: α)
  (n_ab n_cb n_bc: Fin N)
  (p q: PreferenceProfile α N)
  (hq: ∀ i: Fin N, voterPrefers (q i) b c)
  (h_nab_dictate_bc: ∀ (pp : PreferenceProfile α N), voterPrefers (pp n_ab) b c → socPrefers R pp b c)
  (h_nbc_pivot : (∀ i ≤ n_bc, socPrefers R (swapping_k p q i.castSucc) b c) ∧ socPrefers R (swapping_k p q n_bc.succ) c b)
  (h_ncb_pivot : (∀ i ≤ n_cb, socPrefers R (swapping_k q p i.castSucc) c b) ∧ socPrefers R (swapping_k q p n_cb.succ) b c)
  : n_cb ≤ n_bc  := by
  -- n_bc ≥ n_ab
  have h_nab_le_nbc : n_ab ≤ n_bc := nab_le_nbc b c n_ab n_bc p q hq h_nab_dictate_bc h_nbc_pivot

  -- n_cb ≤ n_ab
  have h_ncb_le_nab: n_cb ≤ n_ab := ncb_le_nab b c n_ab n_cb p q hq h_nab_dictate_bc h_ncb_pivot

  exact le_trans h_ncb_le_nab h_nab_le_nbc

lemma n_ab_pivotal_bc_cb
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ}
  {R: SocialWelfareFunction α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (n_ab n_cb n_bc: Fin N)
  (p q: PreferenceProfile α N)
  (hp: ∀ i: Fin N, voterPrefers (p i) c b)
  (hq: ∀ i: Fin N, voterPrefers (q i) b c)
  (hunanimity: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  (h_nab_dictate_bc: ∀ (pp : PreferenceProfile α N), voterPrefers (pp n_ab) b c → socPrefers R pp b c)
  (h_nbc_pivot : (∀ i ≤ n_bc, socPrefers R (swapping_k p q i.castSucc) b c) ∧ socPrefers R (swapping_k p q n_bc.succ) c b)
  (h_ncb_pivot : (∀ i ≤ n_cb, socPrefers R (swapping_k q p i.castSucc) c b) ∧ socPrefers R (swapping_k q p n_cb.succ) b c)
  : n_bc = n_cb ∧ n_cb = n_ab := by
  -- n_bc ≥ n_ab
  have h_nab_le_nbc : n_ab ≤ n_bc := nab_le_nbc b c n_ab n_bc p q hq h_nab_dictate_bc h_nbc_pivot

  -- n_cb ≤ n_ab
  have h_ncb_le_nab: n_cb ≤ n_ab := ncb_le_nab b c n_ab n_cb p q hq h_nab_dictate_bc h_ncb_pivot

  have h_ncb_le_nbc: n_cb ≤ n_bc := nbc_le_ncb b c n_ab n_cb n_bc p q hq h_nab_dictate_bc h_nbc_pivot h_ncb_pivot
  -- n_bc ≥ n_ab ≥ n_cb
  -- n_cb ≥ n_bc
  -- As b and c are distinct and arbitrary, n_bc ≤ n_cb also holds
  have h_nbc_le_ncb: n_bc ≤ n_cb := by
    obtain ⟨n_ac, h_nac_dictate_cb ⟩ := nab_pivotal_bc a c b hac hab (Ne.symm hbc) hunanimity hAIIA
    exact nbc_le_ncb c b n_ac n_bc n_cb q p hp h_nac_dictate_cb h_ncb_pivot h_nbc_pivot

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb: n_bc = n_cb := by exact le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_ncb_eq_nab: n_cb = n_ab := by
    have h_nab_le_n_cb: n_ab ≤ n_cb := by exact le_trans h_nab_le_nbc h_nbc_le_ncb
    exact le_antisymm h_ncb_le_nab h_nab_le_n_cb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

theorem Impossibility
    {α : Type} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SocialWelfareFunction α N,
    (unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictactorship _ _ R) := by
  by_contra h
  obtain ⟨ R, ⟨ hunanimity, hAIIA, hNonDictactor ⟩⟩ := h
  apply hNonDictactor

  -- i j k | in the paper are translated into
  -- a b c

  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha

  obtain ⟨n_ab, h_nab_dictate_bc ⟩ := nab_pivotal_bc a b c hab hac hbc hunanimity hAIIA

  -- swapping process for b c
  let p: PreferenceProfile α N := fun i => preorderFromRanking c b _ (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
  let q: PreferenceProfile α N := fun i => preorderFromRanking b c _ hbc (Ne.symm hac) (Ne.symm hab)
  have hp: ∀ i: Fin N, voterPrefers (p i) c b:= by intro i; exact preorderFromRanking_lt_01 c b _ (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
  have hq: ∀ i: Fin N, voterPrefers (q i) b c := by intro i;  exact preorderFromRanking_lt_01 b c _ hbc (Ne.symm hac) (Ne.symm hab)

  obtain ⟨n_bc, h_nbc_pivot ⟩ := swapping_exists_pivotal b c hbc p q hp hq hunanimity
  obtain ⟨n_cb, h_ncb_pivot ⟩ := swapping_exists_pivotal c b (Ne.symm hbc) q p hq hp hunanimity

  obtain ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩ := (
    n_ab_pivotal_bc_cb
    a b c
    hab hac hbc
    n_ab n_cb n_bc
    p q hp hq
    hunanimity hAIIA
    h_nab_dictate_bc h_nbc_pivot h_ncb_pivot
  )
  -- n_bc = n_cb = n_ab can be extended to n_ts

  -- but (*) requires n_ab holds dictatorship over all ordered pairs of alternatives
  sorry
