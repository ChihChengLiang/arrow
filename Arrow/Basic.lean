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
def dictate_two {α : Type} {N : ℕ} (R : SocialWelfareFunction α N) (k : Fin N) (a b : α): Prop :=
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
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → dictate_two R i a b)

def swapping_k
  {α : Type} {N:ℕ} (p q: PreferenceProfile α N) (k: Fin (N+1))
  : PreferenceProfile α N :=
  fun i: Fin N => if i < k.val then p i else q i

def preferAoverB {α : Type} [LinearOrder α] (a b : α) (hab : a ≠ b) : Preorder' α where
  le x y :=
    if x = b then True           -- b is below everything
    else if y = a then True      -- a is above everything
    else if x = a then y = a     -- a is only ≤ itself (it's the top)
    else if y = b then x = b     -- b is only ≥ itself (it's the bottom)
    else x ≤ y                   -- everything else uses existing order
  refl := by
    intro x
    simp
  trans := by
    intro x y z hxy hyz
    simp
    intro hxb hza
    split_ifs with hxa hzb
    split_ifs at hxy ⊢ with hya
    split_ifs at hyz ⊢ with hyb
    rw[hya] at hyb
    exact absurd hyb hab
    exact hyz
    exact absurd hxy hya
    split_ifs at hxy ⊢ with hya hyb
    split_ifs at hyz ⊢ with hyb
    rw[hya] at hyb
    exact absurd hyb hab
    exact absurd hyz hza
    exact hxy
    split_ifs at hyz
    exact absurd hyz hyb
    split_ifs at hxy ⊢ with hya hyb
    split_ifs at hyz ⊢ with hyb
    rw[hya] at hyb
    exact absurd hyb hab
    exact absurd hyz hza
    exact absurd hxy hxb
    split_ifs at hyz
    exact le_trans hxy hyz

  total := by
    intro x y
    split_ifs with hxb hyb hxa hya hya hyb hxa hxa hyb hyb
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
    exact le_total x y

  antisymm := by
    intro x y hxb hyb
    split_ifs at hxb ⊢ with hxb2 hya hxa hyb2
    split_ifs at hyb ⊢ with hyb3 hxa hya
    rw [ hyb3, hxb2]
    rw[hxa] at hxb2
    exact absurd hxb2 hab
    rw[hya, hyb]
    rw[hxb2, hyb]
    split_ifs at hyb ⊢ with hyb2 hxa
    rw[hya] at hyb2
    exact absurd hyb2 hab
    rw[hya, hxa]
    exact absurd hyb hxa
    rw[hxa, hxb]
    rw[hyb2, hxb]
    split_ifs at hyb
    exact le_antisymm hxb hyb

def preferBoverA {α : Type} [LinearOrder α] (a b : α) (hab : a ≠ b) : Preorder' α :=
  preferAoverB b a (Ne.symm hab)

omit [Fintype α] in
lemma preferAoverB_lt {α : Type} [LinearOrder α] (a b : α) (hab : a ≠ b) : voterPrefers (preferAoverB a b hab) a b := by
  simp only [Preorder'.lt, preferAoverB]
  constructor
  split_ifs
  split_ifs with hab2 hba
  tauto
  tauto
  exact hba

omit [Fintype α] in
lemma preferBoverA_lt {α : Type} [LinearOrder α] (a b : α) (hab : a ≠ b) : voterPrefers (preferBoverA a b hab) b a := by
  simp only [Preorder'.lt, preferBoverA, preferAoverB]
  constructor
  split_ifs
  split_ifs with hab2
  tauto
  tauto

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

def isSwappingProcessAB
  {α : Type}
  {N : ℕ}
  (a b : α)
  (f: profileGen α N): Prop :=
    ∀ (k: Fin (N+1)) (i: Fin N),
    (i.val < k.val → voterPrefers (f k i) b a ) ∧
    (i.val ≥ k.val → voterPrefers (f k i) a b )

def isPivotalAB
  {α : Type}
  {N : ℕ}
  (R : SocialWelfareFunction α N)
  (f: profileGen α N)
  (a b : α)
  (n_ab: Fin N): Prop :=
  (∀ i ≤ n_ab,  socPrefers R (f i.castSucc) a b) ∧
  socPrefers R (f n_ab.succ) b a

-- Canonical profiles: p = everyone ranks b > a, q = everyone ranks a > b
def canonSwappingProcess
  {α : Type} [LinearOrder α]
  {N : ℕ}
  (a b : α)
  (hab : a ≠ b)
  : profileGen α N :=
  let p : PreferenceProfile α N := fun _ => preferAoverB b a (Ne.symm hab) -- b on top
  let q : PreferenceProfile α N := fun _ => preferAoverB a b hab           -- a on top
  swapping_k p q

noncomputable def pivotalVoter
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SocialWelfareFunction α N)
  (a b : α) (hab : a ≠ b)
  (hu : unanimity _ _ R) : Fin N :=
  let sp := canonSwappingProcess a b hab
  let P := fun k: Fin N => socPrefers R (sp k.succ) b a
  let hN: ∃ k, P k := by
    use (0:Fin N).rev
    unfold P sp canonSwappingProcess swapping_k
    have: 0 < N := by exact Nat.pos_of_ne_zero (NeZero.ne N)
    simp [Nat.sub_add_cancel this]
    apply hu
    simp [preferAoverB_lt b a (Ne.symm hab)]
  -- Find the minimum k where the flip happens
  Fin.find P hN

-- pivotalVoter is independent of profile
lemma pivotalVoter_spec
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SocialWelfareFunction α N)
  (a b : α) (hab : a ≠ b)
  (f : Fin (N+1) → PreferenceProfile α N)
  (hf: isSwappingProcessAB a b f)
  (hAIIA: AIIA _ _ R )
  (hu : unanimity _ _ R) :
  isPivotalAB R f a b (pivotalVoter R a b hab hu) := by
  let n_ab := pivotalVoter R a b hab hu
  let sp: profileGen α N := canonSwappingProcess a b hab
  let P := fun k: Fin N => socPrefers R (sp k.succ) b a

  -- Get the existence witness for Fin.find
  have hN: ∃ k, P k := by
    use (0:Fin N).rev
    unfold P sp canonSwappingProcess swapping_k
    have hpos: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    simp [Nat.sub_add_cancel hpos]
    apply hu
    simp [preferAoverB_lt b a (Ne.symm hab)]

  -- P n_ab holds: society prefers b > a at column n_ab.succ
  have hPn : P n_ab := Fin.find_spec hN

  -- For j < n_ab, ¬P j: society doesn't prefer b > a, hence prefers a > b
  have hPmin : ∀ j : Fin N, j < n_ab → ¬P j := fun j hj => Fin.find_min hN hj

  -- Helper: sameCol for any column k between f and canonical swapping process
  have hSameColGen : ∀ k : Fin (N+1), sameCol (f k) (sp k) a b := by
    intro k i; unfold sp canonSwappingProcess swapping_k
    split_ifs with hik
    . -- i < k.val: swapping_k uses p, which has b > a, so ¬(a > b)
      rw [← not_iff_not]
      have hfba := (hf k i).1 hik
      constructor
      . intro h; apply Preorder'.lt_asymm; exact preferAoverB_lt b a (Ne.symm hab)
      . intro h; apply Preorder'.lt_asymm; exact hfba
    . -- i ≥ k.val: swapping_k uses q, which has a > b
      simp at hik
      have hfba := (hf k i).2 hik
      simp [hfba]
      exact preferAoverB_lt a b hab

  have hSameCol: sameCol (f n_ab.succ) (sp n_ab.succ) a b := hSameColGen n_ab.succ

  constructor
  · -- Part 1: ∀ i ≤ n_ab, socPrefers R (f i.castSucc) a b
    intro i hi
    have hSameCol_i : sameCol (f i.castSucc) (sp i.castSucc) a b := hSameColGen i.castSucc
    -- Need to show society prefers a > b at swapping_k p q i.castSucc
    have hNotP : ¬ socPrefers R (sp i.castSucc) b a := by
      by_cases hilt : i < n_ab
      · -- i < n_ab: use Fin.find_min
        intro hcontra
        by_cases hizero : i.val = 0
        · -- Column 0: everyone prefers a > b by unanimity on q
          have hall : ∀ j : Fin N, voterPrefers (sp i.castSucc j) a b := by
            intro j
            unfold sp canonSwappingProcess swapping_k
            simp [hizero]
            exact preferAoverB_lt a b hab
          have hsoc := hu (sp i.castSucc) a b hall
          exact Preorder'.lt_asymm _ _ _ hsoc hcontra
        · -- Column i.val > 0: use that j = i-1 satisfies j+1 = i and j < n_ab
          have hipos : 0 < i.val := Nat.pos_of_ne_zero hizero
          let j : Fin N := ⟨i.val - 1, by omega⟩
          have hjsucc : j.succ.val = i.castSucc.val := by simp [j]; omega
          have hjlt : j < n_ab := by
            simp only [Fin.lt_def, j]
            have : i.val < n_ab.val := hilt
            omega
          have hnotPj := hPmin j hjlt
          simp only [P] at hnotPj
          -- hnotPj : ¬ socPrefers R (swapping_k p q j.succ) b a
          -- We need: socPrefers R (swapping_k p q i.castSucc) b a → False
          -- Since j.succ.val = i.castSucc.val, the profiles are the same
          have heq : j.succ = i.castSucc := by
            apply Fin.ext
            exact hjsucc
          rw [← heq] at hcontra
          exact hnotPj hcontra
      · -- i = n_ab case (since i ≤ n_ab and ¬(i < n_ab))
        push_neg at hilt
        have hieq : i = n_ab := le_antisymm hi hilt
        subst hieq
        intro hcontra
        -- At column n_ab.castSucc.val = n_ab.val
        -- By the same argument as above:
        by_cases hnzero : n_ab.val = 0
        · -- Column 0: unanimity
          have hall : ∀ j : Fin N, voterPrefers (sp n_ab.castSucc j) a b := by
            intro j
            unfold sp canonSwappingProcess swapping_k
            simp [hnzero]
            exact preferAoverB_lt a b hab
          have hsoc := hu (sp n_ab.castSucc) a b hall
          exact Preorder'.lt_asymm _ _ _ hsoc hcontra
        · -- Column n_ab.val > 0: use j = n_ab - 1
          have hnpos : 0 < n_ab.val := Nat.pos_of_ne_zero hnzero
          let j : Fin N := ⟨n_ab.val - 1, by omega⟩
          have hjsucc : j.succ.val = n_ab.castSucc.val := by simp [j]; omega
          have hjlt : j < n_ab := by simp only [Fin.lt_def, j]; omega
          have hnotPj := hPmin j hjlt
          simp only [P] at hnotPj
          have heq : j.succ = n_ab.castSucc := by
            apply Fin.ext
            exact hjsucc
          rw [heq] at hnotPj
          exact hnotPj hcontra
    -- Now use AIIA to transfer to f
    -- socPrefers R p a b = (R p).lt b a, so hNotP : ¬(R ...).lt a b
    -- We want (R ...).lt b a, use lt_of_not_lt with swapped arguments
    have hsoc_swp : socPrefers R (sp i.castSucc) a b :=
      Preorder'.lt_of_not_lt (R (sp i.castSucc)) b a (Ne.symm hab) hNotP
    exact (hAIIA (f i.castSucc) (sp i.castSucc) a b hSameCol_i).mpr hsoc_swp
  · -- Part 2: socPrefers R (f n_ab.succ) b a
    -- hPn : socPrefers R (swapping_k p q n_ab.succ) b a
    -- Need: socPrefers R (f n_ab.succ) b a
    -- Use AIIA with sameCol for b a (which follows from sameCol for a b)
    have hSameCol_ba : sameCol (f n_ab.succ) (sp n_ab.succ) b a := by
      intro i
      -- In a total preorder, a>b ↔ ¬(b>a) for a ≠ b
      have h := hSameCol i
      constructor
      · intro hba
        by_contra hnotba
        have haq : voterPrefers (sp n_ab.succ i) a b := by
          exact Preorder'.lt_of_not_lt _ _ _ (Ne.symm hab) hnotba
        have haf : voterPrefers (f n_ab.succ i) a b := h.mpr haq
        exact Preorder'.lt_asymm _ _ _ hba haf
      · intro hba
        by_contra hnotba
        have haq : voterPrefers (f n_ab.succ i) a b := by
          exact Preorder'.lt_of_not_lt _ _ _ (Ne.symm hab) hnotba
        have haf : voterPrefers (sp n_ab.succ i) a b := h.mp haq
        exact Preorder'.lt_asymm _ _ _ hba haf
    exact (hAIIA (f n_ab.succ) (sp n_ab.succ) b a hSameCol_ba).mpr hPn

lemma pivotalVoter_pivot_canon
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SocialWelfareFunction α N)
  (a b : α) (hab : a ≠ b)
  (hAIIA: AIIA _ _ R )
  (hu : unanimity _ _ R) :
  isPivotalAB R (canonSwappingProcess a b hab) a b (pivotalVoter R a b hab hu) := by
  let n_ab := pivotalVoter R a b hab hu
  let sp: profileGen α N := canonSwappingProcess a b hab

  have hf : isSwappingProcessAB a b sp := by
    unfold isSwappingProcessAB sp canonSwappingProcess swapping_k
    intro k i
    constructor
    . intro h; simp [h]; exact preferAoverB_lt b a (Ne.symm hab)
    . intro h;
      have :¬ i < k.val := by omega
      simp [this]
      exact preferAoverB_lt a b hab
  exact pivotalVoter_spec R a b hab sp hf hAIIA hu


lemma nab_pivotal_bc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  {R: SocialWelfareFunction α N}
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  : dictate_two R (pivotalVoter R a b hab hu) b c := by
  let n_ab := pivotalVoter R a b hab hu
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

  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  have hf : isSwappingProcessAB a b (swapping_k p q) := by
    unfold isSwappingProcessAB swapping_k
    intro k i
    constructor
    . intro h; simp [h]; exact ((p i).lt_trans (hp i).2 (hp i).1)
    . intro h; split_ifs
      . omega
      . exact (hq i).1
  have h_nab_pivot_p := pivotalVoter_spec R a b hab (swapping_k p q) hf hAIIA hu

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
      apply hu at h
      exact h
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
  {N:ℕ} [NeZero N]
  {R: SocialWelfareFunction α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  :
  -- n_ab ≤ n_bc
  pivotalVoter R a b hab hu ≤ pivotalVoter R b c hbc hu  := by
  -- need to use the h_nbc_pivot to show that n_bc must be latter than n_ab.
  -- if n_bc flipped, but not the dictacterous n_ab, then the result is still b > c.
  let n_ab := pivotalVoter R a b hab hu
  let n_bc := pivotalVoter R b c hbc hu
  have h_nab_dictate_bc := nab_pivotal_bc a b c hab hac hbc hu hAIIA
  have h_nbc_pivot := pivotalVoter_pivot_canon R b c hbc hAIIA hu
  by_contra h
  push_neg at h
  let pp := (canonSwappingProcess b c hbc) n_bc.succ
  have h3 :  voterPrefers (pp n_ab) b c:= by
    unfold pp canonSwappingProcess swapping_k
    split_ifs with hh
    . simp at *; omega
    . exact preferAoverB_lt b c hbc
  have h4 := h_nab_dictate_bc pp h3
  have h5 := by apply Preorder'.lt_asymm at h4; exact h4
  exact absurd  h_nbc_pivot.2 h5

lemma ncb_le_nab
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SocialWelfareFunction α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  -- n_cb ≤ n_ab
  : pivotalVoter R c b (Ne.symm hbc) hu  ≤ pivotalVoter R a b hab hu := by
  -- the society ranking of c > b should flip no later than n_ab does it.
  let n_cb := pivotalVoter R c b (Ne.symm hbc) hu
  let n_ab := pivotalVoter R a b hab hu
  have h_nab_dictate_bc := nab_pivotal_bc a b c hab hac hbc hu hAIIA
  have h_ncb_pivot := pivotalVoter_pivot_canon R c b (Ne.symm hbc) hAIIA hu

  by_contra h
  push_neg at h
  -- profile at n_cb column
  let pp := (canonSwappingProcess c b (Ne.symm hbc)) n_cb.castSucc
  -- We haven't reached pivotal voter n_cb, society supposed to rank c > b
  have h1: socPrefers R pp c b := h_ncb_pivot.1 n_cb (le_refl n_cb)
  -- But n_ab already flipped to b > c, the dictactorial position should flip society ranking already
  have h2: socPrefers R pp b c := by
    have h20: voterPrefers (pp n_ab) b c := by
      unfold pp canonSwappingProcess swapping_k
      have: n_ab < n_cb.val := by omega
      simp [this]
      exact preferAoverB_lt b c hbc
    exact h_nab_dictate_bc pp h20
  have h3 := by apply Preorder'.lt_asymm at h2; exact h2
  exact absurd h1 h3

lemma nbc_le_ncb
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SocialWelfareFunction α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  : -- n_cb ≤ n_bc
  pivotalVoter R c b (Ne.symm hbc) hu ≤ pivotalVoter R b c hbc hu := by
  let n_ab := pivotalVoter R a b hab hu
  let n_bc := pivotalVoter R b c hbc hu
  let n_cb := pivotalVoter R c b (Ne.symm hbc) hu
  -- n_bc ≥ n_ab
  have h_nab_le_nbc: n_ab ≤ n_bc := nab_le_nbc a b c hab hac hbc hu hAIIA

  -- n_cb ≤ n_ab
  have h_ncb_le_nab: n_cb ≤ n_ab := ncb_le_nab a b c hab hac hbc hu hAIIA

  exact le_trans h_ncb_le_nab h_nab_le_nbc

lemma n_ab_pivotal_bc_cb
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SocialWelfareFunction α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  :
  -- n_bc = n_cb = n_ab
  (pivotalVoter R b c hbc hu) = (pivotalVoter R c b (Ne.symm hbc) hu) ∧
  (pivotalVoter R c b (Ne.symm hbc) hu) = pivotalVoter R a b hab hu := by

  let n_ab := pivotalVoter R a b hab hu
  let n_bc := pivotalVoter R b c hbc hu
  let n_cb := pivotalVoter R c b (Ne.symm hbc) hu
  have h_nab_dictate_bc := nab_pivotal_bc a b c hab hac hbc hu hAIIA
  -- n_bc ≥ n_ab
  have h_nab_le_nbc: n_ab ≤ n_bc := nab_le_nbc a b c hab hac hbc hu hAIIA

  -- n_cb ≤ n_ab
  have h_ncb_le_nab: n_cb ≤ n_ab := ncb_le_nab a b c hab hac hbc hu hAIIA

  have h_ncb_le_nbc: n_cb ≤ n_bc := nbc_le_ncb a b c hab hac hbc hu hAIIA
  -- n_bc ≥ n_ab ≥ n_cb
  -- n_cb ≥ n_bc
  -- As b and c are distinct and arbitrary, n_bc ≤ n_cb also holds
  have h_nbc_le_ncb: n_bc ≤ n_cb := by
    let n_ac := pivotalVoter R a c hac hu
    have h_nac_dictate_cb := nab_pivotal_bc a c b hac hab (Ne.symm hbc) hu hAIIA
    exact nbc_le_ncb a c b hac hab (Ne.symm hbc) hu hAIIA

  -- n_bc = n_cb = n_ab
  have h_nbc_eq_ncb: n_bc = n_cb := by exact le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_ncb_eq_nab: n_cb = n_ab := by
    have h_nab_le_n_cb: n_ab ≤ n_cb := by exact le_trans h_nab_le_nbc h_nbc_le_ncb
    exact le_antisymm h_ncb_le_nab h_nab_le_n_cb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

-- n_bc = n_cb = n_ab can be extended to n_ts
lemma n_ab_dictate_xy
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SocialWelfareFunction α N}
  (a b c x y: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hxy : x ≠ y)
  (hu: unanimity _ _ R)
  (hAIIA: (AIIA _ _ R)):
  dictate_two R (pivotalVoter R a b hab hu) x y := by

  have h_nab_dictate_bc := nab_pivotal_bc a b c hab hac hbc hu hAIIA
  obtain ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩ := n_ab_pivotal_bc_cb a b c hab hac hbc hu hAIIA

  rcases eq_or_ne x a with hxa | hxnea
  . --x=a
    rcases eq_or_ne y b with hyb | hyneb
    . -- y=b
      sorry
    . -- y≠b
      rcases eq_or_ne y c with hyc | hynec
      . -- y = c
        sorry
      . -- y ∉ {a,b,c}
        sorry
  . --x≠a
    rcases eq_or_ne x b with hxb | hxneb
    . -- x=b
      rcases eq_or_ne y a with hya | hynea
      . -- y=a
        sorry
      . -- y≠ a
        rcases eq_or_ne y c with hyc | hynec
        . -- y = c
          rw[hxb, hyc]
          exact h_nab_dictate_bc
        . -- y ∉ {a,b,c}
          sorry
    . --x≠b
      rcases eq_or_ne x c with hxc | hxnec
      . --x=c
        sorry
      . --x  ∉ {a,b,c}
        rcases eq_or_ne y a with hya | hynea
        . -- y=a
          sorry
        . -- y≠a
          rcases eq_or_ne y b with hyb | hyneb
          . -- y=b
            sorry
          . -- y≠b
            rcases eq_or_ne y c with hyc | hynec
            . --y=c
              sorry
            . -- y ∉ {a,b,c}
              have h_nax_dictate_xy := nab_pivotal_bc a b x hab (Ne.symm hxnea) (Ne.symm hxneb) hu hAIIA
              have h_nax_dictate_xy := nab_pivotal_bc a x y (Ne.symm hxnea) (Ne.symm hynea) hxy hu hAIIA
              obtain ⟨ h_nxy_eq_nyx, h_nyx_eq_nax⟩ := n_ab_pivotal_bc_cb a x y (Ne.symm hxnea) (Ne.symm hynea) hxy hu hAIIA
              sorry

theorem Impossibility
    {α : Type} [Fintype α] [DecidableEq α] [LinearOrder α]
    {N:ℕ } [NeZero N]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SocialWelfareFunction α N,
    (unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictactorship _ _ R) := by
  by_contra h
  obtain ⟨ R, ⟨ hu, hAIIA, hNonDictactor ⟩⟩ := h
  apply hNonDictactor

  -- i j k | in the paper are translated into
  -- a b c

  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha

  let n_ab := pivotalVoter R a b hab hu

  use n_ab
  intro x y hxy
  exact n_ab_dictate_xy a b c x y hab hac hbc hxy hu hAIIA
