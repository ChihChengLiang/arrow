import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

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

#check @preferBoverA
example : Preorder' (Fin 3) := preferBoverA (⟨0, by decide⟩ : Fin 3) ⟨1, by decide⟩ (by decide)
#reduce (preferBoverA (a := 0) (b := 1) (by decide) : Preorder' (Fin 3)).le

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

-- A profile where voters 0..k-1 prefer a over b, and voters k..N-1 prefer b over a
def swappedProfile {α : Type} [LinearOrder α] {N:ℕ} (k : Fin (N+1)) (a b : α) (hab : a ≠ b): PreferenceProfile α N :=
  fun j ↦ if j.val < k.val then preferAoverB a b hab else preferBoverA a b hab

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

-- voter k isPivotal when their switch affects the society
def isPivotal {α : Type} [LinearOrder α] {N : ℕ}
    (R : SocialWelfareFunction α N) (k : Fin N) (f: profileGen α N) (a b : α): Prop :=
  socPrefers R (f k.castSucc) a b ∧  -- a preferred before k
  socPrefers R (f k.succ) b a        -- b preferred after k

-- profile generator f flips R when all or none voters change minds
def isFlipping  {α : Type} {N : ℕ} (R : SocialWelfareFunction α N) (f: profileGen α N) (a b : α): Prop :=
  socPrefers R (f 0) a b  ∧ socPrefers R (f (Fin.last N)) b a

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

-- if a property holds at 0 and not at N (or vice versa),
-- there must be a first index where it flips
lemma exists_pivotal
  {α : Type}
  [LinearOrder α]
  (a b : α)
  (hab : a ≠ b)
  (N:ℕ)
  {R: SocialWelfareFunction α N}
  (f: profileGen α N)
  (hf: isFlipping R f a b):
    ∃ k : Fin N, isPivotal R k f a b := by
  obtain ⟨ hStart, hEnd ⟩ := hf
  let P := fun k => socPrefers R (f k) b a
  have hp0: ¬ P 0 := by
    simp [P]
    apply  Preorder'.lt_asymm at hStart
    exact hStart
  have hpN: P (Fin.last N) := by
    simp [P]
    exact hEnd
  have hh: ∃ k : Fin N, ¬ P k.castSucc ∧ P k.succ := by
    exact flip_exists N P hp0 hpN
  obtain ⟨ k, hk ⟩ := hh
  simp [P] at hk
  rcases hk with ⟨ hleft, hright ⟩
  use k
  constructor
  exact Preorder'.lt_of_not_lt _ b a (Ne.symm hab) hleft
  exact hright

lemma exists_two_distinct {α : Type} [Fintype α] (ha : Fintype.card α ≥ 3) :
  ∃ a b : α, a ≠ b := by
  by_contra h
  push_neg at h
  rw [← Fintype.card_le_one_iff] at h
  omega

lemma exists_third {α : Type} [Fintype α] [DecidableEq α]
    (ha : Fintype.card α ≥ 3) (a b : α) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  by_contra h
  push_neg at h
  have h' : ∀ c : α, c = a ∨ c = b := by
    intro c
    by_cases hca : c = a
    · left; exact hca
    · right; exact h c hca
  have hle : Fintype.card α ≤ 2 := by
    have hsub: Finset.univ ⊆ {a, b} := by
      intro x _
      simp [Finset.mem_insert]
      exact h' x
    calc Finset.univ.card
          ≤ ({a, b} : Finset α).card := Finset.card_le_card hsub
        _ ≤ 2 := by apply le_trans (Finset.card_insert_le a {b}); simp
  omega



theorem Impossibility
    {α : Type} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SocialWelfareFunction α N,
    (unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictactorship _ _ R) := by
  by_contra h
  obtain ⟨ R, h⟩ := h
  rcases h with ⟨ hunanimity, hAIIA, hNonDictactor ⟩
  apply hNonDictactor
  obtain ⟨a, b, hab⟩ := exists_two_distinct ha
  obtain ⟨c, hca, hcb⟩ := exists_third ha a b

  -- let p
  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  let p: profileGen α N :=
    fun k =>
      fun i =>
        if i.val < k.val
          then preorderFromRanking b c a (Ne.symm hcb) hca (Ne.symm hab)
          else preorderFromRanking a b c hab (Ne.symm hcb) (Ne.symm hca)
  have hpflipping: isFlipping R p a b := by
    simp only [isFlipping]
    constructor
    -- k = 0
    . apply hunanimity
      intro i
      simp only [p]
      have hi0: ¬ (i.val < 0) := Nat.not_lt_zero _
      simp
      exact preorderFromRanking_lt_01 a b c hab (Ne.symm hcb) (Ne.symm hca)
    -- k = N
    . apply hunanimity
      intro i
      simp only [p]
      have : ((i.castSucc).val < (Fin.last N).val) := by
        simp [Fin.castSucc, Fin.last]
      simp
      exact preorderFromRanking_lt_02 b c a (Ne.symm hcb) hca (Ne.symm hab)

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
        . exact preorderFromRanking_lt_01 b c a (Ne.symm hcb) hca (Ne.symm hab)
        . exact preorderFromRanking_lt_12 a b c hab (Ne.symm hcb) (Ne.symm hca)
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
          then preorderFromRanking b c a (Ne.symm hcb) hca (Ne.symm hab)
          else if i.val = k.val
            then preorderFromRanking b a c (Ne.symm hab) (Ne.symm hca) (Ne.symm hcb)
            else preorderFromRanking a b c hab (Ne.symm hcb) (Ne.symm hca)

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
          simp [preorderFromRanking_lt_01 b a c (Ne.symm hab) (Ne.symm hca) (Ne.symm hcb)]
          simp [preorderFromRanking_lt_02 b c a (Ne.symm hcb) hca (Ne.symm hab)]
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
          simp [preorderFromRanking_lt_02 a b c hab (Ne.symm hcb) (Ne.symm hca)]
          simp [preorderFromRanking_lt_12 b a c (Ne.symm hab) (Ne.symm hca) (Ne.symm hcb)]
        . simp only [hhh, if_false]
    have hSocPreferPac: socPrefers R (p n_ab.castSucc) a c := by
      obtain ⟨ hab, hbc ⟩ := habc
      exact (R (p n_ab.castSucc)).lt_trans hbc hab
    apply hAIIA at hSameCol
    exact hSameCol.mp hSocPreferPac


  -- focusing on b c
  -- by AIIA with p q
  -- n_ab dictate b c (*)
  have h_n_ab_dictacte_bc: dictate_ab R n_ab b c := by sorry

  -- n_bc ≥ n_ab
  let n_bc: Fin N := sorry
  have h_nab_le_nbc: n_ab ≤ n_bc := by sorry


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
