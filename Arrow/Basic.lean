import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

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

-- Map individual i to their preferences
def PreferenceProfile (α : Type) (N : ℕ) :=
  Fin N → Preorder' α

def SocialWelfareFunction (α : Type) (N : ℕ) :=
  (Fin N → Preorder' α) → Preorder' α

-- A constitution respects unanimity if society puts alternative `a` strictly above
-- `b` whenever every individual puts `a` strictly above `b`.
def unanimity (R : SocialWelfareFunction α N) : Prop :=
  ∀ (profile: PreferenceProfile α N) (a b: α),
    (∀ i: Fin N, (profile i).lt a b) -> (R profile).lt a b


-- (AIIA: Arrow's Independence of Irrelevant Alternatives)
-- If each individual's preferences over `a` and `b` are the same in profile `p` and profile `q`,
-- then SocialWelfareFunction(p) and SocialWelfareFunction(q) rank the two alternatives the same
def AIIA (R : SocialWelfareFunction α N) : Prop :=
  ∀ (p q: PreferenceProfile α N) (a b: α),
      (∀ i: Fin N, (p i).lt a b ↔ (q i).lt a b) →
      ((R p).lt a b ↔ (R q).lt a b)

def NonDictactorship (R : SocialWelfareFunction α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (p: PreferenceProfile α N ) (a b: α), (p i).lt a b → (R p).lt a b )


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

-- A profile where voters 0..k-1 prefer a over b, and voters k..N-1 prefer b over a
def swappedProfile {α : Type} [LinearOrder α] {N:ℕ} (k : Fin (N+1)) (a b : α) (hab : a ≠ b): PreferenceProfile α N :=
  fun j ↦ if j.val < k.val then preferAoverB a b hab else preferBoverA a b hab

omit [Fintype α] in
lemma preferAoverB_lt {α : Type} [LinearOrder α] (a b : α) (hab : a ≠ b) : (preferAoverB a b hab).lt b a := by
  simp only [Preorder'.lt, preferAoverB]
  constructor
  split_ifs
  split_ifs with hab2 hba
  tauto
  tauto
  exact hba

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
  (hun: (unanimity _ _ R)):
    ∃ k : Fin N,
    (R (swappedProfile k.castSucc a b hab)).lt a b ∧
    (R (swappedProfile k.succ a b hab)).lt b a := by
  -- when k = 0, everyone prefers b over a, so society prefers b over a
  have hStart : (R (swappedProfile 0 a b hab)).lt a b := by
    apply hun
    intro i
    rw[swappedProfile]
    have : ¬ (i.val < 0) := Nat.not_lt_zero _
    simp
    simp only [preferBoverA]
    exact preferAoverB_lt b a (Ne.symm hab)
  -- when k = N, everyone prefers a over b, so society prefers a over b
  have hEnd : (R (swappedProfile (Fin.last N) a b hab)).lt b a := by
    apply hun
    intro i
    rw[swappedProfile]
    have : ((i.castSucc).val < (Fin.last N).val) := by
      simp [Fin.castSucc, Fin.last]
    simp
    exact preferAoverB_lt a b hab
  let P := fun k => (R (swappedProfile k a b hab)).lt b a
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
  exact Preorder'.lt_of_not_lt _ a b hab hleft
  exact hright

theorem Impossibility :
    ¬ ∃ R : SocialWelfareFunction α N,
    (unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictactorship _ _ R) := by
  by_contra h
  obtain ⟨ R, h⟩ := h
  rcases h with ⟨ hunanimity, hAIIANonDictactor ⟩
  rcases hAIIANonDictactor with ⟨ hAIIA, hNonDictactor ⟩
  apply hNonDictactor
  constructor
  intro p a b
    sorry

  sorry

def hello := "world"
