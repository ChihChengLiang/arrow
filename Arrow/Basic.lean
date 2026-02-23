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

def Preorder'.lt {α : Type} (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a

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
      (∀ i: Fin N, (p i).lt a b) ↔ (∀ i: Fin N, (q i).lt a b) ->
      ((R p).lt a b ↔ (R q).lt a b)

def NonDictactorship (R : SocialWelfareFunction α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (p: PreferenceProfile α N ) (a b: α), (p i).lt a b → (R p).lt a b )


def preferAoverB {α : Type} (a b : α) (hab : a ≠ b) : Preorder' α where
  le x y := x = y ∨ x = b ∨ y = a  ∨ (x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b) -- a is top, b is bottom, else arbitrary
  refl := by
    intro x
    left
    rfl
  trans := by
    intro x y z hxy hyz
    rcases hxy with hxy | hxb | hya | hneg
    rcases hyz with hyz | hyb | hxa | hneg
    rw[hyz] at hxy
    left
    exact hxy
    rw[hyb] at hxy
    right
    left
    exact hxy
    right
    right
    left
    exact hxa
    right
    right
    right
    rw [← hxy] at hneg
    exact hneg
    right
    left
    exact hxb
    rcases hyz with hyz | hyb | hxa | hneg
    right
    right
    left
    rw[hyz] at hya
    exact hya
    have : a = b := by rw [← hya, hyb]
    exact absurd this hab
    right
    right
    left
    exact hxa
    exact absurd hya hneg.left
    rcases hyz with hyz | hyb | hxa | hneg2
    rw[hyz] at hneg
    right
    right
    right
    exact hneg
    exact absurd hyb hneg.right.right.right
    right
    right
    left
    exact hxa
    right
    right
    right
    constructor
    exact hneg.left
    constructor
    exact hneg.right.left
    constructor
    exact hneg2.right.right.left
    exact hneg2.right.right.right

  total := by
    intro x y
    by_cases hxa : x = a
    right
    right
    right
    left
    exact hxa
    by_cases hxb : x = b
    left
    right
    left
    exact hxb
    by_cases hya: y = a
    left
    right
    right
    left
    exact hya
    by_cases hyb: y = b
    right
    right
    left
    exact hyb
    left
    right
    right
    right
    push_neg at hxa hxb hya hyb
    constructor
    exact hxa
    constructor
    exact hxb
    constructor
    exact hya
    exact hyb

def preferBoverA {α : Type} (a b : α) (hab : a ≠ b) : Preorder' α :=
  preferAoverB b a (Ne.symm hab)

#check @preferBoverA
example : Preorder' (Fin 3) := preferBoverA (⟨0, by decide⟩ : Fin 3) ⟨1, by decide⟩ (by decide)
#reduce (preferBoverA (a := 0) (b := 1) (by decide) : Preorder' (Fin 3)).le

-- A profile where voters 0..k-1 prefer a over b, and voters k..N-1 prefer b over a
def swappedProfile {α : Type} {N:ℕ} (k : Fin (N+1)) (a b : α) (hab : a ≠ b): PreferenceProfile α N :=
  fun j ↦ if j.val < k.val then preferAoverB a b hab else preferBoverA a b hab

omit [Fintype α] in
lemma preferAoverB_lt (a b : α) (hab : a ≠ b) : (preferAoverB a b hab).lt b a := by
  simp only [Preorder'.lt, preferAoverB]
  constructor
  right
  left
  tauto
  push_neg
  constructor
  exact hab
  constructor
  exact hab
  constructor
  exact Ne.symm hab
  intro h
  by_contra hh
  apply h
  rfl

-- if a property holds at 0 and not at N (or vice versa),
-- there must be a first index where it flips
lemma exists_pivotal
  {α : Type}
  (a b : α)
  (hab : a ≠ b)
  (N:ℕ)
  {R: SocialWelfareFunction α N}
  (hun: (unanimity _ _ R)):
    ∃ k : Fin N,
    (R (swappedProfile k.castSucc a b hab)).lt b a ∧
    (R (swappedProfile k.succ a b hab)).lt a b := by
  -- when k = 0, everyone prefers b over a, so society prefers b over a
  have hStart : (R (swappedProfile 0 a b hab)).lt b a := by
    show (R (swappedProfile 0 a b hab)).lt b a
    apply hun
    intro i
    rw[swappedProfile]
    have : ¬ (i.val < 0) := Nat.not_lt_zero _
    simp
    simp only [Preorder'.lt]
    simp only [preferBoverA]
    simp only [preferAoverB]


    -- swappedProfile 0 means all voters prefer b over a
    sorry
  sorry

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
