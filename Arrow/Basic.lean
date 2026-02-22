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

-- A profile where voters 0..k-1 prefer a over b, and voters k..N-1 prefer b over a
def swappedProfile (k : Fin (N+1)) (a b : α) : PreferenceProfile α N :=
  -- def preferAoverB := fun (x  y : α): (p : Preorder' α) ↦ if x = a ∧ y = b then  x > y else x = y
  fun j ↦ if j.val < k.val then b < a else a < b


-- The pivotal voter is the first k where society flips
def pivotalVoter (R : SocialWelfareFunction α N) (a b : α) : Fin N := sorry

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

def hello := "world"
