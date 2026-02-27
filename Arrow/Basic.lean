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

def contiguous {α : Type} (p : Preorder' α)  {a b : α} :=
  ∀ c:α, c≠ a ∧ c≠ b → p.lt c a ↔ p.lt c b

-- Map individual i to their preferences
def PreferenceProfile (α : Type) (N : ℕ) :=
  Fin N → Preorder' α

def SocialWelfareFunction (α : Type) (N : ℕ) :=
  (Fin N → Preorder' α) → Preorder' α

def profileUpdate
  {α : Type} {N : ℕ} (p: PreferenceProfile α N) (p' : Preorder' α) (i: Fin N)
  : PreferenceProfile  α N :=
  fun j => if j = i then p' else p j


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

-- if everyone like `a` over `b`, so is society
def unanimity (R : SocialWelfareFunction α N) : Prop :=
  ∀ (p: PreferenceProfile α N) (a b: α),
    (∀ i: Fin N, voterPrefers (p i) a b) → socPrefers R p a b

--- all voters in both profile p and q prefer a over b
def sameCol {α : Type} {N : ℕ}
    (p q : PreferenceProfile α N) (a b : α) : Prop :=
  ∀ i, voterPrefers (p i) a b ↔ voterPrefers (q i) a b  -- voter i prefers a over b in p iff in q

-- (AIIA: Arrow's Independence of Irrelevant Alternatives)
-- If each individual's preferences over `a` and `b` are the same in profile `p` and profile `q`,
-- then SocialWelfareFunction(p) and SocialWelfareFunction(q) rank the two alternatives the same
def AIIA (R : SocialWelfareFunction α N) : Prop :=
  ∀ (p q: PreferenceProfile α N) (a b: α),
    sameCol p q a b → (socPrefers R p a b ↔ socPrefers R q a b)

def dictate_ab {α : Type} {N : ℕ} (R : SocialWelfareFunction α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: PreferenceProfile α N ), voterPrefers (p k) a b → socPrefers R p a b

def NonDictactorship (R : SocialWelfareFunction α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), dictate_ab R i a b)

-- voter k isPivotal when their switch affects the society
def isPivotal {α : Type} {N : ℕ}
    (R : SocialWelfareFunction α N) (k : Fin N) (p: PreferenceProfile α N): Prop :=
    ∃ p': Preorder' α, R (profileUpdate p p' k) ≠ R p

def isABPivotal {α : Type} {N : ℕ}
    (R : SocialWelfareFunction α N) (k : Fin N) (p: PreferenceProfile α N) (a b: α): Prop :=
    ∃ p': Preorder' α, socPrefers R p a b ↔ socPrefers R (profileUpdate p p' k) b a

lemma ab_pivotal_transfers {α : Type} [LinearOrder α] {N : ℕ}
  (R : SocialWelfareFunction α N)
  (k : Fin N)
  (p: PreferenceProfile α N)
  (a b: α)
  (hab: a ≠ b)
  (hPivotal: isABPivotal R k p a b)
  (hAIIA: AIIA _ _ R):
  ∀ p' : PreferenceProfile α N,
    (∀ j : Fin N, voterPrefers (p j) a b ↔ voterPrefers (p' j) a b) → isABPivotal R k p' a b := by
    intro p' h
    obtain ⟨ pp, hPivotal2 ⟩ := hPivotal
    unfold isABPivotal
    use pp
    have h2: sameCol p' p a b := by
      simp [sameCol]
      intro i
      apply h at i
      rw[i]
    apply  hAIIA at h2
    have h3: sameCol (profileUpdate p' pp k) (profileUpdate p pp k) b a := by
      simp [sameCol]
      intro i
      simp [profileUpdate]
      split_ifs with hh
      . rfl
      . have hhh := h i
        simp only [voterPrefers] at *
        rw [← not_iff_not, iff_comm]
        constructor
        · intro h hh
          have hhhh := Preorder'.lt_of_not_lt (p i) b a (Ne.symm hab) h
          have hhhhh := hhh.mp hhhh
          have hhhhhh := Preorder'.lt_asymm (p' i) b a hhhhh
          exact absurd hh hhhhhh
        · intro h  h2
          have h3 := Preorder'.lt_asymm (p i) a b h2
          rw [← not_iff_not] at hhh
          apply hhh.mp at h3
          have h4 := Preorder'.lt_of_not_lt (p' i) a b hab h3
          exact absurd h4 h
    apply  hAIIA at h3
    rw [h2, h3]
    exact hPivotal2

-- k is positively AB pivotal at p under R
def positivelyABPivotal {α : Type} {N : ℕ} (R : SocialWelfareFunction α N)
  (k : Fin N)
  (p: PreferenceProfile α N)
  (a b: α): Prop :=
    (isABPivotal R k p a b)∧
    (∀ p': Preorder' α, voterPrefers p' a b → socPrefers R (profileUpdate p p' k) a b)

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
