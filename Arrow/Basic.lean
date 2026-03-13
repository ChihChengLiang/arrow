import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Classical

variable (α: Type) -- α is the type of alternatives
variable (N: ℕ ) -- N is the number of voters

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

lemma Preorder'.lt_of_not_lt {α : Type} (p : Preorder' α) (a b : α)
    (hab : a ≠ b) (h : ¬ p.lt b a) : p.lt a b := by
  unfold Preorder'.lt at *; push_neg at h
  rcases p.total a b with hab' | hba'
  . constructor
    . exact hab'
    . by_contra hba; exact hab (p.antisymm a b hab' hba)
  . constructor
    . exact h hba'
    . by_contra hba; exact hab (p.antisymm a b (h hba') hba)

lemma Preorder'.lt_trans  {α : Type} (p : Preorder' α) {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h
      exact h1.2 (p.trans _ _ _ h2.1 h)

lemma Preorder'.lt_iff {α : Type} (p q: Preorder' α) {a b: α}
  (h_iff: p.lt b a ↔ q.lt b a)(hab: a≠b): p.lt a b ↔ q.lt a b := by
  rw [← not_iff_not]
  constructor <;> intro h
  . exact q.lt_asymm _ _ (h_iff.mp (p.lt_of_not_lt _ _ (Ne.symm hab) h))
  . exact p.lt_asymm _ _ (h_iff.mpr (q.lt_of_not_lt _ _ (Ne.symm hab) h))

-- A preference profile maps individual i to their preferences
def Profile (α : Type) (N : ℕ) := Fin N → Preorder' α

-- Social Welfare Function
def SWF (α : Type) (N : ℕ) := (Fin N → Preorder' α) → Preorder' α

-- society prefers a over b in profile p
notation a " ≻[" R p "] " b => Preorder'.lt (R p) b a
notation a " ≽[" R p "] " b => Preorder'.le (R p) b a
notation a " ≻[" R p "] " b "≻ " c =>
  Preorder'.lt (R p) b a ∧ Preorder'.lt (R p) b c

--- voter strictly prefers a over b
notation a " ≻[" p  "] " b => Preorder'.lt p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c

-- In society R, voter k dictate just ab
def Dictates {α : Type} {N : ℕ} (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b

-- all voters in both profile p and q prefer a over b
def AgreeOn {α : Type} {N : ℕ} (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, (a ≻[p i] b) ↔ a ≻[q i] b -- voter i prefers a over b in p iff in q

-- if everyone like `a` over `b`, so is society
def Unanimity {α : Type} {N : ℕ} (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α),
    (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b

-- (AIIA: Arrow's Independence of Irrelevant Alternatives)
-- If each individual's preferences over `a` and `b` are the same in profile `p` and profile `q`,
-- then `SWF(p)` and `SWF(q)` rank the two alternatives the same
def AIIA {α : Type} {N : ℕ} (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≻[R p] b) ↔ a ≻[R q] b)

def NonDictatorship {α : Type} {N : ℕ} (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)

def orderFromRanking {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) : Preorder' α where
  le x y :=
    -- first handle the 6 ordered pairs among a₀, a₁, a₂
    if x = a₂ then True              -- a₂ is bottom, below everything
    else if y = a₀ then True         -- a₀ is top, everything is below it
    else if x = a₀ then y = a₀      -- a₀ only ≤ itself
    else if y = a₂ then x = a₂      -- a₂ only ≥ itself
    -- now x, y ∉ {a₀, a₂} handled, only a₁ vs others remain
    else x ≤ y                        -- fallback to LinearOrder
  refl := by intro x; simp
  trans := by
    intro a b c ha hb; split_ifs with haa2 hca0 haa0 hca2 <;> simp_all
    by_cases hba0: b = a₀
    . simp_all
    . simp_all; exact le_trans ha.2 hb
  total := by intro a b; split_ifs <;> simp_all [le_total a b]
  antisymm := by
    intro a b ha hb
    split_ifs at ha with haa2 hba0 haa0 hba2 <;> simp_all
    . by_cases hba2: b = a₂
      . rw [← hba2]
      . exact absurd (hb hba2) (Ne.symm h02)
    . exact le_antisymm ha hb

lemma orderFromRanking_lt_01 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) :
    (orderFromRanking a₀ a₁ a₂ h02).lt a₁ a₀ := by
  simp [Preorder'.lt, orderFromRanking]
  exact ⟨h02, Ne.symm h01⟩

lemma orderFromRanking_lt_12 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂) :
    (orderFromRanking a₀ a₁ a₂ h02).lt a₂ a₁ := by
  simp [Preorder'.lt, orderFromRanking]
  split_ifs with ha10
  . exact absurd (Eq.symm ha10) h01
  . exact ⟨ h12, Ne.symm h02, h12 ⟩

lemma orderFromRanking_lt_02 {α : Type} [LinearOrder α]
    (a₀ a₁ a₂ : α) (h02 : a₀ ≠ a₂) :
    (orderFromRanking a₀ a₁ a₂ h02).lt a₂ a₀ := by
  simp [Preorder'.lt, orderFromRanking]
  exact ⟨h02, Ne.symm h02⟩

-- Canonical profiles: before, everyone ranks b ≻ a; after, everyone ranks a ≻ b
def canonicalSwap
  {α : Type} [LinearOrder α]
  {N : ℕ}
  (a b : α)
  (hab : a ≠ b)
  : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      -- put extra b or a just to reuse a 3 items ranking
      then orderFromRanking b b a (Ne.symm hab) -- b on top
      else orderFromRanking a b b hab           -- a on top

def flipping
  {α : Type} [LinearOrder α]
  {N : ℕ}
  (R : SWF α N)
  (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => b ≻[R ((canonicalSwap a b hab) k.succ)] a

lemma flip_exists
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (hu : Unanimity R):
  ∃ k, flipping R a b hab k := by
  use (0:Fin N).rev
  unfold flipping canonicalSwap
  have: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  simp [Nat.sub_add_cancel this]
  apply hu
  simp [orderFromRanking_lt_02 b _ a (Ne.symm hab)]

-- Find the minimum k where the flip happens
noncomputable def pivotalVoter
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  {R : SWF α N}
  (a b : α) (hab : a ≠ b)
  (hu : Unanimity R) : Fin N :=
  Fin.find (flipping R a b hab) (flip_exists R a b hab hu)

-- before pivot, no flip
lemma no_flip {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  {R : SWF α N}
  (a b : α) {hab : a ≠ b}
  (i : Fin N)
  {hu: Unanimity R}:
  i < pivotalVoter a b hab hu → a ≻[R (canonicalSwap a b hab i.succ)] b := by
  intro hilt
  exact Preorder'.lt_of_not_lt _ _ _ (Ne.symm hab)
    (Fin.find_min (flip_exists R a b hab hu) hilt)

-- at pivot, it flips
lemma flipped {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  {R : SWF α N}
  (a b : α) {hab : a ≠ b}
  {hu: Unanimity R}:
  b ≻[R (canonicalSwap a b hab (pivotalVoter a b hab hu).succ)] a := by
  exact Fin.find_spec (flip_exists R a b hab hu)

lemma nab_pivotal_bc
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : Dictates R (pivotalVoter a b hab hu) b c := by
  let n_ab := pivotalVoter a b hab hu

  -- Magic profile 1
  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  let mg1: Profile α N := fun i: Fin N =>
    if i < n_ab.val
      then orderFromRanking b c a (Ne.symm hab)
      else orderFromRanking a b c hac
  -- soc prefer a > b > c
  have habc: a ≻[R mg1] b ≻ c  := by
    constructor
    -- a > b by def of n_ab
    . by_cases hn : n_ab = 0
      . -- Case n_ab = 0: All voters prefer a > b, use unanimity
        have h : ∀ i : Fin N, a ≻[mg1 i] b := by
          intro i; simp [mg1, hn]
          exact orderFromRanking_lt_01 a b c hab hac
        exact hu _ _ _ h
      . -- Case n_ab ≠ 0: Use no_flip
        let k := n_ab - 1
        have hk : k.val < n_ab := by
          simp only [k]
          rw [Fin.val_sub_one_of_ne_zero hn]
          exact Nat.sub_one_lt (Fin.val_ne_of_ne hn)
        have hp : AgreeOn mg1 (canonicalSwap a b hab k.succ) a b := by
          intro i
          simp only [mg1, canonicalSwap]
          have hk_eq : (i.val < k.succ.val) ↔ (i.val < n_ab.val) := by
            simp only [k, Fin.val_succ, Fin.val_sub_one_of_ne_zero hn]
            omega
          by_cases hi : i.val < n_ab.val
          · -- Case i < n_ab: both orderings have b ≻ a, so a ≻ b is false
            simp only [hi, hk_eq.mpr hi, ↓reduceIte]
            rw[Preorder'.lt_iff _ _ _ (Ne.symm hab)]
            simp only [orderFromRanking_lt_02 b c a (Ne.symm hab), orderFromRanking_lt_02 b b a (Ne.symm hab)]
          · -- Case i ≥ n_ab: both orderings have a ≻ b
            have hi' : ¬(i.val < k.succ.val) := hk_eq.not.mpr hi
            simp only [hi, hi', ↓reduceIte, orderFromRanking_lt_01 a b b hab hab, orderFromRanking_lt_01 a b c hab hac]
        apply (hAIIA _ _ _ _ hp).mpr
        exact no_flip a b k hk
    -- b > c by unanimity
    . have h: ∀ i: Fin N, b ≻[mg1 i] c := by
        intro i; unfold mg1; split_ifs
        . exact orderFromRanking_lt_01 b c a hbc (Ne.symm hab)
        . exact orderFromRanking_lt_12 a b c hab hbc hac
      exact hu _ _ _ h
  intro pp h

  -- Magic profile 2: match arbitrary profile `pp` whose n_ab prefer b over c
  -- 0...k-1 prefer b > a ∧ c > a
  -- k prefer b > a > c
  -- k+1 ... N prefer a > b ∧ c < a
  -- result: socPrefer b ≥ a > c
  let mg2 : Profile α N := fun i: Fin N =>
    if i < n_ab
      then
        if b ≻[pp i] c
          then orderFromRanking b c a (Ne.symm hab)
          else orderFromRanking c b a (Ne.symm hac)
      else
        if i = n_ab
        then orderFromRanking b a c hbc
        else if b ≻[pp i] c
          then orderFromRanking a b c hac
          else orderFromRanking a c b hab

  have h_agree: AgreeOn pp mg2 b c := by
    unfold AgreeOn mg2; intro i; split_ifs with _ hppibc hieqnab hppibc
    . simp [orderFromRanking_lt_01 b c a hbc (Ne.symm hab), hppibc]
    . rw [Preorder'.lt_iff _ _ _ (Ne.symm hbc)]
      simp only [Preorder'.lt_of_not_lt _ _ _ hbc hppibc,
        orderFromRanking_lt_01 c b a (Ne.symm hbc) (Ne.symm hac)]
    . simp [orderFromRanking_lt_02 b a c hbc, hieqnab]; exact h
    . simp [orderFromRanking_lt_12 a b c hab hbc hac, hppibc]
    . rw [Preorder'.lt_iff _ _ _ (Ne.symm hbc)]
      simp only [Preorder'.lt_of_not_lt _ _ _ hbc hppibc,
        orderFromRanking_lt_12 a c b hac (Ne.symm hbc) hab]

  have hbac: b ≻[R mg2] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn mg2 (canonicalSwap a b hab n_ab.succ) b a := by
        unfold AgreeOn canonicalSwap; intro i; split_ifs with h
        . simp only [orderFromRanking_lt_02 b b a (Ne.symm hab)]; unfold mg2; simp at h
          split_ifs with hinab hppibc hieqnab hppibc
          . simp only [orderFromRanking_lt_02 b c a (Ne.symm hab)]
          . simp only [orderFromRanking_lt_12 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)]
          . simp only [orderFromRanking_lt_01 b a c (Ne.symm hab) hbc]
          . omega
          . omega
        . unfold mg2; simp at h
          have : ¬(i < n_ab) := by omega
          rw [Preorder'.lt_iff _ _ _ hab]
          simp only [orderFromRanking_lt_02 a b b hab]
          split_ifs
          . omega
          . simp only [orderFromRanking_lt_01 a b c hab hac]
          . simp only [orderFromRanking_lt_02 a c b hab]
      apply (hAIIA _ _ _ _ h_agree_ba).mpr
      exact flipped a b
    -- By AIIA
    . have h_agree_ac: AgreeOn mg1 mg2 a c := by
        unfold AgreeOn mg2 mg1; intro i; simp
        split_ifs with hinab hppibc hieqnab hppibc
        . rfl
        . rw [Preorder'.lt_iff _ _ _ (Ne.symm hac)]
          simp only [orderFromRanking_lt_02 c b a (Ne.symm hac), orderFromRanking_lt_12 b c a hbc (Ne.symm hac)]
        . simp only [orderFromRanking_lt_12 b a c (Ne.symm hab) hac hbc, orderFromRanking_lt_02 a b c hac]
        . simp only [orderFromRanking_lt_02 a b c hac]
        . simp [orderFromRanking_lt_01 a c b hac hab, orderFromRanking_lt_02 a b c hac]
      exact (hAIIA _ _ _ _ h_agree_ac).mp ((R mg1).lt_trans habc.2 habc.1)
  exact (hAIIA _ _ _ _ h_agree).mpr ((R mg2).lt_trans hbac.2 hbac.1)

-- n_ab pivot b and c, so n_bc shouldn't flip the b c order earlier than n_ab
lemma nab_le_nbc
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : pivotalVoter a b hab hu ≤ pivotalVoter b c hbc hu := by
  by_contra h; push_neg at h;
  let cs := canonicalSwap b c hbc (pivotalVoter b c hbc hu).succ
  have h_pref : b ≻[cs (pivotalVoter a b hab hu)] c := by
    simp only [cs, canonicalSwap]
    split_ifs with hh
    . simp at hh; omega
    . exact orderFromRanking_lt_02 b _ c hbc
  exact absurd
    (nab_pivotal_bc a b c hab hac hbc hu hAIIA cs h_pref) -- n_ab still dictates b over c
    (Preorder'.lt_asymm _ _ _ (flipped b c))              -- but n_bc flipped, so society should prefer c over b

-- n_cb should flip c b order before n_ab do so
lemma ncb_le_nab
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R)):
  pivotalVoter c b (Ne.symm hbc) hu ≤ pivotalVoter a b hab hu := by
  by_contra h; push_neg at h
  let n_ab := pivotalVoter a b hab hu
  let n_cb := pivotalVoter c b (Ne.symm hbc) hu
  let cs := canonicalSwap c b (Ne.symm hbc) n_ab.succ
  have: b ≻[cs n_ab] c := by simp [cs, canonicalSwap, orderFromRanking_lt_02 b _ c hbc]
  exact absurd
    (nab_pivotal_bc a b c hab hac hbc hu hAIIA cs this) -- n_ab prefer b over c, so is society
    (Preorder'.lt_asymm _ _ _ (no_flip c b n_ab h))     -- n_ab before pivoter, so b c shouldn't flip

lemma nbc_le_ncb
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : pivotalVoter c b (Ne.symm hbc) hu ≤ pivotalVoter b c hbc hu :=
  le_trans (ncb_le_nab a b c hab hac hbc hu hAIIA) (nab_le_nbc a b c hab hac hbc hu hAIIA)

lemma n_ab_pivotal_bc_cb
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R)):
  -- n_bc = n_cb = n_ab
  (pivotalVoter b c hbc hu) = (pivotalVoter c b (Ne.symm hbc) hu) ∧
  (pivotalVoter c b (Ne.symm hbc) hu) = pivotalVoter a b hab hu := by

  let n_ab := pivotalVoter a b hab hu
  let n_bc := pivotalVoter b c hbc hu
  let n_cb := pivotalVoter c b (Ne.symm hbc) hu
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

-- n_bc = n_cb = n_ab can be extended to any pair x y
lemma n_ab_dictate_xy
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c x y: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
  (hu: Unanimity R) (hAIIA: AIIA R):
  Dictates R (pivotalVoter a b hab hu) x y := by
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

theorem Impossibility
    {α : Type} [Fintype α] [LinearOrder α]
    {N:ℕ } [NeZero N]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N, (Unanimity R) ∧ (AIIA R) ∧ (NonDictatorship R) := by
  by_contra ⟨ R, ⟨ hu, hAIIA, hNonDictactor ⟩⟩
  apply hNonDictactor
  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha
  use pivotalVoter a b hab hu
  intro x y hxy
  exact n_ab_dictate_xy a b c x y hab hac hbc hxy hu hAIIA
