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

lemma Preorder'.lt_iff {α : Type} (p q: Preorder' α) {a b: α}
  (h_iff: p.lt b a ↔ q.lt b a)(hab: a≠b): p.lt a b ↔ q.lt a b := by
  rw [← not_iff_not]
  constructor <;> intro h
  . exact q.lt_asymm _ _ (h_iff.mp (p.lt_of_not_lt _ _ (Ne.symm hab) h))
  . exact p.lt_asymm _ _ (h_iff.mpr (q.lt_of_not_lt _ _ (Ne.symm hab) h))

-- A preference profile maps individual i to their preferences
def Profile (α : Type) (N : ℕ) :=
  Fin N → Preorder' α

-- Social Welfare Function
def SWF (α : Type) (N : ℕ) :=
  (Fin N → Preorder' α) → Preorder' α

-- Useful for building profile with a pivotal voter
abbrev SwapSequence: Type := Fin (N+1) →  Profile α N

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
def AgreeOn {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) : Prop :=
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

def swapping_k
  {α : Type} {N:ℕ} (p q: Profile α N) (k: Fin (N+1))
  : Profile α N :=
  fun i: Fin N => if i < k.val then p i else q i

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

def IsSequentialSwap
  {α : Type}
  {N : ℕ}
  (a b : α)
  (f: SwapSequence α N): Prop :=
    ∀ (k: Fin (N+1)) (i: Fin N),
    (i.val < k.val → b ≻[f k i] a ) ∧
    (i.val ≥ k.val → a ≻[f k i] b )

def IsPivotal
  {α : Type}
  {N : ℕ}
  (R : SWF α N)
  (f: SwapSequence α N)
  (a b : α)
  (n_ab: Fin N): Prop :=
  (∀ i ≤ n_ab, a ≻[R (f i.castSucc)] b) ∧ b ≻[R (f n_ab.succ)] a

-- Canonical profiles: p = everyone ranks b > a, q = everyone ranks a > b
def canonicalSwap
  {α : Type} [LinearOrder α]
  {N : ℕ}
  (a b : α)
  (hab : a ≠ b)
  : SwapSequence α N :=
  -- put extra b or a just to reuse a 3 items ranking
  let p : Profile α N := fun _ => orderFromRanking b b a (Ne.symm hab) -- b on top
  let q : Profile α N := fun _ => orderFromRanking a b b hab           -- a on top
  swapping_k p q

noncomputable def pivotalVoter
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  {R : SWF α N}
  (a b : α) (hab : a ≠ b)
  (hu : Unanimity R) : Fin N :=
  let cs := canonicalSwap a b hab
  let P := fun k: Fin N => b ≻[R (cs k.succ)] a
  let hN: ∃ k, P k := by
    use (0:Fin N).rev
    unfold P cs canonicalSwap swapping_k
    have: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    simp [Nat.sub_add_cancel this]
    apply hu
    simp [orderFromRanking_lt_02 b _ a (Ne.symm hab)]
  -- Find the minimum k where the flip happens
  Fin.find P hN

-- pivotalVoter is independent of profile
lemma pivotalVoter_spec
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (f : Fin (N+1) → Profile α N)
  (hf: IsSequentialSwap a b f)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : IsPivotal R f a b (pivotalVoter a b hab hu) := by
  let n_ab := pivotalVoter a b hab hu
  let cs: SwapSequence α N := canonicalSwap a b hab
  let P := fun k: Fin N => b ≻[R (cs k.succ)] a

  -- Get the existence witness for Fin.find
  have hN: ∃ k, P k := by
    use (0:Fin N).rev
    unfold P cs canonicalSwap swapping_k
    have hpos: 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    simp [Nat.sub_add_cancel hpos]
    apply hu
    simp [orderFromRanking_lt_02 b _ a (Ne.symm hab)]

  -- P n_ab holds: society prefers b > a at column n_ab.succ
  have hPn : P n_ab := Fin.find_spec hN

  -- For j < n_ab, ¬P j: society doesn't prefer b > a, hence prefers a > b
  have hPmin : ∀ j : Fin N, j < n_ab → ¬P j := fun j hj => Fin.find_min hN hj

  -- Helper: Agree on for any column k between f and canonical swapping process
  have hAgreeGen : ∀ k : Fin (N+1), AgreeOn (f k) (cs k) a b := by
    intro k i; unfold cs canonicalSwap swapping_k
    split_ifs with hik
    . rw [Preorder'.lt_iff _ _ _ (Ne.symm hab)]
      simp [orderFromRanking_lt_02 b _ a (Ne.symm hab), (hf k i).1 hik]
    . simp at hik
      simp [orderFromRanking_lt_02 a _ b hab, (hf k i).2 hik]

  constructor
  . intro i hi
    have h_soc_ab := hAIIA (f i.castSucc) (cs i.castSucc) a b (hAgreeGen i.castSucc)
    apply h_soc_ab.mpr
    by_cases hizero : i.val = 0
    . -- i = 0
      apply hu (cs i.castSucc) a b
      intro j
      unfold cs canonicalSwap swapping_k
      simp [hizero]
      exact orderFromRanking_lt_02 a _ b hab
    . -- i ≠ 0
      let j : Fin N := ⟨i.val - 1, by omega⟩
      have : 0 < i.val := Nat.pos_of_ne_zero hizero
      have hjlt : j < n_ab := by simp only [Fin.lt_def, j]; omega
      have hnotPj := hPmin j hjlt
      have heq : j.succ = i.castSucc := by apply Fin.ext; simp [j]; omega
      simp only [P, heq] at hnotPj
      exact Preorder'.lt_of_not_lt _ _ _ (Ne.symm hab) hnotPj
  . have h_agree_ba : AgreeOn (f n_ab.succ) (cs n_ab.succ) b a := by
      intro i; have h := hAgreeGen n_ab.succ i
      exact Preorder'.lt_iff (f n_ab.succ i) (cs n_ab.succ i) h hab
    exact (hAIIA (f n_ab.succ) (cs n_ab.succ) b a h_agree_ba).mpr hPn

lemma pivotalVoter_pivot_canon
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : IsPivotal R (canonicalSwap a b hab) a b (pivotalVoter a b hab hu) := by
  let cs: SwapSequence α N := canonicalSwap a b hab
  have hf : IsSequentialSwap a b cs := by
    unfold IsSequentialSwap cs canonicalSwap swapping_k
    intro k i
    constructor
    . intro h; simp [h]; exact orderFromRanking_lt_02 b _ a (Ne.symm hab)
    . intro h;
      have :¬ i < k.val := by omega
      simp [this]
      exact orderFromRanking_lt_02 a _ b hab
  exact pivotalVoter_spec R a b hab cs hf hu hAIIA


lemma nab_pivotal_bc
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : Dictates R (pivotalVoter a b hab hu) b c := by
  let n_ab := pivotalVoter a b hab hu
  let p: Profile α N := fun i => orderFromRanking b c a (Ne.symm hab)
  let q: Profile α N := fun i => orderFromRanking a b c hac

  have hp: ∀ i: Fin N, b ≻[p i] c ≻ a := by
    intro i; constructor
    . exact orderFromRanking_lt_01 b c a hbc (Ne.symm hab)
    . exact orderFromRanking_lt_12 b c a hbc (Ne.symm hac) (Ne.symm hab)
  have hq: ∀ i: Fin N, a ≻[q i] b ≻ c := by
    intro i; constructor
    . exact orderFromRanking_lt_01 a b c hab hac
    . exact orderFromRanking_lt_12 a b c hab hbc hac

  -- 0...k-1 prefer b > c > a
  -- k ... N prefer a > b > c
  -- result: socPrefer a > b > c
  have hf : IsSequentialSwap a b (swapping_k p q) := by
    unfold IsSequentialSwap swapping_k
    intro k i
    constructor
    . intro h; simp [h]; exact ((p i).lt_trans (hp i).2 (hp i).1)
    . intro h; split_ifs
      . omega
      . exact (hq i).1
  have h_nab_pivot_p := pivotalVoter_spec R a b hab (swapping_k p q) hf hu hAIIA

  -- soc prefer a > b > c
  have habc: a ≻[R (swapping_k p q n_ab.castSucc)] b ≻ c  := by
    constructor
    -- a > b by def of n_ab
    . exact h_nab_pivot_p.1 n_ab (le_refl n_ab)
    -- b > c by unanimity
    . have h: ∀ i: Fin N, b ≻[swapping_k p q n_ab.castSucc i] c := by
        intro i; unfold swapping_k; split_ifs
        . exact (hp i).1
        . exact (hq i).2
      exact hu _ _ _ h
  intro pp h

  -- let rr
  -- 0...k-1 prefer b > a ∧ c > a
  -- k prefer b > a > c
  -- k+1 ... N prefer a > b ∧ c < a
  -- result: socPrefer b ≥ a > c
  let rr : Profile α N := fun i: Fin N =>
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

  have h_agree: AgreeOn pp rr b c := by
    unfold AgreeOn rr
    intro i
    split_ifs with hi hppibc hieqnab hppibc
    . simp [orderFromRanking_lt_01 b c a hbc (Ne.symm hab), hppibc]
    . rw [Preorder'.lt_iff _ _ _ (Ne.symm hbc)]
      simp only [Preorder'.lt_of_not_lt _ _ _ hbc hppibc,
        orderFromRanking_lt_01 c b a (Ne.symm hbc) (Ne.symm hac)]
    . simp [orderFromRanking_lt_02 b a c hbc, hieqnab]; exact h
    . simp [orderFromRanking_lt_12 a b c hab hbc hac, hppibc]
    . rw [Preorder'.lt_iff _ _ _ (Ne.symm hbc)]
      simp only [Preorder'.lt_of_not_lt _ _ _ hbc hppibc,
        orderFromRanking_lt_12 a c b hac (Ne.symm hbc) hab]

  have hbac: b ≻[R rr] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have h_agree_ba: AgreeOn (swapping_k p q n_ab.succ) rr b a := by
        unfold AgreeOn swapping_k
        intro i
        split_ifs with h
        . simp [(p i).lt_trans (hp i).2 (hp i).1]
          unfold rr
          simp at *
          have h2: ¬(i > n_ab) := by omega
          split_ifs with hinab hppibc hieqnab hppibc
          . exact orderFromRanking_lt_02 b c a (Ne.symm hab)
          . exact orderFromRanking_lt_12 c b a (Ne.symm hbc) (Ne.symm hab) (Ne.symm hac)
          . exact orderFromRanking_lt_01 b a c (Ne.symm hab) hbc
          . omega
          . omega
        . unfold rr q; simp at h
          have : ¬(i < n_ab) := by omega
          rw [Preorder'.lt_iff _ _ _ hab]
          split_ifs
          . omega
          . simp only [orderFromRanking_lt_01 a b c hab hac]
          . simp only [orderFromRanking_lt_02 a c b hab, orderFromRanking_lt_01 a b c hab hac]
      exact (hAIIA _ _ _ _ h_agree_ba).mp h_nab_pivot_p.2
    -- By AIIA
    . have hsoc_swp_ac: a ≻[R (swapping_k p q n_ab.castSucc)] c :=
        (R (swapping_k p q n_ab.castSucc)).lt_trans habc.2 habc.1
      have h_agree_ac: AgreeOn (swapping_k p q n_ab.castSucc) rr a c := by
        unfold AgreeOn rr swapping_k
        intro i
        simp at *
        split_ifs with hinab hppibc hieqnab hppibc
        . rfl
        . rw [Preorder'.lt_iff _ _ _ (Ne.symm hac)]
          simp only [orderFromRanking_lt_02 c b a (Ne.symm hac), (hp i).2]
        . simp [orderFromRanking_lt_12 b a c (Ne.symm hab) hac hbc]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [orderFromRanking_lt_02 a b c hac]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [orderFromRanking_lt_01 a c b hac hab]
          exact (q i).lt_trans (hq i).2 (hq i).1

      exact (hAIIA _ _ _ _ h_agree_ac).mp hsoc_swp_ac

  have hrr_bc := (R rr).lt_trans hbac.2 hbac.1
  exact (hAIIA _ _ _ _ h_agree).mpr hrr_bc

-- n_ab pivot b and c, so n_bc shouldn't flip the b c order earlier than n_ab
lemma nab_le_nbc
  {α : Type} [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hu: Unanimity R) (hAIIA: (AIIA R))
  : pivotalVoter a b hab hu ≤ pivotalVoter b c hbc hu := by
  by_contra h; push_neg at h
  let pp := (canonicalSwap b c hbc) (pivotalVoter b c hbc hu).succ
  have h_pref : b ≻[pp (pivotalVoter a b hab hu)] c := by
    simp only [pp, canonicalSwap, swapping_k]
    split_ifs with hh
    . simp at hh; omega
    . exact orderFromRanking_lt_02 b _ c hbc
  exact absurd (pivotalVoter_pivot_canon R b c hbc hu hAIIA).2
    (Preorder'.lt_asymm _ _ _ (nab_pivotal_bc a b c hab hac hbc hu hAIIA pp h_pref))

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
  let n_cb := pivotalVoter c b (Ne.symm hbc) hu
  let pp := (canonicalSwap c b (Ne.symm hbc)) n_cb.castSucc
  have h_pref : b ≻[pp (pivotalVoter a b hab hu)] c := by
    unfold pp canonicalSwap swapping_k
    have hlt : (pivotalVoter a b hab hu).val < n_cb.val := by omega
    simp [hlt]
    exact orderFromRanking_lt_02 b _ c hbc
  exact absurd ((pivotalVoter_pivot_canon R c b (Ne.symm hbc) hu hAIIA).1 n_cb (le_refl n_cb))
    (Preorder'.lt_asymm _ _ _ (nab_pivotal_bc a b c hab hac hbc hu hAIIA pp h_pref))

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
  by_cases hxa : x = a
  . rw [hxa]
    by_cases hyb : y = b
    . rw [hyb]
      simpa [← h_nba_eq_nca, ← h_nab_eq_nba] using nab_pivotal_bc c a b (Ne.symm hac) (Ne.symm hbc) hab hu hAIIA
    . by_cases hyc : y = c
      . rw [hyc]
        simpa [← h_nab_eq_nba] using nab_pivotal_bc b a c (Ne.symm hab) hbc hac hu hAIIA
      . rw [hxa] at hxy
        simpa [← h_nab_eq_nba] using nab_pivotal_bc b a y (Ne.symm hab) (Ne.symm hyb) hxy hu hAIIA
  . by_cases hxb : x = b
    . rw [hxb]
      by_cases hya : y = a
      . rw [hya]
        simpa [h_ncb_eq_nab] using nab_pivotal_bc c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) hu hAIIA
      . by_cases hyc : y = c
        . rw [hyc]; exact nab_pivotal_bc a b c hab hac hbc hu hAIIA
        . rw [hxb] at hxy; exact nab_pivotal_bc a b y hab (Ne.symm hya) hxy hu hAIIA
    . by_cases hxc : x = c
      . rw [hxc]
        by_cases hya : y = a
        . rw [hya]
          simpa [h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc b c a hbc (Ne.symm hab) (Ne.symm hac) hu hAIIA
        . by_cases hyb : y = b
          . rw [hyb]
            simpa [← h_nbc_eq_nac, h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc a c b hac hab (Ne.symm hbc) hu hAIIA
          . rw [hxc] at hxy
            simpa [h_nbc_eq_ncb, h_ncb_eq_nab] using nab_pivotal_bc b c y hbc (Ne.symm hyb) hxy hu hAIIA
      . -- x ∉ {a,b,c}
        obtain ⟨h_nbx_eq_nxb, h_nxb_eq_nab⟩ := n_ab_pivotal_bc_cb a b x hab (Ne.symm hxa) (Ne.symm hxb) hu hAIIA
        obtain ⟨_, h_nbx_eq_nax⟩ := n_ab_pivotal_bc_cb a x b (Ne.symm hxa) hab hxb hu hAIIA
        by_cases hya : y = a
        . rw [hya]
          simpa [h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc b x a (Ne.symm hxb) (Ne.symm hab) hxa hu hAIIA
        . by_cases hyb : y = b
          . rw [hyb]
            simpa [← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc a x b (Ne.symm hxa) hab hxb hu hAIIA
          . by_cases hyc : y = c
            . rw [hyc]
              simpa [← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc a x c (Ne.symm hxa) hac hxc hu hAIIA
            . simpa [h_nbx_eq_nxb, h_nxb_eq_nab] using nab_pivotal_bc b x y (Ne.symm hxb) (Ne.symm hyb) hxy hu hAIIA

theorem Impossibility
    {α : Type} [Fintype α] [LinearOrder α]
    {N:ℕ } [NeZero N]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N,
    (Unanimity R) ∧ (AIIA R) ∧ (NonDictatorship R) := by
  by_contra h
  obtain ⟨ R, ⟨ hu, hAIIA, hNonDictactor ⟩⟩ := h
  apply hNonDictactor

  -- i j k | in the paper are translated into
  -- a b c

  obtain ⟨ a, b, c, ⟨ hab, hac, hbc⟩ ⟩ := Fintype.two_lt_card_iff.mp ha

  let n_ab := pivotalVoter a b hab hu

  use n_ab
  intro x y hxy
  exact n_ab_dictate_xy a b c x y hab hac hbc hxy hu hAIIA
