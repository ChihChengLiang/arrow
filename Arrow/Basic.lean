import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Classical

variable (α: Type) [Fintype α]-- α is the type of alternatives
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

@[simp]
lemma Preorder'.not_lt {α : Type} (p : Preorder' α) (a b : α) :
    ¬ p.lt a b ↔ p.le b a := by
  unfold Preorder'.lt
  constructor
  . intro h; push_neg at h
    rcases p.total a b with hab | hba
    . exact h hab
    . exact hba
  . intro hba; push_neg; intro _; exact hba

lemma Preorder'.le_of_lt {α : Type} (p : Preorder' α) (a b : α) :
    p.lt a b → p.le a b := by
    intro h
    exact h.1

lemma Preorder'.lt_trans  {α : Type} (p : Preorder' α) {a b c : α}
    (h1 : p.lt a b) (h2 : p.lt b c) : p.lt a c := by
    constructor
    . exact p.trans _ _ _ h1.1 h2.1
    . intro h
      exact h1.2 (p.trans _ _ _ h2.1 h)

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
notation a " ≽[" p  "] " b => Preorder'.le p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c

-- In society R, voter k dictate just ab
def Dictates {α : Type} {N : ℕ} (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b

-- all voters in both profile p and q prefer a over b
def AgreeOn {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)

lemma AgreeOnStrongly {α : Type} {N : ℕ}
    (p q : Profile α N) (a b : α) :
    (∀ i, (a ≻[p i] b) ↔ (a ≻[q i] b)) → AgreeOn p q a b := by
  intro h i
  by_cases hab : a = b
  . subst hab; simp only [(p i).refl, (q i).refl, iff_self, and_self]
  . -- For a ≠ b: r.lt a b ↔ ¬r.lt b a (by asymm + total + antisymm)
    have key : ∀ r : Preorder' α, r.lt a b ↔ ¬r.lt b a := fun r =>
      ⟨r.lt_asymm a b, fun hn => (r.total a b).elim
        (fun h => ⟨h, fun hba => hab (r.antisymm a b h hba)⟩)
        (fun h => absurd ⟨h, fun h' => hab (r.antisymm b a h h').symm⟩ hn)⟩
    simp only [← Preorder'.not_lt, not_iff_not]
    exact ⟨by rw [key, key, not_iff_not]; exact h i, h i⟩

-- if everyone like `a` over `b`, so is society
def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α),
    (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b

-- (AIIA: Arrow's Independence of Irrelevant Alternatives)
-- If each individual's preferences over `a` and `b` are the same in profile `p` and profile `q`,
-- then SocialWelfareFunction(p) and SocialWelfareFunction(q) rank the two alternatives the same
def AIIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≻[R p] b) ↔ a ≻[R q] b)

def NonDictatorship (R : SWF α N): Prop :=
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
  total := by intro a b; split_ifs <;> simp_all [le_total a b]
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
  (∀ i ≤ n_ab, a ≻[R (f i.castSucc)] b) ∧ b ≽[R (f n_ab.succ)] a

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

def functionToFind
  {α : Type} [LinearOrder α]
  {N : ℕ}
  (R : SWF α N)
  (a b : α) (hab : a ≠ b) :=
  let cs := canonicalSwap a b hab
  fun k: Fin N => b ≽[R (cs k.succ)] a

lemma functionCanBeFound
  {α : Type} [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (hu : Unanimity _ _ R):
  ∃ k, functionToFind R a b hab k := by
  let cs: SwapSequence α N := canonicalSwap a b hab
  use (0:Fin N).rev
  unfold functionToFind canonicalSwap swapping_k
  have: 0 < N := by exact Nat.pos_of_ne_zero (NeZero.ne N)
  simp [Nat.sub_add_cancel this]
  have hstrong: b ≻[R (fun i => orderFromRanking b b a (Ne.symm hab))] a := by
    apply hu
    simp [orderFromRanking_lt_02 b _ a (Ne.symm hab)]
  apply Preorder'.le_of_lt at hstrong
  exact hstrong

noncomputable def pivotalVoter
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (hu : Unanimity _ _ R) : Fin N :=
  -- Find the minimum k where the flip happens
  Fin.find (functionToFind R a b hab) (functionCanBeFound R a b hab hu)

-- pivotalVoter is independent of profile
lemma pivotalVoter_spec
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (f : Fin (N+1) → Profile α N)
  (hf: IsSequentialSwap a b f)
  (hAIIA: AIIA _ _ R )
  (hu : Unanimity _ _ R) :
  IsPivotal R f a b (pivotalVoter R a b hab hu) := by
  let n_ab := pivotalVoter R a b hab hu
  let cs: SwapSequence α N := canonicalSwap a b hab
  let P := functionToFind R a b hab

  -- Get the existence witness for Fin.find
  have hN := functionCanBeFound R a b hab hu

  -- P n_ab holds: society prefers b > a at column n_ab.succ
  have hPn : P n_ab := Fin.find_spec hN

  -- For j < n_ab, ¬P j: society doesn't prefer b > a, hence prefers a > b
  have hPmin : ∀ j : Fin N, j < n_ab → ¬P j := fun j hj => Fin.find_min hN hj

  -- Helper: sameCol for any column k between f and canonical swapping process
  have hSameColGen : ∀ k : Fin (N+1), AgreeOn (f k) (cs k) a b := by
    intro k i; unfold cs canonicalSwap swapping_k
    split_ifs with hik
    . -- i < k.val: swapping_k uses p, which has b > a, so ¬(a > b)
      rw [← not_iff_not]
      have hfba := (hf k i).1 hik
      constructor
      . intro h; apply Preorder'.lt_asymm; exact orderFromRanking_lt_02 b _ a (Ne.symm hab)
      . intro h; apply Preorder'.lt_asymm; exact hfba
    . -- i ≥ k.val: swapping_k uses q, which has a > b
      simp at hik
      have hfba := (hf k i).2 hik
      simp [hfba]
      exact orderFromRanking_lt_02 a _ b hab

  have hSameCol: AgreeOn (f n_ab.succ) (cs n_ab.succ) a b := hSameColGen n_ab.succ

  constructor
  . -- Part 1: ∀ i ≤ n_ab, socPrefers R (f i.castSucc) a b
    intro i hi
    have hSameCol_i : AgreeOn (f i.castSucc) (cs i.castSucc) a b := hSameColGen i.castSucc
    -- Need to show society prefers a > b at swapping_k p q i.castSucc
    have hgoal: a ≻[R (cs i.castSucc)] b := by
      by_cases hilt : i < n_ab
      . by_cases hizero : i.val = 0
        · -- Column 0: everyone prefers a > b by unanimity on q
          have hall : ∀ j : Fin N, a ≻[cs i.castSucc j] b := by
            intro j; unfold cs canonicalSwap swapping_k; simp [hizero]
            exact orderFromRanking_lt_02 a _ b hab
          exact hu (cs i.castSucc) a b hall
        · -- Column i.val > 0: use that j = i-1 satisfies j+1 = i and j < n_ab
          have hipos : 0 < i.val := Nat.pos_of_ne_zero hizero
          let j : Fin N := ⟨i.val - 1, by omega⟩
          have hjlt : j < n_ab := by
            simp only [Fin.lt_def, j]
            have : i.val < n_ab.val := hilt
            omega
          have hnotPj := hPmin j hjlt
          simp only [P, functionToFind] at hnotPj
          have heq : j.succ = i.castSucc := by apply Fin.ext; simp [j]; omega
          rw [heq] at hnotPj
          simp [← Preorder'.not_lt] at hnotPj
          exact hnotPj
      . have hieq: i = n_ab := by omega
        subst hieq
        by_cases hnzero : n_ab.val = 0
        . -- Column 0: unanimity
          have hall : ∀ j : Fin N, a ≻[cs n_ab.castSucc j] b := by
            intro j
            unfold cs canonicalSwap swapping_k
            simp [hnzero]
            exact orderFromRanking_lt_02 a _ b hab
          have hsoc := hu (cs n_ab.castSucc) a b hall
          exact hsoc
        . -- Column n_ab.val > 0: use j = n_ab - 1
          have hnpos : 0 < n_ab.val := Nat.pos_of_ne_zero hnzero
          let j : Fin N := ⟨n_ab.val - 1, by omega⟩
          have hjlt : j < n_ab := by simp only [Fin.lt_def, j]; omega
          have hnotPj := hPmin j hjlt
          simp only [P, functionToFind] at hnotPj
          have heq : j.succ = n_ab.castSucc := by apply Fin.ext; simp [j]; omega
          rw [heq] at hnotPj
          simp [← Preorder'.not_lt] at hnotPj
          exact hnotPj
    exact (hAIIA (f i.castSucc) (cs i.castSucc) a b hSameCol_i).mpr hgoal
  . -- Part 2: socWeakPrefers R (f n_ab.succ) b a
    apply hAIIA at hSameCol
    rw [← not_iff_not, Preorder'.not_lt, Preorder'.not_lt] at hSameCol
    apply hSameCol.mpr
    exact hPn

lemma pivotalVoter_pivot_canon
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N : ℕ} [NeZero N]
  (R : SWF α N)
  (a b : α) (hab : a ≠ b)
  (hAIIA: AIIA _ _ R )
  (hu : Unanimity _ _ R) :
  IsPivotal R (canonicalSwap a b hab) a b (pivotalVoter R a b hab hu) := by
  let n_ab := pivotalVoter R a b hab hu
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
  exact pivotalVoter_spec R a b hab cs hf hAIIA hu


lemma nab_pivotal_bc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  {R: SWF α N}
  (hu: Unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  : Dictates R (pivotalVoter R a b hab hu) b c := by
  let n_ab := pivotalVoter R a b hab hu
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
  have h_nab_pivot_p := pivotalVoter_spec R a b hab (swapping_k p q) hf hAIIA hu

  -- soc prefer a > b > c
  have habc: a ≻[R (swapping_k p q n_ab.castSucc)] b ≻ c  := by
    constructor
    -- a > b by def of n_ab
    . exact h_nab_pivot_p.1 n_ab (le_refl n_ab)
    -- b > c by unanimity
    . have h: ∀ i: Fin N, b ≻[swapping_k p q n_ab.castSucc i] c := by
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

  have hSameCol: AgreeOn pp rr b c := by
    unfold AgreeOn
    intro i
    unfold rr
    split_ifs with hi hppibc hieqnab hppibc
    . simp [orderFromRanking_lt_01 b c a hbc (Ne.symm hab)]
      exact hppibc
    . rw [← not_iff_not]
      constructor
      . intro
        apply  Preorder'.lt_asymm
        simp [orderFromRanking_lt_01 c b a (Ne.symm hbc) (Ne.symm hac)]
      . intro
        exact hppibc
    . simp [orderFromRanking_lt_02 b a c hbc]
      rw [hieqnab]
      exact h
    . simp [orderFromRanking_lt_12 a b c hab hbc hac]; exact hppibc
    . rw [← not_iff_not]
      constructor
      . intro
        apply  Preorder'.lt_asymm
        simp [orderFromRanking_lt_12 a c b hac (Ne.symm hbc) hab]
      . intro
        exact hppibc

  have hbac: b ≻[R rr] a ≻ c := by
    constructor
    -- By AIIA on nab pivoting defintion
    . have hSameCol_ba: AgreeOn (swapping_k p q n_ab.succ) rr b a := by
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
        . rw [← not_iff_not]
          constructor
          . intro h; apply Preorder'.lt_asymm
            unfold rr
            simp at *
            have h2: ¬(i < n_ab) := by omega
            split_ifs
            . omega
            . exact orderFromRanking_lt_01 a b c hab hac
            . exact orderFromRanking_lt_02 a c b hab
          . intro h; apply Preorder'.lt_asymm; exact (hq i).1
      have hSocPrefer_rr_ba := by apply hAIIA at hSameCol_ba; exact hSameCol_ba;
      exact hSocPrefer_rr_ba.mp h_nab_pivot_p.2
    -- By AIIA
    . have hsoc_swp_ac: a ≻[R (swapping_k p q n_ab.castSucc)] c :=
        (R (swapping_k p q n_ab.castSucc)).lt_trans habc.2 habc.1
      have hSameCol_ac: AgreeOn (swapping_k p q n_ab.castSucc) rr a c := by
        unfold AgreeOn rr swapping_k
        intro i
        simp at *
        split_ifs with hinab hppibc hieqnab hppibc
        . rw [← not_iff_not]
        . rw [← not_iff_not]
          constructor
          . intro h; apply Preorder'.lt_asymm
            exact orderFromRanking_lt_02 c b a (Ne.symm hac)
          . intro h; apply Preorder'.lt_asymm
            exact (hp i).2
        . simp [orderFromRanking_lt_12 b a c (Ne.symm hab) hac hbc]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [orderFromRanking_lt_02 a b c hac]
          exact (q i).lt_trans (hq i).2 (hq i).1
        . simp [orderFromRanking_lt_01 a c b hac hab]
          exact (q i).lt_trans (hq i).2 (hq i).1

      have hSoc_rr_ac := by apply hAIIA at hSameCol_ac; exact hSameCol_ac
      exact hSoc_rr_ac.mp hsoc_swp_ac

  have hrr_bc := (R rr).lt_trans hbac.2 hbac.1
  have hSocPrefer := by apply hAIIA at hSameCol; exact hSameCol
  exact hSocPrefer.mpr hrr_bc

lemma nab_le_nbc
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: Unanimity _ _ R)
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
  let pp := (canonicalSwap b c hbc) n_bc.succ
  have h3: b ≻[pp n_ab] c:= by
    unfold pp canonicalSwap swapping_k
    split_ifs with hh
    . simp at *; omega
    . exact orderFromRanking_lt_02 b _ c hbc
  have h4 := h_nab_dictate_bc pp h3
  have h5 := by apply Preorder'.lt_asymm at h4; exact h4
  exact absurd  h_nbc_pivot.2 h5

lemma ncb_le_nab
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: Unanimity _ _ R)
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
  let pp := (canonicalSwap c b (Ne.symm hbc)) n_cb.castSucc
  -- We haven't reached pivotal voter n_cb, society supposed to rank c > b
  have h1: c ≻[R pp] b := h_ncb_pivot.1 n_cb (le_refl n_cb)
  -- But n_ab already flipped to b > c, the dictactorial position should flip society ranking already
  have h2: b ≻[R pp] c := by
    have h20: b ≻[pp n_ab] c := by
      unfold pp canonicalSwap swapping_k
      have: n_ab < n_cb.val := by omega
      simp [this]
      exact orderFromRanking_lt_02 b _ c hbc
    exact h_nab_dictate_bc pp h20
  have h3 := by apply Preorder'.lt_asymm at h2; exact h2
  exact absurd h1 h3

lemma nbc_le_ncb
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: Unanimity _ _ R)
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
  {R: SWF α N}
  (a b c: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hu: Unanimity _ _ R)
  (hAIIA: (AIIA _ _ R))
  :
  -- n_bc = n_cb = n_ab
  (pivotalVoter R b c hbc hu) = (pivotalVoter R c b (Ne.symm hbc) hu) ∧
  (pivotalVoter R c b (Ne.symm hbc) hu) = pivotalVoter R a b hab hu := by

  let n_ab := pivotalVoter R a b hab hu
  let n_bc := pivotalVoter R b c hbc hu
  let n_cb := pivotalVoter R c b (Ne.symm hbc) hu
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
  have h_nbc_eq_ncb: n_bc = n_cb := by exact le_antisymm h_nbc_le_ncb h_ncb_le_nbc
  have h_ncb_eq_nab: n_cb = n_ab := by
    have h_nab_le_n_cb: n_ab ≤ n_cb := by exact le_trans h_nab_le_nbc h_nbc_le_ncb
    exact le_antisymm h_ncb_le_nab h_nab_le_n_cb

  exact ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩

-- n_bc = n_cb = n_ab can be extended to n_ts
lemma n_ab_dictate_xy
  {α : Type} [DecidableEq α] [LinearOrder α]
  {N:ℕ} [NeZero N]
  {R: SWF α N}
  (a b c x y: α)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (hxy : x ≠ y)
  (hu: Unanimity _ _ R)
  (hAIIA: (AIIA _ _ R)):
  Dictates R (pivotalVoter R a b hab hu) x y := by

  let n_ab := pivotalVoter R a b hab hu
  have h_nab_dictate_bc := nab_pivotal_bc a b c hab hac hbc hu hAIIA
  obtain ⟨ h_nbc_eq_ncb, h_ncb_eq_nab⟩ := n_ab_pivotal_bc_cb a b c hab hac hbc hu hAIIA
  have h_nca_dictate_ab := nab_pivotal_bc c a b (Ne.symm hac) (Ne.symm hbc) hab  hu hAIIA
  obtain ⟨ h_nab_eq_nba, h_nba_eq_nca⟩ := n_ab_pivotal_bc_cb c a b (Ne.symm hac) (Ne.symm hbc) hab hu hAIIA
  obtain ⟨ _ , h_nbc_eq_nac⟩ := n_ab_pivotal_bc_cb a c b hac hab (Ne.symm hbc) hu hAIIA
  rcases eq_or_ne x a with hxa | hxnea
  . --x=a
    rw[hxa]
    rcases eq_or_ne y b with hyb | hyneb
    . -- y=b
      rw[hyb]
      rw [← h_nba_eq_nca,← h_nab_eq_nba ] at h_nca_dictate_ab
      exact h_nca_dictate_ab
    . -- y≠b
      rcases eq_or_ne y c with hyc | hynec
      . -- y = c
        rw[hyc]
        have h_nba_dictate_ac := nab_pivotal_bc b a c (Ne.symm hab) hbc hac hu hAIIA
        rw[← h_nab_eq_nba] at h_nba_dictate_ac
        exact h_nba_dictate_ac
      . -- y ∉ {a,b,c}
        rw[hxa] at hxy
        have h_nba_dictate_ay := nab_pivotal_bc b a y (Ne.symm hab) (Ne.symm hyneb) hxy hu hAIIA
        rw[← h_nab_eq_nba] at h_nba_dictate_ay
        exact h_nba_dictate_ay
  . --x≠a
    rcases eq_or_ne x b with hxb | hxneb
    . -- x=b
      rw[hxb]
      rcases eq_or_ne y a with hya | hynea
      . -- y=a
        rw[hya]
        have h_ncb_dictate_ba := nab_pivotal_bc c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) hu hAIIA
        rw[h_ncb_eq_nab] at h_ncb_dictate_ba
        exact h_ncb_dictate_ba
      . -- y≠ a
        rcases eq_or_ne y c with hyc | hynec
        . -- y = c
          rw[hyc]
          exact h_nab_dictate_bc
        . -- y ∉ {a,b,c}
          rw[hxb] at hxy
          exact nab_pivotal_bc a b y hab (Ne.symm hynea) hxy hu hAIIA
    . --x≠b
      rcases eq_or_ne x c with hxc | hxnec
      . --x=c
        rw[hxc]
        rcases eq_or_ne y a with hya | hynea
        . -- y=a
          rw[hya]
          have h_nbc_dictate_ca := nab_pivotal_bc b c a hbc (Ne.symm hab) (Ne.symm hac) hu hAIIA
          rw [h_nbc_eq_ncb, h_ncb_eq_nab] at h_nbc_dictate_ca
          exact h_nbc_dictate_ca
        . -- y≠a
          rcases eq_or_ne y b with hyb | hyneb
          . -- y=b
            rw[hyb]
            have h_nac_dictate_cb := nab_pivotal_bc a c b hac hab (Ne.symm hbc) hu hAIIA
            rw[← h_nbc_eq_nac, h_nbc_eq_ncb, h_ncb_eq_nab] at h_nac_dictate_cb
            exact h_nac_dictate_cb
          . -- y≠b
            rw[hxc] at hxy
            have h_nbc_dictate_cy := nab_pivotal_bc b c y hbc (Ne.symm hyneb) hxy hu hAIIA
            rw[h_nbc_eq_ncb, h_ncb_eq_nab] at h_nbc_dictate_cy
            exact h_nbc_dictate_cy
      . --x  ∉ {a,b,c}
        obtain ⟨ h_nbx_eq_nxb, h_nxb_eq_nab⟩ := n_ab_pivotal_bc_cb a b x hab (Ne.symm hxnea) (Ne.symm hxneb) hu hAIIA
        obtain ⟨ _, h_nbx_eq_nax⟩ := n_ab_pivotal_bc_cb a x b (Ne.symm hxnea) hab hxneb hu hAIIA
        rcases eq_or_ne y a with hya | hynea
        . -- y=a
          rw[hya]
          have h_nbx_dictate_xa := nab_pivotal_bc b x a (Ne.symm hxneb) (Ne.symm hab) hxnea hu hAIIA
          rw[h_nbx_eq_nxb, h_nxb_eq_nab] at h_nbx_dictate_xa
          exact h_nbx_dictate_xa
        . -- y≠a
          rcases eq_or_ne y b with hyb | hyneb
          . -- y=b
            rw[hyb]
            have h_nax_dictate_xb := nab_pivotal_bc a x b (Ne.symm hxnea) hab hxneb hu hAIIA
            rw[← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] at h_nax_dictate_xb
            exact h_nax_dictate_xb
          . -- y≠b
            rcases eq_or_ne y c with hyc | hynec
            . --y=c
              rw[hyc]
              have h_nax_dictate_xc := nab_pivotal_bc a x c (Ne.symm hxnea) hac hxnec hu hAIIA
              rw[← h_nbx_eq_nax, h_nbx_eq_nxb, h_nxb_eq_nab] at h_nax_dictate_xc
              exact h_nax_dictate_xc
            . -- y ∉ {a,b,c}
              have h_nbx_dictate_xy := nab_pivotal_bc b x y (Ne.symm hxneb) (Ne.symm hyneb) hxy hu hAIIA
              rw[h_nbx_eq_nxb, h_nxb_eq_nab] at h_nbx_dictate_xy
              exact h_nbx_dictate_xy

theorem Impossibility
    {α : Type} [Fintype α] [DecidableEq α] [LinearOrder α]
    {N:ℕ } [NeZero N]
    (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N,
    (Unanimity _ _ R) ∧ (AIIA _ _ R) ∧ (NonDictatorship _ _ R) := by
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
