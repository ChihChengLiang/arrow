import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../Arrow"
set_option verso.exampleModule "Arrow"

def yu2012 : InProceedings where
  title := inlines!"A one-shot proof of Arrow's impossibility theorem"
  authors := #[inlines!"Ning Neil Yu"]
  year := 2012
  booktitle := inlines!"Economic Theory"
  url := "https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf"

#doc (Manual) "A Formalization of Arrow's Impossibility Theorem" =>
%%%
authors := ["CC Liang"]
shortTitle := "Arrow"
%%%

Arrow's Impossibility Theorem is one of the most celebrated results in social choice theory.
Proved by Kenneth Arrow in 1951, it shows that no voting system with three or more alternatives
can simultaneously satisfy three basic fairness conditions.
This project contains a formal proof in Lean 4, following the one-shot proof of {citep yu2012}[].

# Preferences

In any social choice setting, each person holds a ranking of the available alternatives.
We model this as a _total preorder_{index}[total preorder]: a binary relation that is reflexive
(everyone is at least as good as themselves), transitive (rankings chain consistently),
and total (any two alternatives are always comparable in at least one direction).

```anchor Preorder
/-- A total preorder: reflexive, transitive, and total. -/
structure Preorder' (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a
```

Note that `le a b` and `le b a` can both hold simultaneously — this captures _indifference_
between `a` and `b`. Strict preference, where one option is unambiguously ranked above the other,
is defined separately:

```anchor StrictPref
/-- Strict preference: `a` is strictly preferred to `b` iff `a ≤ b` but not `b ≤ a`. -/
@[simp]
def Preorder'.lt (p : Preorder' α) (a b : α) : Prop :=
  p.le a b ∧ ¬p.le b a
```

So `p.lt a b` holds when `a` is weakly below `b` but `b` is _not_ weakly below `a`.

The proof uses two notation shorthands throughout:

```anchor Notation
-- Notation: `a ≻[p] b` means voter with preference `p` strictly prefers `a` over `b`
notation a " ≻[" p  "] " b => Preorder'.lt p b a
notation a " ≽[" p  "] " b => Preorder'.le p b a
notation a " ≻[" p  "] " b "≻ " c => (a ≻[p] b) ∧ b ≻[p] c
notation a " ≽[" p  "] " b "≻ " c => (a ≽[p] b) ∧ b ≻[p] c
```

Notice the reversal: `a ≻[p] b` expands to `Preorder'.lt p b a`.
Since `lt x y` means "`x` is below `y`", to say "`a` is above `b`" we write `lt b a`.
The notation hides this reversal so the mathematical reading stays natural: `a ≻[p] b` means
"under preference `p`, alternative `a` is strictly preferred to `b`."

Several useful properties of `lt` are proved as lemmas: asymmetry (`lt_asymm`),
transitivity (`lt_trans`), and a mixed version (`lt_of_lt_of_le`) that upgrades
a strict preference followed by a weak preference into a strict one.

# Social Welfare Functions

With `N` voters each holding a preference ordering over alternatives `α`,
a _preference profile_{index}[preference profile] records everyone's ranking simultaneously:

```anchor Profile
/-- A preference profile assigns each voter `i ∈ Fin N` their preference ordering. -/
def Profile (α : Type) (N : ℕ) := Fin N → Preorder' α
```

A _Social Welfare Function_{index}[Social Welfare Function] (SWF) is a procedure that takes
a preference profile and produces a single _social_ preference ordering — a way of aggregating
individual opinions into a collective verdict:

```anchor SWF
/-- A Social Welfare Function aggregates individual preferences into a social ordering. -/
def SWF (α : Type) (N : ℕ) := Profile α N → Preorder' α
```

## Arrow's Three Conditions

Arrow identified three normative requirements that any "fair" SWF should satisfy.

_Unanimity_{index}[unanimity] (also called the Pareto condition):
if _every_ voter strictly prefers `a` to `b`, then society must also strictly prefer `a` to `b`.
No SWF should override a unanimous opinion.

```anchor Unanimity
/-- **Unanimity** (Pareto): If all voters prefer `a` over `b`, so does society. -/
def Unanimity (R : SWF α N) : Prop :=
  ∀ (p: Profile α N) (a b: α), (∀ i: Fin N, a ≻[p i] b) → a ≻[R p] b
```

_Independence of Irrelevant Alternatives_{index}[independence of irrelevant alternatives] (IIA):
the social ranking of any pair `(a, b)` must depend _only_ on how individuals rank `a` against `b`,
and not on their opinions about unrelated alternatives `c`, `d`, etc.

To state this precisely, two profiles _agree on_ `(a, b)` when every voter has identical
views on that pair in both profiles:

```anchor AgreeOn
/-- Two profiles agree on `(a, b)` if every voter ranks `a` vs `b` the same way in both. -/
@[simp]
def AgreeOn (p q : Profile α N) (a b : α) : Prop :=
  ∀ i, ((a ≽[p i] b) ↔ a ≽[q i] b) ∧ ((b ≽[p i] a) ↔ b ≽[q i] a)
```

IIA then says that whenever two profiles agree on `(a, b)`, the social output must too:

```anchor IIA
/-- **Independence of Irrelevant Alternatives**: The social ranking of `a` vs `b`
    depends only on individual rankings of `a` vs `b`. -/
def IIA (R : SWF α N) : Prop :=
  ∀ (p q: Profile α N) (a b: α),
    AgreeOn p q a b → ((a ≽[R p] b) ↔ a ≽[R q] b) ∧ ((b ≽[R p] a) ↔ b ≽[R q] a)
```

_Non-Dictatorship_{index}[non-dictatorship]:
there must be no single voter who always gets their way on every pair of alternatives.
Formally, voter `k` _dictates_{index}[dictator] the pair `(a, b)` if society always copies
voter `k`'s strict preference on that pair, regardless of how everyone else votes:

```anchor Dictates
/-- Voter `k` is a dictator for the pair `(a, b)` if whenever `k` prefers `a` over `b`,
    society also prefers `a` over `b`. -/
def Dictates (R : SWF α N) (k : Fin N) (a b : α): Prop :=
  ∀ (p: Profile α N ), (a ≻[p k] b) → a ≻[R p] b
```

A _dictator_ is a voter who dictates every distinct pair.
Non-Dictatorship rules this out:

```anchor NonDictatorship
/-- **Non-Dictatorship**: No single voter dictates the outcome for all pairs. -/
def NonDictatorship (R : SWF α N): Prop :=
  ¬ (∃ i: Fin N, ∀ (a b: α), (a ≠ b) → Dictates R i a b)
```

# Proof Overview

Arrow's theorem says these three conditions are mutually incompatible when there are at least
three alternatives and at least one voter.
The proof proceeds by contradiction: assume all three conditions hold, then construct an explicit
dictator — violating Non-Dictatorship.

The central idea is the _pivotal voter_{index}[pivotal voter].
Fix two distinct alternatives `a` and `b`, and imagine flipping voters one by one
from preferring `a ≻ b` to preferring `b ≻ a`.

```
         k=0          k=1          k=2          k=N
  a≻b  [0,1,...,N-1]  [1,...,N-1]  [2,...,N-1]   ∅
  b≻a  ∅              {0}          {0,1}          [0,...,N-1]
```

When `k = 0`, everyone prefers `a ≻ b`, so by Unanimity, society prefers `a ≻ b`.
When `k = N`, everyone prefers `b ≻ a`, so by Unanimity, society prefers `b ≻ a`.
Somewhere along the way, the social preference must flip.
The _pivotal voter_ is the first voter whose switch causes this flip.

The clever part: using IIA, one can show that this pivotal voter must dictate
_every_ pair of alternatives — not just `(a, b)`. This contradicts Non-Dictatorship.

# Constructing Concrete Preferences

The proof needs to reason about specific profiles with known rankings.
To do this, it uses a helper function {anchorName prefer}`prefer` that builds a `Preorder'`
from an explicit ordering of three alternatives.

First, a type for the three tie patterns:

```anchor Tie
/-- Where ties occur in a 3-element preference ranking -/
inductive Tie | Not | Top | Bot
```

Then {anchorName prefer}`prefer` produces a `Preorder'` where `a₀` is the top-ranked
alternative and `a₂` is the bottom-ranked one, with `tie` controlling indifference:

```anchor prefer
/-- Construct a preference ordering with optional ties:
    - `Tie.Not`: a₀ > a₁ > a₂ (strict ranking)
    - `Tie.Top`: a₀ ~ a₁ > a₂ (top two tied)
    - `Tie.Bot`: a₀ > a₁ ~ a₂ (bottom two tied) -/
def prefer (a₀ _a₁ a₂ : α) (tie : Tie) (h02 : a₀ ≠ a₂) : Preorder' α where
```

The proof only requires `a₀ ≠ a₂` (the top and bottom are distinct); the middle
element can even be a duplicate of `a₀` or `a₂`, which the proof exploits — for example,
`prefer b b a .Not h` effectively creates a ranking where `b ≻ a` with `b` duplicated.

# The Canonical Swap

The central construction is a parametric family of profiles indexed by `k ∈ Fin (N+1)`.
In profile `canonicalSwap a b hab k`, voters `0, …, k-1` all prefer `b ≻ a`
while voters `k, …, N-1` all prefer `a ≻ b`:

```anchor canonicalSwap
/-- A family of profiles indexed by `k ∈ Fin (N+1)`:
    voters `0..k-1` prefer `b ≻ a`, voters `k..N-1` prefer `a ≻ b`. -/
@[simp]
def canonicalSwap (a b : α) (hab : a ≠ b) : Fin (N+1) → Profile α N :=
  fun k: Fin (N+1) =>
    fun i: Fin N => if i < k.val
      -- `prefer` takes 3 items, we duplicate middle as a workaround
      then prefer b b a .Not (Ne.symm hab)  -- b on top
      else prefer a b b .Not hab            -- a on top
```

At index `k = 0`, every voter prefers `a ≻ b` and society must follow by Unanimity.
At index `k = N`, every voter prefers `b ≻ a` and society must follow by Unanimity.

{anchorName flipping}`flipping` records the event that society's preference has switched:
when the first `k+1` voters have been flipped to prefer `b ≻ a`, society no longer
strictly prefers `a ≻ b`:

```anchor flipping
/-- `flipping R a b hab k` holds iff society prefers `b ≻ a` when voters `0..k` prefer `b ≻ a`. -/
def flipping (R : SWF α N) (a b : α) (hab : a ≠ b) :=
  fun k: Fin N => ¬ a ≻[R (canonicalSwap a b hab k.succ)] b
```

The lemma `flip_exists` uses Unanimity to show that flipping must occur for some `k`.

# The Pivotal Voter

The _pivotal voter_{index}[pivotal voter] for the pair `(a, b)` is defined as the _minimum_
voter index at which flipping first occurs:

```anchor pivoter
/-- The pivotal voter for `(a, b)`: the minimum `k` where society flips from `a ≻ b` to `b ≻ a`. -/
noncomputable def pivoter (a b : α) (hab : a ≠ b) (hu : Unanimity R) : Fin N :=
  Fin.find (flipping R a b hab) (flip_exists R a b hab hu)
```

Being the minimum, it satisfies two precise boundary conditions.

Before the pivot — for any voter `i` strictly earlier than the pivotal voter —
society still prefers `a ≻ b` when voters `0, …, i` have been flipped:

```anchor no_flip
/-- Before the pivotal voter, society still prefers `a ≻ b`. -/
lemma no_flip (a b : α) {hab : a ≠ b} (i : Fin N) {hu: Unanimity R}:
    i < pivoter a b hab hu → a ≻[R (canonicalSwap a b hab i.succ)] b := by
```

At the pivot itself, society has (at least weakly) switched to `b ≽ a`:

```anchor flipped
/-- At the pivotal voter, society flips to `b ≻ a`. -/
lemma flipped (a b : α) {hab : a ≠ b} {hu: Unanimity R}:
    b ≽[R (canonicalSwap a b hab (pivoter a b hab hu).succ)] a := by
```

Note that {anchorName flipped}`flipped` gives a _weak_ preference `b ≽ a`, not a strict one.
This is because `pivoter` is the first `k` where `¬(a ≻ b)`, which by `not_lt` is equivalent
to `b ≽ a`, but doesn't immediately imply `b ≻ a`.

Together, voter `pivoter` is precisely the tipping point: include one fewer voter and society
still prefers `a`; include the pivotal voter and society switches to weakly preferring `b`.

# From Pivotal Voter to Dictator

## The Key Lemma

The crux of the proof is the following: the pivotal voter for any pair `(a, b)` also
controls the social ranking of a _third_ alternative `c`:

```anchor nab_dictate_bc
/-- The pivotal voter for `(a, b)` dictates the pair `(b, c)`. -/
lemma nab_dictate_bc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    : Dictates R (pivoter a b hab hu) b c := by
```

The proof is the most intricate part of the argument and uses two carefully crafted
"magic profiles" to leverage IIA.
Write `n` for `pivoter a b hab hu`.

:::paragraph
*Magic profile 1.*{margin}[The specific layout is chosen so that (a,b) and (b,c) can each be analyzed using the pivotal voter lemmas independently.]
Voters `0, …, n-1` prefer `b ≻ c ≻ a` and voters `n, …, N-1` prefer `a ≻ b ≻ c`.

In this profile:
- Society prefers `a ≻ b`: by IIA with the canonical swap, this profile's `(a,b)` rankings
  match a canonical swap profile where {anchorName no_flip}`no_flip` applies.
- Society prefers `b ≻ c`: every single voter prefers `b ≻ c`, so Unanimity kicks in.

Therefore society prefers `a ≻ b ≻ c` in magic profile 1.
:::

:::paragraph
*Magic profile 2.*
Now take any profile `pp` where voter `n` strictly prefers `b ≻ c`.
Build a new profile that:
- For voters `i < n`: copies `pp`'s ranking of `(b, c)` but ranks that block above `a`.
- For voter `i = n`: gives `b ≻ a ≻ c`.
- For voters `i > n`: copies `pp`'s ranking of `(b, c)` but ranks `a` at the top.

In this profile:
- Society weakly prefers `b ≽ a`: by IIA with the canonical swap and the {anchorName flipped}`flipped` lemma.
- Society strictly prefers `a ≻ c`: by IIA comparing with magic profile 1.

Combining: `b ≽ a ≻ c`, which by `lt_of_lt_of_le` gives `b ≻ c`.

Finally, profiles `pp` and magic profile 2 agree on `(b, c)` by construction,
so IIA transfers: society prefers `b ≻ c` in `pp` too.
Since `pp` was arbitrary (with voter `n` preferring `b ≻ c`), voter `n` dictates `(b, c)`. ∎
:::

## Pivotal Voters Coincide

The proof next shows that the pivotal voter is the _same_ for every pair of alternatives.
It establishes two ordering inequalities between pivotal voters for different pairs.

{anchorName nab_le_nbc}`nab_le_nbc` — the pivotal voter for `(a, b)` comes _no later_ than the one for `(b, c)`:

```anchor nab_le_nbc
/-- The pivotal voter for `(a, b)` comes no later than the one for `(b, c)`. -/
lemma nab_le_nbc (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R)
    : pivoter a b hab hu ≤ pivoter b c hbc hu := by
```

Proof by contradiction: if the `(a,b)` pivotal voter `n_ab` came _after_ `n_bc`,
then in the canonical swap for `(b,c)` at step `n_bc + 1`,
voter `n_ab` already prefers `b ≻ c`.
By {anchorName nab_dictate_bc}`nab_dictate_bc`, voter `n_ab` forces society to prefer `b ≻ c` there too.
But that profile is exactly where `n_bc` caused society to flip away from `b`,
giving a contradiction.

{anchorName ncb_le_nab}`ncb_le_nab` — the pivotal voter for `(c, b)` comes _no later_ than the one for `(a, b)`:

```anchor ncb_le_nab
/-- The pivotal voter for `(c, b)` comes no later than the one for `(a, b)`. -/
lemma ncb_le_nab (a b c: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu: Unanimity R) (hIIA: IIA R):
    pivoter c b (Ne.symm hbc) hu ≤ pivoter a b hab hu := by
```

Proof by contradiction: if `n_cb` came after `n_ab`, then at step `n_ab` in the canonical swap
for `(c,b)`, voter `n_ab` prefers `b ≻ c`.
By {anchorName nab_dictate_bc}`nab_dictate_bc`, society also prefers `b ≻ c`.
But `n_ab` is before `n_cb`, so by {anchorName no_flip}`no_flip`, society should still prefer `c ≻ b` — contradiction.

Combining both inequalities cyclically (and applying them to `(b,c)` and `(c,b)` symmetrically),
all pivotal voters for pairs within `{a, b, c}` collapse to a single voter.

## Dictating Every Pair

With all pivotal voters identified as the same voter `n`,
{anchorName nab_dictate_xy}`nab_dictate_xy` extends dictatorship to _every_ pair `(x, y)`:

```anchor nab_dictate_xy
/-- The pivotal voter for any pair `(a, b)` dictates *every* pair `(x, y)`. -/
lemma nab_dictate_xy (a b c x y: α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y)
    (hu: Unanimity R) (hIIA: IIA R):
    Dictates R (pivoter a b hab hu) x y := by
```

The proof is a case split on whether `x` and `y` lie in `{b, c}`.
Each case routes through one or two applications of {anchorName nab_dictate_bc}`nab_dictate_bc` (with appropriate
bridging alternatives) and uses the pivotal-voter equality lemmas to transfer the
identity of the pivotal voter across pairs.

# Arrow's Impossibility Theorem

Assembling all the pieces:
if an SWF satisfies Unanimity and IIA, its pivotal voter for any pair
dictates every other pair — making them a full dictator and contradicting Non-Dictatorship.

```anchor Impossibility
/-- **Arrow's Impossibility Theorem**: No SWF with ≥3 alternatives and ≥1 voters
    can satisfy Unanimity, IIA, and Non-Dictatorship simultaneously. -/
theorem Impossibility [Fintype α] (ha : Fintype.card α ≥ 3):
    ¬ ∃ R : SWF α N, (Unanimity R) ∧ (IIA R) ∧ (NonDictatorship R) := by
```

The proof:
1. Assume for contradiction that such an `R` exists with `hu : Unanimity R`, `hIIA : IIA R`, and `hNonDictator : NonDictatorship R`.
2. Since `|α| ≥ 3`, extract three distinct alternatives `a`, `b`, `c` using `Fintype.two_lt_card_iff`.
3. Let `n = pivoter a b hab hu`.
4. By {anchorName nab_dictate_xy}`nab_dictate_xy`, voter `n` dictates every distinct pair `(x, y)`.
5. This gives an explicit dictator, contradicting `hNonDictator`. ∎

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
