module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section



/-!
# Unramified and G-unramified ring maps

Let `R → S` be a ring map. It is *unramified* if it is of finite type and `Ω_{S/R} = 0`, and
*G-unramified* — the notion of EGA — if it is of finite presentation and `Ω_{S/R} = 0`. Given a
prime `q` of `S`, the map is unramified (resp. G-unramified) *at `q`* if there is a `g ∈ S`,
`g ∉ q`, with `R → S_g` unramified (resp. G-unramified). Since a map of finite presentation is of
finite type, a G-unramified map is unramified, and likewise at a prime.

The vanishing of the module of differentials is the same condition as formal unramifiedness, the
uniqueness of lifts along a square-zero extension (Lemma 00UO), so `R → S` is unramified exactly
when it is formally unramified and of finite type, and G-unramified exactly when it is formally
unramified and of finite presentation (Lemma 00UU).

## Main definitions

* `Algebra.GUnramified`: item (2), `R → S` of finite presentation with `Ω_{S/R} = 0`.

## Implementation notes

*Only item (2) is new; the other three are already available.* Item (1) is Mathlib's
`Algebra.Unramified`, which is `Algebra.FormallyUnramified` together with `Algebra.FiniteType` and
already carries the tag of this definition. Item (3), the source's `∃ g ∉ q` with `R → S_g`
unramified, is `∃ g ∉ q, Algebra.Unramified R (Localization.Away g)`, and it is what Mathlib's
`Algebra.IsUnramifiedAt R q` (formal unramifiedness of `S_q`) amounts to for an algebra of finite
type: `Algebra.exists_unramified_of_isUnramifiedAt` produces the `g` from the localization at `q`,
and `Algebra.basicOpen_subset_unramifiedLocus_iff` returns from a basic open to the prime. Item
(4) is then `∃ g ∉ q, Algebra.GUnramified R (Localization.Away g)`, written directly from the
class defined here; it is given no name of its own, as Lemma 07BU writes smoothness at a prime as
`∃ g ∉ q, Algebra.Smooth R (Localization.Away g)`.

*`Ω_{S/R} = 0` is spelled `Algebra.FormallyUnramified`.* That is Lemma 00UO,
`Algebra.formallyUnramified_iff : FormallyUnramified R S ↔ Subsingleton Ω[S⁄R]`, and it is the
shape Mathlib gives `Algebra.Unramified`, `Algebra.Smooth` and `Algebra.Etale`, all of which pair
a `Formally*` hypothesis with a finiteness one. Taking the formal condition as the field makes
`Algebra.GUnramified R S → Algebra.Unramified R S` the source's remark that a G-unramified map is
unramified, provable from the two fields and `Algebra.FiniteType.of_finitePresentation` alone.

*A `class`, with its fields registered as instances.* As for `Algebra.Smooth` and
`Algebra.Etale`, the fields are populated by `infer_instance` at construction time, and
`Algebra.GUnramified.formallyUnramified` and `Algebra.GUnramified.finitePresentation` are
instances, so a `GUnramified R S` in the context is found wherever `Algebra.FormallyUnramified
R S` or `Algebra.FinitePresentation R S` is wanted, without unfolding the definition.

*Stated for an `R`-algebra, not for a bare ring map.* This is how Mathlib states the neighbouring
notions; for `f : R →+* S` the definition is `Algebra.GUnramified R S` at `f.toAlgebra`, which is
how `RingHom.FormallyUnramified` is built from `Algebra.FormallyUnramified`.

Faithfulness to [Stacks 00UT]. (1) No hypothesis is idle: the two fields are the source's two
conjuncts for item (2), and there is nothing else — no finiteness or flatness of `R`, no
Noetherian assumption, and no hypothesis on `S` beyond the algebra structure, which is the ring
map of the source. (2) The scalars and the base are the source's: both finite presentation and the
vanishing of the differentials are over `R`, the base of the given map, not over a localization of
`R` and not over `S`; in item (4) the differentials are those of `S_g` over that same `R`. (3) The
canonical maps are pinned: the algebra structure `Algebra R S` *is* the map `R → S`, and in items
(3) and (4) `S_g` is pinned as `Localization.Away g` with its canonical map from `S`, so the
localization is not an abstract algebra asserted to exist. (4) The instantiation is not
degenerate: `R → R` is G-unramified for every commutative ring `R`, so is `R → R_f` for `f : R`
(`Algebra.FormallyUnramified.of_isLocalization` and `IsLocalization.Away.finitePresentation`), and
so is `ℚ → ℚ[x]/(x² - 2)`; while `ℚ → ℚ[x]` is of finite presentation and is not G-unramified, its
differentials being free of rank one, and `𝔽_p(t) → 𝔽_p(t)[x]/(x^p - t)` is a finite field
extension that is not, so the class is neither empty nor everything.

## References

* [Stacks 00UT](https://stacks.math.columbia.edu/tag/00UT), Definition 10.151.1, in Section
  10.151 "Unramified ring maps" (Section 00US), where the G-unramified notion is attributed to
  EGA and the unramified one to [Henselian]. Lemma 00UU identifies the two definitions with
  formal unramifiedness plus the corresponding finiteness condition; Lemma 00UO is the vanishing
  of `Ω_{S/R}`.
-/

@[expose] public section

/-- A ring map `R → S` is **G-unramified** if it is of finite presentation and `Ω_{S/R} = 0`
(Stacks 00UT (2)); the vanishing of the differentials is recorded as formal unramifiedness, which
is the same condition by Lemma 00UO. This is the notion of EGA; dropping finite presentation to
finite type gives `Algebra.Unramified`, item (1) of the same definition. -/
@[stacks 00UT "Item (2). `Ω_{S/R} = 0` is `Algebra.FormallyUnramified` (Lemma 00UO,
`Algebra.formallyUnramified_iff`), as in Mathlib's `Algebra.Unramified`, `Algebra.Smooth` and
`Algebra.Etale`. Item (1) is `Algebra.Unramified`, item (3) is
`∃ g ∉ q, Algebra.Unramified R (Localization.Away g)` and item (4) is
`∃ g ∉ q, Algebra.GUnramified R (Localization.Away g)`. See the module docstring."]
public class Algebra.GUnramified (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] :
    Prop where
  /-- A G-unramified algebra has vanishing module of differentials, i.e. it is formally
  unramified. -/
  formallyUnramified : Algebra.FormallyUnramified R S := by infer_instance
  /-- A G-unramified algebra is of finite presentation. -/
  finitePresentation : Algebra.FinitePresentation R S := by infer_instance

attribute [instance] Algebra.GUnramified.formallyUnramified
  Algebra.GUnramified.finitePresentation

end
