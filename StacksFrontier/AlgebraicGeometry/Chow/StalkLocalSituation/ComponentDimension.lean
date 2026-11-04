module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension

/-!
# The component through a point of delta-dimension `k` has coheight one there

Let `ξ` be a point of delta-dimension `k` in the closed nowhere dense exceptional locus of a
scheme `X` of delta-dimension at most `k + 1` over the base of a Chow situation, so that
`𝒪_{X, ξ}` has Krull dimension one
(`Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one_of_mem_isNowhereDense`). Each
minimal prime `q` of `𝒪_{X, ξ}` indexes an irreducible component of `X` through `ξ`, and this
file records that `ξ` has coheight one on that component: equivalently `q` is not the maximal
ideal, equivalently `ringKrullDim (𝒪_{X, ξ} ⧸ q) = 1`.

That is the hypothesis `hco : coheight ξ = 1` of `Stacks.Chow.ord_eq_ringOrd_germ`, which
turns `Ring.ord` on the component's local ring into `AlgebraicGeometry.Scheme.ord`.

## Main results

* `Stacks.Chow.StalkLocalSituation.ne_maximalIdeal_of_mem_minimalPrimes`: in a local ring of
  Krull dimension at least one, no minimal prime is the maximal ideal.
* `Stacks.Chow.StalkLocalSituation.ringKrullDim_quotient_eq_one_of_mem_minimalPrimes`: in a
  local ring of Krull dimension one, the quotient by a minimal prime again has Krull dimension
  one.
* `Stacks.Chow.StalkLocalSituation.ringKrullDim_quotient_minimalPrime_stalk_eq_one`: the same at
  the stalk, with the geometric hypotheses of [Stacks, Tag 02SW] as input.
* `Stacks.Chow.StalkLocalSituation.coheight_eq_one_of_ringKrullDim_stalk`: a point whose local
  ring has Krull dimension one has coheight one. Read on the component, this is the hypothesis
  that `Stacks.Chow.ord_eq_ringOrd_germ` asks for.
* `Stacks.Chow.StalkLocalSituation.coheight_eq_one_of_mem_minimalPrimes_idealStalk`: the
  conclusion on the component itself — for a closed subscheme whose stalk ideal at the point is
  a minimal prime of `𝒪_{X, ξ}`, the point has coheight one *on that subscheme*. This is
  literally the hypothesis `hco` of `Stacks.Chow.ord_eq_ringOrd_germ` and
  `Stacks.Chow.ord_eq_componentMultiplicity`.
* `Stacks.Chow.StalkLocalSituation.coheight_eq_one_of_ringEquiv_quotient_minimalPrime`: the same
  across an arbitrary identification of a local ring with `𝒪_{X, ξ} ⧸ q`, for a consumer whose
  component is not presented as an `AlgebraicGeometry.Scheme.IdealSheafData`.

## Implementation notes

**The delta-function argument is not repeated here.** It would run: the component cut out by
`q` has delta-dimension `k + 1` while `δ(ξ) = k`, so `ξ` is not its generic point, so `q` is
not maximal. But the same conclusion is a consequence of `dim 𝒪_{X, ξ} = 1` alone and needs no
dimension function at all: a local ring of Krull dimension at least one has *some* strict
inclusion of primes, hence its maximal ideal is not minimal, hence no minimal prime is the
maximal ideal. The delta-function content was already spent in proving
`ringKrullDim_stalk_eq_one_of_mem_isNowhereDense`; this file is the ring-theoretic consequence,
and is stated for an arbitrary local ring so that it carries no geometry.

Upper and lower bounds on `ringKrullDim (R ⧸ q)` are taken separately with `le_antisymm` over
`Mathlib`'s `ringKrullDim_quotient`, which presents the quotient's spectrum as the zero locus of
`q`: the upper bound is the inclusion of that zero locus into the whole spectrum, the lower
bound is the single strict inclusion `q < 𝔪`. No rewriting inside a `⨆` is needed.

No affine open and no point is chosen anywhere: `q` is an arbitrary minimal prime, as it must be
for a consumer summing over the minimal primes of the stalk, and the component is an arbitrary
`AlgebraicGeometry.Scheme.IdealSheafData` rather than one built here.

Every hypothesis of the component statement is phrased at the point `Z.subschemeι z` rather than
at a separate `ξ` with an equation `Z.subschemeι z = ξ`. That is deliberate: `Z` and the type of
`q` both mention `ξ`, so such an equation cannot be substituted, and rewriting it underneath
`X.presheaf.stalk` is a dependent rewrite. Phrasing everything at `Z.subschemeι z` removes the
rewrite entirely, and the consumer discharges the minimality hypothesis at that same point with
`Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk`.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public section

open AlgebraicGeometry Topology

universe u

namespace Stacks.Chow.StalkLocalSituation

/-! ### A minimal prime of a local ring of positive dimension -/

/-- **In a local ring of Krull dimension at least one, no minimal prime is the maximal ideal.**
Positive dimension gives a strict inclusion `x < y` of primes; since `y` lies in the maximal
ideal, `x` is strictly inside it, so the maximal ideal is not minimal. -/
theorem ne_maximalIdeal_of_mem_minimalPrimes {R : Type*} [CommRing R] [IsLocalRing R]
    (hR : 1 ≤ ringKrullDim R) {q : Ideal R} (hq : q ∈ minimalPrimes R) :
    q ≠ IsLocalRing.maximalIdeal R := by
  intro hqm
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.mp hR
  have hqmin : Minimal Ideal.IsPrime q := (IsMinimalPrime.iff_minimal q).mp hq
  have hxtop : x < (⊤ : PrimeSpectrum R) := lt_of_lt_of_le hxy le_top
  have hxle : x.asIdeal ≤ q := hqm ▸ IsLocalRing.le_maximalIdeal x.isPrime.ne_top
  have hxlt : x.asIdeal < q :=
    lt_of_le_of_ne hxle fun h => hxtop.ne (PrimeSpectrum.ext (h.trans hqm))
  exact hxlt.not_ge (hqmin.2 x.isPrime hxlt.le)

/-- **In a local ring of Krull dimension one, the quotient by a minimal prime again has Krull
dimension one.** The primes above a minimal prime `q` form a subset of the whole spectrum, which
bounds the dimension by one, and `q < 𝔪` is a strict inclusion inside that subset, which bounds
it below by one. -/
theorem ringKrullDim_quotient_eq_one_of_mem_minimalPrimes {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {q : Ideal R} (hq : q ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ q) = 1 := by
  have hqp : q.IsPrime := hq.isPrime
  have hqm : q ≠ IsLocalRing.maximalIdeal R := ne_maximalIdeal_of_mem_minimalPrimes hR.ge hq
  rw [ringKrullDim_quotient]
  refine le_antisymm (le_trans (Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum.zeroLocus (q : Set R) => (p : PrimeSpectrum R))
    fun _ _ h => h) hR.le) ?_
  refine Order.one_le_krullDim_iff.mpr ⟨⟨⟨q, hqp⟩, ?_⟩, ⟨⊤, ?_⟩, ?_⟩
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr subset_rfl
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (SetLike.coe_subset_coe.mpr (IsLocalRing.le_maximalIdeal hqp.ne_top))
  · exact Subtype.mk_lt_mk.mpr
      (lt_of_le_of_ne le_top fun h => hqm (congrArg PrimeSpectrum.asIdeal h))

/-! ### At the stalk -/

/-- **The minimal primes of the local ring at a point of delta-dimension `k` are not its maximal
ideal.** Equivalently: `ξ` is not the generic point of any irreducible component of `X` through
it. -/
theorem ne_maximalIdeal_of_mem_minimalPrimes_stalk (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k)
    {q : Ideal (X.presheaf.stalk ξ)} (hq : q ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    q ≠ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
  ne_maximalIdeal_of_mem_minimalPrimes
    (ringKrullDim_stalk_eq_one_of_mem_isNowhereDense C f hdim hT hT' hξT hξ).ge hq

/-- **The component through a point of delta-dimension `k` has coheight one there**, in the form
`ringKrullDim (𝒪_{X, ξ} ⧸ q) = 1` for an arbitrary minimal prime `q` of `𝒪_{X, ξ}`. All the
hypotheses are the geometric ones of [Stacks, Tag 02SW]: the bound on the delta-dimension, the
closed nowhere dense locus containing `ξ`, and the value of the dimension function at `ξ`. -/
theorem ringKrullDim_quotient_minimalPrime_stalk_eq_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k)
    {q : Ideal (X.presheaf.stalk ξ)} (hq : q ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    ringKrullDim ((X.presheaf.stalk ξ) ⧸ q) = 1 :=
  ringKrullDim_quotient_eq_one_of_mem_minimalPrimes
    (ringKrullDim_stalk_eq_one_of_mem_isNowhereDense C f hdim hT hT' hξT hξ) hq

/-! ### Read as a coheight on the component -/

/-- **A point whose local ring has Krull dimension one has coheight one.** The converse direction
of [Stacks, Tag 02IZ] to the one used in
`Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one`; this is the form in which
`Stacks.Chow.ord_eq_ringOrd_germ` takes its hypothesis. -/
theorem coheight_eq_one_of_ringKrullDim_stalk {Y : Scheme.{u}} {z : Y}
    (h : ringKrullDim (Y.presheaf.stalk z) = 1) : Order.coheight z = 1 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_injective h

/-- **The point has coheight one on the component.** For a closed subscheme `Z` of `X` whose
stalk ideal at a point is a minimal prime of the local ring there, a point `z` of `Z` over it has
coheight one in `Z`: the local ring of `Z` at `z` is `𝒪_{X, ξ} ⧸ Z.stalk ξ`
(`Stacks.Chow.ringKrullDim_quotient_idealStalk_eq`), which has Krull dimension one.

This is the hypothesis `hco` of `Stacks.Chow.ord_eq_ringOrd_germ` and of
`Stacks.Chow.ord_eq_componentMultiplicity`, both of which read it on the component. -/
theorem coheight_eq_one_of_mem_minimalPrimes_idealStalk (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) (Z : X.IdealSheafData) (z : Z.subscheme)
    (hξT : Z.subschemeι z ∈ T)
    (hξ : relativeDimension C.dimensionFunction f (Z.subschemeι z) = k)
    (hq : IdealSheafData.stalk Z (Z.subschemeι z) ∈
      minimalPrimes (X.presheaf.stalk (Z.subschemeι z))) :
    Order.coheight z = 1 :=
  coheight_eq_one_of_ringKrullDim_stalk
    ((Stacks.Chow.ringKrullDim_quotient_idealStalk_eq Z z).symm.trans
      (ringKrullDim_quotient_minimalPrime_stalk_eq_one C f hdim hT hT' hξT hξ hq))

/-- **The coheight of `ξ` on the component indexed by a minimal prime `q` is one**, given an
identification of the component's local ring with `𝒪_{X, ξ} ⧸ q`. The identification is a
hypothesis rather than a construction: it is what the closed immersion of the component into
`X` provides at `ξ`, and it is produced on the Chow side, where the component is cut out by an
`AlgebraicGeometry.Scheme.IdealSheafData`. -/
theorem coheight_eq_one_of_ringEquiv_quotient_minimalPrime (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k)
    {q : Ideal (X.presheaf.stalk ξ)} (hq : q ∈ minimalPrimes (X.presheaf.stalk ξ))
    {Y : Scheme.{u}} {z : Y} (e : Y.presheaf.stalk z ≃+* ((X.presheaf.stalk ξ) ⧸ q)) :
    Order.coheight z = 1 :=
  coheight_eq_one_of_ringKrullDim_stalk
    ((ringKrullDim_eq_of_ringEquiv e).trans
      (ringKrullDim_quotient_minimalPrime_stalk_eq_one C f hdim hT hT' hξT hξ hq))

end Stacks.Chow.StalkLocalSituation

end
