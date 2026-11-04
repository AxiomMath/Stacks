module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorNormalDiscreteValuationRing

/-!
# Order of vanishing zero at a prime divisor of a normal space means a unit

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S` which is
normal, let `Z ⊆ X` be a prime divisor with generic point `ξ`, and let `s` be a meromorphic
section of an `𝒪_X`-module read through a choice of generator at `ξ`. If `ord_{Z, ℒ}(s) = 0`
then the ratio `s / s_ξ` is the image of a **unit** of `𝒪^h_{X, ξ}`.

This is the exact converse of
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit`, and it is where normality
is used: the order of vanishing is a difference of two lengths, and on a ring that is merely
reduced, Noetherian and one-dimensional two different elements can have quotients of equal
length without being associated, so a vanishing difference says nothing. On a normal `X` the
ring `𝒪^h_{X, ξ}` is a discrete valuation ring
(`AlgebraicGeometry.Space.PrimeDivisor.exists_isDiscreteValuationRing_genericHenselianLocalRing`),
the order of vanishing is its valuation, and valuation zero is exactly unit-ness.

This is the step at a codimension-one point in the proof of Stacks 0EPX: there the source reads
`0 = ord_{Z, ℒ}(t) = ord_{𝒪^h_{X, ξ}}(f_ξ)` and concludes that `f_ξ` is a unit of the discrete
valuation ring `𝒪^h_{X, ξ}`.

## Main results

* `Ring.exists_isUnit_eq_algebraMap_of_ordTotalFracInt_eq_zero`: on a discrete valuation ring, a
  unit of the field of fractions whose order of vanishing is zero is the image of a unit of the
  ring.
* `AlgebraicGeometry.Space.exists_isUnit_of_orderOfVanishingSection_eq_zero`: the converse of
  `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit`, for an arbitrary choice
  of generator at `ξ`.
* `Space.PrimeDivisor.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero`:
  the same at the constructed ratio `s / s_ξ` of Stacks 0EPR and a regular meromorphic section,
  in the shape `AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart` uses.

## Implementation notes

The ring-theoretic statement is phrased with `Ring.ordTotalFrac`, the order of vanishing on a
*total* ring of fractions which the algebraic space development uses. On a discrete valuation ring
the total ring of fractions is the field of fractions and `Ring.ordTotalFrac` is Mathlib's
`Ring.ordFrac` on the nose, which is what lets `Ring.mker_ordFrac_eq_isUnitSubmonoid` close it.

Neither the domain structure nor the discrete valuation ring structure on `𝒪^h_{X, ξ}` is an
instance — on a merely integral `X` the ring need not be a domain — so both are obtained from
the hypotheses and installed locally. The three instance arguments on the henselian local rings,
nontriviality, Noetherianity and the dimension bound, are the ones
`AlgebraicGeometry.Space.orderOfVanishingSection` itself carries; they hold on such an `X` and
`AlgebraicGeometry.Space.PrimeDivisor.nontrivial_genericHenselianLocalRing` and its two
companions discharge them.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

/-! ### The ring-theoretic statement -/

namespace Ring

/-- **On a discrete valuation ring, order of vanishing zero means a unit.** A unit `x` of the
field of fractions with `ord(x) = 0` is the image of a unit of the ring: the order of vanishing
on a field of fractions is the valuation, read multiplicatively, and the kernel of that
homomorphism is the image of the units, which is
`Ring.mker_ordFrac_eq_isUnitSubmonoid`.

The hypothesis is stated with `Ring.ordTotalFracInt`, the integer-valued order of vanishing on a
*total* ring of fractions, because that is the one the order of vanishing along a prime divisor
of an algebraic space is defined by; on a domain the two agree. -/
theorem exists_isUnit_eq_algebraMap_of_ordTotalFracInt_eq_zero (R : Type*) [CommRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (x : K) (hx : IsUnit x)
    (h : ordTotalFracInt R x hx = 0) :
    ∃ r : R, IsUnit r ∧ algebraMap R K r = x := by
  have hne : ordTotalFrac R (K := K) x ≠ 0 := (hx.map (ordTotalFrac R (K := K))).ne_zero
  have hzero : Multiplicative.toAdd (WithZero.unzero hne) = 0 := h
  have hunz : WithZero.unzero hne = 1 := by
    simpa using congrArg (Multiplicative.ofAdd (α := ℤ)) hzero
  have hfrac : ordFrac R (K := K) x = 1 := by
    change ordTotalFrac R (K := K) x = 1
    rw [← WithZero.coe_unzero hne, hunz, WithZero.coe_one]
  have hmem : x ∈ (IsUnit.submonoid R).map (algebraMap R K) := by
    rw [← mker_ordFrac_eq_isUnitSubmonoid (R := R) (K := K)]
    exact hfrac
  obtain ⟨r, hr, hre⟩ := hmem
  exact ⟨r, hr, hre⟩

end Ring

/-! ### The statement along a prime divisor -/

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hNormal : IsNormal B S hS X)
    [∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    [∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    [∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    (Z : PrimeDivisor B S hS X)

include hInt hN hNormal in
/-- **On a normal space, order of vanishing zero along a prime divisor means a unit.** If the
order of vanishing of a meromorphic section `s` of an `𝒪_X`-module along a prime divisor `Z`,
taken through a choice of generator `s_ξ` at the generic point of `Z`, is zero, then the ratio
`s / s_ξ` is the image of a unit of `𝒪^h_{X, ξ}`.

This is the converse of `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit`,
and normality of `X` is what makes it true: the order of vanishing is a difference of lengths,
and that difference vanishing forces the ratio into the units of the local ring only because
`𝒪^h_{X, ξ}` is a discrete valuation ring, by
`AlgebraicGeometry.Space.PrimeDivisor.exists_isDiscreteValuationRing_genericHenselianLocalRing`. -/
theorem exists_isUnit_of_orderOfVanishingSection_eq_zero (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (ratio : LocalRatio.{u, u} B S hS hX hdec Z L)
    (h : orderOfVanishingSection.{u, u} B S hS hX hdec Z L s ratio = 0) :
    ∃ v : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit v ∧
      (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec) v := by
  obtain ⟨hdom, hdvr⟩ :=
    Z.exists_isDiscreteValuationRing_genericHenselianLocalRing B S hS hX hdec hInt hN hNormal
  let : IsDomain ↥(Z.genericHenselianLocalRing B S hS hX hdec) := hdom
  let : IsDiscreteValuationRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) := hdvr
  obtain ⟨v, hv, hve⟩ := Ring.exists_isUnit_eq_algebraMap_of_ordTotalFracInt_eq_zero
    ↥(Z.genericHenselianLocalRing B S hS hX hdec)
    (K := Z.genericTotalFractionRing B S hS hX hdec)
    (ratio s : Z.genericTotalFractionRing B S hS hX hdec) (ratio s).isUnit h
  exact ⟨v, hv, hve.symm⟩

include hNormal in
/-- **The constructed ratio `s / s_ξ` of a regular meromorphic section with vanishing order of
vanishing is the image of a unit of `𝒪^h_{X, ξ}`**, on a normal `X`.

This is
`AlgebraicGeometry.Space.exists_isUnit_of_orderOfVanishingSection_eq_zero` at the ratio family
Stacks 0EPR constructs, whose value at a regular meromorphic section is the ratio
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio` by
`AlgebraicGeometry.Space.PrimeDivisor.coe_canonicalLocalRatio`. The conclusion is in the shape
of `AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart`, which is the other input
that the construction of Stacks 0EPW takes at the canonical choices. -/
theorem PrimeDivisor.exists_isUnit_canonicalGenericRatio_of_orderOfVanishingSection_eq_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (h : orderOfVanishingSection.{u, u} B S hS hX hdec Z L s
      (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) = 0) :
    ∃ v : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit v ∧
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s =
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec) v := by
  obtain ⟨v, hv, hve⟩ := exists_isUnit_of_orderOfVanishingSection_eq_zero B S hS hX hdec hInt hN
    hNormal Z L s (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hN) h
  exact ⟨v, hv, ((Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hN s hs).symm.trans hve)⟩

end AlgebraicGeometry.Space

end
