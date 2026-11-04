module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MinimalPrimesOfAffineOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicStalks
public import StacksFrontier.RingTheory.Etale.TotalFractionRing

/-!
# Meromorphic functions on the affine étale charts of an algebraic space

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6:

* (a) every weakly associated point of `X` is a point of codimension `0`, and
* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many irreducible
  components, the condition of Stacks 0BB1.

Over an *affine* étale chart `U` the regular sections of `𝒪_X` are the nonzerodivisors of
`𝒪_X(U)` (Stacks 0EN4), so the presheaf `U ↦ 𝒮_X(U)⁻¹ 𝒪_X(U)` whose sheafification is the
sheaf of meromorphic functions `𝒦_X` takes the value `Q(𝒪_X(U))`, the total ring of fractions.

For a morphism `V ⟶ U` of affine étale charts, writing `A = 𝒪_X(U)` and `B = 𝒪_X(V)`, the
canonical map

`Q(A) ⊗_A B ⟶ Q(B)`

is an isomorphism, stated as: a total ring of fractions of `B` is already the localization of
`B` at the image of the regular sections over `U`.

## Main results

* `AlgebraicGeometry.Space.regularSections_eq_nonZeroDivisors`: Stacks 0EN4 read as an equality
  of multiplicative subsets over an affine chart.
* `AlgebraicGeometry.Space.schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints`:
  hypothesis (a) read on an étale scheme chart, and
  `AlgebraicGeometry.Space.finite_irreducibleComponents_chartScheme`: hypothesis (b).
* `AlgebraicGeometry.Space.finite_minimalPrimes_chartSections` and
  `AlgebraicGeometry.Space.exists_mem_minimalPrimes_chartSections_of_notMem_nonZeroDivisors`:
  the two hypotheses read on the ring of sections over an affine chart.
* `AlgebraicGeometry.Space.algebraEtale_chartSections`: for a morphism of affine étale charts
  the ring of sections over the source is an étale algebra over the ring of sections over the
  target.
* `AlgebraicGeometry.Space.isLocalization_algebraMapSubmonoid_regularSections`: **the comparison
  `Q(A) ⊗_A B = Q(B)`** for a morphism of affine étale charts.
* `AlgebraicGeometry.Space.isFractionRing_localization_regularSections`: on an affine chart the
  sectionwise localization at the regular sections is the total ring of fractions of the ring of
  sections.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EN4](https://stacks.math.columbia.edu/tag/0EN4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Regular sections over an affine chart -/

/-- **Stacks 0EN4, as an equality of multiplicative subsets.** Over an affine étale chart of an
algebraic space the regular sections of the structure sheaf are exactly the nonzerodivisors of
the ring of sections. -/
theorem regularSections_eq_nonZeroDivisors (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    regularSections B S hS F U = ((structurePresheaf B S hS F).obj (op U))⁰ :=
  Submonoid.ext fun s => isRegularSection_iff_mem_nonZeroDivisors B S hS F U hU s

/-! ### The hypotheses of Stacks 0EN6 read on a chart -/

/-- **Hypothesis (a) of Stacks 0EN6 read on an étale scheme chart.** If every weakly associated
point of `X` is a point of codimension `0`, then every weakly associated point of an étale
scheme chart of `X` is a generic point of an irreducible component of that chart. -/
theorem schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints
    (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (U : SmallEtale B S hS X.1) :
    Stacks.Divisors.schemeWeaklyAssociatedPoints (chartScheme U) ⊆
      genericPoints (chartScheme U) := by
  intro y hy
  have hEt : IsEtale B S hS U.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).mpr U.property
  have hcp : ChartPoint B S hS U.obj.left U.obj.hom y (chartSchemeToPoints B S hS X.1 U y) :=
    ⟨canonicalSiteFieldPoint B S hS U.obj.left y,
      canonicalSiteFieldPoint_point B S hS U.obj.left y, rfl⟩
  exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS X.2 _).mp
    (hwa _ (mem_weaklyAssociatedPointsOfSpace_chartSchemeToPoints B S hS X U y hy))
    U.obj.left U.obj.hom y hEt hcp

/-- **Hypothesis (b) of Stacks 0EN6 read on an étale scheme chart.** Every quasi-compact open of
an étale scheme chart of a space satisfying the condition of Stacks 0BB1 has finitely many
irreducible components. -/
theorem finite_irreducibleComponents_chartScheme {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) (U : SmallEtale B S hS F)
    (W : (chartScheme U).Opens) (hW : IsCompact (W : Set (chartScheme U))) :
    (irreducibleComponents W).Finite :=
  hfin U.obj.left U.obj.hom
    ((isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).mpr U.property) W hW

/-! ### The hypotheses read on the ring of sections over an affine chart -/

/-- **Hypothesis (b) of Stacks 0EN6 on the ring of sections of an affine chart.** The ring of
sections of the structure sheaf over an affine étale chart has finitely many minimal primes. -/
theorem finite_minimalPrimes_chartSections {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) (U : SmallEtale B S hS F)
    (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    (minimalPrimes ((structurePresheaf B S hS F).obj (op U))).Finite :=
  have := hU
  finite_minimalPrimes_appTop (smallEtaleScheme B S hS F U)
    (finite_irreducibleComponents_chartScheme B S hS hfin U)

/-- **Hypothesis (a) of Stacks 0EN6 on the ring of sections of an affine chart.** Every
zerodivisor of the ring of sections of the structure sheaf over an affine étale chart lies in a
minimal prime of that ring. -/
theorem exists_mem_minimalPrimes_chartSections_of_notMem_nonZeroDivisors
    (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (a : (structurePresheaf B S hS X.1).obj (op U))
    (ha : a ∉ ((structurePresheaf B S hS X.1).obj (op U))⁰) :
    ∃ q ∈ minimalPrimes ((structurePresheaf B S hS X.1).obj (op U)), a ∈ q :=
  have := hU
  exists_mem_minimalPrimes_of_notMem_nonZeroDivisors (X := smallEtaleScheme B S hS X.1 U) ⊤
    (isAffineOpen_top _) (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints
      B S hS X hwa U) a ha

/-! ### The comparison `Q(A) ⊗_A B = Q(B)` on affine charts -/

/-- **The ring of sections over an affine chart is étale over the ring of sections over an
affine chart below it.** -/
theorem algebraEtale_chartSections {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine (smallEtaleScheme B S hS F U))
    (hV : IsAffine (smallEtaleScheme B S hS F V)) :
    letI : Algebra ((structurePresheaf B S hS F).obj (op U))
        ((structurePresheaf B S hS F).obj (op V)) :=
      ((structurePresheaf B S hS F).map f.op).hom.toAlgebra
    Algebra.Etale ((structurePresheaf B S hS F).obj (op U))
      ((structurePresheaf B S hS F).obj (op V)) :=
  have : IsAffine
      (unop ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op.obj (op U))) := hU
  have : IsAffine
      (unop ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op.obj (op V))) := hV
  RingHom.Etale.toAlgebra
    (HasRingHomProperty.appTop (P := @Etale) _ (etale_toScheme_toOver_map B S hS F f))

/-- **The comparison `Q(A) ⊗_A B = Q(B)` of the proof of Stacks 0EN6.** Let `X` be an algebraic
space satisfying hypotheses (a) and (b) of Stacks 0EN6, let `V ⟶ U` be a morphism of affine
étale charts of `X`, and write `A = 𝒪_X(U)` and `B = 𝒪_X(V)`. Then a total ring of fractions of
`B` — equivalently, by Stacks 0EN4, a localization of `B` at the regular sections over `V` — is
already the localization of `B` at the image of the regular sections over `U`. -/
theorem isLocalization_algebraMapSubmonoid_regularSections (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (hV : IsAffine (smallEtaleScheme B S hS X.1 V))
    (T : Type u) [CommRing T] [Algebra ((structurePresheaf B S hS X.1).obj (op V)) T]
    [IsLocalization (regularSections B S hS X.1 V) T] :
    letI : Algebra ((structurePresheaf B S hS X.1).obj (op U))
        ((structurePresheaf B S hS X.1).obj (op V)) := chartAlgebra (hF := X.2) f
    IsLocalization (Algebra.algebraMapSubmonoid
      ((structurePresheaf B S hS X.1).obj (op V)) (regularSections B S hS X.1 U)) T := by
  let _ : Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((structurePresheaf B S hS X.1).obj (op V)) := chartAlgebra (hF := X.2) f
  have _ : Algebra.Etale ((structurePresheaf B S hS X.1).obj (op U))
      ((structurePresheaf B S hS X.1).obj (op V)) :=
    algebraEtale_chartSections B S hS f hU hV
  have hT : IsFractionRing ((structurePresheaf B S hS X.1).obj (op V)) T := by
    rw [IsFractionRing, ← regularSections_eq_nonZeroDivisors B S hS X.1 V hV]
    infer_instance
  have hmain := IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_etale
    (A := (structurePresheaf B S hS X.1).obj (op U))
    (B := (structurePresheaf B S hS X.1).obj (op V))
    (finite_minimalPrimes_chartSections B S hS hfin U hU)
    (exists_mem_minimalPrimes_chartSections_of_notMem_nonZeroDivisors B S hS X hwa U hU) T
  rwa [regularSections_eq_nonZeroDivisors B S hS X.1 U hU]

/-- **On an affine chart the sectionwise localization at the regular sections is the total ring
of fractions.** Over an affine étale chart `U`, the localization of the ring of sections
`𝒪_X(U)` at the regular sections is a total ring of fractions of `𝒪_X(U)`. -/
theorem isFractionRing_localization_regularSections
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS F)
    (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    IsFractionRing ((structurePresheaf B S hS F).obj (op U))
      (Localization (regularSections B S hS F U)) := by
  rw [IsFractionRing, ← regularSections_eq_nonZeroDivisors B S hS F U hU]
  infer_instance

/-- The value of the presheaf of sectionwise localizations at an étale chart is the
localization of the ring of sections there at the regular sections. -/
theorem regularLocalizationPresheaf_obj (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1) :
    ((regularLocalizationPresheaf B S hS X).obj (op U) : Type u) =
      Localization (regularSections B S hS X.1 U) := rfl

end AlgebraicGeometry.Space

end
