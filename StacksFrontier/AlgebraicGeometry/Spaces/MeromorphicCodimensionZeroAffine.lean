module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Meromorphic functions on an affine chart as a product over the codimension-zero points

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a), (b) and (c) of
Stacks 0ENA, let `P` be a presentation of its schematic locus at the codimension-zero points and
let `U` be an *affine* étale chart of `X`.  This file proves that the comparison

`𝒦_X(U) ⟶ ∏_{η ∈ X⁰} (j_{η, *}𝒪_{X, η})(U)`

is bijective.  Both sides are localizations of `𝒪_X(U)` at its nonzerodivisors: the left-hand
side by Stacks 0EN6 part (2), and the right-hand side because the base-changed charts
`U ×_X Spec(𝒪_{X, η})` are discrete schemes whose points are exactly the codimension-zero points
of `U`, each contributing its local ring.

## Main results

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.mem_range_genericPointProjection_iff`: the
  image of `U ×_X Spec(𝒪_{X, η}) ⟶ U` is the set of points of `U` lying over `η`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.bijective_sigma_genericPointProjection`:
  the points of the base-changed charts, taken together over all `η ∈ X⁰`, are exactly the
  generic points of `U`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.isLocalization_pi_genericPointSections`:
  the product of the sections of the direct images over `U` is the total ring of fractions of
  `𝒪_X(U)`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.bijective_pi_genericPointComparison_app`:
  the comparison is bijective on an affine chart.

## Implementation notes

The identification of the image of the projection uses that every point of `Spec(𝒪_{X, η})` maps
to `η` and the cartesian square defining the base change, in the direction of Stacks 03H4 for
the surjectivity.  The points of `U` are compared with the points of the scheme underlying it
through `AlgebraicGeometry.Space.pointsEquivScheme`.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0)

/-! ### The image of the projection from the base-changed chart -/

/-- **The image of the projection `U ×_X Spec(𝒪_{X, η}) ⟶ U` is the set of points of `U` lying
over `η`.** -/
theorem mem_range_genericPointProjection_iff (U : SmallEtale B S hS X.1)
    (y : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U)) ↔
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y) = x := by
  have hsq := (P.representable_genericMorphism hx).isPullback U.1.hom
  have key : ∀ w, pointsMap B S hS _ (yoneda.map (P.genericPointProjection hx U)) w =
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm
        ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U)
          (pointsToScheme B S hS
            ((SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj
              (P.genericPointChart hx U)) w)) := fun w =>
    (Equiv.eq_symm_apply _).mpr (pointsToScheme_pointsMap_yoneda B S hS _ w)
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := (pointsEquivScheme B S hS _).surjective z
    have hw' : yoneda.map (P.genericPointProjection hx U) ≫ U.1.hom =
        (P.representable_genericMorphism hx).fst U.1.hom ≫
          (P.genericMorphism hx X.2).hom := hsq.w.symm
    erw [← key, ← pointsMap_comp_apply, hw']
    exact (pointsMap_comp_apply B S hS _ _ w).trans (P.pointsMap_fromSpecStalk hx X.2 _)
  · intro hy
    have : IsLocalRing (P.stalk hx) :=
      inferInstanceAs (IsLocalRing (P.schemeObj.presheaf.stalk (P.schemePointAt hx)))
    set W : AlgebraicSpaces B S hS :=
      ⟨yoneda.obj ((P.representable_genericMorphism hx).pullback U.1.hom),
        isAlgebraicSpace_yoneda B S hS _⟩
    set Uspace : AlgebraicSpaces B S hS :=
      ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U), isAlgebraicSpace_yoneda B S hS _⟩
    have hsq' : IsPullback
        (ObjectProperty.homMk ((P.representable_genericMorphism hx).fst U.1.hom) :
          W ⟶ P.specStalkSpace hx)
        (ObjectProperty.homMk (yoneda.map (P.genericPointProjection hx U)) : W ⟶ Uspace)
        (P.genericMorphism hx X.2) (ObjectProperty.homMk U.1.hom : Uspace ⟶ X) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq
    obtain ⟨w, -, hw2⟩ := exists_point_of_isPullback B S hS hsq'
      ((pointsEquivScheme B S hS (P.specStalk hx)).symm
        (IsLocalRing.closedPoint (P.stalk hx)))
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y)
      ((P.pointsMap_fromSpecStalk hx X.2 _).trans hy.symm)
    refine ⟨pointsToScheme B S hS ((P.representable_genericMorphism hx).pullback U.1.hom) w, ?_⟩
    exact (pointsEquivScheme B S hS _).symm.injective ((key w).symm.trans hw2)

/-! ### The points of the base-changed charts are the generic points of the chart -/

/-- The scheme underlying the base change of an étale chart `U` of `X` along `j_η` is a discrete
scheme: it is a flat preimmersion over `U`, its local rings have dimension zero, and `U` has
finitely many generic points. -/
theorem discreteTopology_genericPointChart
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    DiscreteTopology ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hx).1).obj (P.genericPointChart hx U))) := by
  have := P.flat_genericPointProjection hx U
  have := P.isPreimmersion_genericPointProjection hx U
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  exact (finite_and_discreteTopology_of_flat_isPreimmersion
    ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection hx U))
    (P.ringKrullDim_stalk_specStalkChart hx X.2 (P.genericPointChart hx U))
    (genericPoints.finite
      (finite_irreducibleComponents_chart_of_hasLocallyFiniteIrreducibleComponents
        B S hS hfin U.1.left U.1.hom (isEtale_of_presheaf_etale B S hS U.2)))).2

/-- **`X⁰`**, the set of points of codimension `0` of an algebraic space, as a type. -/
abbrev CodimensionZeroPoints (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Type (u + 1) :=
  {y : points B S hS F // localRingDimension B S hS y = 0}

/-- **The projection from the base-changed chart lands in the generic points of the chart**: it is
a flat preimmersion and the local rings of its source have dimension zero. -/
theorem mem_genericPoints_genericPointProjection (U : SmallEtale B S hS X.1)
    (y : points B S hS X.1) (hy : localRingDimension B S hS y = 0)
    (z : (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace hy).1).obj (P.genericPointChart hy U))) :
    (BigFppfOver.toScheme B S hS).map (P.genericPointProjection hy U) z ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj U)) := by
  have := P.flat_genericPointProjection hy U
  have := P.isPreimmersion_genericPointProjection hy U
  exact mem_genericPoints_of_flat_isPreimmersion _
    (P.ringKrullDim_stalk_specStalkChart hy X.2 (P.genericPointChart hy U)) z

/-- **The points of the base-changed charts are exactly the generic points of the chart.**  Over
each `η ∈ X⁰` the points of `U ×_X Spec(𝒪_{X, η})` are the points of `U` lying over `η`, and every
generic point of `U` lies over a codimension-zero point of `X`. -/
theorem bijective_sigma_genericPointProjection (U : SmallEtale B S hS X.1) :
    Function.Bijective (fun z : Σ η : CodimensionZeroPoints B S hS X.1,
          (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
            (P.specStalkSpace η.2).1).obj (P.genericPointChart η.2 U)) =>
      (⟨(BigFppfOver.toScheme B S hS).map (P.genericPointProjection z.1.2 U) z.2,
        P.mem_genericPoints_genericPointProjection U z.1.1 z.1.2 z.2⟩ :
          genericPoints ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS X.1).obj U)))) := by
  constructor
  · rintro ⟨η, z⟩ ⟨ξ, w⟩ h
    have hzw : (BigFppfOver.toScheme B S hS).map (P.genericPointProjection η.2 U) z =
        (BigFppfOver.toScheme B S hS).map (P.genericPointProjection ξ.2 U) w :=
      congrArg Subtype.val h
    have hη := (P.mem_range_genericPointProjection_iff η.2 U _).mp ⟨z, rfl⟩
    have hξ := (P.mem_range_genericPointProjection_iff ξ.2 U _).mp ⟨w, rfl⟩
    have he : η = ξ := Subtype.ext (hη.symm.trans ((congrArg
      (fun y => pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y))
      hzw).trans hξ))
    subst he
    have := P.isPreimmersion_genericPointProjection η.2 U
    obtain rfl : z = w :=
      ((BigFppfOver.toScheme B S hS).map
        (P.genericPointProjection η.2 U)).isEmbedding.injective hzw
    rfl
  · intro y
    have hy : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y.1)) = 0 := by
      refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS X.2 _).mpr
        ⟨(SmallEtale.toOver B S hS X.1).obj U, U.1.hom, y.1,
          isEtale_of_presheaf_etale B S hS U.2, ?_, y.2⟩
      have h := chartPoint_pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y.1)
      have hps : pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm y.1) = y.1 :=
        (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).apply_symm_apply y.1
      rwa [hps] at h
    obtain ⟨z, hz⟩ := (P.mem_range_genericPointProjection_iff hy U y.1).mpr rfl
    exact ⟨⟨⟨_, hy⟩, z⟩, Subtype.ext hz⟩

/-! ### The product of the sections over an affine chart -/

/-- **The product over `X⁰` of the sections of the direct images `j_{η, *}𝒪_{X, η}` over an affine
étale chart `U` is the total ring of fractions of `𝒪_X(U)`.**  Each factor is the ring of global
sections of the discrete scheme `U ×_X Spec(𝒪_{X, η})`, hence the product of the local rings of
`U` at the points over `η`; taken together these are the local rings at all the generic points of
`U`, whose product is the total ring of fractions by Stacks 02LX. -/
theorem isLocalization_pi_genericPointSections
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    letI : ∀ η : CodimensionZeroPoints B S hS X.1,
        Algebra ((structurePresheaf B S hS X.1).obj (op U))
          ((P.genericPointStructureSheaf η.2).obj.obj (op U)) := fun η =>
      ((P.genericPointSharp η.2).hom.app (op U)).hom.toAlgebra
    IsLocalization ((structurePresheaf B S hS X.1).obj (op U))⁰
      (∀ η : CodimensionZeroPoints B S hS X.1,
        (P.genericPointStructureSheaf η.2).obj.obj (op U)) := by
  have := hU
  have (η : CodimensionZeroPoints B S hS X.1) :
      Flat ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection η.2 U)) :=
    P.flat_genericPointProjection η.2 U
  have (η : CodimensionZeroPoints B S hS X.1) :
      IsPreimmersion ((BigFppfOver.toScheme B S hS).map (P.genericPointProjection η.2 U)) :=
    P.isPreimmersion_genericPointProjection η.2 U
  have (η : CodimensionZeroPoints B S hS X.1) : DiscreteTopology
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS
        (P.specStalkSpace η.2).1).obj (P.genericPointChart η.2 U))) :=
    P.discreteTopology_genericPointChart η.2 hfin U hU
  exact isLocalization_pi_sections_of_genericPoints (smallEtaleScheme B S hS X.1 U)
    (fun η : CodimensionZeroPoints B S hS X.1 => (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (P.specStalkSpace η.2).1).obj (P.genericPointChart η.2 U)))
    (fun η => (BigFppfOver.toScheme B S hS).map (P.genericPointProjection η.2 U))
    (fun η z => P.mem_genericPoints_genericPointProjection U η.1 η.2 z)
    (P.bijective_sigma_genericPointProjection U)
    (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa U)
    (fun W hW => finite_irreducibleComponents_chartScheme B S hS hfin U W hW)

/-! ### The comparison is bijective on an affine chart -/

/-- **The comparison `𝒦_X(U) ⟶ ∏_{η ∈ X⁰} (j_{η, *}𝒪_{X, η})(U)` is bijective over an affine
étale chart `U`.**  Both sides are localizations of `𝒪_X(U)` at its nonzerodivisors — the source
by Stacks 0EN6 part (2), the target by
`AlgebraicGeometry.Space.CodimensionZeroPresentation.isLocalization_pi_genericPointSections` —
and the comparison is a map of `𝒪_X(U)`-algebras between them. -/
theorem bijective_pi_genericPointComparison_app
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (U : SmallEtale B S hS X.1)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    Function.Bijective (fun s : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) =>
      fun η : CodimensionZeroPoints B S hS X.1 =>
        ((P.genericPointComparison η.2).hom.app (op U)).hom s) := by
  let : Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  have : IsLocalization ((structurePresheaf B S hS X.1).obj (op U))⁰
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin U hU
  let : ∀ η : CodimensionZeroPoints B S hS X.1,
      Algebra ((structurePresheaf B S hS X.1).obj (op U))
        ((P.genericPointStructureSheaf η.2).obj.obj (op U)) := fun η =>
    ((P.genericPointSharp η.2).hom.app (op U)).hom.toAlgebra
  have : IsLocalization ((structurePresheaf B S hS X.1).obj (op U))⁰
      (∀ η : CodimensionZeroPoints B S hS X.1,
        (P.genericPointStructureSheaf η.2).obj.obj (op U)) :=
    P.isLocalization_pi_genericPointSections hwa hfin U hU
  exact IsLocalization.bijective ((structurePresheaf B S hS X.1).obj (op U))⁰
    (RingHom.pi fun η : CodimensionZeroPoints B S hS X.1 =>
      ((P.genericPointComparison η.2).hom.app (op U)).hom)
    (by
      refine RingHom.ext fun r => funext fun η => ?_
      change ((P.genericPointComparison η.2).hom.app (op U)).hom
          (((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom r) = _
      rw [P.genericPointComparison_app_toMeromorphicFunctionSheaf η.2 U r]
      rfl)

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
