module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkAffineHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceChartModels

/-!
# Flatness of geometric stalks of affine representables over rings of global functions

Let `g : V' ⟶ V` be a morphism of affine objects of the big fppf site over `S` and `ȳ'` a
geometric point of `yoneda.obj V'` with image `ȳ`. The map
`𝒪_{ȳ} ⊗_{Γ(V)} Γ(V') ⟶ 𝒪_{ȳ'}` is flat (Stacks 08HV, read through the identification of the
geometric stalks with strict henselizations of the local rings, Stacks 04KF), and every prime of
`Γ(V)` is the image of a prime of some geometric stalk.

## Main results

* `AlgebraicGeometry.Space.flat_baseChangeTensorRingMap_representedAffineStalk`
* `AlgebraicGeometry.Space.exists_mem_range_comap_representedAffineStalkRingHom`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Flat

variable {V' V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (g : V' ⟶ V)
  (y : GeometricPoint B S hS (yoneda.obj V'))

/-- The stalk ring map `A ⟶ 𝒪_{x̄}` of an affine representable factors through the local ring of
the identity chart, by the map of Stacks 05VP. -/
theorem representedAffineStalkRingHom_eq_chartLocalRing (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (x : GeometricPoint B S hS (yoneda.obj U))
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    representedAffineGlobalStalkRingHom B S hS U x a =
      (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x).symm
        (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          (yonedaIdentityNeighborhood U x)
          (((BigFppfOver.toScheme B S hS).obj U).presheaf.germ ⊤
            (chartPoint B S hS (yoneda.obj U) (yonedaIdentityNeighborhood U x)) trivial a)) := by
  refine (RingEquiv.eq_symm_apply _).2 ?_
  refine (pointStalkRingEquiv_representedAffineGlobalStalkRingHom B S hS U x a).trans ?_
  exact (chartLocalRingToEtaleLocalRing_germ B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (yonedaIdentityNeighborhood U x) a).symm

/-- The geometric stalk ring of an affine representable is a henselization of the local ring of
the identity chart, with the algebra structure of Stacks 05VP. -/
private theorem isHenselization_geometricStalkRing_chart (U : BigFppfOver B S hS)
    (x : GeometricPoint B S hS (yoneda.obj U))
    [Algebra ↥(yonedaChartLocalRing B S hS U x)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x)]
    (h : ∀ r, (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x).symm
        (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          (yonedaIdentityNeighborhood U x) r) =
      algebraMap ↥(yonedaChartLocalRing B S hS U x)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) r) :
    letI := isLocalRing_geometricStalkRing B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x
    IsHenselization ↥(yonedaChartLocalRing B S hS U x)
      (separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS U x))
        (chartGeometricPoint (yonedaIdentityNeighborhood U x)).residueField)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) := by
  let := isLocalRing_geometricStalkRing B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x
  let := isLocalRing_etaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) x
  have hh := isHenselization_etaleLocalRing_chart B S hS (isAlgebraicSpace_yoneda B S hS U)
    (yonedaIdentityNeighborhood U x)
  let : Algebra ↥(yonedaChartLocalRing B S hS U x) ↥(etaleLocalRing B S hS (yoneda.obj U) x) :=
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (yonedaIdentityNeighborhood U x)).toAlgebra
  exact IsHenselization.of_ringEquiv
    (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x).symm h

/-- **Stacks 08HV for affine representables, global against stalk.** For a morphism `g : V' ⟶ V`
of affine objects of the big fppf site and a geometric point `ȳ'` of `yoneda.obj V'` with image
`ȳ`, the map `𝒪_{ȳ} ⊗_{Γ(V)} Γ(V') ⟶ 𝒪_{ȳ'}` is flat. -/
theorem flat_baseChangeTensorRingMap_representedAffineStalk :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y)) :=
      (representedAffineGlobalStalkRingHom B S hS V
        (geometricPointMap (representedSpaceMap B S hS g).hom y)).toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) :=
      (representedAffineCommRingCatHom B S hS g).hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      (representedAffineGlobalStalkRingHom B S hS V' y).toAlgebra
    letI : Algebra
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y))
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      (stalkStructureMap B S hS (representedSpaceMap B S hS g) y).hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      ((representedAffineGlobalStalkRingHom B S hS V' y).comp
        (representedAffineCommRingCatHom B S hS g).hom).toAlgebra
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y))
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
      IsScalarTower.of_algebraMap_eq'
        (RingHom.ext (stalkStructureMap_representedAffineStalkRingHom B S hS g y)).symm
    RingHom.Flat (RingTheory.TorIndependence.baseChangeTensorRingMap
      (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (A := geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
      (A' := geometricStalkRing B S hS
        (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y)) := by
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y)) :=
    (representedAffineGlobalStalkRingHom B S hS V
      (geometricPointMap (representedSpaceMap B S hS g).hom y)).toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) :=
    (representedAffineCommRingCatHom B S hS g).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    (representedAffineGlobalStalkRingHom B S hS V' y).toAlgebra
  let : Algebra (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    (stalkStructureMap B S hS (representedSpaceMap B S hS g) y).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    ((representedAffineGlobalStalkRingHom B S hS V' y).comp
      (representedAffineCommRingCatHom B S hS g).hom).toAlgebra
  let : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    IsScalarTower.of_algebraMap_eq'
      (RingHom.ext (stalkStructureMap_representedAffineStalkRingHom B S hS g y)).symm
  -- names
  have hUW : (⊤ : ((BigFppfOver.toScheme B S hS).obj V').Opens) ≤
      (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ ⊤ := le_top
  have hu : (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)) ∈
      (⊤ : ((BigFppfOver.toScheme B S hS).obj V').Opens) := trivial
  have halg : ∀ r, algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) r =
        (((BigFppfOver.toScheme B S hS).map g).appLE ⊤ ⊤ hUW).hom r := by
    intro r
    show (((BigFppfOver.toScheme B S hS).map g).app ⊤).hom r = _
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  let := isLocalRing_geometricStalkRing B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
    (geometricPointMap (representedSpaceMap B S hS g).hom y)
  let := isLocalRing_geometricStalkRing B S hS ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ y
  have := isLocalHom_stalkStructureMap B S hS (representedSpaceMap B S hS g) y
  -- the chart local rings
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y)) :=
    ((BigFppfOver.toScheme B S hS).obj V).presheaf.germ ⊤
      (((BigFppfOver.toScheme B S hS).map g).base
        (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y))) (hUW hu)
      |>.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) ↥(yonedaChartLocalRing B S hS V' y) :=
    ((BigFppfOver.toScheme B S hS).obj V').presheaf.germ ⊤
      (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)) hu |>.hom.toAlgebra
  let : Algebra
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      ↥(yonedaChartLocalRing B S hS V' y) :=
    (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y))).hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ↥(yonedaChartLocalRing B S hS V' y) :=
    ((algebraMap
        ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
        ↥(yonedaChartLocalRing B S hS V' y)).comp
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        ↥(yonedaChartLocalRing B S hS V
          (geometricPointMap (representedSpaceMap B S hS g).hom y)))).toAlgebra
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      ↥(yonedaChartLocalRing B S hS V' y) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) ↥(yonedaChartLocalRing B S hS V' y) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (germ_stalkMap_appLE_apply ((BigFppfOver.toScheme B S hS).map g) hUW hu r).trans
        (congrArg (((BigFppfOver.toScheme B S hS).obj V').presheaf.germ ⊤
          (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)) hu).hom
          (halg r)).symm
  have : IsLocalization.AtPrime
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      ((isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)).primeIdealOf
        ⟨((BigFppfOver.toScheme B S hS).map g).base
          (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)), hUW hu⟩).asIdeal :=
    (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)).isLocalization_stalk
      ⟨((BigFppfOver.toScheme B S hS).map g).base
        (chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)), hUW hu⟩
  have : IsLocalization.AtPrime ↥(yonedaChartLocalRing B S hS V' y)
      ((isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V')).primeIdealOf
        ⟨(chartPoint B S hS (yoneda.obj V') (yonedaIdentityNeighborhood V' y)), hu⟩).asIdeal :=
    (isAffineOpen_top _).isLocalization_stalk ⟨_, hu⟩
  -- the chart local rings to the geometric stalks
  let : Algebra
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y)) :=
    ((pointStalkRingEquiv B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (geometricPointMap (representedSpaceMap B S hS g).hom y)).symm.toRingHom.comp
      (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
        (yonedaIdentityNeighborhood V
          (geometricPointMap (representedSpaceMap B S hS g).hom y)))).toAlgebra
  let : Algebra ↥(yonedaChartLocalRing B S hS V' y)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    ((pointStalkRingEquiv B S hS ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩
        y).symm.toRingHom.comp
      (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V') (isAlgebraicSpace_yoneda B S hS V')
        (yonedaIdentityNeighborhood V' y))).toAlgebra
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y)) :=
    IsScalarTower.of_algebraMap_eq fun r => representedAffineStalkRingHom_eq_chartLocalRing
      B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y) r
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
      ↥(yonedaChartLocalRing B S hS V' y)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      representedAffineStalkRingHom_eq_chartLocalRing B S hS V' y r
  let : Algebra
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS V' y)
        (geometricStalkRing B S hS
          (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y)).comp
      (algebraMap
        ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
        ↥(yonedaChartLocalRing B S hS V' y))).toAlgebra
  have : IsScalarTower
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      ↥(yonedaChartLocalRing B S hS V' y)
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ↥(yonedaChartLocalRing B S hS V (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
          (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y),
        IsScalarTower.algebraMap_apply Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
          ↥(yonedaChartLocalRing B S hS V' y)
          (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y),
        ← IsScalarTower.algebraMap_apply Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) ↥(yonedaChartLocalRing B S hS V' y)]
      rfl
  -- henselizations
  have := isHenselization_geometricStalkRing_chart B S hS V
    (geometricPointMap (representedSpaceMap B S hS g).hom y) fun _ => rfl
  have := isHenselization_geometricStalkRing_chart B S hS V' y fun _ => rfl
  have hflat := flat_tensorProduct_lift_chart ((BigFppfOver.toScheme B S hS).map g)
    (isAffineOpen_top _) (isAffineOpen_top _) hUW hu
    (Rp := ↥(yonedaChartLocalRing B S hS V
      (geometricPointMap (representedSpaceMap B S hS g).hom y)))
    (Sq := ↥(yonedaChartLocalRing B S hS V' y))
    (Rsh := geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (geometricPointMap (representedSpaceMap B S hS g).hom y))
    (Ssh := geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y)
    halg
    (LR := separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS V
        (geometricPointMap (representedSpaceMap B S hS g).hom y)))
      (chartGeometricPoint (yonedaIdentityNeighborhood V
        (geometricPointMap (representedSpaceMap B S hS g).hom y))).residueField)
    (LS := separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS V' y))
      (chartGeometricPoint (yonedaIdentityNeighborhood V' y)).residueField)
  have hcomm : RingTheory.TorIndependence.baseChangeTensorRingMap
      (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      (A := geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
        (geometricPointMap (representedSpaceMap B S hS g).hom y))
      (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))
      (A' := geometricStalkRing B S hS
        (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y) =
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y))
      (IsScalarTower.toAlgHom Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y))
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) y))
      fun _ _ => Commute.all _ _).toRingHom.comp
      (Algebra.TensorProduct.comm Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (geometricPointMap (representedSpaceMap B S hS g).hom y))
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)).toRingHom := by
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]
    | tmul a r =>
      rw [RingTheory.TorIndependence.baseChangeTensorRingMap_tmul, RingHom.comp_apply]
      show _ = (Algebra.TensorProduct.lift _ _ _) ((Algebra.TensorProduct.comm _ _ _) (a ⊗ₜ r))
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.lift_tmul]
      exact mul_comm _ _
  rw [hcomm]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (Algebra.TensorProduct.comm _ _ _).bijective) hflat

/-- **Every prime of the ring of an affine representable comes from a geometric point**: for
`q ∈ Spec Γ(U)` there is a geometric point `x̄` of `yoneda.obj U` with `q` in the image of
`Spec 𝒪_{x̄} → Spec Γ(U)`. -/
theorem exists_mem_range_comap_representedAffineStalkRingHom (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (q : PrimeSpectrum Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ∃ x : GeometricPoint B S hS (yoneda.obj U),
      q ∈ Set.range (PrimeSpectrum.comap (representedAffineGlobalStalkRingHom B S hS U x)) := by
  have hU := isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj U)
  obtain ⟨u, hu⟩ : ∃ u : (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens), hU.primeIdealOf u = q :=
    ⟨hU.isoSpec.inv q, by
      show (hU.isoSpec.inv ≫ hU.isoSpec.hom) q = q
      rw [Iso.inv_hom_id]
      rfl⟩
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS U u.1
  obtain ⟨x, hx⟩ := exists_geometricRepresentative B S hS (yoneda.obj U) z
  refine ⟨x, ?_⟩
  have hpt : chartPoint B S hS (yoneda.obj U) (yonedaIdentityNeighborhood U x) = u.1 := by
    rw [← hz, ← hx]
    rfl
  let := isLocalRing_etaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) x
  -- the closed point of the stalk is the image of a prime of the étale local ring
  obtain ⟨P, hP⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1
    (faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (yonedaIdentityNeighborhood U x))).2
    (IsLocalRing.closedPoint _)
  refine ⟨PrimeSpectrum.comap
    (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x).toRingHom P, ?_⟩
  obtain ⟨u, hu0⟩ := u
  dsimp only at hpt
  subst hpt hu
  refine Eq.trans ?_ (hU.primeIdealOf_eq_map_closedPoint _).symm
  ext a
  show _ ↔ (((BigFppfOver.toScheme B S hS).obj U).presheaf.germ ⊤
      (chartPoint B S hS (yoneda.obj U) (yonedaIdentityNeighborhood U x)) trivial).hom a ∈
    (IsLocalRing.closedPoint _).asIdeal
  have e1 : (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x)
      (representedAffineGlobalStalkRingHom B S hS U x a) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (yonedaIdentityNeighborhood U x)
        ((((BigFppfOver.toScheme B S hS).obj U).presheaf.germ ⊤
          (chartPoint B S hS (yoneda.obj U) (yonedaIdentityNeighborhood U x)) trivial).hom a) := by
    rw [representedAffineStalkRingHom_eq_chartLocalRing, RingEquiv.apply_symm_apply]
  show (pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x)
      (representedAffineGlobalStalkRingHom B S hS U x a) ∈ P.asIdeal ↔ _
  rw [e1, ← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal, hP]
  rfl

end Flat

end AlgebraicGeometry.Space

end
