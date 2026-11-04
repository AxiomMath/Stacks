module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAEAssembly
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseStalkTransport
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartTargetCornerSpellings
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquarePasting
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompIdentification

/-!
# The chart's outer rectangle and the source identification of the cube

`AlgebraicGeometry.BaseChangeChart.outerSquare_comm`,
`AlgebraicGeometry.BaseChangeChart.localRingsSourceIso_comp_squareComparison`,
`AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceIso`,
`AlgebraicGeometry.BaseChangeChart.localTail` and
`AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap_eq_germGenerator`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- The chart's outer rectangle: the chart's square of coordinate rings with its two target
corners pushed to the local rings at a point of `U'`. -/
public theorem outerSquare_comm (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    ((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom =
      (f'.stalkMap (ch.incU' y)).hom.comp ((ch.toStalkR' y).comp ch.b.hom) :=
  RingTheory.TorIndependence.pastedSquare_comm ch.a.hom ch.b.hom ch.c.hom ch.d.hom
    (ch.toStalkR' y) (ch.toStalkA' y ε') (f'.stalkMap (ch.incU' y)).hom ch.isPushout_hom
    (ch.toStalkA'_d y ε' h₁ h₂)

/-- **The source identification of the cube, read against the comparison of the local rings.**
At a complex `P` of `𝒪_{X, g' x'}`-modules, the source identification
`AlgebraicGeometry.BaseChangeChart.localRingsSourceIso` followed by the Tag 065Z comparison of
the four local rings of the square of schemes at `x'` is the Tag 065Z comparison of the chart's
outer rectangle — the chart's square of coordinate rings with its two target corners pushed to
the local rings — followed by the two identifications of that rectangle's target. -/
public theorem localRingsSourceIso_comp_squareComparison (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z)
    (P : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' (ch.incU' y))))) :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    (ch.localRingsSourceIso y w).hom.app P ≫
        (RingTheory.TorIndependence.squareComparison.{u, u}
          (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
          (g'.stalkMap (ch.incU' y)).hom (f'.stalkMap (ch.incU' y)).hom
          (stalkMap_square f g f' g' w (ch.incU' y))).app P =
      (RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom
            ((ch.toStalkR' y).comp ch.b.hom) ((ch.toStalkA' y ε').comp ch.c.hom)
            (f'.stalkMap (ch.incU' y)).hom (ch.outerSquare_comm y ε' h₁ h₂)).app
          ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj P) ≫
        (ModuleCat.restrictScalars.{u}
            (f'.stalkMap (ch.incU' y)).hom).mapDerivedCategory.map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
              ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj P) ≫
            (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
              (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app P) := by
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkR y
  have := ch.isLocalization_toStalkA y
  have hcube := NatTrans.congr_app (ch.squareComparison_localRings y w ε' h₁ h₂) P
  have hpast := NatTrans.congr_app (RingTheory.TorIndependence.squareComparison_pasted.{u, u}
    ch.a.hom ch.b.hom ch.c.hom ch.d.hom (ch.toStalkR' y) (ch.toStalkA' y ε')
    (f'.stalkMap (ch.incU' y)).hom ch.isPushout_hom (ch.toStalkA'_d y ε' h₁ h₂))
    ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj P)
  have hcod : ∀ Z : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' (ch.incU' y)))),
      (RingTheory.TorIndependence.localizedSquareCodomainIso.{u, u} (ch.primeComplA y)
            (g'.stalkMap (ch.incU' y)).hom (f'.stalkMap (ch.incU' y)).hom).hom.app Z =
        (ModuleCat.restrictScalars.{u}
            (f'.stalkMap (ch.incU' y)).hom).mapDerivedCategory.map
          ((RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
            (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app Z) := fun Z => by
    dsimp only [RingTheory.TorIndependence.localizedSquareCodomainIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    exact Category.id_comp _
  have hL : ch.localRingsSourceIso y w =
      Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory)
          (Functor.isoWhiskerLeft ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory)
            (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
              (ch.toStalkR'_b y w)).symm) ≪≫
        RingTheory.TorIndependence.localizedSquareDomainIso.{u, u} (ch.primeComplR y) ch.a.hom
          (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
          (ch.toStalkA_a y) := rfl
  rw [hpast, hL]
  simp only [NatTrans.comp_app] at hcube
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj]
  rw [Category.assoc, hcube]
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, hcod]
  simp only [Functor.whiskerRight_app, Functor.associator_hom_app, Functor.comp_obj,
    Category.id_comp, CategoryTheory.Functor.map_comp]

/-- **The cube at a chart, on cohomology.** The source identification of the cube followed by the
base-change comparison on cohomology of the four local rings at a point of `U'` is the
base-change comparison on cohomology of the chart's outer rectangle — the chart's square of
coordinate rings with its two target corners pushed to the local rings — taken at the morphism
`φ` precomposed with the two identifications of the outer rectangle's target corner. -/
public theorem cohomologyComparisonMap_localRingsSourceIso (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z)
    (Kst : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' (ch.incU' y)))))
    (K'st : DerivedCategory (ModuleCat.{u} (X'.presheaf.stalk (ch.incU' y)))) (n : ℤ) :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    letI := ch.a.hom.toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
    letI := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    ∀ α : (totalDerivedExtensionScalars.{u, u, u}
        (g'.stalkMap (ch.incU' y)).hom).functor.obj Kst ⟶ K'st,
      (DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((ch.localRingsSourceIso y w).hom.app Kst) ≫
          RingTheory.TorIndependence.cohomologyComparisonMapGeneral
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) Kst K'st α n =
        RingTheory.TorIndependence.cohomologyComparisonMapGeneral (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj Kst) K'st
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
              ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj Kst) ≫
            (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
                (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app Kst ≫ α) n := by
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ch.a.hom.toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  have : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  intro α
  have hloc : RingTheory.TorIndependence.squareDerivedComparisonGeneral
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y))) =
      RingTheory.TorIndependence.squareComparison.{u, u}
        (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
        (g'.stalkMap (ch.incU' y)).hom (f'.stalkMap (ch.incU' y)).hom
        (stalkMap_square f g f' g' w (ch.incU' y)) := rfl
  have houter : RingTheory.TorIndependence.squareDerivedComparisonGeneral (R := ToType ch.R)
        (A := ToType ch.A) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y))) =
      RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom
        ((ch.toStalkR' y).comp ch.b.hom) ((ch.toStalkA' y ε').comp ch.c.hom)
        (f'.stalkMap (ch.incU' y)).hom (ch.outerSquare_comm y ε' h₁ h₂) := rfl
  dsimp only [RingTheory.TorIndependence.cohomologyComparisonMapGeneral,
    RingTheory.TorIndependence.ringComparison]
  rw [hloc, houter, ← Category.assoc, ← CategoryTheory.Functor.map_comp, ← Category.assoc,
    ch.localRingsSourceIso_comp_squareComparison y w ε' h₁ h₂ Kst]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rfl

/-- The tail of the chart's outer-rectangle comparison at a point of `U'`: the two
identifications of the rectangle's target corner, followed by the pointwise morphism of
Stacks 0DJ7 transported to the stalks. -/
public abbrev localTail (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) (K : DerivedCategory X.Modules)
    {K' : DerivedCategory X'.Modules}
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    (totalDerivedExtensionScalars.{u, u, u} ((ch.toStalkA' y ε').comp ch.c.hom)).functor.obj
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ⟶
      (derivedStalkFunctor (ch.incU' y)).obj K' :=
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
        (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
      ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
    (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
          (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
      ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
        (derivedStalkFunctor (ch.incU' y)).map φ)

/-- **The source identification of the cube, absorbed into the comparison.** The pointwise
comparison of Stacks 0DJ7 at `x'`, evaluated on the image of `m` under
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap`, is the comparison of the chart's outer
rectangle — the chart's square of coordinate rings with its two target corners pushed to the
local rings — evaluated on the germ generator `1 ⊗ m` alone. -/
public theorem cohomologyComparisonMap_localRingsSourceMap_eq_germGenerator
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
    letI := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u),
      (RingTheory.TorIndependence.cohomologyComparisonMapGeneral
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
            ((derivedStalkFunctor (ch.incU' y)).obj K')
            ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
              (derivedStalkFunctor (ch.incU' y)).map φ) n).hom
          (ch.localRingsSourceMap y w K hK n m) =
        (RingTheory.TorIndependence.cohomologyComparisonMapGeneral (R := ToType ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((affineDerivedSections ch.incU).obj K)
            ((derivedStalkFunctor (ch.incU' y)).obj K')
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                    (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                  (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                  ((affineDerivedSections ch.incU).obj K)) ≫
              (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                    (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                  (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
                ch.localTail y ε' h₁ h₂ K φ) n).hom
          ((ch.homologyBaseChangeLocalizedIso y K n).inv.hom
            ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ⊗ₜ[ch.R', ch.toStalkR' y] m)) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro m
  have hB := ch.cohomologyComparisonMap_localRingsSourceIso y w ε' h₁ h₂
    ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
    ((derivedStalkFunctor (ch.incU' y)).obj K') n
    ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
      (derivedStalkFunctor (ch.incU' y)).map φ)
  have h3 := RingTheory.TorIndependence.cohomologyComparisonMapGeneral_map
    (R := ToType ch.R) (A := ToType ch.A)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    (A' := ToType (X'.presheaf.stalk (ch.incU' y)))
    ((ModuleCat.restrictScalars.{u}
        (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K)))
    ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
    ((derivedStalkFunctor (ch.incU' y)).obj K')
    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom (ch.localTail y ε' h₁ h₂ K φ) n
  have h2 := RingTheory.TorIndependence.cohomologyComparisonMapGeneral_map
    (R := ToType ch.R) (A := ToType ch.A)
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    (A' := ToType (X'.presheaf.stalk (ch.incU' y)))
    ((affineDerivedSections ch.incU).obj K)
    ((ModuleCat.restrictScalars.{u}
        (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K)))
    ((derivedStalkFunctor (ch.incU' y)).obj K')
    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
      ((affineDerivedSections ch.incU).obj K))
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
            (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
      ch.localTail y ε' h₁ h₂ K φ) n
  have hchain : RingTheory.TorIndependence.cohomologyComparisonMapGeneral (R := ToType ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) ((derivedStalkFunctor (ch.incU' y)).obj K')
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
            ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
              (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
              ((affineDerivedSections ch.incU).obj K)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
              (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
            ch.localTail y ε' h₁ h₂ K φ) n =
      (DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.R)
                  (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).functor.map
              ((ModuleCat.restrictScalars.{u} (algebraMap (ToType ch.R)
                    (ToType ch.A))).mapDerivedCategory.map
                ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                  (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                  ((affineDerivedSections ch.incU).obj K)))) ≫
        (DerivedCategory.homologyFunctor
                (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.R)
                    (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).functor.map
                ((ModuleCat.restrictScalars.{u} (algebraMap (ToType ch.R)
                      (ToType ch.A))).mapDerivedCategory.map
                  (ch.restrictGermDerivedStalkSectionsIso y K hK).hom)) ≫
          (DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
                ((ch.localRingsSourceIso y w).hom.app
                  ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
            RingTheory.TorIndependence.cohomologyComparisonMapGeneral
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
              ((derivedStalkFunctor (ch.incU' y)).obj K')
              ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
                (derivedStalkFunctor (ch.incU' y)).map φ) n := by
    rw [h2, h3, ← hB]
  exact ConcreteCategory.congr_hom hchain.symm _

end BaseChangeChart

end AlgebraicGeometry

end
