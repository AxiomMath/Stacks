module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceBijective
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAEWiring

/-!
# Stacks 0DJ8

`AlgebraicGeometry.BaseChangeChart.sourceBridgeMap` is the bijection the source bridge of
Stacks 0DJ8 asks for; this module proves it bijective, proves that it carries the pointwise map
of Stacks 0DJ7 to the germ-localized chart map of Stacks 0DJ8 (2), and concludes the three-way
equivalence.

## Main results

* `AlgebraicGeometry.BaseChangeChart.bijective_sourceBridgeMap`: the source bridge's map is a
  bijection.
* `AlgebraicGeometry.BaseChangeChart.baseChangeCohomologyMap_sourceBridgeMap`: the source
  bridge's map carries the pointwise map of Stacks 0DJ7 to the germ-localized chart map of
  Stacks 0DJ8 (2).
* `AlgebraicGeometry.baseChange_tfae`: **Stacks 0DJ8.**

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct ChangeOfRings

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- Preserve the locally small models previously provided by imported global instances.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace AlgebraicGeometry

/-- `extendScalarsComp f g` sends `z ⊗ m` to `z • (1 ⊗ (1 ⊗ m))`. -/
private theorem extendScalarsComp_app_hom_tmul {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) (M : ModuleCat.{u} A) (z : C) (m : M) :
    ((ModuleCat.extendScalarsComp f g).app M).hom.hom (z ⊗ₜ[A, g.comp f] m) =
      z • (show (ModuleCat.extendScalars.{u, u, u} g).obj
          ((ModuleCat.extendScalars.{u, u, u} f).obj M) from
        (1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] m)) := by
  refine Eq.trans (congrArg _ (ModuleCat.extendScalars_tmul_eq_smul_one_tmul (g.comp f) M z m)) ?_
  refine Eq.trans (LinearMap.map_smul _ z _) ?_
  exact congrArg (fun t => z • t) (ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m)

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The source bridge's map is a bijection.** Each of its five factors is: the two
cancellations of the iterated extension of scalars and the transport along
`chartPushoutRingMap_eq` are isomorphisms of modules, the germ comparison at `U'` is an additive
equivalence, and the source identification is invertible by
`bijective_extendScalarsTranspose_localRingsSourceMap`. -/
public theorem bijective_sourceBridgeMap (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp
      (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    Function.Bijective
      (ch.sourceBridgeMap y w K hK n ε' h₁ h₂) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp
    (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  have : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  have : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  let : Algebra (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
        ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  have : IsIso (ch.localRingsSourceTranspose y w K hK n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ch.bijective_extendScalarsTranspose_localRingsSourceMap y w K hK n _ fun _ => rfl)
  have hb1 : Function.Bijective
      ((((ModuleCat.extendScalarsComp (RingTheory.TorIndependence.baseChangeTensorRingMap
          (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A'))
        (specGermRingHom ch.A' y)).app
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n)).inv).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hb3 : Function.Bijective
      (((eqToIso (congrArg
          (fun p : (ch.A ⊗[ch.R] ch.R') →+* (ToType (X'.presheaf.stalk (ch.incU' y))) =>
            (ModuleCat.extendScalars.{u, u, u} p).obj
              (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n))
          (ch.chartPushoutRingMap_eq y w ε' h₁ h₂))).hom).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hb4 : Function.Bijective
      ((((ModuleCat.extendScalarsComp (algebraMap (ch.A ⊗[ch.R] ch.R')
            (ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
          (RingTheory.TorIndependence.baseChangeTensorRingMap
          (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          (A' := ToType (X'.presheaf.stalk (ch.incU' y))))).app
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n)).hom).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hb5 : Function.Bijective
      (((ModuleCat.extendScalars.{u, u, u} (RingTheory.TorIndependence.baseChangeTensorRingMap
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y))))).map
        (ch.localRingsSourceTranspose y w K hK n)).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact hb5.comp (hb4.comp (hb3.comp
    ((ModuleCat.extendScalarsTargetEquiv
        ((specGermRingHom ch.A' y).comp (RingTheory.TorIndependence.baseChangeTensorRingMap
            (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A')))
        ε' (ch.incU'.stalkMap y).hom h₂ h₁
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n)).bijective.comp hb1)))

/-- **The source bridge's map carries the pointwise map of Stacks 0DJ7 to the germ-localized
chart map of Stacks 0DJ8 (2).** Both sides are additive, so it is enough to check the generators
`z ⊗ (1 ⊗ m)` of the source; there `AlgebraicGeometry.baseChangeCohomologyMap_one_tmul` and
`RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral_one_tmul` replace the two maps by
the two cohomology comparisons, and
`AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap` identifies
them. -/
public theorem baseChangeCohomologyMap_sourceBridgeMap (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (hK' : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (n : ℤ)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    ∀ m : ((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).obj
        ((ModuleCat.extendScalars.{u, u, u} (RingTheory.TorIndependence.baseChangeTensorRingMap
          (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A'))).obj
          (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n)) : Type u),
      (baseChangeCohomologyMap f g f' g' w K K' φ (ch.incU' y) n).hom
          (ch.sourceBridgeMap y w K hK n ε' h₁ h₂ m) =
        (homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂ n).hom.hom
          (((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).map
            (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral (R := ch.R) (R' := ch.R')
              ((affineDerivedSections ch.incU).obj K)
              ((affineDerivedSections ch.incU').obj K')
              (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n)).hom m) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp
    (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  have : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  have : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  let : Algebra (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))
        ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  intro m
  let kc := RingTheory.TorIndependence.baseChangeTensorRingMap
    (R := ch.R) (A := ch.A) (R' := ch.R') (A' := ch.A')
  let kl := RingTheory.TorIndependence.baseChangeTensorRingMap
    (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
    (A := ToType (X.presheaf.stalk (g' (ch.incU' y))))
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    (A' := ToType (X'.presheaf.stalk (ch.incU' y)))
  let qq := algebraMap (ch.A ⊗[ch.R] ch.R')
    (ToType (X.presheaf.stalk (g' (ch.incU' y)))
      ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
      ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  let pp := specGermRingHom ch.A' y
  let HH := RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
    ((affineDerivedSections ch.incU).obj K) n
  let Phi := ch.localRingsSourceTranspose y w K hK n
  let io := (ModuleCat.extendScalarsComp kc pp).app HH
  let th1 := io.inv
  let th2 := ModuleCat.extendScalarsTargetEquiv (pp.comp kc) ε'
    (ch.incU'.stalkMap y).hom h₂ h₁ HH
  let th3 := (eqToIso (congrArg
    (fun r : (ch.A ⊗[ch.R] ch.R') →+* ToType (X'.presheaf.stalk (ch.incU' y)) =>
      (ModuleCat.extendScalars.{u, u, u} r).obj HH)
    (ch.chartPushoutRingMap_eq y w ε' h₁ h₂))).hom
  let th4 := ((ModuleCat.extendScalarsComp qq kl).app HH).hom
  let th5 := (ModuleCat.extendScalars.{u, u, u} kl).map Phi
  have hdef : ∀ t, ch.sourceBridgeMap y w K hK n ε' h₁ h₂ t =
      th5.hom (th4.hom (th3.hom (th2 (th1.hom t)))) := fun _ => rfl
  have hc1 : ∀ m₀ : (HH : Type u),
      th1.hom ((1 : ToType ((Spec ch.A').presheaf.stalk y)) ⊗ₜ[ch.A', pp]
          ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀)) =
        (1 : ToType ((Spec ch.A').presheaf.stalk y)) ⊗ₜ[ch.A ⊗[ch.R] ch.R', pp.comp kc] m₀ :=
    fun m₀ =>
      Eq.trans (congrArg th1.hom
          (ModuleCat.extendScalarsComp_hom_app_one_tmul kc pp HH m₀).symm)
        (ModuleCat.iso_inv_hom_apply ((ModuleCat.extendScalarsComp kc pp).app HH) _)
  let HL := RingTheory.TorIndependence.baseChangeCohomology
    (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n
  have hthgen : ∀ (z : ToType ((Spec ch.A').presheaf.stalk y)) (m₀ : (HH : Type u)),
      ch.sourceBridgeMap y w K hK n ε' h₁ h₂
          (z ⊗ₜ[ch.A', pp] ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀)) =
        ε' z • (show (ModuleCat.extendScalars.{u, u, u} kl).obj HL from
          ((1 : ToType (X'.presheaf.stalk (ch.incU' y))) ⊗ₜ[_, kl]
            (ch.localRingsSourceMap y w K hK n m₀))) := by
    intro z m₀
    have s1 : th1.hom (z ⊗ₜ[ch.A', pp] ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀)) =
        z ⊗ₜ[ch.A ⊗[ch.R] ch.R', pp.comp kc] m₀ := by
      refine Eq.trans (congrArg th1.hom
        (ModuleCat.extendScalars_tmul_eq_smul_one_tmul pp
          ((ModuleCat.extendScalars.{u, u, u} kc).obj HH) z _)) ?_
      refine Eq.trans (th1.hom.map_smul z _) ?_
      refine Eq.trans (congrArg (fun t => z • t) (hc1 m₀)) ?_
      exact (ModuleCat.ExtendScalars.smul_tmul (pp.comp kc) z 1 m₀).trans
        (congrArg (fun c : ToType ((Spec ch.A').presheaf.stalk y) =>
          c ⊗ₜ[ch.A ⊗[ch.R] ch.R', pp.comp kc] m₀) (mul_one z))
    have s2 : th2 (z ⊗ₜ[ch.A ⊗[ch.R] ch.R', pp.comp kc] m₀) =
        ε' z ⊗ₜ[ch.A ⊗[ch.R] ch.R', ε'.comp (pp.comp kc)] m₀ :=
      ModuleCat.extendScalarsTargetEquiv_tmul _ _ _ h₂ h₁ HH z m₀
    have s3 : th3.hom (ε' z ⊗ₜ[ch.A ⊗[ch.R] ch.R', ε'.comp (pp.comp kc)] m₀) =
        ε' z ⊗ₜ[ch.A ⊗[ch.R] ch.R', kl.comp qq] m₀ :=
      ModuleCat.eqToHom_extendScalars_tmul (ch.chartPushoutRingMap_eq y w ε' h₁ h₂)
        HH (ε' z) m₀
    have s4 : th4.hom (ε' z ⊗ₜ[ch.A ⊗[ch.R] ch.R', kl.comp qq] m₀) =
        ε' z • (show (ModuleCat.extendScalars.{u, u, u} kl).obj
            ((ModuleCat.extendScalars.{u, u, u} qq).obj HH) from
          ((1 : ToType (X'.presheaf.stalk (ch.incU' y))) ⊗ₜ[_, kl]
            ((1 : ToType (X.presheaf.stalk (g' (ch.incU' y)))
                ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ⊗ₜ[ch.A ⊗[ch.R] ch.R', qq] m₀))) := by
      exact extendScalarsComp_app_hom_tmul qq kl HH (ε' z) m₀
    have s5 : th5.hom (ε' z • (show (ModuleCat.extendScalars.{u, u, u} kl).obj
            ((ModuleCat.extendScalars.{u, u, u} qq).obj HH) from
          ((1 : ToType (X'.presheaf.stalk (ch.incU' y))) ⊗ₜ[_, kl]
            ((1 : ToType (X.presheaf.stalk (g' (ch.incU' y)))
                ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ⊗ₜ[ch.A ⊗[ch.R] ch.R', qq] m₀)))) =
        ε' z • (show (ModuleCat.extendScalars.{u, u, u} kl).obj HL from
          ((1 : ToType (X'.presheaf.stalk (ch.incU' y))) ⊗ₜ[_, kl]
            (ch.localRingsSourceMap y w K hK n m₀))) := by
      refine Eq.trans (th5.hom.map_smul (ε' z) _) ?_
      refine congrArg (fun t => ε' z • t) ?_
      refine Eq.trans (ModuleCat.ExtendScalars.map_tmul kl Phi
        (1 : ToType (X'.presheaf.stalk (ch.incU' y))) _) ?_
      exact congrArg (fun t => (show (ModuleCat.extendScalars.{u, u, u} kl).obj HL from
          ((1 : ToType (X'.presheaf.stalk (ch.incU' y))) ⊗ₜ[_, kl] t)))
        (ch.localRingsSourceTranspose_one_tmul y w K hK n m₀)
    exact (hdef _).trans ((congrArg th5.hom ((congrArg th4.hom
      ((congrArg th3.hom ((congrArg th2 s1).trans s2)).trans s3)).trans s4)).trans s5)
  let CCl := RingTheory.TorIndependence.cohomologyComparisonMapGeneral
    (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
    ((derivedStalkFunctor (ch.incU' y)).obj K')
    ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
      (derivedStalkFunctor (ch.incU' y)).map φ) n
  let CCc := RingTheory.TorIndependence.cohomologyComparisonMapGeneral (R := ch.R) (R' := ch.R')
    ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
    (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n
  let RBC := RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral (R := ch.R) (R' := ch.R')
    ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
    (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n
  let HC' := (DerivedCategory.homologyFunctor (ModuleCat.{u} ch.A') n).obj
    ((affineDerivedSections ch.incU').obj K')
  let RI := homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂ n
  let BC := baseChangeCohomologyMap f g f' g' w K K' φ (ch.incU' y) n
  have hfac1 : ∀ m₀ : (HH : Type u),
      CCl.hom (ch.localRingsSourceMap y w K hK n m₀) =
        RI.hom.hom ((1 : ToType ((Spec ch.A').presheaf.stalk y)) ⊗ₜ[ch.A', pp]
          CCc.hom m₀) :=
    ch.cohomologyComparisonMap_localRingsSourceMap y w K K' hK hK' φ ε' h₁ h₂ n
  have hgen : ∀ (z : ToType ((Spec ch.A').presheaf.stalk y)) (m₀ : (HH : Type u)),
      BC.hom (ch.sourceBridgeMap y w K hK n ε' h₁ h₂
          (z ⊗ₜ[ch.A', pp] ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀))) =
        RI.hom.hom (((ModuleCat.extendScalars.{u, u, u} pp).map RBC).hom
          (z ⊗ₜ[ch.A', pp] ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀))) := by
    intro z m₀
    have hR : RI.hom.hom (((ModuleCat.extendScalars.{u, u, u} pp).map RBC).hom
          (z ⊗ₜ[ch.A', pp] ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀))) =
        ε' z • RI.hom.hom ((1 : ToType ((Spec ch.A').presheaf.stalk y)) ⊗ₜ[ch.A', pp]
          CCc.hom m₀) := by
      refine Eq.trans (congrArg RI.hom.hom
        (ModuleCat.ExtendScalars.map_tmul pp RBC z _)) ?_
      refine Eq.trans (congrArg (fun t => RI.hom.hom (z ⊗ₜ[ch.A', pp] t))
        (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral_one_tmul (R := ch.R)
          (R' := ch.R') ((affineDerivedSections ch.incU).obj K)
          ((affineDerivedSections ch.incU').obj K')
          (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n m₀)) ?_
      refine Eq.trans (congrArg RI.hom.hom
        (ModuleCat.extendScalars_tmul_eq_smul_one_tmul pp HC' z (CCc.hom m₀))) ?_
      refine Eq.trans (RI.hom.hom.map_smul z _) ?_
      exact ModuleCat.restrictScalars.smul_def' ε' z _
    refine Eq.trans (congrArg BC.hom (hthgen z m₀)) ?_
    refine Eq.trans (BC.hom.map_smul (ε' z) _) ?_
    refine Eq.trans (congrArg (fun t => ε' z • t)
      ((baseChangeCohomologyMap_one_tmul f g f' g' w (ch.incU' y) K K' φ n
        (ch.localRingsSourceMap y w K hK n m₀)).trans (hfac1 m₀))) ?_
    exact hR.symm
  have hb0 : ch.sourceBridgeMap y w K hK n ε' h₁ h₂ 0 = 0 := by
    simp only [hdef, map_zero]
  have hbadd : ∀ t₁ t₂, ch.sourceBridgeMap y w K hK n ε' h₁ h₂ (t₁ + t₂) =
      ch.sourceBridgeMap y w K hK n ε' h₁ h₂ t₁ +
        ch.sourceBridgeMap y w K hK n ε' h₁ h₂ t₂ := by
    intro t₁ t₂
    simp only [hdef, map_add]
  let P : ((ModuleCat.extendScalars.{u, u, u} pp).obj
      ((ModuleCat.extendScalars.{u, u, u} kc).obj HH) : Type u) → Prop := fun t =>
    BC.hom (ch.sourceBridgeMap y w K hK n ε' h₁ h₂ t) =
      RI.hom.hom (((ModuleCat.extendScalars.{u, u, u} pp).map RBC).hom t)
  have hP0 : P 0 := by
    refine Eq.trans (congrArg BC.hom hb0) ?_
    refine Eq.trans BC.hom.map_zero ?_
    exact Eq.symm (Eq.trans (congrArg RI.hom.hom
      (((ModuleCat.extendScalars.{u, u, u} pp).map RBC).hom.map_zero)) RI.hom.hom.map_zero)
  have hPadd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂) := by
    intro t₁ t₂ ht₁ ht₂
    refine Eq.trans (congrArg BC.hom (hbadd t₁ t₂)) ?_
    refine Eq.trans (BC.hom.map_add _ _) ?_
    refine Eq.trans (congrArg₂ (· + ·) ht₁ ht₂) ?_
    exact Eq.symm (Eq.trans (congrArg RI.hom.hom
      (((ModuleCat.extendScalars.{u, u, u} pp).map RBC).hom.map_add t₁ t₂))
      (RI.hom.hom.map_add _ _))
  have key : ∀ v, P (io.hom.hom v) := by
    intro v
    refine TensorProduct.induction_on (motive := fun t => P (io.hom.hom t)) v ?_ ?_ ?_
    · exact Eq.mpr (congrArg P io.hom.hom.map_zero) hP0
    · intro c m₀
      let cc : ToType ((Spec ch.A').presheaf.stalk y) := c
      refine Eq.mpr (congrArg P ?_) (hgen cc m₀)
      refine Eq.trans (extendScalarsComp_app_hom_tmul kc pp HH cc m₀) ?_
      exact (ModuleCat.extendScalars_tmul_eq_smul_one_tmul pp
        ((ModuleCat.extendScalars.{u, u, u} kc).obj HH) cc
        ((1 : ch.A') ⊗ₜ[ch.A ⊗[ch.R] ch.R', kc] m₀)).symm
    · intro v₁ v₂ hv₁ hv₂
      exact Eq.mpr (congrArg P (io.hom.hom.map_add v₁ v₂)) (hPadd _ _ hv₁ hv₂)
  exact Eq.mpr (congrArg P (ModuleCat.iso_hom_inv_apply io m).symm) (key (io.inv.hom m))

end BaseChangeChart

/-- **Stacks 0DJ8.** Let

`X' ⟶ X`, `X' ⟶ S'`, `X ⟶ S`, `S' ⟶ S`

be a Cartesian square of schemes, `K` an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves, `K'` an object of `D(𝒪_{X'}')` with quasi-coherent cohomology sheaves, and
`φ : L(g')^*K ⟶ K'`. Then the following are equivalent.

1. The pointwise map of Stacks 0DJ7 is an isomorphism at every point of `X'` and in every
   degree.
2. The comparison map of every Cartesian affine-open chart is an isomorphism.
3. The comparison map of every chart in some family whose opens `U'` cover `X'` is an
   isomorphism.

The implications are read off the source bridge
`AlgebraicGeometry.baseChange_tfae_of_sourceBridge`: at a chart, a point `y` of
`Spec 𝒪_{X'}(U')` and a degree, `AlgebraicGeometry.BaseChangeChart.sourceBridgeMap` is a
bijection of the two maps' sources — `AlgebraicGeometry.BaseChangeChart.bijective_sourceBridgeMap`
— commuting with them through the identification of their targets, by
`AlgebraicGeometry.BaseChangeChart.baseChangeCohomologyMap_sourceBridgeMap`. -/
@[stacks 0DJ8]
public theorem baseChange_tfae {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    List.TFAE
      [∀ (x' : X') (i : ℤ), IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ x' i),
       ∀ ch : BaseChangeChart f g f' g', IsIso (ch.comparison K K' φ),
       ∃ 𝒞 : Set (BaseChangeChart f g f' g'),
         (∀ ch ∈ 𝒞, IsIso (ch.comparison K K' φ)) ∧
           ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x'] := by
  refine baseChange_tfae_of_sourceBridge f g f' g' sq K K' hK' φ fun ch => ?_
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  intro n y ε' h₁ h₂
  exact ⟨ch.sourceBridgeMap y sq.w K hK n ε' h₁ h₂,
    ch.bijective_sourceBridgeMap y sq.w K hK n ε' h₁ h₂,
    ch.baseChangeCohomologyMap_sourceBridgeMap y sq.w K K' hK hK' φ n ε' h₁ h₂⟩

end AlgebraicGeometry

end
