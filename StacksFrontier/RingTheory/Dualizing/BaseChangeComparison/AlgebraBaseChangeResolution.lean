module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ResolvedProjectionFormula
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraIsoComputation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMate

/-!
# The base change of the algebra, at a resolution

`Dualizing.derivedBaseChangeAlgebraIso` identifies the derived base change along `R → R'` of the
algebra `A`, viewed as a degree-zero complex of `R`-modules, with `A ⊗_R R'` viewed as a
degree-zero complex of `R'`-modules.  This file writes it as the comparison morphism of the model
of derived base change at the degree-zero complex, followed by the class of one explicit chain map
`Dualizing.algebraBaseChangeChain`, and deduces that a K-flat resolution `p : P ⟶ A[0]` over `R`
base changes to a K-flat resolution `Dualizing.baseChangeResolution` of `(A ⊗_R R')[0]` over `R'`.
That is the resolution at which the projection formula over `R' → A ⊗_R R'` is evaluated in the
proof of [stacks 0E2A].

## Main definitions

* `Dualizing.algebraBaseChangeChain` — the chain map `R' ⊗_R A[0] ⟶ (A ⊗_R R')[0]`.
* `Dualizing.baseChangeResolution` — the base change of a resolution of `A[0]`.

* `Dualizing.extendScalarsCompIsoOfEq` — the composition isomorphism of two extensions of
  scalars, retargeted along an equality of ring maps.

## Main results

* `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_chain` — the base change of the algebra is the
  comparison morphism followed by the class of `Dualizing.algebraBaseChangeChain`.
* `Dualizing.quasiIso_baseChangeResolution` — the base change of a K-flat resolution of `A[0]` is
  a quasi-isomorphism onto `(A ⊗_R R')[0]`; this is where Tor independence is used.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- The composition isomorphism of extensions of scalars, retargeted along an equality of ring
maps; its forward direction is `RingTheory.TorIndependence.extendScalarsCompInvOfEq`. -/
def extendScalarsCompIsoOfEq {S : Type uR} {T : Type uA} {T' : Type uRp} [CommRing S]
    [CommRing T] [CommRing T'] (f : S →+* T) (h : T →+* T') (hc : S →+* T')
    (hfh : h.comp f = hc) :
    ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f ⋙
        ModuleCat.extendScalars.{uA, uRp, max v uR uA uRp} h ≅
      ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} hc :=
  (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v} f h).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} hfh)

/-- The forward direction of `Dualizing.extendScalarsCompIsoOfEq`. -/
theorem extendScalarsCompIsoOfEq_hom {S : Type uR} {T : Type uA} {T' : Type uRp} [CommRing S]
    [CommRing T] [CommRing T'] (f : S →+* T) (h : T →+* T') (hc : S →+* T')
    (hfh : h.comp f = hc) :
    (extendScalarsCompIsoOfEq.{uR, uA, uRp, v} f h hc hfh).hom =
      RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, uRp, v} f h hc hfh :=
  rfl

variable [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

/-- The degree-zero chain map carrying `R' ⊗_R A` to `A ⊗_R R'`, read off the base change of the
algebra. -/
def algebraBaseChangeChain :
    ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ) 0).obj
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ⟶
      (HomologicalComplex.single (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ) 0).obj
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R' (TensorProduct R A R'))).obj
          (ModuleCat.of (TensorProduct R A R') (ULift.{max v uR uA uRp} (TensorProduct R A R')))) :=
  ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapCochainComplexSingleFunctor 0).inv.app
        (ModuleCat.of A (ULift.{max v uR uA uRp} A))) ≫
    (NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.derivedBaseChangeComparison
        (algebraMap R A) (algebraMap R R')
        (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
        ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
          (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
        baseChangeR baseChangeA comparisonR comparisonA).1
      (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A (ULift.{max v uR uA uRp} A))) ≫
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R' (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
            (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app
          (ModuleCat.of A (ULift.{max v uR uA uRp} A))).hom ≫
        (HomologicalComplex.single (ModuleCat.{max v uR uA uRp} (TensorProduct R A R'))
          (ComplexShape.up ℤ) 0).map
          (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
            (algebraMap A (TensorProduct R A R'))).hom) ≫
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R' (TensorProduct R A R'))).mapCochainComplexSingleFunctor 0).hom.app
      (ModuleCat.of (TensorProduct R A R') (ULift.{max v uR uA uRp} (TensorProduct R A R')))

include hA hR in
/-- **The base change of the algebra, as a comparison followed by a chain map.** -/
theorem derivedBaseChangeAlgebraIso_hom_eq_chain :
    (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
        baseChangeA comparisonA hA).hom =
      comparisonR.app
          ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ) 0).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).obj
              (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
        DerivedCategory.Q.map (algebraBaseChangeChain.{uR, uA, uRp, v} baseChangeR comparisonR
          baseChangeA comparisonA) := by
  rw [derivedBaseChangeAlgebraIso_hom_eq_single.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA]
  simp only [algebraBaseChangeChain, Functor.map_comp, Category.assoc]
  congr 3
  have h1 := ((ModuleCat.restrictScalars.{max v uR uA uRp}
    (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.inv.naturality
      ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
            (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app
          (ModuleCat.of A (ULift.{max v uR uA uRp} A))).hom)
  have h2 := ((ModuleCat.restrictScalars.{max v uR uA uRp}
    (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.inv.naturality
      ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} (TensorProduct R A R'))
          (ComplexShape.up ℤ) 0).map
          (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
            (algebraMap A (TensorProduct R A R'))).hom))
  have h3 := Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R' (TensorProduct R A R')))
      (ModuleCat.of (TensorProduct R A R') (ULift.{max v uR uA uRp} (TensorProduct R A R')))
  dsimp only [Functor.comp_map] at h1 h2
  rw [← reassoc_of% h1]
  congr 1
  rw [← h3, reassoc_of% h2]
  rfl

section Resolution

variable (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
  (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A))

/-- The resolution of the algebra over `R`, base changed to a resolution of `A ⊗_R R'` over
`R'`. -/
def baseChangeResolution :
    ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      algebraComplex.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom :=
  ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).map p ≫
    algebraBaseChangeChain.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA

include hA hR in
/-- The base change of a resolution, read against the base change of the algebra. -/
theorem comparisonR_app_comp_Q_map_baseChangeResolution [QuasiIso p] :
    comparisonR.app P ≫ DerivedCategory.Q.map (baseChangeResolution.{uR, uA, uRp, v} baseChangeR
      comparisonR baseChangeA comparisonA P p) =
    baseChangeR.map (DerivedCategory.Q.map p) ≫
      (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
        baseChangeA comparisonA hA).hom := by
  rw [derivedBaseChangeAlgebraIso_hom_eq_chain.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA, baseChangeResolution, DerivedCategory.Q.map_comp,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact (comparisonR.naturality p).symm

include hTor hA hR in
/-- **The base change of a K-flat resolution of the algebra is a resolution.** -/
theorem quasiIso_baseChangeResolution [QuasiIso p]
    (hP : CochainComplex.KFlat.{uR, max v uA uRp} P) :
    QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA P p) := by
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR P hP
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have h := comparisonR_app_comp_Q_map_baseChangeResolution.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR baseChangeA comparisonA P p
  have : IsIso (comparisonR.app P ≫ DerivedCategory.Q.map (baseChangeResolution.{uR, uA, uRp, v}
      baseChangeR comparisonR baseChangeA comparisonA P p)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (comparisonR.app P) _

end Resolution

end Dualizing
