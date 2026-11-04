module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison

/-!
# The derived base change of the algebra, computed

`Dualizing.derivedBaseChangeAlgebraIso` is the identification `A' = A ⊗ᴸ_R R'` used in the proof
of Stacks 0E2A: derived base change along `R → R'` carries the algebra `A`, viewed as a
degree-zero complex of `R`-modules, to `A ⊗_R R'` viewed as a degree-zero complex of
`R'`-modules.  Only its *existence* was recorded.  The isomorphism is produced by a tactic block,
and nothing said what its underlying morphism is, so every compatibility that has to be checked
against it is opaque to a diagram chase — and since the isomorphism does not depend on the object
of `D(A)`, pinning that object down does not help.

This file computes it.  The isomorphism is built from the same call to
`RingTheory.TorIndependence.derivedBaseChangeComparison` — the comparison of Stacks 0661 — that
`Dualizing.restrictionBaseChangeIsoGeneral` is built from, evaluated at the degree-zero complex on
`ULift A` and conjugated by canonical isomorphisms.  The equations of
`StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations` compute that comparison
wherever the counit of derived extension of scalars along `A → A ⊗_R R'` is invertible, which it
is at a degree-zero complex on a flat module.  Carrying that through leaves an expression in which
the opaque derived comparison does not occur: only the *underived* comparison, which
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul` evaluates on pure tensors,
the counit `comparisonR`, and the canonical isomorphisms of `CategoryTheory.Functor` and
`DerivedCategory`.

## Main results

* `Dualizing.isIso_comparison_app_single_algebra` — the counit of derived extension of scalars
  along `A → A ⊗_R R'` is invertible at the degree-zero complex on `ULift A`.  This is the
  K-flatness side condition of `Dualizing.derivedBaseChangeAlgebraIso`, which that definition
  proves internally and therefore did not expose.
* `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_comparison` — the isomorphism *is* the comparison
  of Stacks 0661 at the image under `DerivedCategory.Q` of the degree-zero complex on `ULift A`,
  pre- and post-composed with canonical isomorphisms.
* `Dualizing.derivedBaseChangeAlgebraIso_hom_eq` — **the computation**: the derived comparison is
  eliminated in favour of the underived one.
* `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` — the same, with `comparisonR` evaluated
  at the degree-zero complex on `A` viewed as an `R`-module rather than at the restriction of
  scalars of a complex, so that the only remaining derived input over `R` is the counit at a
  single complex.

## Implementation notes

The one step that looked like an obstruction is free.  Crossing between
`DerivedCategory.singleFunctor C n` and `CochainComplex.singleFunctor C n ⋙ DerivedCategory.Q` is
Mathlib's `CategoryTheory.DerivedCategory.singleFunctorIsoCompQ`, which is `Iso.refl` — the
derived single functors are *defined* as the postcomposition of the cochain-complex ones with
`DerivedCategory.Q` — so `rfl` moves between the two spellings, and
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_comparison` is a single `rfl`.  The statements here
spell the single complex as `HomologicalComplex.single _ (ComplexShape.up ℤ) 0` rather than as
`CochainComplex.singleFunctor _ 0`, because that is the spelling in which Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`
— the lemma that fuses the two leading factors into one `DerivedCategory.Q.map` — states its
left-hand side.

The two `IsLeftDerivedFunctor` arguments are instance binders, as in
`StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations` and for the same reason: the
statements name `RingTheory.TorIndependence.derivedBaseChangeComparison`, whose signature takes
them as instances.  The two `Functor.IsLeftAdjoint` side conditions of that signature are
discharged by `ModuleCat.extendRestrictScalarsAdj`; they have to be supplied with their module
universe written out, since universe unification does not solve `max uRp ?u =?= max v uR uA uRp`.

No `@[stacks]` attribute is placed here: this is computational infrastructure for the proof of
Stacks 0E2A, not a statement of it.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extension of scalars along a ring homomorphism `f : S →+* T` is an additive functor. -/
local instance {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T) :
    (ModuleCat.extendScalars.{uS, uT, w} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]

/-- The counit of derived extension of scalars along `A → A ⊗_R R'` is invertible at the
degree-zero complex on `ULift A`: that complex is flat over `A` in every degree, hence K-flat.
This is the side condition that `Dualizing.derivedBaseChangeAlgebraIso` discharges internally. -/
theorem isIso_comparison_app_single_algebra :
    IsIso (comparisonA.app
      ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) := by
  let UA : ModuleCat.{max v uR uA uRp} A := ModuleCat.of A (ULift.{max v uR uA uRp} A)
  let X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{max v uR uA uRp} A) 0).obj UA
  have hflat : ∀ n : ℤ, Module.Flat A (X.X n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 UA).toLinearEquiv
    · have : Subsingleton (X.X n) := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 UA n hn)
      infer_instance
  exact @CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{uA,
      max uA uRp, max v uR} A (TensorProduct R A R') _ _ (algebraMap A (TensorProduct R A R')) _ _
      baseChangeA comparisonA isLeftDerivedA X (CochainComplex.KFlat.kFlat_of_flat X 0)

/-- `Dualizing.derivedBaseChangeAlgebraIso` is the comparison of Stacks 0661 at the image under
`DerivedCategory.Q` of the degree-zero complex on `ULift A`, pre- and post-composed with canonical
isomorphisms.  The passage from `DerivedCategory.singleFunctor`, in which the isomorphism is
stated, to `DerivedCategory.Q` of a single cochain complex, in which the equations of the
comparison are stated, is definitional. -/
theorem derivedBaseChangeAlgebraIso_hom_eq_comparison :
    (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).hom =
      baseChangeR.map
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategorySingleFunctor 0).inv.app
            (ModuleCat.of A (ULift.{max v uR uA uRp} A))) ≫
        (RingTheory.TorIndependence.derivedBaseChangeComparison
            (algebraMap R A) (algebraMap R R')
            (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
            ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
              (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
            baseChangeR baseChangeA comparisonR comparisonA).2.1.app
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
              (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
          (comparisonA.app
              ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A))) ≫
            DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex
                (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                  (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app
                (ModuleCat.of A (ULift.{max v uR uA uRp} A))).hom ≫
            (DerivedCategory.singleFunctor
              (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')) 0).map
              (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
                (algebraMap A (TensorProduct R A R'))).hom) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R' (TensorProduct R A R'))).mapDerivedCategorySingleFunctor 0).hom.app
          (ModuleCat.of (TensorProduct R A R')
            (ULift.{max v uR uA uRp} (TensorProduct R A R'))) :=
  rfl

/-- **The derived base change of the algebra, computed.** The opaque derived comparison of
Stacks 0661 is eliminated: what is left is the counit `comparisonR` of derived base change along
`R → R'`, the *underived* comparison — evaluated on pure tensors by
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul` — and canonical
isomorphisms. -/
theorem derivedBaseChangeAlgebraIso_hom_eq :
    (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).hom =
      baseChangeR.map (DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapCochainComplexSingleFunctor 0).inv.app
            (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
        comparisonR.app
            (((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (RingTheory.TorIndependence.derivedBaseChangeComparison
                (algebraMap R A) (algebraMap R R')
                (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
                ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
                  (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
                baseChangeR baseChangeA comparisonR comparisonA).1
              (ComplexShape.up ℤ)).app
              ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
              (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
            (DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                    (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app
                  (ModuleCat.of A (ULift.{max v uR uA uRp} A))).hom ≫
              (DerivedCategory.singleFunctor
                (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')) 0).map
                (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
                  (algebraMap A (TensorProduct R A R'))).hom) ≫
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategorySingleFunctor 0).hom.app
            (ModuleCat.of (TensorProduct R A R')
              (ULift.{max v uR uA uRp} (TensorProduct R A R'))) := by
  have := isIso_comparison_app_single_algebra.{uR, uA, uRp, v} baseChangeA comparisonA
  have : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uR, uRp}
      (algebraMap R R')).isLeftAdjoint
  have : (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
      (algebraMap A (TensorProduct R A R'))).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, max uA uRp}
      (algebraMap A (TensorProduct R A R'))).isLeftAdjoint
  rw [derivedBaseChangeAlgebraIso_hom_eq_comparison.{uR, uA, uRp, v} hTor baseChangeR comparisonR
      baseChangeA comparisonA,
    RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_eq.{uR, uA, uRp,
      max uA uRp, v} (algebraMap R A) (algebraMap R R')
      (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
      ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
        (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
      baseChangeR baseChangeA comparisonR comparisonA
      ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A (ULift.{max v uR uA uRp} A))), Functor.map_comp]
  simp only [Category.assoc, IsIso.inv_comp, IsIso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc,
    Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app,
    IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id_app (ModuleCat.restrictScalars.{max v uR uA uRp}
      (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors _)]

/-- `Dualizing.derivedBaseChangeAlgebraIso_hom_eq` with the counit `comparisonR` moved, by its own
naturality, to the degree-zero complex on `A` viewed as an `R`-module.  Over `R` the only derived
input left is that one component; everything between it and the canonical isomorphisms of
restriction of scalars along `R' → A ⊗_R R'` is `DerivedCategory.Q` of a morphism of cochain
complexes. -/
theorem derivedBaseChangeAlgebraIso_hom_eq_single :
    (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).hom =
      comparisonR.app
          ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ) 0).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).obj
              (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
        DerivedCategory.Q.map
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
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
                ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                  (ComplexShape.up ℤ) 0).obj
                  (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
              (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
                (ComplexShape.up ℤ) 0).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
            (DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                    (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app
                  (ModuleCat.of A (ULift.{max v uR uA uRp} A))).hom ≫
              (DerivedCategory.singleFunctor
                (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')) 0).map
                (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
                  (algebraMap A (TensorProduct R A R'))).hom) ≫
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R' (TensorProduct R A R'))).mapDerivedCategorySingleFunctor 0).hom.app
            (ModuleCat.of (TensorProduct R A R')
              (ULift.{max v uR uA uRp} (TensorProduct R A R'))) := by
  have hnat : (DerivedCategory.Q ⋙ baseChangeR).map
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapCochainComplexSingleFunctor 0).inv.app
            (ModuleCat.of A (ULift.{max v uR uA uRp} A))) ≫
        comparisonR.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A)
              (ComplexShape.up ℤ) 0).obj (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) =
      comparisonR.app
          ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ) 0).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).obj
              (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≫
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q).map
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapCochainComplexSingleFunctor 0).inv.app
            (ModuleCat.of A (ULift.{max v uR uA uRp} A))) :=
    comparisonR.naturality _
  rw [derivedBaseChangeAlgebraIso_hom_eq.{uR, uA, uRp, v} hTor baseChangeR comparisonR
      baseChangeA comparisonA,
    ← Category.assoc, ← Functor.comp_map DerivedCategory.Q baseChangeR, hnat, Category.assoc,
    Functor.comp_map, ← Functor.map_comp_assoc]

end Dualizing

end
