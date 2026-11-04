module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologySingleTor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTorSmul

/-!
# The right tensor factor acts on the bridge by functoriality of `Tor` in its first variable

Let `R → A` and `R → R'` be homomorphisms of commutative rings and `M` an `A`-module.
`RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor` identifies the degree `-i`
cohomology of the derived base change of `M[0]` with `Tor_i^R(R', M)`, and
`RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor_includeLeft_smul` says that the left
tensor factor `A` of `A ⊗_R R'` acts through functoriality of `Tor_i^R(R', ·)` in its *second*
variable. This file supplies the other half: the right tensor factor `R'` acts through
functoriality of `Tor_i^R(·, M)` in its *first* variable, at multiplication by `r` on `R'`. With
both halves the bridge is `A ⊗_R R'`-linear.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor_includeRight_smul`: **the bridge
  carries the action of `Algebra.TensorProduct.includeRight r` to `Tor_i^R(·, M)` applied to
  multiplication by `r` on `R'`.**

## Implementation notes

`RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul` identifies the action of
`Algebra.TensorProduct.includeRight r` with the ambient `R'`-action, so what has to be shown is
that the bridge is `R'`-linear for that ambient action, the `R'`-action on the `Tor` side being
`RingTheory.TorIndependence.mulByAlg`. Of the two factors of the bridge, the first is
restriction of scalars applied to a morphism of `ModuleCat R'` and so commutes with a scalar
multiple of an identity for formal reasons; the second is
`RingTheory.TorIndependence.derivedExtensionSingleIsoTor`, whose compatibility is
`RingTheory.TorIndependence.derivedExtensionSingleIsoTor_smul`. That one rests on
`CategoryTheory.NatTrans.leftDerived_smul_id`: the ambient `R'`-action on the left derived
functor of extension of scalars is the left derived functor of `r • 𝟙`, which is what a
projective resolution compares with the `Tor` side.

The model of the derived category stays a free `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]`
binder for each of the three rings, and `totalDerivedExtensionScalars` is written with all five
universe arguments explicit, as in the files this one builds on.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u w

namespace RingTheory.TorIndependence

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- The component of `RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor` at `M`: the
identification of restriction of scalars with the single-object functor, then the bridge of
`RingTheory.TorIndependence.derivedExtensionSingleIsoTor` at `M` read over `R`. -/
theorem baseChangeCohomologySingleIsoTor_hom_app (i : ℕ) (M : ModuleCat.{u} A) :
    (baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M =
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (((totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map
            (((ModuleCat.restrictScalars.{u, u, u}
              (algebraMap R A)).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
        (derivedExtensionSingleIsoTor (R := R) (R' := R') i).hom.app
          ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj M) :=
  rfl

/-- **The bridge at an `A`-module carries the ambient `R'`-action to functoriality of `Tor` in
its first variable.** -/
theorem baseChangeCohomologySingleIsoTor_smul (i : ℕ) (M : ModuleCat.{u} A) (r : R') :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 (baseChangeCohomologyOverBase (R := R) (R' := R')
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ)))) ≫
        (baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M =
      (baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M ≫
        ((Tor (ModuleCat.{u} R) i).map (mulByAlg (R := R) r)).app
          ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj M) := by
  have hsq : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 (baseChangeCohomologyOverBase (R := R) (R' := R')
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ)))) ≫
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (((totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map
            (((ModuleCat.restrictScalars.{u, u, u}
              (algebraMap R A)).mapDerivedCategorySingleFunctor 0).hom.app M)) =
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (((totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map
            (((ModuleCat.restrictScalars.{u, u, u}
              (algebraMap R A)).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
            (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).obj
                ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj M))) :=
    Functor.map_smul_id_comp _ _ r
  rw [baseChangeCohomologySingleIsoTor_hom_app, ← Category.assoc, hsq, Category.assoc,
    derivedExtensionSingleIsoTor_smul, ← Category.assoc]
  rfl

/-- **The right tensor factor acts by functoriality of `Tor` in its first variable.** -/
theorem baseChangeCohomologySingleIsoTor_includeRight_smul (i : ℕ) (M : ModuleCat.{u} A)
    (r : R')
    (m : baseChangeCohomology (R := R) (R' := R')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ))) :
    ((baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M).hom
        ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
      (((Tor (ModuleCat.{u} R) i).map (mulByAlg (R := R) r)).app
          ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj M)).hom
        (((baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M).hom m) := by
  have hel := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (baseChangeCohomologySingleIsoTor_smul (R := R) (R' := R') i M r)) m
  exact (congrArg _ (baseChangeCohomology_includeRight_smul (R := R) (R' := R')
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ)) r m)).trans hel

end RingTheory.TorIndependence

end
