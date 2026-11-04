module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.Augmentation
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Local cohomology is naturally the small Čech object, in a free module universe

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `R` in `Type u`. Local
cohomology `RΓ_{V(I)}` on `D(ModuleCat.{v} R)` is the right adjoint of the inclusion of the
complexes with `I`-power-torsion cohomology (Stacks 0A6Q), and
`StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/Augmentation.lean` gives the small model
`Cech.extendedCechComplexShrink` the same universal property relative to its augmentation onto
`M`. Uniqueness of a coreflection therefore identifies the two, *naturally in `M`*, with the
module universe `v` independent of the ring universe `u`.

This is `StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Comparison.lean` with the
constraint `ModuleCat.{max u v}` removed. The argument is purely formal — the comparison is
unique subject to carrying the counit to the augmentation, and uniqueness forces naturality — so
nothing beyond the two universal properties is used.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyCounitShrink` — the counit of Stacks 0A6Q as a natural
  transformation between functors on `ModuleCat.{v} R`.
* `Stacks.LocalCohomology.cechComparisonHomShrink`,
  `Stacks.LocalCohomology.cechComparisonInvShrink` — the two comparison maps.
* `Stacks.LocalCohomology.localCohomologyIsoCechShrink` — **the natural isomorphism
  `RΓ_{V(I)}(M⟦0⟧) ≅ C^•(f₁, …, f_r; M)` at a module universe independent of the ring
  universe.**

## Main results

* `Stacks.LocalCohomology.localCohomologyIsoCechShrink_hom_app_comp_augmentation` — the natural
  comparison carries the counit of Stacks 0A6Q to the Čech augmentation.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R) (hI : I.FG)

/-! ### The counit as a natural transformation -/

/-- The counit of the local-cohomology adjunction of Stacks 0A6Q, as a natural transformation
between functors on `ModuleCat.{v} R` with `v` independent of the ring universe. -/
def localCohomologyCounitShrink :
    localCohomologyOnModules.{u, v} R I hI ⟶
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 where
  app M := (Dualizing.localCohomologyAdjunction R I hI).counit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)
  naturality _ _ g := (Dualizing.localCohomologyAdjunction R I hI).counit.naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map g)

/-- At each module the transformation is the counit of the local-cohomology adjunction. -/
@[simp] theorem localCohomologyCounitShrink_app (M : ModuleCat.{v} R) :
    (localCohomologyCounitShrink.{v} I hI).app M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) :=
  rfl

/-- Local cohomology of a module, viewed in `D(R)`, has `I`-power-torsion cohomology. -/
theorem derivedPowerTorsionProperty_localCohomologyOnModulesShrink (M : ModuleCat.{v} R) :
    Dualizing.derivedPowerTorsionProperty R I hI
      ((localCohomologyOnModules.{u, v} R I hI).obj M) :=
  ((Dualizing.localCohomologyFunctor R I hI).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).property

/-- The universal property of the small Čech augmentation, phrased for its functor. -/
theorem bijective_comp_cechAugmentationHomShrink_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{v} R) (W : DerivedCategory (ModuleCat.{v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun g : W ⟶ (extendedCechObjectFunctorShrink.{v} f).obj M =>
      g ≫ (cechAugmentationHomShrink.{v} f).app M) :=
  bijective_comp_extendedCechAugmentationHomShrink.{v} f I hI M hIf W hW

/-- The universal property of the counit at a module placed in degree zero, phrased for the
functor `Stacks.LocalCohomology.localCohomologyOnModules`. -/
theorem bijective_comp_localCohomologyCounitShrink_app (M : ModuleCat.{v} R)
    (W : DerivedCategory (ModuleCat.{v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun h : W ⟶ (localCohomologyOnModules.{u, v} R I hI).obj M =>
      h ≫ (localCohomologyCounitShrink.{v} I hI).app M) :=
  bijective_comp_localCohomologyCounitShrink.{v} I hI _ W hW

/-! ### The comparison maps -/

/-- The comparison from local cohomology to the small Čech object: the unique map whose composite
with the augmentation is the counit. -/
def cechComparisonHomShrink (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{v} R) :
    (localCohomologyOnModules.{u, v} R I hI).obj M ⟶
      (extendedCechObjectFunctorShrink.{v} f).obj M :=
  (Equiv.ofBijective _ (bijective_comp_cechAugmentationHomShrink_app.{v} f I hI hIf M
      ((localCohomologyOnModules.{u, v} R I hI).obj M)
      (derivedPowerTorsionProperty_localCohomologyOnModulesShrink.{v} I hI M))).symm
    ((localCohomologyCounitShrink.{v} I hI).app M)

/-- The comparison composed with the augmentation is the counit, which characterizes it. -/
@[simp] theorem cechComparisonHomShrink_comp_augmentation (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{v} R) :
    cechComparisonHomShrink.{v} f I hI hIf M ≫ (cechAugmentationHomShrink.{v} f).app M =
      (localCohomologyCounitShrink.{v} I hI).app M :=
  (Equiv.ofBijective _ (bijective_comp_cechAugmentationHomShrink_app.{v} f I hI hIf M
    ((localCohomologyOnModules.{u, v} R I hI).obj M)
    (derivedPowerTorsionProperty_localCohomologyOnModulesShrink.{v} I hI M))).apply_symm_apply _

/-- The comparison from the small Čech object to local cohomology: the unique map whose composite
with the counit is the augmentation. -/
def cechComparisonInvShrink (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{v} R) :
    (extendedCechObjectFunctorShrink.{v} f).obj M ⟶
      (localCohomologyOnModules.{u, v} R I hI).obj M :=
  (Equiv.ofBijective _ (bijective_comp_localCohomologyCounitShrink_app.{v} I hI M
      ((extendedCechObjectFunctorShrink.{v} f).obj M)
      (derivedPowerTorsionProperty_extendedCechObjectShrink.{v} f I hI M hIf))).symm
    ((cechAugmentationHomShrink.{v} f).app M)

/-- The comparison composed with the counit is the augmentation, which characterizes it. -/
@[simp] theorem cechComparisonInvShrink_comp_counit (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{v} R) :
    cechComparisonInvShrink.{v} f I hI hIf M ≫ (localCohomologyCounitShrink.{v} I hI).app M =
      (cechAugmentationHomShrink.{v} f).app M :=
  (Equiv.ofBijective _ (bijective_comp_localCohomologyCounitShrink_app.{v} I hI M
    ((extendedCechObjectFunctorShrink.{v} f).obj M)
    (derivedPowerTorsionProperty_extendedCechObjectShrink.{v} f I hI M hIf))).apply_symm_apply _

/-! ### The natural isomorphism -/

/-- **Local cohomology is naturally the small Čech object, at a module universe independent of
the ring universe.** For an ideal `I = (f₁, …, f_r)` of `R`, the functor sending an `R`-module
`M` in `Type v` to `RΓ_{V(I)}(M⟦0⟧)` is naturally isomorphic to the functor sending `M` to the
small model of the extended alternating Čech complex `C^•(f₁, …, f_r; M)`, viewed in `D(R)`.

This is `Stacks.LocalCohomology.localCohomologyIsoCech` with the constraint
`ModuleCat.{max u v}` removed. -/
def localCohomologyIsoCechShrink (hIf : Ideal.span (Set.range f) = I) :
    localCohomologyOnModules.{u, v} R I hI ≅ extendedCechObjectFunctorShrink.{v} f where
  hom :=
    { app M := cechComparisonHomShrink.{v} f I hI hIf M
      naturality {M N} g := by
        refine (bijective_comp_cechAugmentationHomShrink_app.{v} f I hI hIf N
          ((localCohomologyOnModules.{u, v} R I hI).obj M)
          (derivedPowerTorsionProperty_localCohomologyOnModulesShrink.{v} I hI M)).injective ?_
        rw [Category.assoc, cechComparisonHomShrink_comp_augmentation,
          (localCohomologyCounitShrink.{v} I hI).naturality g, Category.assoc,
          (cechAugmentationHomShrink.{v} f).naturality g, ← Category.assoc,
          cechComparisonHomShrink_comp_augmentation] }
  inv :=
    { app M := cechComparisonInvShrink.{v} f I hI hIf M
      naturality {M N} g := by
        refine (bijective_comp_localCohomologyCounitShrink_app.{v} I hI N
          ((extendedCechObjectFunctorShrink.{v} f).obj M)
          (derivedPowerTorsionProperty_extendedCechObjectShrink.{v} f I hI M hIf)).injective ?_
        rw [Category.assoc, cechComparisonInvShrink_comp_counit,
          (cechAugmentationHomShrink.{v} f).naturality g, Category.assoc,
          (localCohomologyCounitShrink.{v} I hI).naturality g, ← Category.assoc,
          cechComparisonInvShrink_comp_counit] }
  hom_inv_id := by
    refine NatTrans.ext (funext fun M => ?_)
    refine (bijective_comp_localCohomologyCounitShrink_app.{v} I hI M
      ((localCohomologyOnModules.{u, v} R I hI).obj M)
      (derivedPowerTorsionProperty_localCohomologyOnModulesShrink.{v} I hI M)).injective ?_
    rw [NatTrans.comp_app, NatTrans.id_app, Category.assoc, cechComparisonInvShrink_comp_counit,
      cechComparisonHomShrink_comp_augmentation, Category.id_comp]
  inv_hom_id := by
    refine NatTrans.ext (funext fun M => ?_)
    refine (bijective_comp_cechAugmentationHomShrink_app.{v} f I hI hIf M
      ((extendedCechObjectFunctorShrink.{v} f).obj M)
      (derivedPowerTorsionProperty_extendedCechObjectShrink.{v} f I hI M hIf)).injective ?_
    rw [NatTrans.comp_app, NatTrans.id_app, Category.assoc,
      cechComparisonHomShrink_comp_augmentation, cechComparisonInvShrink_comp_counit,
      Category.id_comp]

/-- The components of the natural isomorphism are the comparison maps. -/
@[simp] theorem localCohomologyIsoCechShrink_hom_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{v} R) :
    (localCohomologyIsoCechShrink.{v} f I hI hIf).hom.app M =
      cechComparisonHomShrink.{v} f I hI hIf M :=
  rfl

/-- The components of the inverse natural isomorphism are the comparison maps. -/
@[simp] theorem localCohomologyIsoCechShrink_inv_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{v} R) :
    (localCohomologyIsoCechShrink.{v} f I hI hIf).inv.app M =
      cechComparisonInvShrink.{v} f I hI hIf M :=
  rfl

/-- The natural comparison carries the counit of Stacks 0A6Q to the Čech augmentation. -/
theorem localCohomologyIsoCechShrink_hom_app_comp_augmentation
    (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{v} R) :
    (localCohomologyIsoCechShrink.{v} f I hI hIf).hom.app M ≫
        extendedCechAugmentationHomShrink.{v} f M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) :=
  cechComparisonHomShrink_comp_augmentation.{v} f I hI hIf M

end Stacks.LocalCohomology

end
