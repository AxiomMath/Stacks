module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Augmentation
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Local cohomology is naturally the Čech object

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `R`. Local cohomology
`RΓ_{V(I)}` is the right adjoint of the inclusion of the complexes with `I`-power-torsion
cohomology (Stacks 0A6Q), and the extended alternating Čech complex `C^•(f₁, …, f_r; M)` has the
same universal property relative to its augmentation onto `M` (Stacks 0A6R, proved in
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`). Two objects with the same universal
property are isomorphic, and the isomorphism is *unique* subject to compatibility with the two
structure maps; uniqueness turns it into a natural isomorphism of functors, which is what
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean` leaves open (its comparison is produced
for one module at a time, as a `Nonempty`).

The argument is the standard one for coreflections. Composing with the counit is a bijection
`Hom(W, RΓ_{V(I)}(X)) ≅ Hom(W, X)` for every torsion `W`, by the adjunction; composing with the
augmentation is a bijection `Hom(W, C^•(f; M)) ≅ Hom(W, M⟦0⟧)`, by the Čech model. Each of
`RΓ_{V(I)}(M⟦0⟧)` and `C^•(f; M)` is torsion, so each bijection produces a map to the other object,
the two composites are the identity because they are so after composing with the structure maps,
and naturality holds because both sides of the square agree after composing with the augmentation.

## Main definitions

* `Stacks.LocalCohomology.cechComparisonHom`, `Stacks.LocalCohomology.cechComparisonInv` — the
  comparison maps between `RΓ_{V(I)}(M⟦0⟧)` and the Čech object.
* `Stacks.LocalCohomology.localCohomologyIsoCech` — **the natural isomorphism**
  `RΓ_{V(I)}(-⟦0⟧) ≅ C^•(f₁, …, f_r; -)` of functors from `R`-modules to `D(R)`.

## Main results

* `Stacks.LocalCohomology.bijective_comp_localCohomologyCounit` — composing with the counit of
  Stacks 0A6Q is a bijection on morphisms out of a torsion object.
* `Stacks.LocalCohomology.localCohomologyIsoCech_hom_app_comp_augmentation` — the comparison is
  compatible with the counit and the augmentation, which is what pins it down.

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

/-! ### The universal property of the counit -/

/-- **The universal property of local cohomology (Stacks 0A6Q).** For an object `W` of `D(R)`
with `I`-power-torsion cohomology, composing with the counit identifies the morphisms from `W` to
`RΓ_{V(I)}(X)` with the morphisms from `W` to `X`. This is the adjunction, transported through the
full faithfulness of the inclusion of the torsion subcategory. -/
theorem bijective_comp_localCohomologyCounit
    (X W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun h : W ⟶ (Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj X) =>
      h ≫ (Dualizing.localCohomologyAdjunction R I hI).counit.app X) := by
  set P := Dualizing.derivedPowerTorsionProperty R I hI with hP
  set adj := Dualizing.localCohomologyAdjunction R I hI with hadj
  set Z := (Dualizing.localCohomologyFunctor R I hI).obj X with hZ
  have hfull : Function.Bijective
      (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g) :=
    P.fullyFaithfulι.homEquiv.bijective
  have hcomp : Function.Bijective
      (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g ≫ adj.counit.app X) := by
    have heq : (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g ≫ adj.counit.app X) =
        (adj.homEquiv ⟨W, hW⟩ X).symm := by
      funext g
      exact (adj.homEquiv_counit _ _ g).symm
    rw [heq]
    exact (adj.homEquiv ⟨W, hW⟩ X).symm.bijective
  exact (hfull.of_comp_iff _).mp hcomp

/-- The counit of the local-cohomology adjunction of Stacks 0A6Q, as a natural transformation
between functors on modules. -/
def localCohomologyCounit :
    localCohomologyOnModules.{u, max u v} R I hI ⟶
      DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0 where
  app M := (Dualizing.localCohomologyAdjunction R I hI).counit.app
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
  naturality _ _ g := (Dualizing.localCohomologyAdjunction R I hI).counit.naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).map g)

/-- At each module the transformation is the counit of the local-cohomology adjunction. -/
@[simp] theorem localCohomologyCounit_app (M : ModuleCat.{max u v} R) :
    (localCohomologyCounit.{v} I hI).app M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) :=
  rfl

/-- The Čech augmentation's universal property, phrased for the functor of
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/CechFunctor.lean`. -/
theorem bijective_comp_cechAugmentationHom_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) (W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun g : W ⟶ (extendedCechObjectFunctor.{v} f).obj M =>
      g ≫ (cechAugmentationHom.{v} f).app M) :=
  bijective_comp_extendedCechAugmentationHom f M I hI hIf W hW

/-- The universal property of the counit at a module placed in degree zero, phrased for the
functor `Stacks.LocalCohomology.localCohomologyOnModules`. -/
theorem bijective_comp_localCohomologyCounit_app (M : ModuleCat.{max u v} R)
    (W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun h : W ⟶ (localCohomologyOnModules R I hI).obj M =>
      h ≫ (localCohomologyCounit.{v} I hI).app M) :=
  bijective_comp_localCohomologyCounit I hI _ W hW

/-- Local cohomology of a module, viewed in `D(R)`, has `I`-power-torsion cohomology. -/
theorem derivedPowerTorsionProperty_localCohomologyOnModules (M : ModuleCat.{max u v} R) :
    Dualizing.derivedPowerTorsionProperty R I hI
      ((localCohomologyOnModules R I hI).obj M) :=
  ((Dualizing.localCohomologyFunctor R I hI).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).property

/-! ### The comparison maps -/

/-- The comparison from local cohomology to the Čech object: the unique map whose composite with
the augmentation is the counit. -/
def cechComparisonHom (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{max u v} R) :
    (localCohomologyOnModules R I hI).obj M ⟶ (extendedCechObjectFunctor.{v} f).obj M :=
  (Equiv.ofBijective _ (bijective_comp_cechAugmentationHom_app f I hI hIf M
      ((localCohomologyOnModules R I hI).obj M)
      (derivedPowerTorsionProperty_localCohomologyOnModules I hI M))).symm
    ((localCohomologyCounit.{v} I hI).app M)

/-- The comparison composed with the augmentation is the counit, which characterizes it. -/
@[simp] theorem cechComparisonHom_comp_augmentation (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) :
    cechComparisonHom f I hI hIf M ≫ (cechAugmentationHom.{v} f).app M =
      (localCohomologyCounit.{v} I hI).app M :=
  (Equiv.ofBijective _ (bijective_comp_cechAugmentationHom_app f I hI hIf M
    ((localCohomologyOnModules R I hI).obj M)
    (derivedPowerTorsionProperty_localCohomologyOnModules I hI M))).apply_symm_apply _

/-- The comparison from the Čech object to local cohomology: the unique map whose composite with
the counit is the augmentation. -/
def cechComparisonInv (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{max u v} R) :
    (extendedCechObjectFunctor.{v} f).obj M ⟶ (localCohomologyOnModules R I hI).obj M :=
  (Equiv.ofBijective _ (bijective_comp_localCohomologyCounit_app I hI M
      ((extendedCechObjectFunctor.{v} f).obj M)
      (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf))).symm
    ((cechAugmentationHom.{v} f).app M)

/-- The comparison composed with the counit is the augmentation, which characterizes it. -/
@[simp] theorem cechComparisonInv_comp_counit (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) :
    cechComparisonInv f I hI hIf M ≫ (localCohomologyCounit.{v} I hI).app M =
      (cechAugmentationHom.{v} f).app M :=
  (Equiv.ofBijective _ (bijective_comp_localCohomologyCounit_app I hI M
    ((extendedCechObjectFunctor.{v} f).obj M)
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf))).apply_symm_apply _

/-! ### The natural isomorphism -/

/-- **Local cohomology is naturally the Čech object.** For an ideal `I = (f₁, …, f_r)` of `R`, the
functor sending an `R`-module `M` to `RΓ_{V(I)}(M⟦0⟧)` is naturally isomorphic to the functor
sending `M` to the extended alternating Čech complex `C^•(f₁, …, f_r; M)`, viewed in `D(R)`.

This upgrades `nonempty_localCohomology_iso_extendedCechObject`, which produces an isomorphism at
each module separately, to a natural one: the comparison is unique subject to carrying the counit
to the augmentation, and uniqueness forces naturality. -/
def localCohomologyIsoCech (hIf : Ideal.span (Set.range f) = I) :
    localCohomologyOnModules.{u, max u v} R I hI ≅ extendedCechObjectFunctor.{v} f where
  hom :=
    { app M := cechComparisonHom f I hI hIf M
      naturality {M N} g := by
        refine (bijective_comp_cechAugmentationHom_app f I hI hIf N
          ((localCohomologyOnModules R I hI).obj M)
          (derivedPowerTorsionProperty_localCohomologyOnModules I hI M)).injective ?_
        rw [Category.assoc, cechComparisonHom_comp_augmentation,
          (localCohomologyCounit.{v} I hI).naturality g, Category.assoc,
          (cechAugmentationHom.{v} f).naturality g, ← Category.assoc,
          cechComparisonHom_comp_augmentation] }
  inv :=
    { app M := cechComparisonInv f I hI hIf M
      naturality {M N} g := by
        refine (bijective_comp_localCohomologyCounit_app I hI N
          ((extendedCechObjectFunctor.{v} f).obj M)
          (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)).injective ?_
        rw [Category.assoc, cechComparisonInv_comp_counit,
          (cechAugmentationHom.{v} f).naturality g, Category.assoc,
          (localCohomologyCounit.{v} I hI).naturality g, ← Category.assoc,
          cechComparisonInv_comp_counit] }
  hom_inv_id := by
    refine NatTrans.ext (funext fun M => ?_)
    refine (bijective_comp_localCohomologyCounit_app I hI M
      ((localCohomologyOnModules R I hI).obj M)
      (derivedPowerTorsionProperty_localCohomologyOnModules I hI M)).injective ?_
    rw [NatTrans.comp_app, NatTrans.id_app, Category.assoc, cechComparisonInv_comp_counit,
      cechComparisonHom_comp_augmentation, Category.id_comp]
  inv_hom_id := by
    refine NatTrans.ext (funext fun M => ?_)
    refine (bijective_comp_cechAugmentationHom_app f I hI hIf M
      ((extendedCechObjectFunctor.{v} f).obj M)
      (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)).injective ?_
    rw [NatTrans.comp_app, NatTrans.id_app, Category.assoc,
      cechComparisonHom_comp_augmentation, cechComparisonInv_comp_counit, Category.id_comp]

/-- The components of the natural isomorphism are the comparison maps. -/
@[simp] theorem localCohomologyIsoCech_hom_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) :
    (localCohomologyIsoCech.{v} f I hI hIf).hom.app M = cechComparisonHom f I hI hIf M := rfl

/-- The components of the inverse natural isomorphism are the comparison maps. -/
@[simp] theorem localCohomologyIsoCech_inv_app (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) :
    (localCohomologyIsoCech.{v} f I hI hIf).inv.app M = cechComparisonInv f I hI hIf M := rfl

/-- The natural comparison carries the counit of Stacks 0A6Q to the Čech augmentation. -/
theorem localCohomologyIsoCech_hom_app_comp_augmentation (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} R) :
    (localCohomologyIsoCech.{v} f I hI hIf).hom.app M ≫ extendedCechAugmentationHom f M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) :=
  cechComparisonHom_comp_augmentation f I hI hIf M

end Stacks.LocalCohomology

end
