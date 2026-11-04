module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The pullback-tensor comparison along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
There are two canonical isomorphisms attached to the pair.  One is the comparison of Stacks
01CD, `h^*(A ⊗_{𝒪_Z} B) ≅ h^*A ⊗ h^*B`, which exists for each of `f`, `g` and `f ≫ g`.  The
other is the composition law for pullback, `g^* ⋙ f^* ≅ (f ≫ g)^*`.  This file proves that the
two are compatible: reading the comparison for `f ≫ g` is the same as reading the comparison
for `g`, then the comparison for `f`, and then the composition law in each tensor factor.

This is the coherence the derived statements need.  Stacks 079U is built by descending the
comparison of Stacks 01CD along total tensor complexes and the K-flat localization, and Stacks
0D5S is built from the composition law; the compatibility of the two *derived* isomorphisms is
proved by reducing to K-flat representatives, where it becomes the compatibility of the total
complexes, which in turn is this statement degree by degree.

## Main results

* `Stacks.PullbackTensorComposition.comparison_comp`: **the comparison of Stacks 01CD is
  compatible with the composition law for pullback.**
* `Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit`: the composition law
  for pullback, read on the pullback-unit image of a local section: it carries the pullback-unit
  image along `f` of the pullback-unit image along `g` to the pullback-unit image along `f ≫ g`.
* `Stacks.PullbackTensorComposition.modulePullbackComp_unit`: the same statement before passing to
  sections, as a compatibility of the units of the three adjunctions.

## Implementation notes

*Which composition law.*  The tree carries two pullback-composition isomorphisms:
`RingedSpaceModuleAdjunction.modulePullbackComp`, which is Mathlib's for sheaves of
modules on a site, and `Stacks.DerivedPullback.Composition.modulePullbackComp`, which is built by
`CategoryTheory.Adjunction.leftAdjointCompIso` from
`RingedSpaceModuleAdjunction.modulePushforwardComp` and is the one Stacks 0D5S is stated
about.  Everything here is about the second: it is the one that appears in
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`.

*Why the unit is the handle.*  The composition law is produced by uniqueness of left adjoints, so
there is no formula for its underlying maps on sections; the only description available is the
mate correspondence, `CategoryTheory.unit_conjugateEquiv_symm`.  Read at a local section that
correspondence *is* the statement about pullback-unit images, because the components of
`modulePushforwardComp` are identity morphisms and pushforward does not change the underlying
maps on sections, only the opens indexing them.  Both of those are `rfl`, which is why
`modulePullbackComp_hom_app_pullbackUnit` follows from `modulePullbackComp_unit` by `congrArg`
alone.

*The extensionality principle is duplicated, not shared.*
`Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext` is the same statement at the monoidal
spelling of Tag 01CA, under a monoidal structure that file registers only as a local instance.
Rather than de-privatise or globalise anything, the principle is restated here at the
`Stacks.RingedSpace.tensorSheaf` spelling that `Stacks.RingedSpace.comparison` is written at, as
a `private` lemma with the same two-line proof.

*Computing on sections without rewriting.*  The section equations are applied to their opens
and sections explicitly, transported through each subsequent map by `congrArg`, and composed
by transitivity. This avoids rewriting across the definitionally equal presentations of opens
under a composite and under successive inverse images. The last tensor comparison uses
`congrArg₂` on the two fully applied pullback-unit equations.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace

open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorComposition

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf TopCat.Sheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  PresheafOfModules.tensorObj Stacks.SheafOfModules.Tensor.sheafTensor
  _root_.SheafOfModules.forget PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Two morphisms out of the pullback of a tensor product of sheaves of modules which agree on
the pullback-unit images of the local pure tensors are equal.

This is `Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext` restated at the
`Stacks.RingedSpace.tensorSheaf` spelling, which is the one
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul` is written at; that declaration is stated
at the monoidal spelling of Tag 01CA, whose monoidal structure is only a local instance there. -/
private lemma pullback_tensorSheaf_hom_ext {W : RingedSpace.{u, u}} (h : W ⟶ Z)
    {A B : SheafOfModules.{u} (structureRingSheaf Z)}
    {N : SheafOfModules.{u} (structureRingSheaf W)}
    {θ₁ θ₂ : (pullbackFunctor h).obj
      (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, B)) ⟶ N}
    (hyp : ∀ (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      θ₁.val.app ((opensMap h).op.obj U)
          (pullbackUnit h (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, B)) U
            (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (Z))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app
                  (PresheafOfModules.tensorObj (O := (Z).presheaf) (A).val (B).val)).app
                    U (a ⊗ₜ b))) =
        θ₂.val.app ((opensMap h).op.obj U)
          (pullbackUnit h (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, B)) U
            (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (Z))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app
                  (PresheafOfModules.tensorObj (O := (Z).presheaf) (A).val (B).val)).app
                    U (a ⊗ₜ b)))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction h).homEquiv (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, B))
      N).injective ?_
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Z.sheaf) (F := A) (G := B)
    (Q := (pushforwardFunctor h).obj N) fun U a b ↦ ?_
  exact (homEquiv_val_app h _ _ θ₁ U _).trans
    ((hyp U a b).trans (homEquiv_val_app h _ _ θ₂ U _).symm)

/-- **The composition law for pullback, on the units of the three adjunctions.**  The unit of
`(f ≫ g)^* ⊣ (f ≫ g)_*`, followed by the pushforward composition isomorphism, is the unit of
`g^* ⊣ g_*` followed by the pushforward along `g` of the unit of `f^* ⊣ f_*`, followed by the
composition law for pullback.

`Stacks.DerivedPullback.Composition.modulePullbackComp` is
`CategoryTheory.Adjunction.leftAdjointCompIso` applied to the pushforward composition
isomorphism, so this is `CategoryTheory.unit_conjugateEquiv_symm` for the mate correspondence
that definition is made by. -/
theorem modulePullbackComp_unit (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (RingedSpaceModuleAdjunction.modulePushforwardComp f g).inv.app
          ((modulePullback (f ≫ g)).obj M) =
      ((modulePullbackPushforwardAdjunction g).comp
            (modulePullbackPushforwardAdjunction f)).unit.app M ≫
        (modulePushforward f ⋙ modulePushforward g).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M) := by
  have h := CategoryTheory.unit_conjugateEquiv_symm
    (modulePullbackPushforwardAdjunction (f ≫ g))
    ((modulePullbackPushforwardAdjunction g).comp (modulePullbackPushforwardAdjunction f))
    (RingedSpaceModuleAdjunction.modulePushforwardComp f g).inv M
  rw [Stacks.DerivedPullback.Composition.modulePullbackComp, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]
  exact h

/-- **The composition law for pullback, on a pullback-unit image.**  It carries the pullback-unit
image along `f` of the pullback-unit image along `g` of a local section of `M` to the
pullback-unit image along `f ≫ g` of that section.

This is `modulePullbackComp_unit` read at a local section: the components of the pushforward
composition isomorphism are identity morphisms and pushforward acts on sections by the identity,
reindexing only the opens, so both passages are `rfl`. -/
theorem modulePullbackComp_hom_app_pullbackUnit
    (M : SheafOfModules.{u} (structureRingSheaf Z)) (U : (Opens Z.carrier)ᵒᵖ)
    (x : M.val.obj U) :
    ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M).val.app
        ((opensMap f).op.obj ((opensMap g).op.obj U))
        (pullbackUnit f ((pullbackFunctor g).obj M) ((opensMap g).op.obj U)
          (pullbackUnit g M U x)) =
      pullbackUnit (f ≫ g) M U x :=
  (congrArg (fun k : M ⟶ (modulePushforward f ⋙ modulePushforward g).obj
      ((modulePullback (f ≫ g)).obj M) => k.val.app U x)
    (modulePullbackComp_unit f g M)).symm

/-- **The comparison of Stacks 01CD is compatible with the composition law for pullback.**  For
sheaves of `𝒪_Z`-modules `A` and `B`, the composition law
`f^*g^*(A ⊗ B) ⟶ (f ≫ g)^*(A ⊗ B)` followed by the comparison for `f ≫ g` is the pullback along
`f` of the comparison for `g`, followed by the comparison for `f`, followed by the composition
law in each tensor factor.

Both sides are morphisms out of a pullback of a tensor product, so they are determined by their
values on the pullback-unit images of the local pure tensors; there the comparison is
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul` and the composition law is
`modulePullbackComp_hom_app_pullbackUnit`. -/
theorem comparison_comp (A B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, B)) ≫
        comparison (f ≫ g) A B =
      (pullbackFunctor f).map (comparison g A B) ≫
        comparison f ((pullbackFunctor g).obj A) ((pullbackFunctor g).obj B) ≫
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            (((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app A,
              (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app B) :
              (((pullbackFunctor f).obj ((pullbackFunctor g).obj A),
                (pullbackFunctor f).obj ((pullbackFunctor g).obj B)) : _ × _) ⟶
                ((pullbackFunctor (f ≫ g)).obj A, (pullbackFunctor (f ≫ g)).obj B)) := by
  refine ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).app
    (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj
        (A, B))).eq_inv_comp.mp ?_
  refine pullback_tensorSheaf_hom_ext (f ≫ g) fun U a b ↦ ?_
  have mappedUnit := fun x ↦
    (congrArg (((pullbackFunctor f).map (comparison g A B)).val.app
        ((opensMap f).op.obj ((opensMap g).op.obj U)))
      ((congrArg (((Stacks.DerivedPullback.Composition.modulePullbackComp f g).app
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj
            (A, B))).inv.val.app ((opensMap f).op.obj ((opensMap g).op.obj U)))
        (modulePullbackComp_hom_app_pullbackUnit f g _ U x).symm).trans
        (Stacks.SheafOfModules.inv_val_app_hom_val_app _ _ _))).trans
      (pullbackUnit_naturality f (comparison g A B) _ _)
  have comparedUnit :=
    (congrArg ((comparison f ((pullbackFunctor g).obj A) ((pullbackFunctor g).obj B)).val.app
        ((opensMap f).op.obj ((opensMap g).op.obj U)))
      (mappedUnit _)).trans
      ((congrArg (fun value => (comparison f ((pullbackFunctor g).obj A)
          ((pullbackFunctor g).obj B)).val.app ((opensMap f).op.obj ((opensMap g).op.obj U))
          (pullbackUnit f _ ((opensMap g).op.obj U) value))
        (comparison_pullbackUnit_unit_tmul g A B U a b)).trans
        (comparison_pullbackUnit_unit_tmul f _ _ _ _ _))
  have tensorComparedUnit :=
    (congrArg (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app A,
              (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app B)).val.app
          ((opensMap f).op.obj ((opensMap g).op.obj U))) comparedUnit).trans
      ((tensorSheaf_map_unit_tmul X _ _ _ _ _).trans
        (congrArg₂ (fun leftValue rightValue => ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
                (PresheafOfModules.tensorObj (O := X.sheaf.obj)
                  ((modulePullback (f ≫ g)).obj A).val
                  ((modulePullback (f ≫ g)).obj B).val)).app
              ((opensMap f).op.obj ((opensMap g).op.obj U)) (leftValue ⊗ₜ rightValue))
          (modulePullbackComp_hom_app_pullbackUnit f g A U a)
          (modulePullbackComp_hom_app_pullbackUnit f g B U b)))
  exact (comparison_pullbackUnit_unit_tmul (f ≫ g) A B U a b).trans tensorComparedUnit.symm

end Stacks.PullbackTensorComposition

end
