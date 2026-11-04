module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of Stacks 01CD is braided

Let `f : X ⟶ Y` be a morphism of ringed spaces. `Stacks.PullbackTensorCoherence` makes `f^*` a
monoidal functor whose tensorator is the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of
[Stacks, Tag 01CD]. This file adds the remaining compatibility: the comparison also commutes
with the symmetry constraint of [Stacks, Tag 01CA], so `f^*` is a *braided* monoidal functor.

That is what makes `f^*` act on sheaves of algebras as a monoidal functor rather than merely as
a functor. `CategoryTheory.Functor.mapMon` turns a lax monoidal functor into a functor on monoid
objects, but the monoidal structure of `CategoryTheory.Mon` needs the braiding, and
`CategoryTheory.Functor.mapMon` is monoidal exactly for a lax *braided* functor. So without the
statement below the comparison of Tag 01CD is an isomorphism of sheaves of modules
`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` but not one of sheaves of algebras.

The proof is the one the rest of `Stacks.PullbackTensorCoherence` uses: both sides are morphisms
out of a pullback of a tensor product, so `Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext`
reduces the identity to the pullback-unit images of the local pure tensors, where the comparison
is computed by `Stacks.PullbackTensorCoherence.pullbackTensorComparison_pullbackUnit` and the
braiding by `Stacks.SheafOfModules.braiding_tensorSectionsAt` — it exchanges the two factors of
a local pure tensor. No tensorator of a monoidal functor is unfolded anywhere.

## Main definitions

* `Stacks.PullbackTensorCoherence.braidedCategory`: the symmetry constraint of Tag 01CA on
  sheaves of modules on a ringed space, named at the `Stacks.RingedSpace.structureRingSheaf`
  spelling of the ring sheaf so that instance search can find it, as
  `Stacks.PullbackGradedAlgebra.monoidalCategory` does for the monoidal structure.
* `Stacks.PullbackTensorCoherence.pullbackComparisonLaxBraided` and
  `pullbackComparisonBraided`: **`f^*` is a braided monoidal functor** for the monoidal
  structure whose tensorator is the comparison of Tag 01CD.

## Main results

* `Stacks.PullbackTensorCoherence.braiding_tmul`: the symmetry constraint exchanges the two
  factors of a local pure tensor, at the `tmul` spelling of this namespace.
* `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`: **the comparison of
  Stacks 01CD commutes with the symmetry constraint of Tag 01CA.**

## Implementation notes

`braidedCategory` and `symmetricCategory` here are `Stacks.SheafOfModules.Strict.braidedCategory`
and `symmetricCategory` with their two arguments supplied from the ringed space, exactly as
`Stacks.PullbackGradedAlgebra.monoidalCategory` does for the monoidal structure; they are not
new structures, and like that one they are declared local instances rather than global ones,
since a global monoidal instance on sheaves of modules would be found in every statement about
sheaves of modules, including those meaning a different tensor product.

The braided structure is stated for
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` and not for
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`: those are two monoidal structures on the
same functor which are not known to be equal, and the proof here is available only for the
first, because it is the one whose tensorator has a section formula.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules

open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The symmetry constraint of Tag 01CA on sheaves of modules on a ringed space, named at the
`Stacks.RingedSpace.structureRingSheaf` spelling of the ring sheaf, which is the spelling the
ringed-space pullback uses. Every argument is determined by the type, so unlike
`Stacks.SheafOfModules.Strict.braidedCategory` applied by hand this is found by instance
search. -/
@[instance_reducible]
noncomputable def braidedCategory (Z : RingedSpace.{u, u}) :
    BraidedCategory (SheafOfModules.{u} (structureRingSheaf Z)) :=
  Stacks.SheafOfModules.Strict.braidedCategory Z.presheaf
    (structureSheafRing Z).property

attribute [local instance] braidedCategory

/-- The symmetry constraint of Tag 01CA on sheaves of modules on a ringed space is a symmetry,
named at the `Stacks.RingedSpace.structureRingSheaf` spelling of the ring sheaf. -/
@[instance_reducible]
noncomputable def symmetricCategory (Z : RingedSpace.{u, u}) :
    SymmetricCategory (SheafOfModules.{u} (structureRingSheaf Z)) :=
  Stacks.SheafOfModules.Strict.symmetricCategory Z.presheaf
    (structureSheafRing Z).property

/-! ### The symmetry constraint on local pure tensors -/

section Sections

variable (Z : RingedSpace.{u, u}) (A B : SheafOfModules.{u} (structureRingSheaf Z))

/-- **The symmetry constraint of Tag 01CA exchanges the two factors of a local pure tensor**, at
the `Stacks.PullbackTensorCoherence.tmul` spelling of the pure tensor. -/
theorem braiding_tmul (U : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (β_ A B).hom.val.app U (tmul Z A B U a b) = tmul Z B A U b a :=
  Stacks.SheafOfModules.braiding_tensorSectionsAt Z.presheaf
    (structureSheafRing Z).property U A B a b

end Sections

/-! ### The comparison of Stacks 01CD commutes with the symmetry constraint -/

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- **The comparison of Stacks 01CD commutes with the symmetry constraint of Tag 01CA.** Both
sides are morphisms out of the pullback `f^*(A ⊗ B)`, hence determined by their values on the
pullback-unit images of the local pure tensors, where both carry the pullback-unit image of
`a ⊗ b` to the pure tensor of the pullback-unit image of `b` with that of `a`. -/
theorem pullbackTensorComparison_braiding :
    (pullbackFunctor f).map (β_ A B).hom ≫ pullbackTensorComparison f B A =
      pullbackTensorComparison f A B ≫
        (β_ ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)).hom :=
  pullback_tensor_hom_ext f fun U a b ↦ by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      pullbackUnit_naturality, braiding_tmul, pullbackTensorComparison_pullbackUnit,
      pullbackTensorComparison_pullbackUnit, braiding_tmul]

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a lax braided
functor** for the monoidal structure whose tensorator is the comparison of Stacks 01CD. -/
@[instance_reducible]
noncomputable def pullbackComparisonLaxBraided :
    letI := pullbackComparisonMonoidal f
    (pullbackFunctor f).LaxBraided :=
  letI := pullbackComparisonMonoidal f
  { toLaxMonoidal := (pullbackComparisonMonoidal f).toLaxMonoidal
    braided := fun M N ↦ by
      rw [pullbackComparisonMonoidal_mu, pullbackComparisonMonoidal_mu, IsIso.eq_comp_inv,
        Category.assoc, pullbackTensorComparison_braiding, IsIso.inv_hom_id_assoc] }

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a braided monoidal
functor** for the monoidal structure whose tensorator is the comparison of Stacks 01CD. -/
@[instance_reducible, ega "0 4.3.4" "partial"]
noncomputable def pullbackComparisonBraided : (pullbackFunctor f).Braided :=
  letI := pullbackComparisonMonoidal f
  letI := pullbackComparisonLaxBraided f
  { toMonoidal := pullbackComparisonMonoidal f
    braided := Functor.LaxBraided.braided }

end Pullback

end Stacks.PullbackTensorCoherence

end
