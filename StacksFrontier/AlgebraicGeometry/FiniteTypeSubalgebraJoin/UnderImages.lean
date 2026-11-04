module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebra.Coproducts
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.CommRingImages
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.FunctorImages

/-!
# Images in a category of objects under a fixed object

If `C` has images and pullbacks then `CategoryTheory.Under Y` has images: the image of a morphism
under `Y` is the image of its underlying morphism in `C`, made an object under `Y` by the
composite of the structure morphism with the corestriction to the image.

With images in `CommRingCat` and in functor categories, and the binary coproducts
`Stacks.UnderCoproducts.hasBinaryCoproducts`, this gives joins of subobjects of a presheaf of
algebras over a presheaf of commutative rings, via `CategoryTheory.Subobject.semilatticeSup`.

## Main definitions

* `Stacks.UnderImages.rightMonoFactorisation`: a mono factorisation under `Y`, read in `C`.
* `Stacks.UnderImages.monoFactorisation` and `Stacks.UnderImages.isImage`: the image of a
  morphism under `Y`.

## Main results

* `Stacks.UnderImages.hasImages`: `CategoryTheory.Under Y` has images.
* `Stacks.UnderImages.presheafAlgebra_exists_sup`: the subobjects of a presheaf of algebras over
  a presheaf of commutative rings have joins.

## Implementation notes

The structure morphism of the image is `A.hom ≫ factorThruImage f.right` and the two
commutativity obligations are `CategoryTheory.Limits.image.fac` and
`CategoryTheory.Limits.image.fac_lift` composed with `CategoryTheory.Under.w`; both need a
`change` first, since `CategoryTheory.Under.mk` does not unfold at the transparency `rw` uses.

As in `Stacks.FunctorImages`, the factorisations are `@[reducible]` so that the image object's
structure morphism is visible to rewriting.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.UnderImages

noncomputable section

variable {C : Type*} [Category C] [HasImages C] [HasPullbacks C] {Y : C}

/-- A mono factorisation of a morphism under `Y`, read as a mono factorisation in `C`. -/
@[reducible]
def rightMonoFactorisation {A B : Under Y} {f : A ⟶ B} (F' : MonoFactorisation f) :
    MonoFactorisation f.right where
  I := F'.I.right
  m := F'.m.right
  m_mono := Under.mono_right_of_mono F'.m
  e := F'.e.right
  fac := congrArg Under.Hom.right F'.fac

/-- The factorisation of a morphism under `Y` through the image of its underlying morphism. -/
@[reducible]
def monoFactorisation {A B : Under Y} (f : A ⟶ B) : MonoFactorisation f where
  I := Under.mk (A.hom ≫ factorThruImage f.right)
  m := Under.homMk (image.ι f.right) (by
    change (A.hom ≫ factorThruImage f.right) ≫ image.ι f.right = B.hom
    rw [Category.assoc, image.fac]
    exact Under.w f)
  m_mono := inferInstance
  e := Under.homMk (factorThruImage f.right) rfl
  fac := by ext; exact image.fac f.right

/-- **The image of a morphism under `Y` is the image of the underlying morphism.** -/
def isImage {A B : Under Y} (f : A ⟶ B) : IsImage (monoFactorisation f) where
  lift F' := Under.homMk (image.lift (rightMonoFactorisation F')) (by
    change (A.hom ≫ factorThruImage f.right) ≫ image.lift (rightMonoFactorisation F')
      = F'.I.hom
    rw [Category.assoc, image.fac_lift]
    exact Under.w F'.e)
  lift_fac F' := by ext; exact image.lift_fac (rightMonoFactorisation F')

/-- A morphism under `Y` has an image. -/
instance hasImage {A B : Under Y} (f : A ⟶ B) : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

/-- **A category of objects under a fixed object has images.** -/
instance hasImages : HasImages (Under Y) where
  has_image f := hasImage f

end

section Presheaf

universe u

variable {J : Type u} [Category.{u} J] (A : J ⥤ CommRingCat.{u})

/-- **The subobjects of a presheaf of algebras over a presheaf of commutative rings have
joins.** Any two subobjects `S` and `T` of `B` have a common upper bound `S ⊔ T`, the image of
the morphism out of their coproduct. -/
theorem presheafAlgebra_exists_sup (B : Under A) (S T : Subobject B) :
    ∃ U : Subobject B, S ≤ U ∧ T ≤ U :=
  ⟨S ⊔ T, le_sup_left, le_sup_right⟩

end Presheaf

end Stacks.UnderImages
