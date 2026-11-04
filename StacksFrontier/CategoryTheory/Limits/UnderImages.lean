module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Images in an under category

If `C` has pullbacks and image factorisations then so does `Under D`, for every object `D` of
`C`.  The image of `f : A ⟶ B` in `Under D` is the image of `f.right` in `C`, equipped with the
composite `D ⟶ A.right ⟶ im f.right`; its monomorphism is a monomorphism of `Under D` because
`CategoryTheory.Under.forget` is faithful, and every mono factorisation in `Under D` restricts
to one in `C`, so the universal property is inherited.  The only thing to check is that the
comparison morphism provided by the image in `C` is a morphism of `Under D`, which follows by
cancelling the monomorphism of the competing factorisation.

Pullbacks are needed only so that a monomorphism of `Under D` has monomorphic underlying
morphism (`CategoryTheory.Under.mono_right_of_mono`); without them a competing mono
factorisation need not restrict to one in `C`.

## Main definitions

* `Stacks.CategoryTheory.monoFactorisationRight`: the mono factorisation of `f.right` underlying
  a mono factorisation of a morphism `f` of an under category.
* `Stacks.CategoryTheory.underImageFactorisation`: the image factorisation of a morphism of an
  under category.

## Main results

* the instance `Stacks.CategoryTheory.hasImages_under`: an under category of a category with
  pullbacks and images has images.

## Implementation notes

The mono factorisation is written out inside `underImageFactorisation` rather than taken from a
named definition, and its universal property's obligation is discharged by the separate lemma
`Stacks.CategoryTheory.factorThruImage_comp_imageLift`, which keeps both the competing mono
factorisation and its structure morphism as variables.  Without those two devices the obligation
mentions `(Under.mk _).right` and `(monoFactorisationRight I).I` in positions typed by
`image f.right` and `I.I.right`; each pair is definitionally but not reducibly equal, so the
obligation is not type-correct at `implicit` transparency and no rewrite applies to it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {D : C} {A B : Under D}

/-- The mono factorisation of `f.right` underlying a mono factorisation of a morphism `f` of an
under category. -/
@[simps]
def monoFactorisationRight {f : A ⟶ B} (I : MonoFactorisation f) : MonoFactorisation f.right where
  I := I.I.right
  m := I.m.right
  m_mono := Under.mono_right_of_mono I.m
  e := I.e.right
  fac := by rw [← Under.comp_right, I.fac]

variable [HasImages C]

omit [HasPullbacks C] in
/-- The comparison morphism from the image of `f.right` to the middle object of a mono
factorisation of `f.right` is a morphism of the under category, as soon as that object carries
a structure morphism `g` compatible with the one of `B`.

Both the mono factorisation and the structure morphism are kept as variables: at the mono
factorisation `monoFactorisationRight I` the corresponding obligation of
`CategoryTheory.Under.homMk` is not type-correct at `implicit` transparency, so no rewrite
applies to it, whereas here every rewrite is syntactic. -/
theorem factorThruImage_comp_imageLift (f : A ⟶ B) (I : MonoFactorisation f.right) {g : D ⟶ I.I}
    (hg : g ≫ I.m = B.hom) : (A.hom ≫ factorThruImage f.right) ≫ image.lift I = g := by
  have hm : Mono I.m := I.m_mono
  refine hm.right_cancellation _ _ ?_
  simp only [Category.assoc, image.lift_fac]
  rw [image.fac, Under.w f, hg]

/-- The image factorisation of a morphism of an under category: the image of the underlying
morphism, with the structure morphism obtained by factoring. -/
noncomputable def underImageFactorisation (f : A ⟶ B) : ImageFactorisation f where
  F :=
    { I := Under.mk (A.hom ≫ factorThruImage f.right)
      m := Under.homMk (image.ι f.right) (by simp [Under.w f])
      e := Under.homMk (factorThruImage f.right)
      fac := by ext; simp [Under.comp_right] }
  isImage :=
    { lift := fun I ↦ Under.homMk (image.lift (monoFactorisationRight I))
        (factorThruImage_comp_imageLift f (monoFactorisationRight I) (Under.w I.m))
      lift_fac := fun I ↦ by
        ext
        exact image.lift_fac (monoFactorisationRight I) }

/-- If `C` has pullbacks and images, then the under category `Under D` has images. -/
instance hasImages_under (D : C) : HasImages (Under D) :=
  ⟨fun f ↦ ⟨⟨underImageFactorisation f⟩⟩⟩

end Stacks.CategoryTheory

end
