module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward

/-!
# The two squares of Stacks 04H1 are Beck–Chevalley mates

Let `f : E ⟶ D` be a morphism of topoi, let `G` be an object of `D` and put `F = f⁻¹G`.  Stacks
04H1 records the commutativity of the localization square twice: on inverse images, as
`MorphismOfTopoi.inverseImageCompToOverIso` (`f⁻¹ ⋙ toOver F ≅ toOver G ⋙ (f')⁻¹`), and on the
direct images, as `MorphismOfTopoi.toOverCompPushforwardIso`
(`toOver F ⋙ f'_* ≅ f_* ⋙ toOver G`).  This file proves that the two are *mates* with respect
to the adjunctions `f⁻¹ ⊣ f_*` and `(f')⁻¹ ⊣ f'_*`, in the element form that the mates
correspondence is pinned down by: the adjunct of the first, followed by the second, is
`toOver G` applied to the unit of `f⁻¹ ⊣ f_*`.

This is what the structure map of a localized morphism of ringed topoi needs.  The direct-image
square is the only non-formal ingredient of [Stacks Project, Tag 04IF]'s identity
`f'_* j_F⁻¹ ≅ j_G⁻¹ f_*`, and the inverse-image square is the only non-formal ingredient of its
identity `f⁻¹ ⋙ j_F⁻¹ ≅ j_G⁻¹ ⋙ (f')⁻¹`; the compatibility of the two is exactly what makes the
structure map of the localized morphism the restriction of the structure map of `f`.

## Main results

* `Stacks.CategoryTheory.homEquiv_symm_comp_rightAdjointUniq_hom_app`: appending the canonical
  comparison of two right adjoints of **the same** left adjoint leaves an adjunct unchanged.
* `MorphismOfTopoi.left_inverseImageCompToOverIso_inv_app_comp_fst`: undoing the inverse-image
  square and projecting to the first factor is `f⁻¹` of the projection to the first factor.
* `MorphismOfTopoi.homEquiv_inverseImageCompToOverIso_inv_app_comp`: **the Beck–Chevalley
  identity**, in the form that determines it.

## Implementation notes

Both squares have `toOver F` and `toOver G` as their two further edges, and those have the two
forgetful functors as left adjoints — `CategoryTheory.forgetAdjToOver`.  That is what makes the
identity computable: `toOverCompPushforwardIso` is a `CategoryTheory.Adjunction.rightAdjointUniq`,
which cannot describe its own components, but it is pinned down after applying the common left
adjoint `Over.forget G ⋙ f⁻¹` — and applying that left adjoint to the equation to be proved
cancels *both* universal properties at once.  What is left is the single equation

```
(ι⁻¹)_Z ≫ fst = f⁻¹(fst) ,
```

the inverse-image square undone and followed by a projection, and that is
`CategoryTheory.Functor.Monoidal.μ_fst`: the comparison `f⁻¹H ⊗ f⁻¹G ≅ f⁻¹(H ⊗ G)` is compatible
with the two projections because `f⁻¹` is left exact.

The two counits of `forgetAdjToOver` are the projections to the first factor, and the last step on
the direct-image side is the naturality of that counit at the unit of `f⁻¹ ⊣ f_*` together with
the triangle identity.  The closing steps are written in terms rather than with `rw`, because
after the two adjuncts are expanded the goal mentions both
`(Over.forget G).obj ((toOver G).obj Z)` and `Z ⊗ G`, which are equal by `rfl` but not
syntactically, so the goal is not type-correct at the `implicit` transparency level that `rw`
uses.

## References

* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ u₁ u₂

/-- **Appending the canonical comparison of two right adjoints of the same left adjoint does not
change an adjunct.**

If `adj₁ : L ⊣ R₁` and `adj₂ : L ⊣ R₂` then `CategoryTheory.Adjunction.rightAdjointUniq` compares
`R₁` with `R₂`, and appending that comparison to a morphism `h : W ⟶ R₁ Z` carries its adjunct
along `adj₂` to its adjunct along `adj₁`.  This is the equation that pins a `rightAdjointUniq`
down, `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`, read through the hom-set
bijections. -/
theorem homEquiv_symm_comp_rightAdjointUniq_hom_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L ⊣ R₁) (adj₂ : L ⊣ R₂)
    {W : C} {Z : D} (h : W ⟶ R₁.obj Z) :
    (adj₂.homEquiv W Z).symm (h ≫ (Adjunction.rightAdjointUniq adj₁ adj₂).hom.app Z) =
      (adj₁.homEquiv W Z).symm h := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.rightAdjointUniq_hom_app_counit]

end Stacks.CategoryTheory

namespace MorphismOfTopoi

universe v v' u u'

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]
  (f : MorphismOfTopoi E D) (G : D) [HasPullbacks D]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- **Stacks 04H1's inverse-image square, undone and followed by the projection to the first
factor, is `f⁻¹` of that projection.**

The component of `MorphismOfTopoi.inverseImageCompToOverIso` at `Z` is, on underlying objects, the
product comparison `f⁻¹Z ⊗ f⁻¹G ≅ f⁻¹(Z ⊗ G)`, so this is
`CategoryTheory.Functor.Monoidal.μ_fst` for the monoidal structure that the left exactness of
`f⁻¹` supplies. -/
theorem left_inverseImageCompToOverIso_inv_app_comp_fst (Z : D) :
    ((f.inverseImageCompToOverIso G).inv.app Z).left ≫
        fst (f.inverseImage.obj Z) (f.inverseImage.obj G) =
      f.inverseImage.map (fst Z G) := by
  have := f.preservesFiniteLimits
  let : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f.inverseImage
  exact (Iso.inv_comp_eq (Functor.Monoidal.μIso f.inverseImage Z G)).2
    (Functor.Monoidal.μ_fst f.inverseImage Z G).symm

/-- **The two squares of Stacks 04H1 are Beck–Chevalley mates.**

The adjunct, along `(f')⁻¹ ⊣ f'_*`, of the inverse-image square undone, followed by the
direct-image square, is `toOver G` applied to the unit of `f⁻¹ ⊣ f_*`.  Since the adjunct is a
bijection and the direct-image square is invertible, this equation determines the inverse-image
square from the direct-image one, which is what it means for the two to be mates.

The proof applies the common left adjoint `Over.forget G ⋙ f⁻¹` of the two adjunctions that
`MorphismOfTopoi.toOverCompPushforwardIso` compares.  That cancels the universal property on the
left and the adjunct along `(f')⁻¹ ⊣ f'_*` on the right, leaving
`left_inverseImageCompToOverIso_inv_app_comp_fst` on one side and the naturality of the counit of
`CategoryTheory.forgetAdjToOver` on the other. -/
theorem homEquiv_inverseImageCompToOverIso_inv_app_comp (Z : D) :
    ((f.over G).adj.homEquiv ((toOver G).obj Z)
          ((toOver (f.inverseImage.obj G)).obj (f.inverseImage.obj Z)))
        ((f.inverseImageCompToOverIso G).inv.app Z) ≫
          (f.toOverCompPushforwardIso G).hom.app (f.inverseImage.obj Z) =
      (toOver G).map (f.adj.unit.app Z) := by
  have hL : ((forgetAdjToOver (f.inverseImage.obj G)).homEquiv
        ((f.over G).inverseImage.obj ((toOver G).obj Z)) (f.inverseImage.obj Z)).symm
        ((f.inverseImageCompToOverIso G).inv.app Z) = f.inverseImage.map (fst Z G) := by
    rw [forgetAdjToOver.homEquiv_symm]
    exact left_inverseImageCompToOverIso_inv_app_comp_fst f G Z
  have hR : (f.adj.homEquiv ((Over.forget G).obj ((toOver G).obj Z)) (f.inverseImage.obj Z)).symm
        (((forgetAdjToOver G).homEquiv ((toOver G).obj Z)
          (f.pushforward.obj (f.inverseImage.obj Z))).symm ((toOver G).map (f.adj.unit.app Z))) =
      f.inverseImage.map (fst Z G) := by
    have hnat : ((toOver G).map (f.adj.unit.app Z)).left ≫
          fst (f.pushforward.obj (f.inverseImage.obj Z)) G =
        fst Z G ≫ f.adj.unit.app Z :=
      (forgetAdjToOver G).counit.naturality (f.adj.unit.app Z)
    rw [forgetAdjToOver.homEquiv_symm, Adjunction.homEquiv_counit, hnat]
    refine Eq.trans (congrArg (fun z ↦ z ≫ f.adj.counit.app (f.inverseImage.obj Z))
      (f.inverseImage.map_comp (fst Z G) (f.adj.unit.app Z))) ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun z ↦ f.inverseImage.map (fst Z G) ≫ z)
      (f.adj.left_triangle_components Z)) (Category.comp_id _)
  refine (((forgetAdjToOver G).comp f.adj).homEquiv ((toOver G).obj Z)
    (f.inverseImage.obj Z)).symm.injective ?_
  refine Eq.trans (Stacks.CategoryTheory.homEquiv_symm_comp_rightAdjointUniq_hom_app
    ((f.over G).adj.comp (forgetAdjToOver (f.inverseImage.obj G)))
    ((forgetAdjToOver G).comp f.adj) _) ?_
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  exact hL.trans hR.symm

end MorphismOfTopoi

end
