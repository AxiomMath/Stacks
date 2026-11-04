module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Shrinking the morphisms of a category over a base

Let `𝒞` be a category and let `𝒳` be a category over it whose total category is locally
`w`-small. Mathlib's `CategoryTheory.ShrinkHoms` replaces every hom type of the total category by
a model in `Type w`; with the structure functor transported along the comparison functor this is
a category over `𝒞` with morphisms in `Type w`, equivalent to `𝒳` in the 2-category of categories
over `𝒞`. It is `CategoryTheory.BasedCategory.shrinkHoms`.

## Main definitions

* `CategoryTheory.BasedCategory.shrinkHoms`: the category over `𝒞` with shrunk hom types.
* `CategoryTheory.BasedCategory.shrinkHomsEquivalenceOver`: its equivalence over `𝒞` with the
  original category.

## Main results

* `CategoryTheory.BasedCategory.shrinkHoms_functor_comp_inverse`: the round trip through the shrunk
  hom types is the identity functor.
* `CategoryTheory.BasedCategory.isFiberedInGroupoids_shrinkHoms`: the shrunk category of a category
  fibred in groupoids is fibred in groupoids.

## Implementation notes

The structure functor of the shrunk category is the comparison functor
`CategoryTheory.ShrinkHoms.inverse` followed by the original structure functor, so the comparison
back to `𝒳` is strictly over `𝒞` by definition. The other comparison is strictly over `𝒞` because
the round trip `ShrinkHoms.functor ⋙ ShrinkHoms.inverse` is the identity functor: on objects on
the nose, and on morphisms because `equivShrink` followed by its inverse is the identity.

That the shrunk category is fibred in groupoids is Stacks 042X,
`CategoryTheory.Functor.IsFiberedInGroupoids.of_isEquivalenceOver`, applied to the comparison
equivalence, whose unit and counit have identity components and hence are vertical.

## References

* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.BasedCategory

universe w v₁ u₁ v₂ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The category over `𝒞` obtained from a category over `𝒞` with locally `w`-small total category
by replacing its hom types with their models in `Type w`. -/
noncomputable def shrinkHoms (𝒳 : BasedCategory.{v₂, u₂} 𝒞) [LocallySmall.{w} 𝒳.obj] :
    BasedCategory.{w, u₂} 𝒞 where
  obj := ShrinkHoms.{u₂} 𝒳.obj
  p := ShrinkHoms.inverse.{w} 𝒳.obj ⋙ 𝒳.p

variable (𝒳 : BasedCategory.{v₂, u₂} 𝒞) [LocallySmall.{w} 𝒳.obj]

attribute [local implicit_reducible] CategoryTheory.ShrinkHoms.functor
    CategoryTheory.ShrinkHoms.inverse in
/-- The round trip through the shrunk hom types is the identity functor. -/
lemma shrinkHoms_functor_comp_inverse :
    ShrinkHoms.functor.{w} 𝒳.obj ⋙ ShrinkHoms.inverse.{w} 𝒳.obj = 𝟭 𝒳.obj := by
  refine Functor.ext (fun _ => rfl) ?_
  intro x y f
  have h : (ShrinkHoms.functor.{w} 𝒳.obj ⋙ ShrinkHoms.inverse.{w} 𝒳.obj).map f = f :=
    (equivShrink (x ⟶ y)).symm_apply_apply f
  rw [h]
  show f = eqToHom (rfl : x = x) ≫ f ≫ eqToHom (rfl : y = y)
  simp

/-- The comparison functor into the shrunk category is strictly over `𝒞`. -/
lemma shrinkHoms_functor_comp :
    ShrinkHoms.functor.{w} 𝒳.obj ⋙ (𝒳.shrinkHoms).p = 𝒳.p := by
  show ShrinkHoms.functor.{w} 𝒳.obj ⋙ (ShrinkHoms.inverse.{w} 𝒳.obj ⋙ 𝒳.p) = 𝒳.p
  rw [← Functor.assoc, shrinkHoms_functor_comp_inverse, Functor.id_comp]

/-- The comparison functor out of the shrunk category is strictly over `𝒞`. -/
lemma shrinkHoms_inverse_comp :
    ShrinkHoms.inverse.{w} 𝒳.obj ⋙ 𝒳.p = (𝒳.shrinkHoms).p := rfl

/-- The comparison functors of `CategoryTheory.ShrinkHoms`, read as an equivalence over `𝒞` in the
sense of `CategoryTheory.Functor.IsEquivalenceOver`: unit and counit have identity components. -/
noncomputable def shrinkHomsIsEquivalenceOver :
    Functor.IsEquivalenceOver 𝒳.p (𝒳.shrinkHoms).p (ShrinkHoms.functor.{w} 𝒳.obj) where
  inv := ShrinkHoms.inverse.{w} 𝒳.obj
  inv_over := shrinkHoms_inverse_comp 𝒳
  unitIso := (ShrinkHoms.equivalence.{w} 𝒳.obj).unitIso.symm
  counitIso := (ShrinkHoms.equivalence.{w} 𝒳.obj).counitIso
  unit_vertical _ := IsHomLift.id rfl
  counit_vertical _ := IsHomLift.id rfl

/-- **A category over `𝒞` is equivalent over `𝒞` to its shrunk category.** -/
noncomputable def shrinkHomsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver 𝒳.p (𝒳.shrinkHoms).p :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (shrinkHoms_functor_comp 𝒳) (shrinkHomsIsEquivalenceOver 𝒳)

/-- The forward functor of `shrinkHomsEquivalenceOver` is `CategoryTheory.ShrinkHoms.functor`. -/
@[simp]
lemma shrinkHomsEquivalenceOver_hom_functor :
    (shrinkHomsEquivalenceOver 𝒳).hom.functor = ShrinkHoms.functor.{w} 𝒳.obj := rfl

/-- The inverse functor of `shrinkHomsEquivalenceOver` is `CategoryTheory.ShrinkHoms.inverse`. -/
@[simp]
lemma shrinkHomsEquivalenceOver_inv_functor :
    (shrinkHomsEquivalenceOver 𝒳).inv.functor = ShrinkHoms.inverse.{w} 𝒳.obj := rfl

/-- **The shrunk category of a category fibred in groupoids is fibred in groupoids.** -/
theorem isFiberedInGroupoids_shrinkHoms (h : 𝒳.p.IsFiberedInGroupoids) :
    (𝒳.shrinkHoms).p.IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_isEquivalenceOver (shrinkHoms_functor_comp 𝒳)
    (shrinkHomsIsEquivalenceOver 𝒳) h

end CategoryTheory.BasedCategory

end
