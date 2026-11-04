module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import Mathlib.CategoryTheory.Category.ULift

/-!
# The 2-fibre product with an algebraic space is an algebraic space (Stacks 0300)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴`, `𝒵` be categories fibred
in groupoids over the big fppf site of `S`. Let `f : 𝒳 ⟶ 𝒴` be representable by algebraic
spaces and let `g : 𝒵 ⟶ 𝒴` be any 1-morphism. Stacks 0302 says that the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is again representable by algebraic spaces, and Stacks 0300 says that if
moreover `𝒵` is represented by an algebraic space then so is `𝒵 ×_𝒴 𝒳`.

Both are stated here for the 2-fibre product of the source,
`AlgebraicGeometry.Stack.twoFibreProduct`, and with independent universes for the three
categories: nothing in either statement constrains them, because a 1-morphism of categories
over the site is a `CategoryTheory.BasedFunctor` and
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` places no relation on its source and
target universes.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductFst`: the projection
  `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`: if `𝒵` is
  represented by an algebraic space, then so is `𝒵 ×_𝒴 𝒳`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`: the same for
  the apex of an abstract 2-fibre product square of the 2-category of categories fibred in
  groupoids; this is the implication (1) ⟹ (2) of Stacks 04ZP.

## Implementation notes

The 2-fibre product of a cospan of categories fibred in groupoids has a larger object universe
than the cospan — an object of it carries a morphism of the common target. The 2-fibre product's
universes do dominate those of the first factor, so the first factor is moved up to them along the
universe-lifting equivalence `CategoryTheory.ULiftHomULiftCategory.equiv`, which is strictly over
the site: its two composites are the identity functors on the nose, so the lifted structure
functor is fibred in groupoids by
`CategoryTheory.Functor.IsFiberedInGroupoids.of_isEquivalenceOver`, it is represented by the same
algebraic space, and the projection to it is representable by algebraic spaces by Stacks 0457.

`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` (`…Stacks.BaseChange`)
states the content of Stacks 0302 for an *arbitrary* 2-fibre product square of the 2-category,
at the universes `CategoryTheory.CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}`
at which the 2-category is closed under forming 2-fibre products.
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct` is stated at those
universes too.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projection of the 2-fibre product `𝒯₁ ×_𝒳 𝒯₂` of two 1-morphisms of categories fibred
in groupoids over the big fppf site of `S` onto its first factor. -/
def twoFibreProductFst
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (𝒯₁ : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val ⥤ᵇ 𝒯₁.val where
  toFunctor := TwoFibreProductOver.fst 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.toFunctor y.toFunctor
  w := TwoFibreProductOver.fst_comp_eq

/-- If `f : 𝒳 ⟶ 𝒴` is a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces and `g : 𝒵 ⟶ 𝒴` is any 1-morphism, then the base
change `𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` is representable by algebraic spaces. No relation is assumed
between the universes of the three categories. -/
@[stacks 0302]
theorem isRepresentableByAlgebraicSpaces_twoFibreProductFst
    (𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (𝒵 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
    (𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
    (g : 𝒵.val ⥤ᵇ 𝒴.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    IsRepresentableByAlgebraicSpaces B S hS (twoFibreProductFst B S hS 𝒴 𝒵 𝒳 g f) := by
  intro U
  dsimp only
  intro z hz
  obtain ⟨F, hF, ⟨e⟩⟩ := hf U (z ⋙ g.toFunctor) (by rw [Functor.assoc, g.w, hz])
  exact ⟨F, hF, ⟨(TwoFibreProductOver.cancelMiddleEquivalenceOver (Over.map U.hom) 𝒳.val.p
    𝒴.val.p 𝒵.val.p z f.toFunctor g.toFunctor hz g.w).trans e⟩⟩

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces, let `g : 𝒵 ⟶ 𝒴` be any 1-morphism, and assume
`𝒵` is represented by an algebraic space over `S`. Then the 2-fibre product `𝒵 ×_𝒴 𝒳` is
represented by an algebraic space over `S`. -/
@[stacks 0300]
theorem isRepresentableByAlgebraicSpace_twoFibreProduct
    (𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (𝒵 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
    (𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
    (g : 𝒵.val ⥤ᵇ 𝒴.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒴 𝒵 𝒳 g f) := by
  let _i₁ : Category.{v₁} (ULift.{max (max (max (u + 1) w₁) w₂) v, w₁} 𝒵.val.obj) :=
    uliftCategory _
  let _i₂ : Category.{max (max u v₁) v₂}
      (ULiftHom.{max (max u v₁) v₂}
        (ULift.{max (max (max (u + 1) w₁) w₂) v, w₁} 𝒵.val.obj)) := ULiftHom.category
  let e : 𝒵.val.obj ≌ ULiftHom.{max (max u v₁) v₂}
      (ULift.{max (max (max (u + 1) w₁) w₂) v, w₁} 𝒵.val.obj) := ULiftHomULiftCategory.equiv _
  have hfunctor : e.functor ⋙ (e.inverse ⋙ 𝒵.val.p) = 𝒵.val.p := rfl
  let 𝒵base : BasedCategory.{max (max u v₁) v₂, max (max (max (u + 1) w₁) w₂) v}
      (BigFppfOver B S hS) := BasedCategory.ofFunctor (e.inverse ⋙ 𝒵.val.p)
  have h𝒵fib : 𝒵base.p.IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver hfunctor
      { inv := e.inverse
        inv_over := rfl
        unitIso := Iso.refl _
        counitIso := Iso.refl _
        unit_vertical := fun _ => IsHomLift.id rfl
        counit_vertical := fun _ => IsHomLift.id rfl } 𝒵.2
  let 𝒵' : CatFiberedInGroupoids.{u, max (max u v₁) v₂, u + 1,
      max (max (max (u + 1) w₁) w₂) v} (BigFppfOver B S hS) := ⟨𝒵base, h𝒵fib⟩
  let up : 𝒵.val ⥤ᵇ 𝒵'.val := { toFunctor := e.functor, w := hfunctor }
  let down : 𝒵'.val ⥤ᵇ 𝒵.val := { toFunctor := e.inverse, w := rfl }
  have hdown : down.toFunctor.IsEquivalence := inferInstanceAs e.inverse.IsEquivalence
  have hid : (BasedFunctor.id (twoFibreProduct B S hS 𝒴 𝒵 𝒳 g f).val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 (twoFibreProduct B S hS 𝒴 𝒵 𝒳 g f).val.obj).IsEquivalence
  have h𝒵' : IsRepresentableByAlgebraicSpace B S hS 𝒵' := by
    obtain ⟨F, hF, ⟨eq⟩⟩ := h𝒵
    refine ⟨F, hF, ⟨StacksRepresentableCFG.EquivalenceOver.trans ?_ eq⟩⟩
    exact
      { hom := { functor := e.inverse, w := rfl }
        inv := { functor := e.functor, w := hfunctor }
        unitIso := Iso.refl _
        counitIso := Iso.refl _
        unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _
          (fun _ => IsHomLift.id rfl)
        counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _
          (fun _ => IsHomLift.id rfl) }
  let r : twoFibreProduct B S hS 𝒴 𝒵 𝒳 g f ⟶ 𝒵' :=
    Bicategory.InducedBicategory.mkHom ((twoFibreProductFst B S hS 𝒴 𝒵 𝒳 g f).comp up)
  exact isRepresentableByAlgebraicSpace_of_representable B S hS _ 𝒵' r
    ((isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      (f' := r.hom) (f := twoFibreProductFst B S hS 𝒴 𝒵 𝒳 g f)
      (a := BasedFunctor.id _) (b := down) (Iso.refl _)).mp
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒴 𝒵 𝒳 g f hf)) h𝒵'

/-- For an abstract 2-fibre product square of the 2-category of categories fibred in groupoids
over the big fppf site of `S`: if `f : 𝒳 ⟶ 𝒴` is representable by algebraic spaces and `𝒵` is
represented by an algebraic space, then the apex of a 2-fibre product square over the cospan
`(g, f)` is represented by an algebraic space.

The universes are those of `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`,
at which the 2-category is closed under forming the 2-fibre product of a cospan. For the 2-fibre
product itself, with no relation between the universes, see
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`. -/
theorem isRepresentableByAlgebraicSpace_of_isTwoFibreProduct
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵) :
    IsRepresentableByAlgebraicSpace B S hS P.pt :=
  isRepresentableByAlgebraicSpace_of_representable B S hS P.pt 𝒵 P.fst
    (isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g P hP hf) h𝒵

/-! ### Stacks 04ZP, the implication (1) ⟹ (2) -/

add_to_stacks 04ZP "the implication (1) ⟹ (2)"
  AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct

end AlgebraicGeometry.Stack

end
