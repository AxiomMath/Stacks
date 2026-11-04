module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Representability by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A category fibred in groupoids over the
big fppf site of `S` is *representable by an algebraic space* (Stacks 04SV) when it is
equivalent, over that site, to the category attached to the sheaf of points of an algebraic
space over `S`. A 1-morphism of categories over that site is *representable by algebraic
spaces* (Stacks 02ZW) when its 2-fibre product with every scheme-valued point of the target is
representable by an algebraic space over that scheme.

## Main definitions

* `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace`: **Stacks 04SV**.
* `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces`: **Stacks 02ZW**.

## Implementation notes

The category attached to a presheaf of sets is the Grothendieck construction of that presheaf
regarded as a presheaf of discrete categories, `CategoryTheory.presheafOfCategories` composed
with `CategoryTheory.typeToCat`. The notion of equivalence is
`StacksRepresentableCFG.EquivalenceOver`, which records 1-morphisms in both directions over the
site together with unit and counit isomorphisms that are 2-cells over the site, and which
allows the two total categories to live in different universes; that last point is what lets a
possibly large category fibred in groupoids be compared with the small category attached to a
presheaf of `Type u`.

Both predicates are abbreviations, so a consumer may use the existential witness, respectively
the universal quantifier, directly.

For `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` the 2-fibre product is taken over
the site of `S`, but its first projection is a category over the site of `U`: for a scheme `U`
over the base, the big fppf site of `U` maps to that of `S` by postcomposition with `U ⟶ S`
(`CategoryTheory.Over.map`), and `CategoryTheory.TwoFibreProductOver.fst` is strictly over that
site. Stating the condition this way avoids having to produce a fibred-in-groupoids witness for
the first projection merely in order to state it. The predicate takes a `BasedFunctor`, so the
source and target may have independent object and morphism universes; for a 1-morphism `f` of
the 2-category `CategoryTheory.CatFiberedInGroupoids`, pass `f.hom`.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ v₂ w₁ w₂

/-- **Stacks 04SV.** A category fibred in groupoids over the big fppf site of `S` is
*represented by an algebraic space* over `S` if it is equivalent, over that site, to the
category of elements of the sheaf of points of an algebraic space over `S`. -/
@[stacks 04SV]
abbrev IsRepresentableByAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) : Prop :=
  ∃ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
    IsAlgebraicSpace B S hS F ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **Stacks 02ZW.** A 1-morphism of categories over the big fppf site of `S` is *representable
by algebraic spaces* if, for every scheme `U` over `S` and every scheme-valued point
`y : (Sch/U)_{fppf} ⟶ 𝒴` of its target, the first projection of the 2-fibre product
`(Sch/U)_{fppf} ×_𝒴 𝒳 ⟶ (Sch/U)_{fppf}` is equivalent, over the big fppf site of `U`, to the
category of elements of the sheaf of points of an algebraic space over `U`. -/
@[stacks 02ZW]
abbrev IsRepresentableByAlgebraicSpaces
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
    (f : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS),
    let 𝒰 := BigFppfOver B U.left.1 U.left.2
    let p𝒰 : 𝒰 ⥤ BigFppfOver B S hS := Over.map U.hom
    ∀ (y : 𝒰 ⥤ 𝒴.obj) (_hy : y ⋙ 𝒴.p = p𝒰),
      ∃ F : 𝒰ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 F ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst p𝒰 𝒳.p 𝒴.p y f.toFunctor)
            (presheafOfCategories (F ⋙ typeToCat)).p)

/-- Taking the iterated slice commutes with the slice of a morphism: the composite
`Over U ⥤ Over V` through `Over S` agrees with the one through `Over U.left`. -/
def iteratedSliceBackward_mapIso
    {C : Type*} [Category C] {S : C} {U V : Over S} (g : U ⟶ V) :
    U.iteratedSliceBackward ⋙ Over.map g ≅
      (Over.map g.left) ⋙ V.iteratedSliceBackward :=
  NatIso.ofComponents
    (fun W =>
      show (Over.map g).obj (U.iteratedSliceBackward.obj W) ≅
        V.iteratedSliceBackward.obj ((Over.map g.left).obj W) from
        Over.isoMk
          (show (Over.mk (W.hom ≫ U.hom) : Over S) ≅
              Over.mk ((W.hom ≫ g.left) ≫ V.hom) from
            Over.isoMk (Iso.refl W.left) (by simp))
          (by ext; simp [Over.iteratedSliceBackward, Over.map]))
    (by
      intro W W' a
      ext
      change a.left ≫ 𝟙 W'.left = 𝟙 W.left ≫ a.left
      simp)

/-! ### Uniqueness of a lift along the identity functor -/

variable {𝒞 : Type u} [CategoryTheory.Category.{v} 𝒞]

/-- Two morphisms with the same source and target lying over one and the same morphism of the
base through an identity functor are equal. -/
public theorem eq_of_isHomLift_id {R T : 𝒞} (f : R ⟶ T) {a b : 𝒞} (φ ψ : a ⟶ b)
    (hφ : (𝟭 𝒞).IsHomLift f φ) (hψ : (𝟭 𝒞).IsHomLift f ψ) : φ = ψ := by
  have := hφ
  have := hψ
  exact (IsHomLift.fac' (𝟭 𝒞) f φ).trans (IsHomLift.fac' (𝟭 𝒞) f ψ).symm

end AlgebraicGeometry.Stack

end
