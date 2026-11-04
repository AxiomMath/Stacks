module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness

/-!
# Charts of an algebraic stack, and the charted affine objects

Let `𝒳` be an algebraic stack over `S`.  By the fourth clause of **Stacks 026O** it has a
*chart*: a scheme `U` over `S` and a 1-morphism `f : (Sch/U) ⟶ 𝒳`, representable by algebraic
spaces, whose base change along every scheme-valued point of `𝒳` is surjective and smooth.
This file packages that datum, and the full subcategory of `𝒳` through which quasi-coherent
modules on `𝒳` are described by their values on the chart (**Stacks 06WT**, read through the
chart rather than through a groupoid presentation).

A *chart affine* is an object `z` of `Sch/U` whose scheme is affine and whose structure morphism
to `U` is flat; its image `f z` in `𝒳` is then a flat object of `𝒳` lying over an affine scheme.
A *charted affine object* of `𝒳` is an object lying over an affine scheme which admits an arrow
to the image of a chart affine.  Every object of `𝒳` is fppf-locally a charted affine object,
and an object lying over an affine scheme with an arrow to a charted affine object is again one.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.Chart`: a chart of an algebraic stack, the
  presentation clause of **Stacks 026O** as data.
* `AlgebraicGeometry.Stack.AlgebraicStacks.Chart.IsChartAffine`: the chart affines.
* `AlgebraicGeometry.Stack.AlgebraicStacks.Chart.IsChartedAffine`: the charted affine objects of
  `𝒳`, an object property.
* `AlgebraicGeometry.Stack.AlgebraicStacks.Chart.FlatChartFactorization`: the statement that an
  object over an affine scheme with arrows to the images of two chart affines factors,
  fppf-locally, through the image of a third chart affine by arrows lying over flat morphisms.
  This is how the arrow space `U ×_𝒳 U` of the chart enters, through its scheme-valued points
  only.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A chart of an algebraic stack**: the presentation clause of **Stacks 026O** as data.  A
scheme `U` over `S` and a 1-morphism `f : (Sch/U) ⟶ 𝒳`, representable by algebraic spaces,
whose base change along every scheme-valued point of `𝒳` is surjective and smooth. -/
structure Chart (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The scheme of the chart. -/
  U : BigFppfOver B S hS
  /-- The 1-morphism from the category represented by `U`. -/
  f : schemeFibredCategory B S hS U ⟶ 𝒳.val
  /-- `f` is representable by algebraic spaces. -/
  isRepresentable : IsRepresentableByAlgebraicSpaces B S hS f.hom
  /-- The base change of `f` along every scheme-valued point of `𝒳` is surjective and smooth. -/
  surjective_smooth : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (schemeFibredCategory B S hS U).val.p
          𝒳.val.val.p y (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)

/-- Every algebraic stack has a chart, by the fourth clause of **Stacks 026O**. -/
theorem nonempty_chart (𝒳 : AlgebraicStacks.{u, w} B S hS) : Nonempty (Chart 𝒳) := by
  obtain ⟨_, _, _, U, f, hfrep, hfprop⟩ := 𝒳.property
  exact ⟨⟨U, Bicategory.InducedBicategory.mkHom f, hfrep, hfprop⟩⟩

namespace Chart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (c : Chart 𝒳)

/-- The functor `Sch/U ⥤ 𝒳` underlying the chart. -/
abbrev functor : (schemeFibredCategory B S hS c.U).val.obj ⥤ 𝒳.val.val.obj :=
  CatFiberedInGroupoids.homFunctor c.f

/-- **A chart affine**: an object of `Sch/U` whose scheme is affine and whose structure morphism
to `U` is flat. -/
def IsChartAffine (z : (schemeFibredCategory B S hS c.U).val.obj) : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj z.left) ∧
    Flat ((BigFppfOver.toScheme B S hS).map z.hom)

/-- **A charted affine object of `𝒳`**: an object lying over an affine scheme which admits an
arrow to the image of a chart affine. -/
def IsChartedAffine : ObjectProperty 𝒳.val.val.obj := fun y =>
  IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) ∧
    ∃ (z : (schemeFibredCategory B S hS c.U).val.obj), c.IsChartAffine z ∧
      Nonempty (y ⟶ c.functor.obj z)

/-- **Flat factorization through the chart.**  Let `y` be an object of `𝒳` lying over an affine
scheme, with arrows `ψ : y ⟶ f z` and `ψ' : y ⟶ f z'` to the images of two chart affines.  Then
fppf-locally on `y` the pair `(ψ, ψ')` factors through the image `f z''` of a third chart affine
by arrows `α : f z'' ⟶ f z` and `α' : f z'' ⟶ f z'` lying over flat morphisms of schemes.

This is the property of the arrow space `U ×_𝒳 U` of the chart that the descent of modules along
the chart uses: the pair `(ψ, ψ')` is a point of the algebraic space `f z ×_𝒳 f z'`, which is
smooth over both factors and has an étale cover by affine schemes; `z''` is a member of that
cover through which the point lifts. -/
def FlatChartFactorization : Prop :=
  ∀ (y : 𝒳.val.val.obj),
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) →
    ∀ (z z' : (schemeFibredCategory B S hS c.U).val.obj), c.IsChartAffine z →
      c.IsChartAffine z' → ∀ (ψ : y ⟶ c.functor.obj z) (ψ' : y ⟶ c.functor.obj z'),
      ∃ R ∈ associatedTopology B S hS 𝒳.val.val.p B.topology y,
        ∀ ⦃y'' : 𝒳.val.val.obj⦄ ⦃k : y'' ⟶ y⦄, R.arrows k →
          ∃ (z'' : (schemeFibredCategory B S hS c.U).val.obj) (_ : c.IsChartAffine z'')
            (α : c.functor.obj z'' ⟶ c.functor.obj z)
            (α' : c.functor.obj z'' ⟶ c.functor.obj z') (β : y'' ⟶ c.functor.obj z''),
            β ≫ α = k ≫ ψ ∧ β ≫ α' = k ≫ ψ' ∧
              Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α)) ∧
              Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map α'))

end Chart

end AlgebraicGeometry.Stack.AlgebraicStacks

end
