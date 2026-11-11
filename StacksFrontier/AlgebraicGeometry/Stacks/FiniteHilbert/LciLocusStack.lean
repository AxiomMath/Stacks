module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusInherited
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.StackDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.SpanDescent

/-!
# The local complete intersection locus is a stack in groupoids

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat and locally of finite presentation, and let `d`
be a natural number. The first assertion of **Stacks 06CL** is that the local complete
intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of Stacks 06CJ is a stack in groupoids. This file proves it,
at those hypotheses and nothing else, in the sense of Stacks 02ZI at the index universe of `𝒳`
and `𝒴`.

The source deduces it from the representability of the inclusion into `ℋ_d(𝒳/𝒴)` and from
Stacks 05UN. Here the same two inputs are used in the form in which they carry the argument: the
ambient `ℋ_d(𝒳/𝒴)` is a stack in groupoids, which is Stacks 05WB,
`AlgebraicGeometry.Stack.isStackInGroupoids_finiteHilbertProjection`, and the locus is a full
subcategory which is inherited along morphisms and local on the base, both read off the open
subscheme representing the base changes of the inclusion,
`AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus`. A full subcategory with those two
properties of a stack in groupoids is a stack in groupoids,
`CategoryTheory.Functor.IsStackInGroupoids.ι_comp`: inheritance along morphisms is
`AlgebraicGeometry.Stack.isFiberedInGroupoids_lciFiniteHilbertCategory` and locality is
`AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_cover`.

## Main results

* `AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat`: **Stacks 06CL**,
  `ℋ_{d,lci}(𝒳/𝒴)` is a stack in groupoids.

The other clauses of Stacks 06CL, that the inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is
representable and an open immersion, are in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusRepresentable`.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- **Stacks 06CL.** For a 1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids over the big fppf site
of `S` which is representable by algebraic spaces, flat and locally of finite presentation, the
local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` is a stack in groupoids over the big fppf site
of `S`.

The ambient `ℋ_d(𝒳/𝒴)` is a stack in groupoids by Stacks 05WB, and the locus is a full
subcategory inherited along morphisms and local on the base by the open locus of Stacks 05X8 and
06CE, `AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus`. The form
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory`, which takes these inputs as
arguments, carries no registration. -/
@[stacks 06CL "ℋ_{d,lci}(𝒳/𝒴) is a stack in groupoids"]
theorem isStackInGroupoids_lciFiniteHilbertCategory_of_flat
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  have hopen := FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp
  isStackInGroupoids_finiteHilbertProjection.ι_comp _
    (isFiberedInGroupoids_lciFiniteHilbertCategory hopen)
    fun V f hf x₀ hx₀ x χ hχ hx => FiniteHilbert.lciLocus_of_cover hopen V f hf x₀ hx₀ x χ hχ hx

end AlgebraicGeometry.Stack

end
