module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap

/-!
# The local complete intersection locus as a category fibred in groupoids

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. `AlgebraicGeometry.Stack.lciFiniteHilbertCategory` is the local
complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of **Stacks 06CJ** as a `CategoryTheory.
BasedCategory` over the site. Every predicate of this library that speaks of an algebraic stack
— `AlgebraicGeometry.Stack.IsAlgebraicStack` among them — is stated of an object of the
2-category `CategoryTheory.CatFiberedInGroupoids`, that is, of a based category *together with*
a witness that its structure functor is fibred in groupoids. This file supplies the bundling, so
that algebraicity of the locus can be stated at all, and reads the hypothesis `hcover` of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatPresentation` at a single degree.

## Main definitions

* `AlgebraicGeometry.Stack.lciFiniteHilbertFibered`: the locus `ℋ_{d,lci}(𝒳/𝒴)` as an object of
  the 2-category of categories fibred in groupoids over the big fppf site of `S`, given a
  witness that its projection is fibred in groupoids.
* `AlgebraicGeometry.Stack.lciFiniteHilbertToTargetFibered`: the 1-morphism
  `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` of that 2-category.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_lciFiniteHilbertCover`: a 1-morphism of stacks in
  groupoids whose target has a representable diagonal and *one* of whose local complete
  intersection loci is an algebraic stack covering the target representably, surjectively and
  smoothly has an algebraic stack for its target. This is the hypothesis `hcover` of Stacks 06DC
  discharged at a single degree.

## Implementation notes

**Where the witness comes from.**
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat` — **Stacks 06CL**
— concludes `CategoryTheory.Functor.IsStackInGroupoids` of the projection of the locus at the
source's hypotheses on `F`, and clause (1) of that structure, its field `isFiberedInGroupoids`,
is one source of the witness these declarations ask for. The witness is taken as an explicit
argument here because the declarations below are stated for the locus as a bundled object.

**The witness is nevertheless available unconditionally**: clause (1) of 06CL is also
`AlgebraicGeometry.Stack.isFiberedInGroupoids_lciFiniteHilbertCategory` of
`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/LciLocusInherited.lean`, which asks only for
`AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`, and that is proved from the
representability, flatness and local finite presentation of `F` by
`AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus`. So the witness costs nothing beyond the
hypotheses of Stacks 06DC itself, and
`AlgebraicGeometry.Stack.isAlgebraicStack_lciFiniteHilbertCategory` of
`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/LciLocusAlgebraic.lean` takes that route and
so takes no witness argument. It also discharges the hypothesis `hlci` below outright. Nothing
else about the locus is assumed here.

**Why one degree and not the coproduct.** The source of Stacks 06DC covers `𝒴` by
`∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴)`, not by a single locus: the degree of the finite locally free
subscheme produced over a field object varies with the field object, so no one `d` works for all
of them, and `AlgebraicGeometry.Stack.isSurjectiveOnObjects_lciFiniteHilbertCoproductToTarget`
(**Stacks 06DA**) is a statement about the coproduct for that reason. What the theorem below
isolates is that the coproduct is needed *only* for surjectivity: once a covering 1-morphism is
in hand, the passage to algebraicity of `𝒴` uses nothing about the index. See the module
docstring of `StacksFrontier/AlgebraicGeometry/Stacks/GroupoidPresentationBootstrap.lean` for the
state of the coproduct itself.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- The local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of **Stacks 06CJ**, read as an object
of the 2-category of categories fibred in groupoids over the big fppf site of `S`
(**Stacks 02XS**).

The witness is clause (1) of **Stacks 06CL**, the field
`CategoryTheory.Functor.IsStackInGroupoids.isFiberedInGroupoids` of
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat`. -/
noncomputable abbrev lciFiniteHilbertFibered
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) h

/-- The 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` of the 2-category of categories fibred in groupoids
over the big fppf site of `S`: the 1-morphism
`AlgebraicGeometry.Stack.lciFiniteHilbertToTarget` of based categories, read in that
2-category. -/
noncomputable abbrev lciFiniteHilbertToTargetFibered
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    lciFiniteHilbertFibered h ⟶
      CatFiberedInGroupoids.mk 𝒴.toBasedCategory 𝒴.isStackInGroupoids.isFiberedInGroupoids :=
  Bicategory.InducedBicategory.mkHom
    (lciFiniteHilbertToTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

/-- **The hypothesis `hcover` of Stacks 06DC discharged at a single degree.** If the local
complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of one degree `d` is an algebraic stack and its
1-morphism to `𝒴` is representable by algebraic spaces and relatively surjective and smooth,
then `𝒴` is an algebraic stack — given that `𝒴` is a stack for the fppf topology and has a
diagonal representable by algebraic spaces.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover` at the
bundled locus. It is stated to record that the coproduct over all degrees which the source of
Stacks 06DC covers `𝒴` with is needed only to make the covering 1-morphism surjective: the
assembly consumes a single covering stack. -/
theorem isAlgebraicStack_of_lciFiniteHilbertCover
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids)
    (hlci : IsAlgebraicStack.{u, w} B S hS
      (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)))
    (hstack : 𝒴.toBasedCategory.p.IsStack (BigFppfOver.topology B S hS))
    (hdiagonal : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS
      (CatFiberedInGroupoids.mk 𝒴.toBasedCategory
        𝒴.isStackInGroupoids.isFiberedInGroupoids)))
    (hq : IsRepresentableByAlgebraicSpaces B S hS (lciFiniteHilbertToTargetFibered h).hom)
    (hqP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
      (lciFiniteHilbertToTargetFibered h) hq) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.toBasedCategory :=
  isAlgebraicStack_of_smoothSurjectiveAlgebraicCover.{u, w} B S hS
    (lciFiniteHilbertToTargetFibered h) hlci hstack hdiagonal hq hqP

end AlgebraicGeometry.Stack

end
