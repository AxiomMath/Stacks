module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOnObjectsDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingAtlasObjects

/-!
# Algebraic stacks locally of finite presentation are limit preserving

Let `𝒳` be an algebraic stack over a scheme `S` whose structure morphism `𝒳 → S` is locally of
finite presentation. Then `𝒳` is limit preserving in the sense of Artin's Axioms,
Definition 07XL, and so is its structure morphism, in the sense of Stacks 0CMR. This is
Stacks 0CMX.

## Main results

In the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:

* `isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation`: a 1-morphism of algebraic
  stacks locally of finite presentation is limit preserving on objects (Stacks 06CU).
* `isLimitPreserving_of_isLocallyOfFinitePresentation`: Stacks 0CMX.

## Implementation notes

The proof is the source's. An object `x` of `𝒳` over the limit `T = lim Tᵢ` of a cofiltered
system of affine schemes is lifted, after a flat surjective morphism locally of finite
presentation `W ⟶ T`, to an atlas `U ⟶ 𝒳` whose composite to the target is limit preserving on
objects; the covering is descended to a single-member fppf covering `W₀ ⟶ T_{i₀}` of a stage
(Stacks 049N), the lift is descended along the composite, and the descended lift is glued back
along the covering at a finite stage, using relative descent of morphisms and of equalities for
the transition isomorphism and its cocycle condition, and the stack condition of `𝒳` for
effectivity. This is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_comp_of_singleCover_lift`. Limit
preservation on objects of the structure morphism together with relative descent of morphisms
and of equalities, which hold for every 1-morphism locally of finite type, is limit preservation
in the sense of Definition 07XL and of Stacks 0CMR.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism of algebraic stacks locally of finite presentation is limit preserving on
objects.** Every object of `𝒳` over a cofiltered limit of affine schemes over `S`, with a
comparison to an object of `𝒴` over a stage, descends to a finite stage compatibly with the
comparison, in the sense of Stacks 06CU. -/
theorem isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val 𝒴.val f.hom := by
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf
  obtain ⟨𝒲, a, H, hLP⟩ := exists_atlas_isLimitPreservingOnObjects_comp B S hS f hf
  exact isLimitPreservingOnObjects_of_comp_of_singleCover_lift B S hS a f.hom
    (isStack_of_isAlgebraicStack B S hS 𝒳.property)
    (isStack_of_isAlgebraicStack B S hS 𝒴.property)
    (fun D c hc => relativeDescentHom_of_isLocallyOfFiniteType B S hS f hft D c hc)
    (fun D c hc => relativeDescentEq_of_isLocallyOfFiniteType B S hS f hft D c hc) H hLP

/-- **Stacks 0CMX.** Let `𝒳` be an algebraic stack over `S` whose structure morphism `𝒳 → S` is
locally of finite presentation. Then `𝒳` is limit preserving in the sense of Artin's Axioms,
Definition 07XL: for every cofiltered system of affine schemes `Tᵢ` over `S` with limit `T`, the
comparison functor `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence. Equivalently, the structure morphism
`𝒳 → S` is limit preserving in the sense of Stacks 0CMR. The index categories are taken in the
scheme universe, which is the smallness the source's directed sets have. -/
@[stacks 0CMX "an algebraic stack locally of finite presentation over S is limit preserving, \
  and so is its structure morphism"]
theorem isLimitPreserving_of_isLocallyOfFinitePresentation
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hf : IsLocallyOfFinitePresentation B S hS (structureMorphism B S hS 𝒳)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳.val ∧
      Stack.IsLimitPreserving.{u, u, u, u + 1, u} B S hS (structureMorphism B S hS 𝒳).hom := by
  have hobj := isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation B S hS _ hf
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf
  exact ⟨isLimitPreserving_artin_of_structureMorphism B S hS 𝒳 hobj hft,
    isLimitPreserving_of_isLimitPreservingOnObjects B S hS _ hobj hft⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
