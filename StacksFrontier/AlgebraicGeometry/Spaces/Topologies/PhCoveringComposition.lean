module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementParts0DBF

/-!
# Composition of ph coverings of algebraic spaces (Stacks 0DFJ, composition)

Let `S` be a scheme contained in a big fppf site `B`. Refining every member of a ph covering of
an algebraic space over `S` by a ph covering of that member gives a ph covering of the original
space, indexed by the dependent sum of the two index types. This is part (2) of Stacks 0DFJ;
parts (1) and (3) are `AlgebraicGeometry.Space.isPHCovering_of_isIso` and
`AlgebraicGeometry.Space.isPHCovering_baseChange`.

## Main results

* `AlgebraicGeometry.Space.isPHCovering_comp`: refining every member of a ph covering by a ph
  covering gives a ph covering.

## References

* [Stacks Project, Tag 0DFJ](https://stacks.math.columbia.edu/tag/0DFJ)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

/-- **Ph coverings compose.** If `{Xᵢ i ⟶ X}` is a ph covering of an algebraic space over `S`
and `{Xᵢⱼ i j ⟶ Xᵢ i}` is a ph covering for every `i`, then the family of all composites
`Xᵢⱼ i j ⟶ Xᵢ i ⟶ X`, indexed by `Σ i, J i`, is a ph covering of `X`. -/
@[stacks 0DFJ "composition"]
theorem isPHCovering_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {J : I → Type w}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Xᵢ i ⟶ X)
    (Xᵢⱼ : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hf : IsPHCovering B S hS Xᵢ f)
    (hg : ∀ i, IsPHCovering B S hS (Xᵢⱼ i) (g i)) :
    IsPHCovering B S hS (fun ij : Σ i, J i ↦ Xᵢⱼ ij.1 ij.2)
      (fun ij : Σ i, J i ↦ g ij.1 ij.2 ≫ f ij.1) :=
  isPHCovering_bind_of_chowLemma B S hS
    ({ I₀ := I, X := Xᵢ, f := f } : PreZeroHypercover.{v} X) hf
    (fun i ↦ ({ I₀ := J i, X := Xᵢⱼ i, f := g i } : PreZeroHypercover.{w} (Xᵢ i))) hg
    fun _ _ p _ _ ↦ chowLemmaStatement.hasChowModification_of_isProper p

end AlgebraicGeometry.Space

end
