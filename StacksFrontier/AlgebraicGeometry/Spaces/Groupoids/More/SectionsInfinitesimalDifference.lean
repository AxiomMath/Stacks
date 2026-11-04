module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection

/-!
# The two comorphisms of two sections infinitesimally close to the unit

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
closed subspace, and let `R₀ = s^{-1}(U₀) ⊆ R`, with `e₀ : U₀ ⟶ R₀` the unit of the restricted
groupoid.  Two elements `δ₁, δ₂` of the set `Γ₀` of [Stacks Project, Tag 0CKB] — sections of `s`
agreeing with the unit on `U₀` — are two morphisms `U ⟶ R` which

* are sections of one and the same morphism `s : R ⟶ U`, and
* have one and the same restriction `e₀ ≫ j` to `U₀`.

So `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq`
applies to them: their comorphisms read through the thickening `U₀ ⊂ U`, as morphisms of sheaves
of rings `𝒪_R ⟶ (e₀ ≫ j)_*(i^{-1}𝒪_U)` on the small étale site of `R`, agree after the
comorphism `s^♯ : 𝒪_U ⟶ s_*𝒪_R`.

That is the geometric content of Equation [Stacks Project, Tag 0CKE] which is not formal: read
on sections it says that the two comorphisms agree on the regular functions pulled back along
the source, and those are exactly the generators of the defining ideal of `R₀` in `R`.

## Main results

* `structureSharp_source_comp_map_structureSharpThroughThickeningAt_eq`: the two comorphisms of
  two elements of `Γ₀`, read through the thickening, agree after the comorphism of the source.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)

/-- **The two comorphisms of two sections of `Γ₀` agree after the comorphism of the source.**
This is `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq`
in the groupoid situation: two elements of `Γ₀` are sections of one and the same morphism `s`
and have one and the same restriction `e₀` to `U₀`. -/
theorem structureSharp_source_comp_map_structureSharpThroughThickeningAt_eq
    (δ₁ δ₂ : InfinitesimalSections G U₀) :
    structureSharp C S hS G.source ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU C S hS G.source)).map
          (structureSharpThroughThickeningAt C S hS U₀ δ₁.1.1
            (restrictedUnit G U₀ ≫
              subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
            (comp_eq_restrictedUnit_comp G U₀ δ₁.2)) =
      structureSharp C S hS G.source ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU C S hS G.source)).map
          (structureSharpThroughThickeningAt C S hS U₀ δ₂.1.1
            (restrictedUnit G U₀ ≫
              subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
            (comp_eq_restrictedUnit_comp G U₀ δ₂.2)) :=
  structureSharp_comp_map_structureSharpThroughThickeningAt_eq C S hS U₀ δ₁.1.1 δ₂.1.1
    G.source _ (comp_eq_restrictedUnit_comp G U₀ δ₁.2)
    (comp_eq_restrictedUnit_comp G U₀ δ₂.2) (δ₁.1.2.trans δ₂.1.2.symm)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
