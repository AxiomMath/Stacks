module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceFormallySmooth
public import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicStack

/-!
# Algebraic stacks satisfy condition (RS*)

Let `𝒳` be an algebraic stack over the big fppf site of `S`. Its atlas `(Sch/U) ⟶ 𝒳` is
representable by algebraic spaces, surjective and smooth. Smooth morphisms of algebraic spaces are
formally smooth (the implication (1) ⟹ (2) of [Stacks Project, Tag 04AM]), so the atlas is
formally smooth on objects ([Stacks Project, Tag 06D3]), and a stack in groupoids with
representable diagonal admitting such an atlas satisfies condition (RS*) of
[Stacks Project, Tag 07Y8] (`Deformation.Artin.satisfiesRSStar_of_atlas`). Hence every algebraic
stack satisfies (RS*): this is [Stacks Project, Tag 0CXP].

## Main results

* `Deformation.Artin.satisfiesRSStar_of_isAlgebraicStack`: **Stacks 0CXP**, every algebraic stack
  satisfies condition (RS*).

## References

* [Stacks Project, Tag 0CXP](https://stacks.math.columbia.edu/tag/0CXP)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u w

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CXP.** Every algebraic stack over `S` satisfies condition (RS*) of
[Stacks Project, Tag 07Y8].

The atlas of the stack is representable by algebraic spaces, surjective and smooth; smooth
morphisms of algebraic spaces are formally smooth
(`AlgebraicGeometry.Space.formallySmooth_of_isSmooth_unconditional`, the implication (1) ⟹ (2) of
[Stacks Project, Tag 04AM]), so the atlas is formally smooth on objects
([Stacks Project, Tag 06D3]), and `Deformation.Artin.satisfiesRSStar_of_atlas` applies. -/
@[stacks 0CXP]
theorem satisfiesRSStar_of_isAlgebraicStack
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳) :
    ∀ hp : 𝒳.p.IsFiberedInGroupoids, SatisfiesRSStar B S hS 𝒳.p hp := by
  intro hp
  obtain ⟨h𝒳', ⟨hst, -⟩, hdiag, U, f, hrep, hprop⟩ := h𝒳
  let 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳 h𝒳'
  let P : Stack.schemeFibredCategory B S hS U ⟶ 𝒳' := Bicategory.InducedBicategory.mkHom f
  have hFS : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U) 𝒳' P :=
    BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth B S hS P hrep
      fun V y hy F hF hE => by
        refine Space.formallySmooth_of_isSmooth_unconditional ?_ ?_ _ (hprop V y hy F hF hE).2
        · exact ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj
            ⟨F, hF⟩).property
        · exact isAlgebraicSpace_yoneda B S hS _
  exact satisfiesRSStar_of_atlas B S hS 𝒳' hst hdiag P hrep hprop hFS

end Deformation.Artin

end
