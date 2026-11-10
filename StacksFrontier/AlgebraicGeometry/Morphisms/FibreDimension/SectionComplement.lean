module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleSectionComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Sections

/-!
# The complement of a section of an unramified morphism: complementarity and affineness

Let `g : X ⟶ S` be a separated morphism of schemes admitting a section `s : S ⟶ X`. The open
subscheme of `X` complementary to the image of `s` is `AlgebraicGeometry.sectionComplement` of
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleSectionComplement`, which also
proves,
for an étale separated `g`, that the complement is affine when `X` is and that passing to it drops
a bound on the fibre degrees by one (`AlgebraicGeometry.boundsFiberDegrees_sectionComplement`), the
splitting step of the second proof of Stacks Project, Tag 04DZ.

This file adds two facts about that same open subscheme which need less than étaleness.

## Main results

* `AlgebraicGeometry.isCompl_opensRange_sectionComplement` — when the section is an open
  immersion, its image and the complement are complementary open subschemes of `X`, so `X` is
  their disjoint union.
* `AlgebraicGeometry.isAffine_sectionComplement_of_unramified` — for an *unramified* separated
  `g` the complement of a section is affine when `X` is, being an open and closed subscheme of an
  affine scheme: the image of the section is open by Stacks Project, Tag 024T part (1). This is
  `AlgebraicGeometry.isAffine_sectionComplement` with `[Etale g]` weakened to `[Unramified g]`.

## References

* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (g : X ⟶ S) (s : S ⟶ X)

/-- The image of a section and its complement are complementary open subschemes of the source:
the source is their disjoint union. For an unramified separated `g` both are genuinely open, the
image by Stacks Project, Tag 024T part (1). -/
theorem isCompl_opensRange_sectionComplement [IsSeparated g] [IsOpenImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    IsCompl s.opensRange (sectionComplement g s hs) := by
  refine ⟨disjoint_iff.mpr (TopologicalSpace.Opens.ext ?_),
    codisjoint_iff.mpr (TopologicalSpace.Opens.ext ?_)⟩
  · change Set.range s.base ∩ (Set.range s.base)ᶜ = (∅ : Set X)
    exact Set.inter_compl_self _
  · change Set.range s.base ∪ (Set.range s.base)ᶜ = (Set.univ : Set X)
    exact Set.union_compl_self _

/-- The complement of a section of a separated unramified morphism is open and closed, hence
affine when the source is affine. This is `AlgebraicGeometry.isAffine_sectionComplement` with
`[Etale g]` weakened to `[Unramified g]`. -/
theorem isAffine_sectionComplement_of_unramified [Unramified g] [IsSeparated g] (hs : s ≫ g = 𝟙 S)
    [IsAffine X] : IsAffine (sectionComplement g s hs).toScheme := by
  have hclosed : IsClosed ((sectionComplement g s hs : X.Opens) : Set X) := by
    rw [coe_sectionComplement]
    exact (isOpenImmersion_of_isSection g s hs).base_open.isOpen_range.isClosed_compl
  have : IsClosedImmersion (sectionComplement g s hs).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed)
  exact isAffine_of_isAffineHom (sectionComplement g s hs).ι

end AlgebraicGeometry

end

end
