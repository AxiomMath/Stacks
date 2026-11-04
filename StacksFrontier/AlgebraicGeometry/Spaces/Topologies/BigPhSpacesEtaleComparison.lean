module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfBigFppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtaleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineKFlatModel

/-!
# The inclusion of the spaces-étale site into the big ph site of an algebraic space

Let `P` be a big ph site of algebraic spaces over `S` and `X` an algebraic space of `P`. The
inclusion `X_{spaces, étale} → (Spaces/X)_ph`, `W ↦ W/X`, defines a morphism of topoi
`h_X : Sh((Spaces/X)_ph) → Sh(X_étale)`; it is the comparison morphism `a_X = π_X ∘ ε_X` of
Stacks 0DGW, for a big étale site of algebraic spaces built on the same big fppf site of schemes,
which always exists. This file reads Stacks 0DGT (1) and Stacks 0DGX (1) on `h_X`.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.bigEtaleSpaceSite`: a big étale site of algebraic spaces with
  the same algebraic spaces as `P`.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.isIso_spacesEtaleComparison_unit`: **Stacks 0DGT (1)** on
  `h_X`, the unit `ℱ ⟶ h_{X,*} h_X⁻¹ ℱ` is invertible, that is `h_X⁻¹` is fully faithful.
* `AlgebraicGeometry.BigPHSpaceSite.mem_essImage_bigPHMorphism_pushforward`: **Stacks 0DGX (1)**
  on `h`: for a proper morphism `f : Y ⟶ X`, the direct image `f_{big, ph, *}` sends sheaves in
  the essential image of `h_Y⁻¹` to sheaves in the essential image of `h_X⁻¹`.

## References

* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
* [Stacks Project, Tag 0DGX](https://stacks.math.columbia.edu/tag/0DGX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S)

/-- A big étale site of algebraic spaces whose algebraic spaces are those of `P`: the one of
Stacks 000X over the auxiliary big fppf site of schemes of `P`. -/
def bigEtaleSpaceSite : BigEtaleSpaceSite S :=
  (Space.bigFppfSpaceSiteOfSchemeSite P.fppfSite S P.fppf_mem).bigEtaleSpaceSite

/-- The big étale site `P.bigEtaleSpaceSite` is built on the big fppf site of schemes of `P`. -/
theorem fppfSite_eq_bigEtaleSpaceSite_fppfSite : P.fppfSite = P.bigEtaleSpaceSite.fppfSite :=
  rfl

/-- The direct image of the comparison morphism `a_X = π_X ∘ ε_X` of Stacks 0DGW is restriction
along the inclusion `X_{spaces, étale} → Spaces/X`. -/
theorem phToSmallEtaleMorphism_pushforward_eq (X : P.Spaces) :
    (phToSmallEtaleMorphism P P.bigEtaleSpaceSite P.fppfSite_eq_bigEtaleSpaceSite_fppfSite
      X).pushforward = (Space.spacesEtaleComparisonMorphism P.topology X).pushforward :=
  rfl

/-- The inverse image along `X_{spaces, étale} → Spaces/X` is the inverse image of the comparison
morphism `a_X` of Stacks 0DGW: the two are left adjoint to the same direct image. -/
def spacesEtaleComparisonInverseImageIso (X : P.Spaces) :
    (Space.spacesEtaleComparisonMorphism P.topology X).inverseImage ≅
      (phToSmallEtaleMorphism P P.bigEtaleSpaceSite P.fppfSite_eq_bigEtaleSpaceSite_fppfSite
        X).inverseImage :=
  (Space.spacesEtaleComparisonMorphism P.topology X).adj.leftAdjointUniq
    (phToSmallEtaleMorphism P P.bigEtaleSpaceSite P.fppfSite_eq_bigEtaleSpaceSite_fppfSite X).adj

/-- **Stacks 0DGT (1) on the inclusion `X_{spaces, étale} → (Spaces/X)_ph`**: the inverse image
`h_X⁻¹` is fully faithful, its unit being invertible. -/
theorem isIso_spacesEtaleComparison_unit (X : P.Spaces) :
    IsIso (Space.spacesEtaleComparisonMorphism P.topology X).adj.unit := by
  have := isIso_phToSmallEtaleMorphism_unit P P.bigEtaleSpaceSite
    P.fppfSite_eq_bigEtaleSpaceSite_fppfSite X
  have hff := ((phToSmallEtaleMorphism P P.bigEtaleSpaceSite
    P.fppfSite_eq_bigEtaleSpaceSite_fppfSite X).adj.fullyFaithfulLOfIsIsoUnit).ofIso
      (spacesEtaleComparisonInverseImageIso P X).symm
  exact @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ _ hff.full hff.faithful

/-- **Stacks 0DGX (1) on the inclusions `X_{spaces, étale} → (Spaces/X)_ph`.** For a proper
morphism `f : Y ⟶ X` of algebraic spaces, the direct image along `f_{big, ph}` of a sheaf in the
essential image of `h_Y⁻¹` is in the essential image of `h_X⁻¹`: it is `h_X⁻¹ f_{small, *}`. -/
theorem mem_essImage_bigPHMorphism_pushforward {X Y : P.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom)
    {M : Sheaf (BigPHSpaceOver.topology P Y) (Type (u + 1))}
    (hM : (Space.spacesEtaleComparisonMorphism P.topology Y).inverseImage.essImage M) :
    (Space.spacesEtaleComparisonMorphism P.topology X).inverseImage.essImage
      ((bigPHMorphism P f).pushforward.obj M) := by
  obtain ⟨K, ⟨e⟩⟩ := hM
  exact ⟨_, ⟨(spacesEtaleComparisonInverseImageIso P X).app _ ≪≫
    (phToSmallEtalePushforwardIsoOfIsProper P _ _ f hf).app K ≪≫
      (bigPHMorphism P f).pushforward.mapIso
        (((spacesEtaleComparisonInverseImageIso P Y).app K).symm ≪≫ e)⟩⟩

end AlgebraicGeometry.BigPHSpaceSite

end
