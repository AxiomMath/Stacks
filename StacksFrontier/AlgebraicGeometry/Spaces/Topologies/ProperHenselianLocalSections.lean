module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperHenselianPairSections
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale global sections of a proper algebraic space over a henselian local ring

Let `A` be a henselian local ring with maximal ideal `𝔪`, let `X` be an algebraic space over `A`
whose structure morphism `f : X ⟶ Spec A` is proper, and let `X₀ = X ×_{Spec A} Spec κ` be the
fibre of `f` over the closed point, where `κ = A ⧸ 𝔪` is the residue field
(`IsLocalRing.ResidueField A` is by definition `A ⧸ 𝔪`). For every sheaf of sets `ℱ` on
`X_étale`, restriction of sections `Γ(X, ℱ) ⟶ Γ(X₀, ℱ|_{X₀})` is bijective, where
`ℱ|_{X₀} = i⁻¹ ℱ` for the inclusion `i : X₀ ⟶ X`. This is [Stacks, Tag 0DFZ].

The proof is the source's: it is the special case `I = 𝔪` of [Stacks, Tag 0DFY]
(`AlgebraicGeometry.Space.isIso_globalSectionsRestriction_closedFibre_of_henselianPair`), since a
henselian local ring forms a henselian pair with its maximal ideal (`henselianPair_maximalIdeal`).

## Main results

* `AlgebraicGeometry.Space.isIso_globalSectionsRestriction_closedFibre_of_henselianLocalRing`:
  **[Stacks, Tag 0DFZ]**.

## References

* [Stacks Project, Tag 0DFZ](https://stacks.math.columbia.edu/tag/0DFZ)
* [Stacks Project, Tag 0DFY](https://stacks.math.columbia.edu/tag/0DFY)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} (A : Type u) [CommRing A] [HenselianLocalRing A]
  (hA : B.Contains (Spec (.of A))) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))),
    isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))⟩)

/-- **[Stacks, Tag 0DFZ].** Let `A` be a henselian local ring, let `X` be an algebraic space over
`A` whose structure morphism `f : X ⟶ Spec A` is proper, and let `i : X₀ ⟶ X` be the inclusion of
the fibre `X₀ = X ×_{Spec A} Spec (A ⧸ 𝔪)` of `f` over the closed point (`A ⧸ 𝔪` is the residue
field of `A`). For every sheaf of sets `ℱ` on `X_étale`, `Γ(X, ℱ) = Γ(X₀, ℱ|_{X₀})`: restriction of
global sections along `i`, natural in `ℱ`, is an isomorphism. -/
@[stacks 0DFZ, sga "4 XII 5.5" "more general"]
theorem isIso_globalSectionsRestriction_closedFibre_of_henselianLocalRing
    (hf : IsProper B (Spec (.of A)) hA f.hom) :
    IsIso (globalSectionsRestriction B (Spec (.of A)) hA
      (closedFibreInclusion A (maximalIdeal A) hA X f)) :=
  isIso_globalSectionsRestriction_closedFibre_of_henselianPair A (maximalIdeal A) hA X f
    (henselianPair_maximalIdeal A) hf

end AlgebraicGeometry.Space

end
