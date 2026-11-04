module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Lipman
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.InvertibleDualizingBlowupSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Lipman's theorem on resolution of two-dimensional schemes

This file registers [Stacks, Tag 0BGP]: the equivalence, for a two-dimensional integral
Noetherian scheme, of having a regular alteration, a resolution of singularities, a resolution by
normalized blowups, and finite normalization with finitely many singular points whose completed
local rings are normal. It is
`AlgebraicGeometry.tfae_exists_isAlteration_isRegular_of_gorensteinChain` of
`…/Resolution/Lipman.lean` with [Stacks, Tag 0BBV] supplied in its Gorenstein form,
`AlgebraicGeometry.exists_singularPointBlowupChain_isGorenstein`.

## Main results

* `AlgebraicGeometry.tfae_exists_isAlteration_isRegular` — [Stacks, Tag 0BGP].

## References

* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BGP (Lipman).** Let `Y` be a two-dimensional integral Noetherian
scheme. The following are equivalent:

1. there exists an alteration `X ⟶ Y` with `X` regular;
2. there exists a resolution of singularities of `Y`;
3. `Y` has a resolution of singularities by normalized blowups;
4. the normalization `Y^ν ⟶ Y` is finite, `Y^ν` has finitely many singular points, and the
   completion of the local ring of `Y^ν` at each of them is normal. -/
@[stacks 0BGP]
theorem tfae_exists_isAlteration_isRegular (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hdim : topologicalKrullDim Y = 2) :
    List.TFAE
      [∃ (X : Scheme.{u}) (f : X ⟶ Y), IsAlteration f ∧ IsRegular X,
       ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f,
       HasResolutionByNormalizedBlowUps Y,
       ∃ hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite,
        IsFinite (Scheme.normalization Y hY) ∧
        (singularLocus (Y.normalizationScheme hY)).Finite ∧
        ∀ y : Y.normalizationScheme hY, y ∈ singularLocus (Y.normalizationScheme hY) →
          IsNormalRing (AdicCompletion
            (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
            ((Y.normalizationScheme hY).presheaf.stalk y))] :=
  tfae_exists_isAlteration_isRegular_of_gorensteinChain
    (fun B _ _ _ _ hN hd hr hc => exists_singularPointBlowupChain_isGorenstein B hN hd hr hc)
    Y hdim

end AlgebraicGeometry

end
