module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentOfCrystal

/-!
# A crystal in quasi-coherent modules satisfies the hypotheses of [Stacks, Tag 07JN]

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  [Stacks, Tag 07JN]
imposes two conditions on a sheaf `F` of `𝒪_{X/S}`-modules on the small crystalline site:

1. `F` is locally quasi-coherent, and
2. for every morphism `(U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` whose map `T ⟶ T'` on ambient
   schemes is a closed immersion, the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is surjective.

[Stacks, Tag 07LM] is stated for a *crystal in quasi-coherent modules*, and [Stacks, Tag 07LN]
observes that the proof uses only those two conditions.  A crystal in quasi-coherent modules
satisfies both; for a crystal the comparison morphisms are in fact locally surjective along
*every* morphism of the site.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.satisfiesVanishingHypotheses_of_isQuasicoherentOnSite` — **a crystal in quasi-coherent
  `𝒪_{X/S}`-modules satisfies conditions (1) and (2) of [Stacks, Tag 07JN]**.

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-- **A crystal in quasi-coherent `𝒪_{X/S}`-modules satisfies conditions (1) and (2) of
[Stacks, Tag 07JN].**

The first conjunct is local quasi-coherence and the second is local surjectivity of the
comparison morphisms along a morphism of `Cris(X/S)` whose map on ambient schemes is a closed
immersion. -/
theorem satisfiesVanishingHypotheses_of_isQuasicoherentOnSite (hF : F.IsQuasicoherentOnSite) :
    IsLocallyQuasiCoherent F ∧ CohomologyRestriction.IsSurjectiveComparison F.val :=
  ⟨isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF,
    isSurjectiveComparison_of_isSheafCrystal (isSheafCrystal_of_isQuasicoherentOnSite F hF)⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
