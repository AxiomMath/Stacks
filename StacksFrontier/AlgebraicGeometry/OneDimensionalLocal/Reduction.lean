module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.OneDimensionalLocal
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.PullbackStalk

/-!
# Tag 09N8 from flat base change alone

`Stacks.AlgebraicGeometry.OneDimensionalLocal.isZero_rightDerived_pushforward_of_isRetrocompact`
states [Stacks, Tag 09N8] from three hypotheses, one for each result the source cites that was
absent when it was proved: [Stacks, Tag 01XC], the vanishing half of [Stacks, Tag 02KH] part
(1), and [Stacks, Tag 0098].

The first and third are now theorems —
`Stacks.AlgebraicGeometry.OneDimensionalLocal.higherDirectImageVanishingAffine` and
`Stacks.AlgebraicGeometry.OneDimensionalLocal.pullbackFromSpecStalkDetectsStalk`. This file
discharges them, leaving the statement of Tag 09N8 resting on
`Stacks.AlgebraicGeometry.OneDimensionalLocal.FlatBaseChangeVanishing` alone.

## Main results

* `isZero_rightDerived_pushforward_of_flatBaseChangeVanishing`, in the namespace
  `Stacks.AlgebraicGeometry.OneDimensionalLocal`: [Stacks, Tag 09N8] from the vanishing half of
  [Stacks, Tag 02KH] part (1) and nothing else.

No `@[stacks 09N8]` attribute is attached: the tag asserts the conclusion unconditionally, and
one hypothesis remains.

## References

* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

/-- **[Stacks, Tag 09N8] from the vanishing half of [Stacks, Tag 02KH] part (1).** Let `X` be
a scheme all of whose local rings are Noetherian of dimension at most one, let `U ⊆ X` be a
retrocompact open and let `ℱ` be a quasi-coherent `𝒪_U`-module. Then `R ᵖ U.ι_* ℱ = 0` for
every `p > 0`, provided flat base change forces vanishing of higher direct images.

This is `isZero_rightDerived_pushforward_of_isRetrocompact` with its first and third
hypotheses discharged by `higherDirectImageVanishingAffine` (which is [Stacks, Tag 01XC]) and
`pullbackFromSpecStalkDetectsStalk` (which is [Stacks, Tag 0098]). Discharging
`FlatBaseChangeVanishing` gives Tag 09N8 with no hypotheses and no restatement. -/
theorem isZero_rightDerived_pushforward_of_flatBaseChangeVanishing
    (hBC : FlatBaseChangeVanishing.{u})
    (X : Scheme.{u}) (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (h_noetherian : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (F : U.toScheme.Modules) (hF : F.IsQuasicoherent)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward U.ι).rightDerived p).obj F) :=
  isZero_rightDerived_pushforward_of_isRetrocompact higherDirectImageVanishingAffine hBC
    pullbackFromSpecStalkDetectsStalk X U hU h_noetherian h_dimension F hF p hp

end Stacks.AlgebraicGeometry.OneDimensionalLocal

end
