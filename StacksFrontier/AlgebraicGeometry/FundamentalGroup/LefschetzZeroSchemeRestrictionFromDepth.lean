module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Chain
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LefschetzZeroSchemeSectionsComplete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lefschetz for the fundamental group: restriction to the zero scheme of an ample section

Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L` and `Y = Z(s)` its zero scheme. [Stacks, Tag 0ELC] says that if

`depth(𝒪_{X, x}) + dim({x}‾) > 1`

at every point `x` of `X ∖ Y`, then the restriction functor `FÉt_X ⟶ FÉt_Y` is fully faithful.
More precisely, `FÉt_V ⟶ FÉt_Y` is fully faithful for every open subscheme `V ⊆ X` containing
`Y`.

This file proves both statements under exactly those hypotheses.

## The proof

The source calls both statements formal consequences of [Stacks, Tag 0EJZ] and of
[Stacks, Tag 0EL1] (respectively [Stacks, Tag 0EL2]). Here that chain is:

* `Stacks.Algebraization.amplePowerSectionsCompleteFromDepth` is [Stacks, Tag 0EL2] read in the
  shape of condition (2) of [Stacks, Tag 0EJZ]. It says that the depth hypothesis makes
  `Γ(V, ℒ^{⊗ m}) → lim Γ(Y_n, ℒ^{⊗ m}|_{Y_n})` bijective, for a suitable power `ℒ` of `L` and
  every `m`, both for `V = X` and for every open `V ⊇ Y`.
* `Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers` and
  `Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree` are the
  implications `(2) ⇒ (3) ⇒ (4)` of [Stacks, Tag 0EKP].
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence` is the
  fully faithful half of [Stacks, Tag 0EL9]: full faithfulness of completion on finite locally
  free modules gives full faithfulness of restriction of finite étale covers. This is
  [Stacks, Tag 0EL8], proved without any auxiliary hypothesis.

`X` is Noetherian because it is proper over a field and quasi-compact
(`Stacks.FundamentalGroup.isNoetherian_of_isProper_of_isAmple`), and so is every open
neighbourhood of `Y`.

## Main results

* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper` — the
  first statement of [Stacks, Tag 0ELC].
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_neighborhood_of_isProper` — the
  second statement of [Stacks, Tag 0ELC].

## References

* [Stacks Project, Tag 0ELC](https://stacks.math.columbia.edu/tag/0ELC)
* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL9](https://stacks.math.columbia.edu/tag/0EL9)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

/-- **[Stacks, Tag 0ELC], first statement.** Let `k` be a field, `X` a proper scheme over `k`,
`L` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)` and `Y = Z(s)` the zero scheme of `s`. If
`depth(𝒪_{X, x}) + dim({x}‾) > 1` at every point `x` of `X ∖ Y`, then the restriction functor
`FÉt_X ⟶ FÉt_Y` is fully faithful.

`CategoryTheory.Functor.FullyFaithful` carries the inverse map on hom sets as data, so full
faithfulness is stated as `Nonempty _.FullyFaithful`. -/
@[stacks 0ELC "first statement: restriction FÉt_X → FÉt_Y to the zero scheme of a section of \
an ample invertible module on a proper scheme over a field is fully faithful when \
depth + dim > 1 off the zero scheme", sga "1 X 2.13" "partial"]
public theorem fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    Nonempty (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).FullyFaithful := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  exact fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence _
    (Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree _
      (Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers _
        (Stacks.Algebraization.amplePowerSectionsCompleteFromDepth k g L hL s hdepth).1))

/-- **[Stacks, Tag 0ELC], second statement.** In the situation of
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper`, the
restriction functor `FÉt_V ⟶ FÉt_Y` is fully faithful for every open subscheme `V ⊆ X`
containing `Y`.

The open subschemes containing `Y` are `Stacks.FundamentalGroup.Neighborhood X Y`, and the
closed immersion `Y ⟶ V` is `Stacks.FundamentalGroup.Neighborhood.toSchemeHom`. -/
@[stacks 0ELC "second statement: restriction FÉt_V → FÉt_Y is fully faithful for every open V \
of X containing the zero scheme", sga "1 X 2.13" "partial", sga "2 XII 3.5" "more general"]
public theorem fullyFaithful_finiteEtaleBaseChange_neighborhood_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : Γ(L, ⊤))
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s))
    (W : Neighborhood X (zeroScheme X L s)) :
    Nonempty (finiteEtaleBaseChange
      (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).FullyFaithful := by
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  have : IsNoetherian (Neighborhood.open X (zeroScheme X L s) W).toScheme :=
    Stacks.Coherent.isNoetherian_of_isOpenImmersion
      (Neighborhood.open X (zeroScheme X L s) W).ι
  exact fullyFaithful_finiteEtaleBaseChange_of_completionEquivalence _
    (Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree _
      (Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers _
        ((Stacks.Algebraization.amplePowerSectionsCompleteFromDepth k g L hL s hdepth).2 W)))

end Stacks.FundamentalGroup

end

end
