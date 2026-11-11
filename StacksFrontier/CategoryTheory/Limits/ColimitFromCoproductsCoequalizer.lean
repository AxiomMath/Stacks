module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksCore.Tactic.StacksAttribute

/-!
# A colimit as a coequalizer of two maps between coproducts

Stacks 002P: for a diagram `M : 𝓘 ⥤ 𝓒`, if the coproducts `∐_{i ∈ Ob 𝓘} M_i` and
`∐_{a ∈ Arrows 𝓘} M_{s(a)}` exist and the coequalizer of the two maps
`φ, ψ : ∐_a M_{s(a)} ⟶ ∐_i M_i` exists (`φ` sends the summand `M_{s(a)}` to the summand
`M_{s(a)}` by the identity, `ψ` sends it to the summand `M_{t(a)}` by `M(a)`), then this
coequalizer is the colimit of the diagram.

Mathlib's `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit` states exactly this,
under exactly the source's hypotheses: it takes colimiting cofans `c₁` over the arrows (with
summands `F.obj f.1.1 = M_{s(a)}`) and `c₂` over the objects, two maps `s t : c₁.pt ⟶ c₂.pt`
pinned down componentwise by `hs` (this is `ψ`) and `ht` (this is `φ`), and a colimiting
cofork of `s, t`, and concludes that the cocone built from that cofork is colimiting.

The other registrations of 002P are variants with stronger hypotheses:
`colimitCoconeOfCoequalizerAndCoproduct` (in `StacksCore/CategoryTheory/Limits.lean`) assumes all
coequalizers exist in `𝓒`, and Mathlib's `has_colimits_of_hasCoequalizers_and_coproducts`
assumes all coproducts and all coequalizers and concludes that all colimits exist.
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 002P "exactly the source's hypotheses: the coequalizer of the two maps between \
  the two given coproducts is the colimit"
  CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit
