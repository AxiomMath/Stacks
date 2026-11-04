module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of the proper direct image, in the shape the Chow squares consume

Let `V` be a locally Noetherian scheme, let `p : W ⟶ V` be a proper morphism and let `G` be a
coherent `𝒪_W`-module. Then `p_* G` is a coherent `𝒪_V`-module. This is the assertion of
[Stacks, Tag 02O5] about the ordinary direct image, which
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward` proves with no hypothesis.

The proper pushforward of cycles under a change of the base scheme, [Stacks, Tag 0FVL], reads a
proper pushforward of cycles as the cycle of a direct image through [Stacks, Tag 02R6], whose
statement in this library carries the coherence of that direct image as an instance hypothesis.
The resulting coherence obligation is universally quantified over the morphism and the module,
because it is discharged at several different morphisms inside one proof: at `f : Y ⟶ X`, at the
base change `f' : Y ×_S S' ⟶ X ×_S S'`, and at the closed immersions cutting out the subschemes
whose cycles are being pushed. This file states [Stacks, Tag 02O5] in exactly that quantified
shape, so that the obligation can be met by a term rather than carried as a binder.

## Main results

* `Stacks.Chow.properDirectImageIsCoherent` — the quantified coherence statement, with no
  hypothesis.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 0FVL](https://stacks.math.columbia.edu/tag/0FVL)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Chow

/-- **[Stacks, Tag 02O5], the ordinary direct image, quantified over the morphism and the
module.** For every proper morphism `p : W ⟶ V` of schemes with `V` locally Noetherian and every
coherent `𝒪_W`-module `G`, the direct image `p_* G` is a coherent `𝒪_V`-module.

This is `AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`, whose proof is
unconditional: it is the degree-zero case of
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`, which rests on the
witness sheaves of [Stacks, Tag 01YI] in the hypothesis-free form
`AlgebraicGeometry.ProperCoherenceWitness.hasGenericCoherentWitness`. -/
@[ega "III 2.2.5" "(i)", ega "III 3.2.2", sga "6 0 3.1" "partial"]
theorem properDirectImageIsCoherent {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p]
    [IsLocallyNoetherian V] (G : W.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pushforward p).obj G).IsCoherent :=
  ProperCoherenceWitness.isCoherent_pushforward p G

/-- The quantified form of `Stacks.Chow.properDirectImageIsCoherent`, as the proper pushforward
of cycles under a change of the base scheme, [Stacks, Tag 0FVL], consumes it: the coherence of
`p_* G` for *every* proper `p` onto a locally Noetherian target and every coherent `G`. -/
theorem forall_properDirectImageIsCoherent :
    ∀ {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] [IsLocallyNoetherian V]
      (G : W.Modules) [G.IsCoherent], ((Scheme.Modules.pushforward p).obj G).IsCoherent :=
  fun p _ _ G _ => properDirectImageIsCoherent p G

end Stacks.Chow

end
