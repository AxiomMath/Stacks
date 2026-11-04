module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibre and the local base change embed into the source

Let `f : X ⟶ S` be a morphism of schemes and `s` a point of `S`. Both the inclusion
`X_s ⟶ X` of the scheme-theoretic fibre over `Spec κ(s)` and the projection
`Spec 𝒪_{S,s} ×_S X ⟶ X` are homeomorphisms onto their images.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isEmbedding_fiberι_and_pullbackSnd_fromSpecStalk`: the two
  maps above are topological embeddings.

## Implementation notes

Both maps are base changes of a preimmersion: `Spec κ(s) ⟶ S` and `Spec 𝒪_{S,s} ⟶ S` are
preimmersions, and preimmersions are stable under base change. A preimmersion is in particular
a topological embedding. This replaces the reduction to the affine case in the Stacks proof.

## References

* [Stacks Project, Tag 01K1](https://stacks.math.columbia.edu/tag/01K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `f : X ⟶ S` be a morphism of schemes and `s ∈ S`. Both the inclusion of the fibre
`X_s = X ×_S Spec κ(s) ⟶ X` and the projection `Spec 𝒪_{S,s} ×_S X ⟶ X` are homeomorphisms onto
their images. -/
@[stacks 01K1]
theorem isEmbedding_fiberι_and_pullbackSnd_fromSpecStalk {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) :
    IsEmbedding (f.fiberι s) ∧ IsEmbedding (pullback.snd (S.fromSpecStalk s) f) :=
  ⟨(f.fiberι s).isEmbedding, (pullback.snd (S.fromSpecStalk s) f).isEmbedding⟩

end AlgebraicGeometry.Scheme.Hom
