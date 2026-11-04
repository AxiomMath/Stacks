module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.RingTheory.PseudoCoherentMap.Noetherian
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence over a locally Noetherian base

Over a locally Noetherian base scheme pseudo-coherence carries no information beyond local
finiteness of type: a morphism to a locally Noetherian scheme is pseudo-coherent if and only if
it is locally of finite type.

## Main results

* `RingHom.PseudoCoherent.of_finiteType`: the algebra content of Stacks 0684, that a ring map of
  finite type out of a Noetherian ring is pseudo-coherent.
* `AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType`: **Stacks 0684**, a morphism to a
  locally Noetherian scheme is pseudo-coherent if and only if it is locally of finite type.

## Implementation notes

The direction from local finiteness of type to pseudo-coherence is read off affine-locally
through `AlgebraicGeometry.HasRingHomProperty.iff_appLE`, using that
`AlgebraicGeometry.hasRingHomProperty_pseudoCoherent` presents
`AlgebraicGeometry.PseudoCoherent` as the morphism property attached to
`RingHom.PseudoCoherent`.

The forward direction holds with no hypothesis on the base and is found by type class search
through `AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent` (Stacks 0682), since a
pseudo-coherent morphism is locally of finite presentation, hence locally of finite type. For the
converse, the sections of a locally Noetherian scheme over an affine open form a Noetherian ring,
and a finite-type algebra over a Noetherian ring is pseudo-coherent by Stacks 067I, already
available as `Algebra.PseudoCoherent.of_finiteType`. The Stacks proof passes explicitly through a
presentation `A = R[x_1, …, x_n]/I` and the fact that `A` is then a pseudo-coherent
`R[x_1, …, x_n]`-module; that argument is what Stacks 067I contains.

## References

* [The Stacks Project, Lemma 37.60.9 (0684)](https://stacks.math.columbia.edu/tag/0684)
* [The Stacks Project, Lemma 15.83.3 (067I)](https://stacks.math.columbia.edu/tag/067I)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace RingHom

/-- **The algebra content of Stacks 0684.** A ring homomorphism of finite type whose source is
Noetherian is pseudo-coherent.

This is Stacks 067I, `Algebra.PseudoCoherent.of_finiteType`, restated for
`RingHom.PseudoCoherent`. -/
theorem PseudoCoherent.of_finiteType {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] {f : A →+* B} (h : f.FiniteType) : PseudoCoherent f := by
  algebraize [f]
  exact Algebra.PseudoCoherent.of_finiteType A B

end RingHom

namespace AlgebraicGeometry

/-- **Stacks 0684.** A morphism of schemes whose target is locally Noetherian is pseudo-coherent
if and only if it is locally of finite type.

A pseudo-coherent morphism is always locally of finite type. Conversely, over a locally
Noetherian base the sections over an affine open form a Noetherian ring, so every map on sections
over a compatible pair of affine opens is a finite-type ring map out of a Noetherian ring, hence
pseudo-coherent by Stacks 067I. -/
@[stacks 0684, sga "6 III 1.3" "loc. noetherian case"]
theorem pseudoCoherent_iff_locallyOfFiniteType {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) : PseudoCoherent f ↔ LocallyOfFiniteType f := by
  refine ⟨fun _ ↦ inferInstance, fun hf ↦ ?_⟩
  rw [HasRingHomProperty.iff_appLE (P := @PseudoCoherent)]
  intro V U e
  have : IsNoetherianRing Γ(S, V.1) := IsLocallyNoetherian.component_noetherian V
  exact RingHom.PseudoCoherent.of_finiteType
    (HasRingHomProperty.appLE @LocallyOfFiniteType f hf V U e)

end AlgebraicGeometry

end
