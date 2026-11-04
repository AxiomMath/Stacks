module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.TransitionSwap

/-!
# Effectivity of a descent datum is local, at the source's hypothesis

Let `f : X ⟶ S` be a surjective, quasi-compact, flat morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S`. [Stacks, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
says that `(V, φ)` is effective as soon as every point `v ∈ V` has an open neighbourhood
`W ⊆ V` with `φ(W ×_S X) ⊆ X ×_S W` such that the restricted datum `(W, φ|_{W ×_S X})` is
effective.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen_le`: Tag 0AP4 with
  exactly the source's hypothesis, the *inclusion* `φ(W ×_S X) ⊆ X ×_S W`.

## Implementation notes

`AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen` proves the same
conclusion from neighbourhoods satisfying the *equality*
`AlgebraicGeometry.DescentDatum.IsTransitionInvariant`. The equality is not assumed here: it is
derived from the inclusion and the cocycle condition of the datum by
`AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_le`. That derivation is also what
makes the restricted datum `(W, φ|_{W ×_S X})`, built by
`AlgebraicGeometry.DescentDatum.restrictOpen`, available under the inclusion alone, which is
how the source uses it.

## References

* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

namespace DescentDatum

open CategoryTheory Limits

/-- **Effectivity of a descent datum is local on the scheme it is carried by.** Let
`f : X ⟶ S` be a surjective, quasi-compact, flat morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S`. Suppose that for every `v ∈ V` there is an open subscheme
`v ∈ W ⊆ V` with `φ(W ×_S X) ⊆ X ×_S W` and such that the descent datum
`(W, φ|_{W ×_S X})` is effective. Then `(V, φ)` is effective.

Only the inclusion `φ(W ×_S X) ⊆ X ×_S W` is asked for. The reverse inclusion, which makes
`φ|_{W ×_S X}` an isomorphism onto `X ×_S W` and so the gluing isomorphism of the restricted
datum, follows from the cocycle condition by
`AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_le`. -/
@[stacks 0AP4]
theorem isEffective_of_forall_exists_restrictOpen_le {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (h : ∀ v : D.over.left, ∃ (W : D.over.left.Opens)
      (hW : D.transitionPullbackIso.hom ''ᵁ (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) ≤
        pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W),
      v ∈ W ∧
        DescentData.IsEffective (D.restrictOpen W (D.isTransitionInvariant_of_le W hW))) :
    DescentData.IsEffective D := by
  refine isEffective_of_forall_exists_restrictOpen D fun v ↦ ?_
  obtain ⟨W, hW, hmem, heff⟩ := h v
  exact ⟨W, D.isTransitionInvariant_of_le W hW, hmem, heff⟩

end DescentDatum

end AlgebraicGeometry
