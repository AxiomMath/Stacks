module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible

/-!
# When the fibrewise connected-component locus is a neighbourhood of a component

Let `f : X ⟶ Y` be a morphism of schemes with a section and let `X⁰ ⊆ X` be the union of the
connected components of the fibres meeting that section.  If `X⁰` is locally constructible and
stable under generalization, then `X⁰` is a neighbourhood of the selected component of every
fibre.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent_of_specializes`:
  the neighbourhood statement from local constructibility and stability under generalization.

## Implementation notes

The fibrewise component is regarded as a subset of the total space through the canonical map
from the scheme-theoretic fibre, and being a neighbourhood of it is membership in its
neighbourhood filter.  Membership in that filter is tested one point at a time, and at each point
the two hypotheses are exactly those of Stacks tag 05LW, that a locally constructible subset of a
scheme containing every generalization of a point is a neighbourhood of that point.

No flatness, finite presentation or reducedness hypothesis appears:  those are what Stacks tag
055Q uses to establish the two hypotheses here.  Local constructibility of `X⁰` for a morphism of
finite presentation is Stacks tag 055P, which is absent from this repository, as are the Stacks
tags 055N, 054Y, 054W and 055G on which it rests.  Stability under generalization is the
discrete-valuation-ring half of the proof of tag 055Q, which runs through Stacks tags 054F and
055J, both present, after a reduction to a Noetherian base which is not.

## References

* [Stacks Project, Lemma 37.29.4 (Tag 055Q)](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Lemma 37.29.3 (Tag 055P)](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- If the fibrewise connected-component locus `X⁰` of a sectioned morphism is locally
constructible and contains every generalization of each of its points, then it is a
neighbourhood of the selected connected component of every fibre.

This is the final assembly of Stacks tag 055Q:  its two hypotheses are, respectively, Stacks
tag 055P and the conclusion of the discrete-valuation-ring step of the source's proof. -/
theorem locus_mem_nhdsSet_fiberComponent_of_specializes (D : ConnectedAlongSection.{u})
    (y : D.Y) (hc : IsLocallyConstructible D.locus)
    (hgen : ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus) :
    D.locus ∈ 𝓝ˢ (D.f.fiberι y '' D.fiberComponent y) := by
  rw [mem_nhdsSet_iff_forall]
  rintro x ⟨z, hz, rfl⟩
  exact mem_nhds_of_isLocallyConstructible_of_specializes_subset hc
    fun _ hx' => hgen _ ((D.mem_locus _).mpr ⟨y, z, hz, rfl⟩) _ hx'

end ConnectedAlongSection

end AlgebraicGeometry

end
