module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.NonSmoothLocus
public import StacksFrontier.AlgebraicGeometry.Variety.AffineSpaceDimension

/-!
# A small non-smooth locus misses a nonempty open of affine space

Let `q : A ⟶ 𝔸(n; Spec k)` be a morphism locally of finite presentation, with `A` locally of
finite type over `k` and a Noetherian space, and let `Σ` be the non-smooth locus of `q` with its
reduced induced structure. If `dim Σ < n` then the image of `Σ` in `𝔸(n; Spec k)` lies in a
proper closed subset, so there is a *nonempty* open `U` of `𝔸(n; Spec k)` whose preimage misses
`Σ` entirely — that is, `q` is smooth at every point over `U`.

This is the shape in which a dimension count on the non-smooth locus is consumed. In the proof of
[Stacks, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6) it is the passage from
"`dim Σ < r`" to the nonempty open over which the members of the linear system are smooth; the
hypothesis `hsing` of
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral` is exactly the conclusion
below, so that declaration's residual content is reduced by this file to the dimension bound
itself.

## Main results

* `AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus`: the nonempty open of
  `𝔸(n; Spec k)` over which `q` is smooth, produced from `dim Σ < n`.
* `AlgebraicGeometry.smooth_restrict_of_topologicalKrullDim_nonSmoothSubscheme_lt`: the same
  conclusion in the form "the restriction of `q` over some nonempty open is smooth".

## Implementation notes

The closed subset avoided is the closure of the image of `Σ`, which is proper by
`AlgebraicGeometry.AffineSpace.closure_range_ne_univ_of_topologicalKrullDim_lt`; its
hypotheses are the structure morphism of `Σ` over `k` (the closed immersion into `A` followed by
the structure morphism of `A`, hence locally of finite type) and the Noetherian space `Σ`
(a subspace of the Noetherian space `A`).

Nothing here needs the non-smooth locus to be *reduced*; what is used is only that
`AlgebraicGeometry.Scheme.Hom.nonSmoothSubschemeι` has the non-smooth points as its range and
that `AlgebraicGeometry.Scheme.Hom.nonSmoothSubschemeToBase` is the composite to the base. The
reduced structure is what makes the dimension of `Σ` the dimension of the closed subset, which
is the side the bound is proved on.

No `@[stacks]` attribute is attached: this is the bridge between a dimension count and an open
locus, not the statement of a tag.
-/

@[expose] public noncomputable section

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {A : Scheme.{u}} (n : Type u) [Finite n]

/-- **A non-smooth locus of dimension `< n` misses a nonempty open of `𝔸(n; Spec k)`.** For `q`
locally of finite presentation with `A` locally of finite type over `k` and a Noetherian space,
if the non-smooth subscheme of `q` has dimension `< n` then there is a nonempty open `U` of
`𝔸(n; Spec k)` with `q ⁻¹ᵁ U` inside the smooth locus of `q`. -/
theorem exists_nonempty_opens_preimage_subset_smoothLocus
    (q : A ⟶ AffineSpace n (Spec (.of k))) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [NoetherianSpace A]
    (hq : q ≫ (AffineSpace n (Spec (.of k)) ↘ Spec (.of k)) = sA)
    (hdim : topologicalKrullDim q.nonSmoothSubscheme < (Nat.card n : WithBot ℕ∞)) :
    ∃ U : (AffineSpace n (Spec (.of k))).Opens, (U : Set (AffineSpace n (Spec (.of k)))).Nonempty ∧
      ((q ⁻¹ᵁ U : A.Opens) : Set A) ⊆ (q.smoothLocus : Set A) := by
  have : NoetherianSpace q.nonSmoothSubscheme :=
    q.nonSmoothSubschemeι.isClosedEmbedding.isInducing.noetherianSpace
  have hcomp : q.nonSmoothSubschemeToBase ≫ (AffineSpace n (Spec (.of k)) ↘ Spec (.of k)) =
      q.nonSmoothSubschemeι ≫ sA := by
    rw [Scheme.Hom.nonSmoothSubschemeToBase_eq, Category.assoc, hq]
  have hne : closure (Set.range q.nonSmoothSubschemeToBase.base) ≠ Set.univ :=
    AffineSpace.closure_range_ne_univ_of_topologicalKrullDim_lt k n
      q.nonSmoothSubschemeToBase (q.nonSmoothSubschemeι ≫ sA) hcomp hdim
  refine ⟨⟨(closure (Set.range q.nonSmoothSubschemeToBase.base))ᶜ,
    isClosed_closure.isOpen_compl⟩, Set.nonempty_compl.mpr hne, fun z hz => ?_⟩
  by_contra hzs
  have hzmem : z ∈ Set.range q.nonSmoothSubschemeι :=
    (Scheme.Hom.range_nonSmoothSubschemeι q).ge hzs
  obtain ⟨w, rfl⟩ := hzmem
  refine hz ?_
  refine subset_closure ⟨w, ?_⟩
  rw [Scheme.Hom.nonSmoothSubschemeToBase_eq, Scheme.Hom.comp_apply]

/-- **The restriction of `q` over a nonempty open is smooth** when the non-smooth subscheme of
`q` has dimension `< n`. -/
theorem smooth_restrict_of_topologicalKrullDim_nonSmoothSubscheme_lt
    (q : A ⟶ AffineSpace n (Spec (.of k))) [LocallyOfFinitePresentation q]
    (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [NoetherianSpace A]
    (hq : q ≫ (AffineSpace n (Spec (.of k)) ↘ Spec (.of k)) = sA)
    (hdim : topologicalKrullDim q.nonSmoothSubscheme < (Nat.card n : WithBot ℕ∞)) :
    ∃ U : (AffineSpace n (Spec (.of k))).Opens, (U : Set (AffineSpace n (Spec (.of k)))).Nonempty ∧
      Smooth ((q ⁻¹ᵁ U).ι ≫ q) := by
  obtain ⟨U, hU, hsub⟩ :=
    exists_nonempty_opens_preimage_subset_smoothLocus k n q sA hq hdim
  refine ⟨U, hU, ?_⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
  intro z _
  rw [Scheme.Hom.mem_preimage]
  exact hsub z.2

end AlgebraicGeometry

end
