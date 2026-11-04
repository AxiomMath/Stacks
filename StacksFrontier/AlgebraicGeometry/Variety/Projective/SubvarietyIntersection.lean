module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ProjectiveIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# Intersections of closed subsets of the projective space of a vector space

Let `V` be a nonzero finite-dimensional vector space over a field `k` and let `X` and `Y` be
nonempty closed subsets of `𝐏(V)` with `dim 𝐏(V) ≤ dim X + dim Y`. Then `X ∩ Y` is nonempty, and
its dimension satisfies `dim X + dim Y ≤ dim (X ∩ Y) + dim 𝐏(V)` — the inequality opposite to
the one that defines proper intersection (Tag 0AZQ), so that two closed subvarieties meeting
properly meet in exactly the expected dimension.

This is Stacks Tag 0B2R read in `𝐏(V)` instead of in `ℙⁿ_k`. The two statements of that tag,
`AlgebraicGeometry.inter_nonempty_projectiveSpaceOverRing` and
`AlgebraicGeometry.le_topologicalKrullDim_inter_projectiveSpaceOverRing`, are about
`AlgebraicGeometry.projectiveSpaceOverRing`; a basis of `V` indexed by `Fin (n + 1)` identifies
the two models by `AlgebraicGeometry.basisProjectiveSpaceIso`, and dimension and nonemptiness are
both invariant under the resulting homeomorphism.

## Main results

* `AlgebraicGeometry.nonempty_inter_projectiveSpaceOfModule`: the intersection is nonempty.
* `AlgebraicGeometry.add_le_topologicalKrullDim_inter_add_projectiveSpaceOfModule`: the
  intersection has at least the expected dimension.

## Implementation notes

Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, and the hypothesis and both
conclusions are stated additively, with no truncated subtraction: the form Tag 0B2R is stated in,
`(r + s - n : ℕ) ≤ dim (X ∩ Y)` with `r`, `s` natural numbers naming the two dimensions, is
recovered inside the proofs. A nonempty closed subset of `𝐏(V)` does have a natural number as its
dimension — it is neither `⊥`, the subset being nonempty, nor `⊤`, the dimension of `𝐏(V)` being
finite — and `natCast_eq_topologicalKrullDim_of_nonempty` is that squeeze.

The vector space is asked to be nonzero rather than `𝐏(V)` to be nonempty: for `V = 0` the
hypothesis that `X` is a nonempty subset of the empty `𝐏(V)` is already contradictory, so no
generality is lost, and `Module.finrank k V = n + 1` is what the coordinate comparison consumes.

## References

* [Stacks Project, Tag 0B2R](https://stacks.math.columbia.edu/tag/0B2R)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- **The dimension of a nonempty subset of a finite-dimensional space is a natural number.** It
is not `⊥` because the subset is nonempty, and not `⊤` because it is bounded by the dimension of
the ambient space. -/
theorem natCast_eq_topologicalKrullDim_of_nonempty {T : Type*} [TopologicalSpace T]
    {S : Set T} (hS : S.Nonempty) {n : ℕ} (hT : topologicalKrullDim T = (n : WithBot ℕ∞)) :
    ∃ r : ℕ, topologicalKrullDim ↥S = (r : WithBot ℕ∞) := by
  have hbot : topologicalKrullDim ↥S ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    obtain ⟨x, hx⟩ := hS
    exact fun h => h.false ⟨x, hx⟩
  have hle : topologicalKrullDim ↥S ≤ (n : WithBot ℕ∞) := by
    rw [← hT]
    exact topologicalKrullDim_subspace_le T S
  have htop : topologicalKrullDim ↥S ≠ ⊤ := by
    intro h
    exact natCast_ne_top_withBot n (top_le_iff.mp (h ▸ hle))
  exact ⟨((topologicalKrullDim ↥S).unbotD 0).toNat, eq_natCast_unbotD_toNat hbot htop⟩

/-- The dimensions of `𝐏(V)`, `X` and `Y` are natural numbers `n`, `r`, `s`, with `n ≤ r + s`, and
`X ∩ Y` is nonempty of dimension at least `r + s - n`: Tag 0B2R transported along a coordinate
identification of `𝐏(V)` with `ℙⁿ_k`. -/
private theorem exists_nat_dims_inter_nonempty_and_le [FiniteDimensional k V] [Nontrivial V]
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥X + topologicalKrullDim ↥Y) :
    ∃ n r s : ℕ, topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) ∧
      topologicalKrullDim ↥X = (r : WithBot ℕ∞) ∧ topologicalKrullDim ↥Y = (s : WithBot ℕ∞) ∧
      (X ∩ Y).Nonempty ∧ ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(X ∩ Y) ∧
      n ≤ r + s := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  obtain ⟨r, hr⟩ := natCast_eq_topologicalKrullDim_of_nonempty hXne hdimP
  obtain ⟨s, hs⟩ := natCast_eq_topologicalKrullDim_of_nonempty hYne hdimP
  have hrs : n ≤ r + s := by
    rw [hdimP, hr, hs] at hle
    exact_mod_cast hle
  set e := (basisProjectiveSpaceIso (Module.finBasisOfFinrankEq k V hn)).hom.homeomorph with he
  have hXd := (topologicalKrullDim_preimage_of_homeomorph e X).trans hr
  have hYd := (topologicalKrullDim_preimage_of_homeomorph e Y).trans hs
  obtain ⟨z, hz⟩ := inter_nonempty_projectiveSpaceOverRing k n r s (e ⁻¹' X) (e ⁻¹' Y)
    (hXc.preimage e.continuous) (hYc.preimage e.continuous)
    (hXne.preimage e.surjective) (hYne.preimage e.surjective) hXd hYd hrs
  have key := le_topologicalKrullDim_inter_projectiveSpaceOverRing k n r s (e ⁻¹' X) (e ⁻¹' Y)
    (hXc.preimage e.continuous) (hYc.preimage e.continuous)
    (hXne.preimage e.surjective) (hYne.preimage e.surjective) hXd hYd hrs
  have hpre : e ⁻¹' X ∩ e ⁻¹' Y = e ⁻¹' (X ∩ Y) := rfl
  rw [hpre, topologicalKrullDim_preimage_of_homeomorph e (X ∩ Y)] at key
  exact ⟨n, r, s, hdimP, hr, hs, ⟨e z, hz.1, hz.2⟩, key, hrs⟩

/-- **Stacks Project, Tag 0B2R (nonemptiness), in `𝐏(V)`.** Two nonempty closed subsets of the
projective space of a nonzero finite-dimensional vector space whose dimensions add up to at least
`dim 𝐏(V)` meet.

This is what makes the hypothesis `X ∩ Y ≠ ∅` of Tag 0B1S do work: for `X` and `Y` intersecting
properly and meeting at all, `dim 𝐏(V) ≤ dim X + dim Y`, and the hypothesis then transfers to
every closed subset of `𝐏(V)` of the same dimension as `X`. -/
theorem nonempty_inter_projectiveSpaceOfModule [FiniteDimensional k V] [Nontrivial V]
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥X + topologicalKrullDim ↥Y) :
    (X ∩ Y).Nonempty := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := exists_nat_dims_inter_nonempty_and_le hXc hYc hXne hYne hle
  exact h

/-- **Stacks Project, Tag 0B2R (dimension), in `𝐏(V)`.** Two nonempty closed subsets of the
projective space of a nonzero finite-dimensional vector space whose dimensions add up to at least
`dim 𝐏(V)` meet in at least the expected dimension, stated without subtraction as
`dim X + dim Y ≤ dim (X ∩ Y) + dim 𝐏(V)`.

This is the inequality opposite to the one defining `AlgebraicGeometry.IntersectProperly`, so
for `X` and `Y` meeting properly the two together pin `dim (X ∩ Y)` down exactly. -/
theorem add_le_topologicalKrullDim_inter_add_projectiveSpaceOfModule [FiniteDimensional k V]
    [Nontrivial V] {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X)
    (hYc : IsClosed Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥X + topologicalKrullDim ↥Y) :
    topologicalKrullDim ↥X + topologicalKrullDim ↥Y ≤
      topologicalKrullDim ↥(X ∩ Y) + topologicalKrullDim (projectiveSpaceOfModule k V) := by
  obtain ⟨n, r, s, hdimP, hr, hs, -, key, hrs⟩ :=
    exists_nat_dims_inter_nonempty_and_le hXc hYc hXne hYne hle
  rw [hdimP, hr, hs]
  calc ((r : WithBot ℕ∞) + (s : WithBot ℕ∞))
      = (((r + s - n : ℕ) : WithBot ℕ∞) + (n : WithBot ℕ∞)) := by
        rw [← Nat.cast_add, ← Nat.cast_add]
        norm_cast
        omega
    _ ≤ topologicalKrullDim ↥(X ∩ Y) + (n : WithBot ℕ∞) := add_le_add key le_rfl

end AlgebraicGeometry

end
