module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The dimension drop of the induction step of Tag 0F27

The induction step of [Stacks, Tag 0F27] replaces a coherent triple `(F, F₀, α)` by the
cokernel `(G, G₀, β)` of multiplication by a section `s` of the invertible triple which does not
vanish at any associated point of `F`. The reason the induction terminates is that the support
of `G` is strictly smaller than the support of `F`: it is contained in it and misses its generic
points, hence is nowhere dense in it, hence has smaller dimension.

This file supplies the second half of that argument — nowhere density to the dimension bound —
in the two forms
`Stacks.Algebraization.HasHilbertInductionStep` consumes, namely

* a bound `e + 1` for `dim(Supp F)` gives the bound `e` for `dim(Supp G)`;
* the bound `0` for `dim(Supp F)` forces `Supp G` to be empty.

The first half, that `Supp G` is nowhere dense in `Supp F`, is the geometric content of the
choice of `s` and is **not** proved here; it enters as a hypothesis, in either of two
interchangeable shapes. See the implementation notes.

## Main results

* `topologicalKrullDim_le_of_isNowhereDense_subspace`: the bounded dimension drop, read between
  two subsets of a common ambient space with the smaller nowhere dense in the larger.
* `eq_empty_of_isNowhereDense_subspace_of_topologicalKrullDim_nonpos`: a subset nowhere dense in
  a zero-dimensional subspace is empty.
* `Stacks.Algebraization.noetherianSpace_puncturedSpectrum`: the punctured spectrum of a
  Noetherian local ring is a Noetherian topological space.
* `Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense`: **the dimension drop
  of the induction step of [Stacks, Tag 0F27], in the two forms the induction consumes**, from
  nowhere density of `Supp G` inside `Supp F`.
* `Stacks.Algebraization.CoherentTriple.dimension_drop_of_forall_irreducibleComponents`: the
  same, with the hypothesis in the shape a supplier checks — `Supp G` contains no irreducible
  component of `Supp F`.

## Implementation notes

Nowhere density has an ambient space, and the ambient space here is `Supp F`, not the punctured
spectrum: `Supp G` is typically nowhere dense in `Supp F` while being very far from nowhere
dense in the punctured spectrum, which may itself have `Supp F` as a nowhere dense subset. So
the hypothesis is `IsNowhereDense` of the preimage of `Supp G` in the subspace `Supp F`, and the
two dimensions are matched across the change of ambient space by
`topologicalKrullDim_preimage_val`.

The second shape of the hypothesis is
`isNowhereDense_preimage_val_iff_forall_irreducibleComponents`: for a subset closed in the
ambient space, nowhere density inside `Supp F` is exactly containing no irreducible component of
`Supp F`. That is the form the source's choice of `s` delivers — a component of `Supp F` has a
generic point, which lies in `Ass(F)`, at which `s` does not vanish, so the component is not
inside the vanishing locus of `s` and therefore not inside `Supp G`.

No part of this file assumes the two supports are related; the containment `Supp G ⊆ Supp F` is
a hypothesis, used only to read the dimension of `Supp G` inside the subspace `Supp F`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing Set TopologicalSpace

universe u

/-! ### The dimension drop between two subsets of a common ambient space -/

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- **A subset nowhere dense in a subspace of dimension at most `n + 1` has dimension at most
`n`.** This is `IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ` read between two
subsets of a common ambient space: the nowhere-density hypothesis is taken inside `Y`, and the
dimension of `A` is the same whether it is read in `Y` or in `X`. -/
public theorem topologicalKrullDim_le_of_isNowhereDense_subspace {Y A : Set X}
    [NoetherianSpace Y] (hAY : A ⊆ Y) (hclosed : IsClosed A)
    (hnd : IsNowhereDense ((Subtype.val : Y → X) ⁻¹' A)) (n : ℕ)
    (hY : topologicalKrullDim Y ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim A ≤ ((n : ℕ) : WithBot ℕ∞) := by
  rw [← topologicalKrullDim_preimage_val Y A hAY]
  exact hnd.topologicalKrullDim_le_of_le_natCast_succ
    (hclosed.preimage continuous_subtype_val) n hY

/-- **A subset nowhere dense in a subspace of dimension at most `0` is empty.** A nowhere dense
closed subset has dimension at least one less, and the only element of `WithBot ℕ∞` that is
below `0` after adding one is `-∞`, which is the dimension of the empty space alone. -/
public theorem eq_empty_of_isNowhereDense_subspace_of_topologicalKrullDim_nonpos {Y A : Set X}
    [NoetherianSpace Y] (hAY : A ⊆ Y) (hclosed : IsClosed A)
    (hnd : IsNowhereDense ((Subtype.val : Y → X) ⁻¹' A))
    (hY : topologicalKrullDim Y ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    A = ∅ := by
  have hle : topologicalKrullDim A + 1 ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_preimage_val Y A hAY]
    exact le_trans
      (hnd.topologicalKrullDim_add_one_le (hclosed.preimage continuous_subtype_val)) hY
  have hlt : topologicalKrullDim A < ((0 : ℕ) : WithBot ℕ∞) :=
    ENat.WithBot.add_one_le_natCast_iff.mp hle
  have hbot : topologicalKrullDim A = ⊥ := by
    rcases eq_or_ne (topologicalKrullDim (A : Set X)) ⊥ with h | h
    · exact h
    · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp h
      rw [← he] at hlt
      simp at hlt
  exact Set.isEmpty_coe_sort.mp ((topologicalKrullDim_eq_bot_iff_isEmpty (A : Set X)).mp hbot)

end Topology

namespace Stacks.Algebraization

/-! ### The punctured spectrum is a Noetherian space -/

/-- **The punctured spectrum of a Noetherian local ring is a Noetherian topological space**,
being a subspace of the spectrum of a Noetherian ring. -/
public theorem noetherianSpace_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : NoetherianSpace (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  NoetherianSpace.set ((Stacks.Divisors.puncturedSpectrum A).1 : Set (PrimeSpectrum A))

/-! ### The dimension drop for the supports of two coherent triples -/

/-- **The dimension drop of the induction step of [Stacks, Tag 0F27], in the two forms the
induction consumes.** If the support of the punctured-spectrum member of `G` is contained in,
closed in, and nowhere dense in the support of the punctured-spectrum member of `T`, then a
bound `e + 1` on the dimension of the latter gives the bound `e` on the dimension of the former,
and the bound `0` forces the former to be empty.

These two implications are the two dimension conjuncts of
`Stacks.Algebraization.HasHilbertInductionStep`. -/
public theorem CoherentTriple.dimension_drop_of_isNowhereDense {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (T G : CoherentTriple A f)
    (hsub : SheafOfModules.supp G.F ⊆ SheafOfModules.supp T.F)
    (hclosed : IsClosed (SheafOfModules.supp G.F))
    (hnd : IsNowhereDense ((Subtype.val : ↥(SheafOfModules.supp T.F) →
      (Stacks.Divisors.puncturedSpectrum A).toScheme) ⁻¹' SheafOfModules.supp G.F)) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim ↥(SheafOfModules.supp G.F) ≤ ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp G.F = ∅) := by
  have := noetherianSpace_puncturedSpectrum A
  have : NoetherianSpace ↥(SheafOfModules.supp T.F) := NoetherianSpace.set _
  exact ⟨fun e he => topologicalKrullDim_le_of_isNowhereDense_subspace hsub hclosed hnd e he,
    fun h0 => eq_empty_of_isNowhereDense_subspace_of_topologicalKrullDim_nonpos hsub hclosed
      hnd h0⟩

/-- **The dimension drop of the induction step of [Stacks, Tag 0F27], with the nowhere-density
hypothesis in the shape a supplier checks.** For a closed subset, being nowhere dense in
`Supp F` is exactly containing no irreducible component of `Supp F`; and the source's choice of
a section not vanishing at any associated point of `F` delivers precisely that, since a generic
point of a component of `Supp F` is an associated point of `F`. -/
public theorem CoherentTriple.dimension_drop_of_forall_irreducibleComponents {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (T G : CoherentTriple A f)
    (hsub : SheafOfModules.supp G.F ⊆ SheafOfModules.supp T.F)
    (hclosed : IsClosed (SheafOfModules.supp G.F))
    (hcomp : ∀ Z ∈ irreducibleComponents ↥(SheafOfModules.supp T.F),
      ¬ ((Subtype.val : ↥(SheafOfModules.supp T.F) →
        (Stacks.Divisors.puncturedSpectrum A).toScheme) '' Z ⊆ SheafOfModules.supp G.F)) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim ↥(SheafOfModules.supp G.F) ≤ ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp G.F = ∅) := by
  have := noetherianSpace_puncturedSpectrum A
  exact T.dimension_drop_of_isNowhereDense G hsub hclosed
    ((isNowhereDense_preimage_val_iff_forall_irreducibleComponents hclosed).2 hcomp)

end Stacks.Algebraization

end
