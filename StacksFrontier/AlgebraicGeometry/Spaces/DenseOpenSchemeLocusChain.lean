module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# The descending chain of affine opens in Rydh's argument has a common point

`StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus` builds the chain of nonempty
affine opens `V₁ ⊇ V₂ ⊇ …` of the source's proof of Tag 086U and extracts a point lying in
every stratum from it, but only *granting* the statement `h01Z2` that a descending chain of
nonempty affine opens of a scheme has nonempty intersection. That hypothesis is the only
consequence of Tag 01Z2 which the argument uses, and the implementation notes of that module
record it as owed to chapter 32.

This file proves it, so that the chain-of-opens half of the source's argument carries no
hypothesis at all.

The proof is not the limit argument of Tag 01Z2. A descending chain of nonempty quasi-compact
opens inside one affine open `U` is a descending chain of nonempty *constructibly closed*
subsets of the spectral space `U`, so its intersection is nonempty by quasi-compactness of
the constructible topology, which is
`SpectralSubset.nonempty_iInter_inter_of_directed`. Nothing about limits of schemes, affine
transition morphisms, or chapter 32 enters.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Scheme.nonempty_iInter_of_antitone_le_affineOpen`: an antitone family of
  nonempty quasi-compact opens of a scheme contained in a fixed affine open has nonempty
  intersection.
* `AlgebraicGeometry.Scheme.nonempty_iInter_of_antitone_affineOpens`: the same for an antitone
  family of nonempty *affine* opens, which is the hypothesis `h01Z2` of
  `AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty` verbatim.
* `AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty_of_exists_affineOpen`:
  `AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty` with `h01Z2` discharged.

## Implementation notes

**Nothing here carries `@[stacks 086U]`, and nothing here carries `@[stacks 01Z2]` either.**
Tag 01Z2 is the statement that the limit of a directed inverse system of nonempty quasi-compact
schemes with affine transition morphisms is a nonempty scheme; what is proved below is a
strictly weaker statement about one scheme, with no limit in it. The full tag is in Mathlib, as
`AlgebraicGeometry.Scheme.nonempty_of_isLimit`, which carries `@[stacks 01Z2]` there; it is not
used here, because the chain the argument produces lives inside a single scheme and the
constructible topology settles it directly.

*Why an ambient affine open is needed.* The underlying space of a scheme is sober,
prespectral and T0, but it is neither quasi-compact nor quasi-separated in general, so it is
not spectral and the compactness argument has no ambient compact space to run in. An affine
open supplies one: `AlgebraicGeometry.Scheme.compactSpace_of_isAffine` and
`AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` complete the two scheme-wide instances
`QuasiSober` and `PrespectralSpace` to `SpectralSpace`. In the application the ambient affine
open is the first member of the chain, which antitonicity puts above every other member.

*Transferring the chain into the affine open.* The members are opens of the ambient scheme, so
they are moved into the affine open by taking preimages along the inclusion `U.ι`. Openness is
continuity; quasi-compactness is `Topology.IsInducing.isCompact_preimage'`, whose range
hypothesis is exactly `V n ≤ U` once `AlgebraicGeometry.Scheme.Opens.range_ι` identifies the
range of the inclusion with the point set of `U`.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 08YG](https://stacks.math.columbia.edu/tag/08YG)
* [Stacks Project, Tag 0901](https://stacks.math.columbia.edu/tag/0901)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- **A descending chain of nonempty quasi-compact opens inside an affine open of a scheme has
a common point.**

The affine open `U` is a spectral space: it is quasi-compact and quasi-separated because it is
affine, and sober, prespectral and T0 because it is a scheme. Inside a spectral space a
quasi-compact open subset is closed for the constructible topology, in which the space is
still quasi-compact, so a descending chain of nonempty such subsets has nonempty intersection;
that is `SpectralSubset.nonempty_iInter_inter_of_directed`, applied with the closed set taken
to be everything. The chain is moved into `U` by taking preimages along the inclusion. -/
theorem Scheme.nonempty_iInter_of_antitone_le_affineOpen {Z : Scheme.{u}} {U : Z.Opens}
    (hU : IsAffineOpen U) (V : ℕ → Z.Opens) (hVle : ∀ n, V n ≤ U)
    (hVc : ∀ n, IsCompact (V n : Set Z)) (hVne : ∀ n, (V n : Set Z).Nonempty)
    (hVanti : Antitone V) :
    (⋂ n, (V n : Set Z)).Nonempty := by
  have _hUaffine : IsAffine U.toScheme := hU
  have _hUspectral : SpectralSpace U.toScheme := ⟨⟩
  have hemb : IsOpenEmbedding U.ι.base := Scheme.Hom.isOpenEmbedding U.ι
  have hrange : Set.range U.ι.base = (U : Set Z) := Scheme.Opens.range_ι U
  set W : ℕ → Set U.toScheme := fun n => U.ι.base ⁻¹' (V n : Set Z) with hWdef
  have hWopen : ∀ n, IsOpen (W n) := fun n => (V n).2.preimage hemb.continuous
  have hWc : ∀ n, IsCompact (W n) := fun n =>
    hemb.isEmbedding.toIsInducing.isCompact_preimage' (hVc n) (by rw [hrange]; exact hVle n)
  have hWdir : Directed (· ⊇ ·) W := fun i j =>
    ⟨max i j, Set.preimage_mono (hVanti (le_max_left i j)),
      Set.preimage_mono (hVanti (le_max_right i j))⟩
  have hWne : ∀ n, (W n ∩ Set.univ).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := hVne n
    exact ⟨⟨x, hVle n hx⟩, hx, Set.mem_univ _⟩
  obtain ⟨y, hy⟩ := SpectralSubset.nonempty_iInter_inter_of_directed W hWopen hWc hWdir
    Set.univ isClosed_univ hWne
  exact ⟨U.ι.base y, Set.mem_iInter.2 fun n => (Set.mem_iInter.1 hy n).1⟩

/-- **The hypothesis `h01Z2` of
`AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty`, proved.** A descending
chain of nonempty affine opens of a scheme has nonempty intersection.

Antitonicity puts every member below the zeroth one, which is affine, so
`AlgebraicGeometry.Scheme.nonempty_iInter_of_antitone_le_affineOpen` applies with `V 0` as the
ambient affine open; an affine open is quasi-compact by
`AlgebraicGeometry.IsAffineOpen.isCompact`. -/
theorem Scheme.nonempty_iInter_of_antitone_affineOpens {Z : Scheme.{u}} (V : ℕ → Z.Opens)
    (hVaff : ∀ n, IsAffineOpen (V n)) (hVne : ∀ n, (V n : Set Z).Nonempty)
    (hVanti : Antitone V) :
    (⋂ n, (V n : Set Z)).Nonempty :=
  Scheme.nonempty_iInter_of_antitone_le_affineOpen (hVaff 0) V
    (fun n => hVanti (Nat.zero_le n)) (fun n => (hVaff n).isCompact) hVne hVanti

/-- **The topological skeleton of the second half of the proof of Tag 086U, with no carried
hypothesis.**

Let `W : ℕ → Y.Opens` be a family of opens of a scheme, let `W 0` contain a nonempty affine
open, and assume every nonempty affine open contained in `W n` meets `W (n + 1)`. Then the
intersection of all the `W n` is nonempty.

This is `AlgebraicGeometry.Scheme.nonempty_iInter_of_forall_inter_nonempty` with its hypothesis
`h01Z2` supplied by `AlgebraicGeometry.Scheme.nonempty_iInter_of_antitone_affineOpens`. In the
source the `W n` are the preimages in an affine étale chart of the strata of Tag 086T, and a
point of the intersection is the point whose field-valued image in the algebraic space has a
fibre of infinite degree. -/
theorem Scheme.nonempty_iInter_of_forall_inter_nonempty_of_exists_affineOpen {Y : Scheme.{u}}
    (W : ℕ → Y.Opens)
    (hbase : ∃ V : Y.Opens, IsAffineOpen V ∧ (V : Set Y).Nonempty ∧ V ≤ W 0)
    (hstep : ∀ (n : ℕ) (V : Y.Opens), IsAffineOpen V → (V : Set Y).Nonempty → V ≤ W n →
      ((V : Set Y) ∩ (W (n + 1) : Set Y)).Nonempty) :
    (⋂ n, (W n : Set Y)).Nonempty :=
  Scheme.nonempty_iInter_of_forall_inter_nonempty
    (fun _Z V hVaff hVne hVanti =>
      Scheme.nonempty_iInter_of_antitone_affineOpens V hVaff hVne hVanti)
    W hbase hstep

end AlgebraicGeometry

end
