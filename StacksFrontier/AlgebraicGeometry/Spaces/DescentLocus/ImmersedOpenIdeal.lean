module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ClosedConstructibleIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Quasi-compact opens of an immersed subscheme of an affine scheme are cut out by ideals

Let `ι : Z ⟶ W` be an immersion into an affine scheme and `C ⊆ Z` a closed subset with
quasi-compact complement. Then there is a finitely generated ideal `J` of `Γ(W, ⊤)` such that a
morphism `h : T ⟶ Z` from an affine scheme lands in `Z \ C` exactly when `J` generates the unit
ideal of `Γ(T, ⊤)` along `h ≫ ι`.

The open `Z \ C` is the trace on `Z` of an open of `W`; its image is quasi-compact, hence covered
by finitely many affine opens of `W` inside that open, whose union `O'` is a quasi-compact open of
`W` with `ι⁻¹(O') = Z \ C`. Its complement is closed and constructible, so it is `V(J)` with `J`
finitely generated (`AlgebraicGeometry.Space.exists_fg_ideal_range_subset_compl_iff`).

This is the topological step of the proof of Stacks 0D23 that cuts the descent locus out of the
bottom rank stratum on an affine chart. It is a private, unregistered helper.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.exists_fg_ideal_range_subset_compl_iff_of_isImmersion`
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space.DescentStratum

/-- **A quasi-compact open of an immersed subscheme of an affine scheme is cut out by a finitely
generated ideal on affine test schemes.** -/
theorem exists_fg_ideal_range_subset_compl_iff_of_isImmersion {W Z : Scheme.{u}} [IsAffine W]
    (ι : Z ⟶ W) [AlgebraicGeometry.IsImmersion ι] {C : Set Z} (hC : IsClosed C)
    (hCc : IsCompact Cᶜ) :
    ∃ J : Ideal Γ(W, ⊤), J.FG ∧ ∀ (T : Scheme.{u}) [IsAffine T] (h : T ⟶ Z),
      (Set.range h.base ⊆ Cᶜ ↔ J.map (h ≫ ι).appTop.hom = ⊤) := by
  obtain ⟨O, hO, hOC⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 hC.isOpen_compl
  have hU : IsCompact (ι.base '' Cᶜ) := hCc.image ι.base.hom.continuous
  have hUO : ι.base '' Cᶜ ⊆ O := Set.image_subset_iff.2 hOC.ge
  have hcov : ∀ x ∈ ι.base '' Cᶜ, ∃ A : W.affineOpens, x ∈ (A : Set W) ∧ (A : Set W) ⊆ O :=
    fun x hx => by
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAO⟩ :=
        W.isBasis_affineOpens.exists_subset_of_mem_open (hUO hx) hO
      exact ⟨⟨A, hA⟩, hxA, hAO⟩
  choose A hxA hAO using hcov
  obtain ⟨σ, hσ⟩ := hU.elim_finite_subcover
    (fun x : ι.base '' Cᶜ => ((A x.1 x.2 : W.Opens) : Set W))
    (fun x => (A x.1 x.2 : W.Opens).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxA x hx⟩)
  let O' : Set W := ⋃ x ∈ σ, ((A x.1 x.2 : W.Opens) : Set W)
  have hO'open : IsOpen O' := isOpen_biUnion fun x _ => (A x.1 x.2 : W.Opens).isOpen
  have hO'comp : IsCompact O' :=
    σ.finite_toSet.isCompact_biUnion fun x _ => (A x.1 x.2).2.isCompact
  have hO'O : O' ⊆ O := Set.iUnion₂_subset fun x _ => hAO x.1 x.2
  have hD : IsConstructible O'ᶜ := isConstructible_compl.2 (hO'comp.isConstructible hO'open)
  obtain ⟨J, hJ, hJiff⟩ :=
    exists_fg_ideal_range_subset_compl_iff (U := W) hO'open.isClosed_compl hD
  refine ⟨J, hJ, fun T _ h => ?_⟩
  rw [← hJiff T (h ≫ ι), compl_compl]
  constructor
  · rintro hh _ ⟨t, rfl⟩
    exact hσ ⟨_, hh ⟨t, rfl⟩, rfl⟩
  · rintro hh _ ⟨t, rfl⟩
    exact hOC.le (hO'O (hh ⟨t, rfl⟩))

end AlgebraicGeometry.Space.DescentStratum
