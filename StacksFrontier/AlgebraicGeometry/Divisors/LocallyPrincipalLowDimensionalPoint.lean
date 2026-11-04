module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier

/-!
# A locally principal closed subscheme has a point of local dimension at most one

Let `X` be a locally Noetherian scheme and let `D ⊆ X` be a nonempty closed subscheme which is
locally principal, i.e. locally cut out by one equation. Then `D` contains a point `x` at which
`dim 𝒪_{X,x} ≤ 1`: on an affine open `Spec R` meeting `D` on which `D = V(e)`, a prime of `R`
minimal over `(e)` has height at most one by Krull's principal ideal theorem, and the local ring
of `X` at the corresponding point is the localization of `R` at that prime.

Consequently a locally principal closed subscheme all of whose points have local rings of
dimension at least two is empty.

## Main results

* `Stacks.Divisors.exists_mem_support_ringKrullDim_stalk_le_one`: a locally principal closed
  subscheme other than the empty one contains a point of local dimension at most one.
* `Stacks.Divisors.eq_top_of_forall_mem_support_two_le_ringKrullDim_stalk`: a locally principal
  closed subscheme all of whose points have local dimension at least two is empty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **A nonempty locally principal closed subscheme contains a point of local dimension at most
one.** -/
theorem exists_mem_support_ringKrullDim_stalk_le_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsLocallyPrincipal D) (hne : D ≠ ⊤) :
    ∃ x ∈ D.support, ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  obtain ⟨x, hx⟩ : (D.support : Set X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne ((Scheme.IdealSheafData.support_eq_bot_iff D).1 (SetLike.coe_injective h))
  obtain ⟨W, hxW, ⟨e, he⟩⟩ := hD x
  have hWa : IsAffineOpen (W : X.Opens) := W.2
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set P := hWa.primeIdealOf ⟨x, hxW⟩ with hP
  have hPx : hWa.fromSpec P = x := hWa.fromSpec_primeIdealOf ⟨x, hxW⟩
  have hzero := (Scheme.IdealSheafData.mem_support_iff_of_mem hxW).1 hx
  have heP : e ∈ P.asIdeal := by
    have hex : x ∉ X.basicOpen e :=
      (X.mem_zeroLocus_iff _ _).1 hzero e (by rw [he]; exact Ideal.mem_span_singleton_self e)
    by_contra hnot
    exact hex (hPx ▸ (SetLike.ext_iff.1 (hWa.fromSpec_preimage_basicOpen e) P).2 hnot)
  obtain ⟨Q, hQmin, -⟩ := Ideal.exists_minimalPrimes_le
    (I := Ideal.span {e}) (J := P.asIdeal) ((Ideal.span_singleton_le_iff_mem _).2 heP)
  have hQprime : Q.IsPrime := hQmin.1.1
  have hQht : Q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {e}) Q hQmin
  let y : Spec Γ(X, W) := (⟨Q, hQprime⟩ : PrimeSpectrum Γ(X, W))
  have hyW : hWa.fromSpec y ∈ (W : X.Opens) := hWa.range_fromSpec.subset ⟨y, rfl⟩
  refine ⟨hWa.fromSpec y, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyW, Scheme.mem_zeroLocus_iff, he]
    intro s hs hsy
    exact (SetLike.ext_iff.1 (hWa.fromSpec_preimage_basicOpen s) y).1 hsy
      (hQmin.1.2 hs)
  · have hinj : hWa.primeIdealOf ⟨hWa.fromSpec y, hyW⟩ = y := by
      have : IsOpenImmersion hWa.fromSpec := hWa.isOpenImmersion_fromSpec
      exact hWa.fromSpec.isOpenEmbedding.injective
        (hWa.fromSpec_primeIdealOf ⟨hWa.fromSpec y, hyW⟩)
    let := X.presheaf.algebra_section_stalk ⟨hWa.fromSpec y, hyW⟩
    rw [(hWa.isLocalization_stalk ⟨hWa.fromSpec y, hyW⟩).ringKrullDim_eq_height, hinj]
    exact_mod_cast hQht

/-- **A locally principal closed subscheme all of whose points have local dimension at least two
is empty.** -/
theorem eq_top_of_forall_mem_support_two_le_ringKrullDim_stalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (hD : IsLocallyPrincipal D)
    (h : ∀ x ∈ D.support, 2 ≤ ringKrullDim (X.presheaf.stalk x)) : D = ⊤ := by
  by_contra hne
  obtain ⟨x, hx, hle⟩ := exists_mem_support_ringKrullDim_stalk_le_one D hD hne
  exact absurd ((h x hx).trans hle) (by decide)

end Stacks.Divisors

end
