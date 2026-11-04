module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Defs

/-!
# Koszul-regularity of a sequence of sections over an affine open

Let `X` be a scheme, `U ⊆ X` an affine open and `f₁, …, f_r ∈ Γ(X, U)`.  Then the sheaf Koszul
complex of `f` is locally exact in positive degrees over `U`, which is the condition of Stacks tag
063D part (2), if and only if `f` is a Koszul-regular sequence in the ring `Γ(X, U)`.

The whole argument runs on the basic opens of an affine open, and never on a stalk.  For `U`
affine and `g ∈ O_X(U)` the ring `O_X(D(g))` is the localization of `O_X(U)` at `g`
(`IsAffineOpen.isLocalization_basicOpen`), and the basic opens form a neighbourhood basis inside
`U` (`IsAffineOpen.exists_basicOpen_le`).  So the sheaf condition of tag 063D — every Koszul
cycle is *locally* a Koszul boundary — may always be tested on a basic open, where
Koszul-regularity is the localized ring condition in every degree at once.  Both directions are
then the two halves of the local-global principle of `KoszulRegularIdealSheaf.Algebra`: the
forward one clears denominators at each maximal ideal of `O_X(U)`, the converse localizes.

## Main results

* `isKoszulRegularSequenceOn_iff_isKoszulRegular`: over an affine open the sheaf condition of
  tag 063D part (2) is Koszul-regularity of the sequence in the ring of sections.
* `not_isKoszulRegularSequenceOn_zero`: the sheaf-side condition is falsifiable too — over an
  affine open with nontrivial ring of sections, the one-term zero sequence fails it.

## Implementation notes

The point of `U` carrying a given maximal ideal of `O_X(U)` is produced from the bijectivity of
`hU.isoSpec` on points (`exists_primeIdealOf_eq`); `IsAffineOpen.fromSpec_primeIdealOf` and
`IsAffineOpen.fromSpec_preimage_basicOpen` then translate `z ∈ D(g)` into `g ∉ m`
(`notMem_primeIdealOf_of_mem_basicOpen`), which is what makes the element of the localizing
submonoid produced by clearing denominators lie outside `m`.

`resFamily_eq_algebraMap` and `resExt_eq_extRes` record that restriction of sections along
`U ⊇ D(g)` *is* the structure map of the localization; both hold by `rfl`, and they are stated
separately so that the two directions of the comparison never ask the elaborator to see through
that identification inside a dependent type.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped ExteriorAlgebra
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.AlgebraicGeometry.H1RegularIdealSheaf
open Stacks.RingTheory.H1RegularIdealSheaf
open Stacks.RingTheory.KoszulRegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf

/-! ### Restriction to a basic open is the localization map -/

section BasicOpen

variable (X : Scheme.{u}) {U : X.Opens} {r : ℕ}

/-- Restricting a family of sections from an affine open to a basic open is the structure map of
the localization. -/
theorem resFamily_eq_algebraMap (f : Fin r → Γ(X, U)) (g : Γ(X, U))
    (h : X.basicOpen g ≤ U) :
    resFamily X.toRingedSpace h f
      = fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i) := rfl

/-- Restricting an exterior-power chain from an affine open to a basic open is base change along
the structure map of the localization. -/
theorem resExt_eq_extRes (g : Γ(X, U)) (h : X.basicOpen g ≤ U) (n : ℕ)
    (z : ⋀[Γ(X, U)]^n (Fin r → Γ(X, U))) :
    resExt X.toRingedSpace h r n z
      = extRes (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) n z := rfl

/-- A maximal ideal of the ring of sections of an affine open is the prime ideal of a point of
that open. -/
theorem exists_primeIdealOf_eq (hU : IsAffineOpen U) (m : Ideal Γ(X, U)) (hm : m.IsMaximal) :
    ∃ y : U, (hU.primeIdealOf y).asIdeal = m := by
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.forgetToTop.map hU.isoSpec.hom)).2 (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(X, U))
  exact ⟨y, congrArg PrimeSpectrum.asIdeal hy⟩

/-- A point of a basic open `D(g)` inside an affine open has `g` outside its prime ideal. -/
theorem notMem_primeIdealOf_of_mem_basicOpen (hU : IsAffineOpen U) (g : Γ(X, U)) (y : U)
    (hyg : (y : X) ∈ X.basicOpen g) : g ∉ (hU.primeIdealOf y).asIdeal := by
  have h₁ : hU.primeIdealOf y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
    show hU.fromSpec (hU.primeIdealOf y) ∈ X.basicOpen g
    rw [hU.fromSpec_primeIdealOf y]
    exact hyg
  rw [hU.fromSpec_preimage_basicOpen] at h₁
  exact (PrimeSpectrum.mem_basicOpen _ _).mp h₁

end BasicOpen

/-! ### The comparison over an affine open -/

section Comparison

variable (X : Scheme.{u}) (U : X.Opens) {r : ℕ} (f : Fin r → Γ(X, U))

/-- The local witness of the sheaf condition, transported to a basic open: if a Koszul cycle `z`
over the affine open `U` becomes a boundary over `W`, and `D(g) ⊆ W`, then its image in
`⋀ⁿ⁺¹` over the localization `O_X(D(g))` is a boundary there. -/
theorem extRes_mem_range_d_of_witness {W : X.Opens} (hWU : W ≤ U) (g : Γ(X, U))
    (hgW : X.basicOpen g ≤ W) (n : ℕ) (z : ⋀[Γ(X, U)]^(n + 1) (Fin r → Γ(X, U)))
    (w : ⋀[Γ(X, W)]^(n + 2) (Fin r → Γ(X, W)))
    (hw : Koszul.d (Koszul.seqDual (resFamily X.toRingedSpace hWU f)) (n + 1) w
      = resExt X.toRingedSpace hWU r (n + 1) z) :
    extRes (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) (n + 1) z
      ∈ LinearMap.range
        (Koszul.d (Koszul.seqDual fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i))
          (n + 1)) := by
  refine ⟨resExt X.toRingedSpace hgW r (n + 2) w, ?_⟩
  have h₁ := resExt_d X.toRingedSpace hgW (resFamily X.toRingedSpace hWU f) (n + 1) w
  rw [hw, resExt_res, resFamily_res, resFamily_eq_algebraMap, resExt_eq_extRes] at h₁
  exact h₁.symm

/-- **Forward direction of the affine comparison.**  The sheaf Koszul-regularity condition over
an affine open forces Koszul-regularity in the ring of sections: a Koszul cycle is locally a
boundary, hence, after clearing denominators on a basic open, a boundary up to a factor outside
each maximal ideal — and membership in the boundaries is local on the base. -/
theorem isKoszulRegular_of_isKoszulRegularSequenceOn (hU : IsAffineOpen U)
    (h : IsKoszulRegularSequenceOn X.toRingedSpace U f) : Koszul.IsKoszulRegular f := by
  rw [isKoszulRegular_iff_forall]
  intro n z hz
  refine LinearMap.mem_range.mp ?_
  refine mem_of_forall_maximal_smul
    (LinearMap.range (Koszul.d (Koszul.seqDual f) (n + 1))) z fun m hm => ?_
  obtain ⟨y, hmy⟩ := exists_primeIdealOf_eq X hU m hm
  have hz' : Koszul.d (Koszul.seqDual (resFamily X.toRingedSpace (le_refl U) f)) n z = 0 := by
    rw [resFamily_self]; exact hz
  obtain ⟨W, hWU, hyW, w, hw⟩ := h U (le_refl U) n z hz' y.1 y.2
  obtain ⟨g, hgW, hyg⟩ := hU.exists_basicOpen_le (⟨y.1, hyW⟩ : W) y.2
  have := hU.isLocalization_basicOpen g
  obtain ⟨t, htT, hta⟩ := exists_smul_mem_range_d (Submonoid.powers g) Γ(X, X.basicOpen g) f n z
    (extRes_mem_range_d_of_witness X U f (hWU.trans (le_refl U)) g hgW n z w hw)
  have hgm := notMem_primeIdealOf_of_mem_basicOpen X hU g y hyg
  obtain ⟨k, rfl⟩ := htT
  exact ⟨g ^ k, fun hmem => hgm (hmy ▸ hm.isPrime.mem_of_pow_mem k hmem), hta⟩

/-- **Converse direction of the affine comparison.**  Koszul-regularity in the ring of sections
of an affine open gives the sheaf condition: Koszul-regularity passes to the localizations
`O_X(D(g))`, and the basic opens are a neighbourhood basis, so a Koszul cycle over any `V ⊆ U` is
already a boundary over a basic open around any given point. -/
theorem isKoszulRegularSequenceOn_of_isKoszulRegular (hU : IsAffineOpen U)
    (h : Koszul.IsKoszulRegular f) : IsKoszulRegularSequenceOn X.toRingedSpace U f := by
  intro V hVU n z hz y hy
  obtain ⟨g, hgV, hgy⟩ := hU.exists_basicOpen_le (⟨y, hy⟩ : V) (hVU hy)
  have := hU.isLocalization_basicOpen g
  have hloc : Koszul.IsKoszulRegular fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i) :=
    isKoszulRegular_localization (Submonoid.powers g) Γ(X, X.basicOpen g) f h
  have hzero : Koszul.d
      (Koszul.seqDual fun i => algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i)) n
        (resExt X.toRingedSpace hgV r (n + 1) z) = 0 := by
    rw [← resFamily_eq_algebraMap X f g (hgV.trans hVU),
      ← resFamily_res X.toRingedSpace hVU hgV f, ← resExt_d, hz, resExt_zero]
  obtain ⟨w, hw⟩ := (isKoszulRegular_iff_forall _).mp hloc n
    (resExt X.toRingedSpace hgV r (n + 1) z) hzero
  refine ⟨X.basicOpen g, hgV, hgy, w, ?_⟩
  rw [resFamily_eq_algebraMap X f g (hgV.trans hVU)]
  exact hw

/-- **Over an affine open the sheaf Koszul-regular condition of Stacks tag 063D is
Koszul-regularity in the ring of sections.** -/
theorem isKoszulRegularSequenceOn_iff_isKoszulRegular (hU : IsAffineOpen U) :
    IsKoszulRegularSequenceOn X.toRingedSpace U f ↔ Koszul.IsKoszulRegular f :=
  ⟨isKoszulRegular_of_isKoszulRegularSequenceOn X U f hU,
    isKoszulRegularSequenceOn_of_isKoszulRegular X U f hU⟩

end Comparison

/-- **The sheaf-side condition is a genuine condition.**  Over an affine open whose ring of
sections is nontrivial, the one-term zero sequence is not Koszul-regular as a sheaf sequence.
Together with `Stacks.RingTheory.KoszulRegularIdealSheaf.not_isKoszulRegular_zero` this makes
both sides of `isKoszulRegularSequenceOn_iff_isKoszulRegular` falsifiable, so that equivalence is
not an identification of two conditions that always hold. -/
theorem not_isKoszulRegularSequenceOn_zero (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] :
    ¬ IsKoszulRegularSequenceOn X.toRingedSpace U (fun _ : Fin 1 => (0 : Γ(X, U))) := fun h =>
  not_isKoszulRegular_zero (isKoszulRegular_of_isKoszulRegularSequenceOn X U _ hU h)

end Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf

end
