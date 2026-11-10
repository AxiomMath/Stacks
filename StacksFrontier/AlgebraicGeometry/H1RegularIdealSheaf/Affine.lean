module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.H1RegularIdealSheaf.Defs

/-!
# Affine-local characterization of `H₁`-regular ideal sheaves

Let `X` be a scheme and `J ⊆ O_X` a sheaf of ideals.  Then `J` is `H₁`-regular if and only if,
around each point of the support of `O_X / J`, it is generated on an affine open by a sequence
which is `H₁`-regular in the ring of sections of that open.

The whole argument runs on the basic opens of an affine open, and never on a stalk.  For `U`
affine and `g ∈ O_X(U)` the ring `O_X(D(g))` is the localization of `O_X(U)` at `g`
(`IsAffineOpen.isLocalization_basicOpen`), and the basic opens form a neighbourhood basis inside
`U` (`IsAffineOpen.exists_basicOpen_le`).  So the sheaf condition of tag 063D — every relation is
*locally* a combination of the trivial ones — may always be tested on a basic open, where
`H₁`-regularity is the localized ring condition.  Both directions are then the two halves of the
local-global principle of `H1RegularIdealSheaf.Algebra`: the forward one clears denominators at
each maximal ideal of `O_X(U)`, the converse localizes.

## Main results

* `isH1RegularSequenceOn_iff_isH1Regular`: over an affine open the sheaf condition of tag 063D
  part (3) is `H₁`-regularity of the sequence in the ring of sections.
* `isH1RegularIdealSheaf_iff_affine`: **Stacks tag 063G**, the `H₁`-regular case.

## Implementation notes

The point of `U` carrying a given maximal ideal of `O_X(U)` is produced from the bijectivity of
`hU.isoSpec` on points; `IsAffineOpen.fromSpec_primeIdealOf` and
`IsAffineOpen.fromSpec_preimage_basicOpen` then translate `z ∈ D(g)` into `g ∉ m`, which is what
makes the element of the localizing submonoid produced by clearing denominators lie outside `m`.

The affine open produced in the forward direction is a basis element contained in the given
witness open, so the generating sequence is restricted to it; `isGeneratedByOn_of_le` and
`isH1RegularSequenceOn_of_le` carry the two hypotheses across that restriction.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.4 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingTheory.H1RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.H1RegularIdealSheaf

section Comparison

variable (X : Scheme.{u}) (U : X.Opens) {r : ℕ} (f : Fin r → Γ(X, U))

/-- **Over an affine open the sheaf `H₁`-regular condition of Stacks tag 063D is `H₁`-regularity
in the ring of sections.** -/
theorem isH1RegularSequenceOn_iff_isH1Regular (hU : IsAffineOpen U) :
    IsH1RegularSequenceOn X.toRingedSpace U f ↔ Koszul.IsH1Regular f := by
  constructor
  · intro h
    rw [Koszul.isH1Regular_iff_forall]
    intro a ha
    refine mem_of_forall_maximal_smul (Koszul.relSpan f) a fun m hm => ?_
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.forgetToTop.map hU.isoSpec.hom)).2 (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(X, U))
    have hmz : (hU.primeIdealOf z).asIdeal = m := congrArg PrimeSpectrum.asIdeal hz
    have ha' : ∑ i, a i * resFamily X.toRingedSpace (le_refl U) f i = 0 := by
      rwa [resFamily_self]
    obtain ⟨W, hWU, hzW, hmem⟩ := h U (le_refl U) a ha' z.1 z.2
    obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (⟨z.1, hzW⟩ : W) z.2
    have := hU.isLocalization_basicOpen g
    have hmem₂ : resFamily X.toRingedSpace hgW (resFamily X.toRingedSpace hWU a)
        ∈ Koszul.relSpan
          (resFamily X.toRingedSpace hgW (resFamily X.toRingedSpace hWU f)) :=
      resFamily_mem_relSpan X.toRingedSpace hgW hmem
    rw [resFamily_res, resFamily_res] at hmem₂
    obtain ⟨t, ⟨n, rfl⟩, hta⟩ :=
      exists_smul_mem_relSpan (Submonoid.powers g) Γ(X, X.basicOpen g) f a hmem₂
    have hgm : g ∉ (hU.primeIdealOf z).asIdeal := by
      have h₁ : hU.primeIdealOf z ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
        change hU.fromSpec (hU.primeIdealOf z) ∈ X.basicOpen g
        rw [hU.fromSpec_primeIdealOf z]
        exact hzg
      rw [hU.fromSpec_preimage_basicOpen] at h₁
      exact (PrimeSpectrum.mem_basicOpen _ _).mp h₁
    exact ⟨g ^ n, fun hmem' => hgm (hmz ▸ hm.isPrime.mem_of_pow_mem n hmem'), hta⟩
  · intro h V hVU a ha y hy
    obtain ⟨g, hgV, hgy⟩ := hU.exists_basicOpen_le (⟨y, hy⟩ : V) (hVU hy)
    refine ⟨X.basicOpen g, hgV, hgy, ?_⟩
    have := hU.isLocalization_basicOpen g
    have hcomp : ∀ i, X.presheaf.map (homOfLE hgV).op (resFamily X.toRingedSpace hVU f i)
        = algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i) :=
      fun i => congrFun (resFamily_res X.toRingedSpace hVU hgV f) i
    have hrel : ∑ i, resFamily X.toRingedSpace hgV a i
        * algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i) = 0 := by
      calc ∑ i, resFamily X.toRingedSpace hgV a i
            * algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f i)
          = X.presheaf.map (homOfLE hgV).op (∑ i, a i * resFamily X.toRingedSpace hVU f i) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, hcomp i]
            rfl
        _ = 0 := by rw [ha, map_zero]
    exact (Koszul.isH1Regular_iff_forall _).mp
      (isH1Regular_localization (Submonoid.powers g) Γ(X, X.basicOpen g) f h) _ hrel

end Comparison

/-- **Stacks Project, Tag 063G (`h1_regular`).** A sheaf of ideals on a scheme is `H₁`-regular if
and only if, around each point of the support of its quotient, it is generated on an affine open
by a sequence which is `H₁`-regular in the ring of sections of that open. -/
@[stacks 063G "h1_regular"]
theorem isH1RegularIdealSheaf_iff_affine (X : Scheme.{u})
    (J : (structureSheafModule X.toRingedSpace).Submodule) :
    IsH1RegularIdealSheaf X.toRingedSpace J ↔
      ∀ x : X, x ∈ idealQuotientSupport X.toRingedSpace J →
        ∃ (U : X.affineOpens) (_hx : x ∈ (U : Set X)) (r : ℕ) (f : Fin r → Γ(X, U.1)),
          IsGeneratedByOn X.toRingedSpace J U.1 f ∧ Koszul.IsH1Regular f := by
  constructor
  · intro h x hx
    obtain ⟨U₀, hxU₀, r, f, hreg, hgen⟩ := h x hx
    obtain ⟨V, hV, hxV, hVU₀⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
    exact ⟨⟨V, hV⟩, hxV, r, resFamily X.toRingedSpace hVU₀ f,
      isGeneratedByOn_of_le U₀ f hgen V hVU₀, (isH1RegularSequenceOn_iff_isH1Regular X V _ hV).mp
        (isH1RegularSequenceOn_of_le X.toRingedSpace U₀ f V hVU₀ hreg)⟩
  · intro h x hx
    obtain ⟨U, hxU, r, f, hgen, hreg⟩ := h x hx
    exact ⟨U.1, hxU, r, f, (isH1RegularSequenceOn_iff_isH1Regular X U.1 f U.2).mpr hreg, hgen⟩

end Stacks.AlgebraicGeometry.H1RegularIdealSheaf

end
