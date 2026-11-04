module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular

/-!
# A factor of a Cartier zero scheme of a tensor product of sections is Cartier

Let `X` be a scheme, let `M` and `N` be invertible `𝒪_X`-modules and let `a ∈ Γ(X, M)`,
`b ∈ Γ(X, N)`. If the zero scheme `Z(a ⊗ b)` is an effective Cartier divisor then so are `Z(a)`
and `Z(b)`.

On an affine open trivializing both modules the three ideals are `(α)`, `(β)` and `(αβ)` for the
local equations `α` of `a` and `β` of `b`, and a factor of a nonzerodivisor is a nonzerodivisor.
There is no hypothesis beyond invertibility of the two modules; in particular neither factor is
assumed regular.

## Main results

* `Stacks.Divisors.linearEquivOfLe` — a trivialization of an invertible module over an affine
  open restricts to a trivialization over any smaller open.
* `Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_tensorSection_left` and
  `…_right` — **a factor of a Cartier zero scheme of a pure tensor is Cartier.**

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### Restricting a trivialization -/

/-- **A trivialization of an invertible module over an affine open restricts to a trivialization
over any smaller open.** The restriction of the preimage of `1` generates the sections there, by
`Stacks.Divisors.bijective_smul_symm_one`. -/
def linearEquivOfLe (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U))
    (V : X.Opens) (hV : V ≤ U) :
    Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Γ(X, V) Γ(L, V) (L.presheaf.map (homOfLE hV).op (e.symm 1)))
    (bijective_smul_symm_one L hU e V hV)).symm

/-! ### A factor of a nonzerodivisor -/

/-- A factor of a nonzerodivisor of a commutative ring is a nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_mul_mem {R : Type*} [CommRing R] {p q : R}
    (h : p * q ∈ nonZeroDivisors R) : p ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff] at h ⊢
  exact ⟨fun z hz => h.1 z (by rw [mul_right_comm, hz, zero_mul]),
    fun z hz => h.2 z (by rw [← mul_assoc, hz, zero_mul])⟩

/-! ### The two factors of a Cartier zero scheme of a pure tensor -/

variable (M N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The local equation of a pure tensor `a ⊗ b` is a nonzerodivisor on an affine open
trivializing both modules, when `Z(a ⊗ b)` is an effective Cartier divisor. -/
theorem isRegular_tensorTrivialization_of_isEffectiveCartierDivisor (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (h : IsEffectiveCartierDivisor
      (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)))
    (U : X.affineOpens) (eM : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))
    (eN : Γ(N, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) :
    IsRegular (eM (M.presheaf.map (homOfLE le_top).op a) *
      eN (N.presheaf.map (homOfLE le_top).op b)) := by
  have hreg : AlgebraicGeometry.IsRegularSection X.sheaf.obj X.ringCatSheaf.property
      (sectionsOfTop (tensorModules M N)
        (tensorSection M N ⊤ a b)) := by
    rwa [← AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X
      (tensorModules M N) (sectionsOfTop (tensorModules M N)
        (tensorSection M N ⊤ a b)),
      sectionsOfTop_eval_top]
  have hcoord := AlgebraicGeometry.isRegular_coordinate_of_isRegularSection X
    (tensorModules M N) (sectionsOfTop (tensorModules M N)
      (tensorSection M N ⊤ a b)) hreg U (tensorTrivialization M N U.2 eM eN)
  rwa [sectionsOfTop_eval_top,
    tensorTrivialization_map_tensorSection M N U eM eN a b] at hcoord

/-- The zero scheme of a section `s` of an invertible module is Cartier once, on affine opens
trivializing both `L` and a second invertible module `K`, the local equation of `s` is a
nonzerodivisor. -/
private theorem isEffectiveCartierDivisor_zeroScheme_of_forall_trivialization (L K : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property K]
    (s : Γ(L, ⊤))
    (h : ∀ (U : X.affineOpens) (eL : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))
      (_ : Γ(K, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)),
      eL (L.presheaf.map (homOfLE le_top).op s) ∈ nonZeroDivisors Γ(X, U.1)) :
    IsEffectiveCartierDivisor (zeroScheme X L s) := by
  rw [Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor]
  intro x
  obtain ⟨U₁, hx₁, -, ⟨eL₁⟩⟩ :=
    AlgebraicGeometry.exists_affineOpens_linearEquiv_le X L x ⊤ trivial
  obtain ⟨U, hxU, hUle, ⟨eK⟩⟩ :=
    AlgebraicGeometry.exists_affineOpens_linearEquiv_le X K x U₁.1 hx₁
  exact ⟨U, hxU, linearEquivOfLe L U₁.2 eL₁ U.1 hUle (L.presheaf.map (homOfLE le_top).op s),
    h U _ eK, zeroScheme_ideal_of_trivialization X L s U (linearEquivOfLe L U₁.2 eL₁ U.1 hUle) _
      rfl⟩

/-- **A factor of a Cartier zero scheme of a pure tensor is Cartier**, for the left factor: if
`Z(a ⊗ b)` is an effective Cartier divisor then so is `Z(a)`. -/
theorem isEffectiveCartierDivisor_zeroScheme_of_tensorSection_left (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (h : IsEffectiveCartierDivisor
      (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b))) :
    IsEffectiveCartierDivisor (zeroScheme X M a) :=
  isEffectiveCartierDivisor_zeroScheme_of_forall_trivialization M N a fun U eM eN =>
    mem_nonZeroDivisors_of_mul_mem
      (isRegular_iff_mem_nonZeroDivisors.mp
        (isRegular_tensorTrivialization_of_isEffectiveCartierDivisor M N a b h U eM eN))

/-- **A factor of a Cartier zero scheme of a pure tensor is Cartier**, for the right factor: if
`Z(a ⊗ b)` is an effective Cartier divisor then so is `Z(b)`. -/
theorem isEffectiveCartierDivisor_zeroScheme_of_tensorSection_right (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (h : IsEffectiveCartierDivisor
      (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b))) :
    IsEffectiveCartierDivisor (zeroScheme X N b) :=
  isEffectiveCartierDivisor_zeroScheme_of_forall_trivialization N M b fun U eN eM =>
    mem_nonZeroDivisors_of_mul_mem (q := eM (M.presheaf.map (homOfLE le_top).op a))
      (by
        rw [mul_comm]
        exact isRegular_iff_mem_nonZeroDivisors.mp
          (isRegular_tensorTrivialization_of_isEffectiveCartierDivisor M N a b h U eM eN))

end Stacks.Divisors

end
