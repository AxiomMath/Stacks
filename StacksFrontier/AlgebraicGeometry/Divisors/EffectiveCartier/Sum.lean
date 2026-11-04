module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The sum of two effective Cartier divisors

Let `X` be a scheme. The sum of two effective Cartier divisors `D₁, D₂ ⊆ X` is the closed
subscheme cut out by the product `ℐ_{D₁} · ℐ_{D₂}` of their ideal sheaves, which is Mathlib's
`Mul` instance on `AlgebraicGeometry.Scheme.IdealSheafData`.  This file proves that the sum is
again an effective Cartier divisor.

## Main results

* `AlgebraicGeometry.isRegular_res_of_isAffineOpen`: a nonzerodivisor section of an affine open
  restricts to a nonzerodivisor on every smaller open.
* `AlgebraicGeometry.isEffectiveCartierDivisor_mul`: **Stacks Tag 01WU.**

## Implementation notes

The whole content is the affine-local criterion
`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal` of Tag 01WS, in the two halves it
is assembled from: `Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor`
produces a nonzerodivisor generator for each summand on an affine open around a given point, and
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen` consumes one for the
product.  The two affine opens need not agree, so they are shrunk to a common basic open with
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`, and the product of the two restricted
generators is the generator wanted there, since `Scheme.IdealSheafData.map_ideal` carries each
principal ideal to the principal ideal on the restriction.

Restriction preserves nonzerodivisors because multiplication by the restricted section is
injective germ by germ, which is `Stacks.Divisors.injective_mul_res`.  That argument needs
nothing of the smaller open beyond being contained in the affine one, so
`isRegular_res_of_isAffineOpen` is stated for an arbitrary open rather than only for a basic
open.

## References

* [Stacks Project, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Restriction preserves nonzerodivisors.**  A nonzerodivisor of the ring of sections of an
affine open `U` of a scheme restricts to a nonzerodivisor of the ring of sections of every open
`V ≤ U`.  The stalks of `X` along `U` are localizations of `Γ(X, U)`, in which a nonzerodivisor
stays one, and a section of `𝒪_X(V)` vanishes as soon as all its germs do. -/
theorem isRegular_res_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) {V : X.Opens} (hVU : V ≤ U) :
    IsRegular ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have h : Function.Injective
      (fun c : Γ(X, V) => c * (X.presheaf.map (homOfLE hVU).op).hom f) :=
    injective_mul_res hU hf V hVU
  exact ⟨fun a b hab => h (by simpa only [mul_comm] using hab), fun a b hab => h hab⟩

/-- **Stacks Project, Tag 01WU.**  The sum of two effective Cartier divisors on a scheme, that
is, the closed subscheme cut out by the product of their ideal sheaves, is again an effective
Cartier divisor. -/
@[stacks 01WU]
theorem isEffectiveCartierDivisor_mul (I J : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (hJ : IsEffectiveCartierDivisor J) :
    IsEffectiveCartierDivisor (I * J) := by
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen (I * J) fun x => ?_
  obtain ⟨U, hU, hxU, f, hf, hIf⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI x
  obtain ⟨V, hV, hxV, g, hg, hJg⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  obtain ⟨f₀, g₀, hfg, hxW⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨hxU, hxV⟩
  set W : X.affineOpens := X.affineBasicOpen (U := ⟨U, hU⟩) f₀ with hW
  have hWU : W ≤ (⟨U, hU⟩ : X.affineOpens) := X.affineBasicOpen_le (V := ⟨U, hU⟩) f₀
  have hWV : W ≤ (⟨V, hV⟩ : X.affineOpens) :=
    hfg.trans_le (X.affineBasicOpen_le (V := ⟨V, hV⟩) g₀)
  refine ⟨W, W.2, hxW, (X.presheaf.map (homOfLE hWU).op).hom f *
    (X.presheaf.map (homOfLE hWV).op).hom g,
    (isRegular_res_of_isAffineOpen hU hf hWU).mul (isRegular_res_of_isAffineOpen hV hg hWV), ?_⟩
  have hmul : (I * J).ideal W = I.ideal W * J.ideal W := rfl
  rw [hmul, ← I.map_ideal hWU, ← J.map_ideal hWV, hIf, hJg, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
  rfl

end AlgebraicGeometry

end
