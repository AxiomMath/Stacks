/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Hilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistAdd
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus

/-!
# Twisting quotients on `ℙⁿ_T` (Stacks 0DP7 on `ℙⁿ`)

The twist `ℱ ↦ ℱ(d)` is an autoequivalence of the modules on `ℙⁿ_T`
(`AlgebraicGeometry.ProjectiveQuot.isEquivalence_twistFunctor`), so it identifies the subobjects
of a module `𝒢` with the subobjects of `𝒢(d)`, the quotient by the image of `K` being the twist of
the quotient by `K`.  Under this identification a quotient is of finite presentation and flat over
`T` exactly when its twist is, and it has fibrewise Hilbert polynomial `P` exactly when its twist
has `t ↦ P(t + d)`: this is Stacks 0DP7 read on `ℙⁿ_T`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistSubobjectEquiv`: `Subobject 𝒢 ≃ Subobject 𝒢(d)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.shiftPolynomial`: `t ↦ P(t + d)`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.isFlatFamily_twist_iff`
* `AlgebraicGeometry.ProjectiveQuotOverSpace.hasFibreHilbertPolynomial_twist_iff`

## References

* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {n : ℕ} {T : Scheme.{u}}

/-- **The subobjects of `𝒢` and of `𝒢(d)` correspond**, through the autoequivalence `ℱ ↦ ℱ(d)`. -/
def twistSubobjectEquiv (d : ℤ) (G : (projectiveSpaceOver n T).Modules) :
    Subobject G ≃ Subobject (twist d G) :=
  Subobject.transportEquiv (twistFunctor n T d).asEquivalence (Iso.refl _)

/-- The quotient by the corresponding subobject is the twist of the quotient. -/
def twistSubobjectCokernelIso (d : ℤ) (G : (projectiveSpaceOver n T).Modules)
    (K : Subobject G) :
    cokernel (twistSubobjectEquiv d G K).arrow ≅ twist d (cokernel K.arrow) :=
  Subobject.cokernelTransportEquivIso (twistFunctor n T d).asEquivalence (Iso.refl _) K

/-- Flatness over `T` is invariant under isomorphism of modules on `ℙⁿ_T`. -/
theorem isFlatOver_of_iso {F G : (projectiveSpaceOver n T).Modules} (e : F ≅ G)
    (h : IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom F) :
    IsFlatOver (projectiveSpaceOver n T ↘ T).toLRSHom.toShHom G :=
  fun x => (flatOverAt_iff_of_iso _ e x).1 (h x)

/-- `IsFlatFamily` is invariant under isomorphism. -/
theorem isFlatFamily_of_iso {F G : (projectiveSpaceOver n T).Modules} (e : F ≅ G)
    (h : IsFlatFamily F) : IsFlatFamily G :=
  ⟨SheafOfModules.IsFinitePresentation.of_iso h.1 e, isFlatOver_of_iso e h.2⟩

/-- `IsFlatFamily` is preserved by twisting. -/
theorem isFlatFamily_twist (d : ℤ) {F : (projectiveSpaceOver n T).Modules} (h : IsFlatFamily F) :
    IsFlatFamily (twist d F) :=
  ⟨isFinitePresentation_twist d F h.1, isFlatOver_twist _ d F h.2⟩

/-- **A quotient is a flat family exactly when its twist is.** -/
theorem isFlatFamily_twist_iff (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    IsFlatFamily (twist d F) ↔ IsFlatFamily F :=
  ⟨fun h => isFlatFamily_of_iso (twistNegTwistIso T d F) (isFlatFamily_twist (-d) h),
    isFlatFamily_twist d⟩

/-- The shifted polynomial `t ↦ P(t + d)`. -/
abbrev shiftPolynomial (P : Polynomial ℚ) (d : ℤ) : Polynomial ℚ :=
  P.comp (Polynomial.X + Polynomial.C (d : ℚ))

/-- The shifted polynomial `shiftPolynomial P d` evaluates at `x` to `P(x + d)`. -/
theorem eval_shiftPolynomial (P : Polynomial ℚ) (d : ℤ) (x : ℚ) :
    (shiftPolynomial P d).eval x = P.eval (x + d) := by
  simp [shiftPolynomial, Polynomial.eval_comp]

/-- **Twisting shifts the fibrewise Hilbert polynomial** (Stacks 0DP7): `ℱ` has fibrewise Hilbert
polynomial `P` exactly when `ℱ(d)` has `t ↦ P(t + d)`. -/
theorem hasFibreHilbertPolynomial_twist_iff (P : Polynomial ℚ) (d : ℤ)
    (F : (projectiveSpaceOver n T).Modules) (hF : F.IsFinitePresentation) :
    HasFibreHilbertPolynomial (shiftPolynomial P d) (twist d F) ↔
      HasFibreHilbertPolynomial P F := by
  have := hF
  have : (twist d F).IsFinitePresentation := isFinitePresentation_twist d F hF
  rw [hasFibreHilbertPolynomial_iff, hasFibreHilbertPolynomial_iff]
  constructor
  · intro h t e
    have := h t (e - d)
    rw [fibreHilbert_twist, eval_shiftPolynomial, sub_add_cancel] at this
    push_cast at this
    simpa using this
  · intro h t e
    rw [fibreHilbert_twist, eval_shiftPolynomial]
    exact_mod_cast h t (e + d)

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
