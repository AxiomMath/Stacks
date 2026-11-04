module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairing
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Module.ZMod

/-!
# Weil's trace formula for a twisted Frobenius of a curve, in `Pic[ℓⁿ]` form

This file states the form of Weil's theorem ([Stacks, Tag 03U1]) that Step 9 of the proof of
[Stacks, Tag 03V3] consumes, for one connected nonsingular projective curve `C` over an
algebraically closed field `Ω` of characteristic `p` and an endomorphism `φ : C → C` over `Ω`
which is a *twisted Frobenius*: there is an automorphism `Ψ` of the scheme `C` with
`Ψ ≫ φ = F^f`, `F` the absolute Frobenius of `C`. (For `C` a connected component of
`Ȳ = Y ×_k Ω`, `k = 𝔽_q`, `q = p^f`, `σ` an automorphism of `Y` over `k` and `φ = σ̄ ∘ π_Y`,
one takes `Ψ = Fr' ∘ σ̄⁻¹` with `Fr'` the arithmetic Frobenius.) The statement is

`#{c ∈ C(Ω) : φ(c) = c} ≡ 1 - Tr(φ^* | Pic(C)[ℓⁿ]) + deg φ  (mod ℓⁿ)`

for every prime `ℓ ≠ p` and `n ≥ 1`. The fixed points of a twisted Frobenius all have
multiplicity one, so the left-hand side is the intersection number `V(φ)` of the source, and
`Pic(C)[ℓⁿ] = J[ℓⁿ]` is the `ℓⁿ`-torsion of the jacobian.

It is recorded as a `Prop`, `Stacks.EtaleCohomology.WeilTraceInput`, the input to Step 9; it
carries no `@[stacks]` attribute.

## Main definitions

* `Stacks.EtaleCohomology.picardTorsionTrace` — the trace over `ℤ/ℓⁿ` of an additive
  endomorphism of `Pic(X)` on the `ℓⁿ`-torsion.
* `Stacks.EtaleCohomology.WeilTraceInput` — the statement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The `ℓⁿ`-torsion `Pic(X)[ℓⁿ]` is a `ℤ/ℓⁿ`-module. -/
instance picardTorsionModule (X : Scheme.{u}) (ℓ n : ℕ) [NeZero ℓ] :
    Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) ((ℓ : ℤ) ^ n)) :=
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (NeZero.ne ℓ)⟩
  AddCommGroup.zmodModule fun x => by
    ext1
    simp [← natCast_zsmul]

/-- The trace over `ℤ/ℓⁿ` of the restriction of an additive endomorphism `σ` of `Pic(X)` to the
`ℓⁿ`-torsion `Pic(X)[ℓⁿ]`. When `Pic(X)[ℓⁿ]` is free of finite rank over `ℤ/ℓⁿ` (for a smooth
projective curve over an algebraically closed field with `ℓ` invertible, of rank `2g`), this is
the usual trace of a matrix of `σ`. -/
def picardTorsionTrace (X : Scheme.{u}) (σ : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X)
    (ℓ n : ℕ) [NeZero ℓ] : ZMod (ℓ ^ n) :=
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (NeZero.ne ℓ)⟩
  LinearMap.trace (ZMod (ℓ ^ n)) _
    ((Stacks.Picard.torsionByRestrict σ ((ℓ : ℤ) ^ n)).toZModLinearMap (ℓ ^ n))

/-- **Weil's trace formula for a twisted Frobenius of a curve, in `Pic[ℓⁿ]` form** (the form of
[Stacks, Tag 03U1] used in Step 9 of [Stacks, Tag 03V3]). For every algebraically closed field
`Ω` of characteristic `p`, algebraic over `𝔽_p`, every connected nonsingular projective curve
`g : C ⟶ Spec Ω`, every endomorphism `φ` of `C` over `Ω` with an automorphism `Ψ` of `C` such
that `Ψ ≫ φ` is the `f`-fold absolute Frobenius of `C` (`f ≥ 1`), every prime `ℓ ≠ p` and every
`n ≥ 1`:

`#{c ∈ C(Ω) : φ c = c} = 1 - Tr(φ^* | Pic(C)[ℓⁿ]) + deg φ` in `ℤ/ℓⁿ`. -/
def WeilTraceInput : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
    (_halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)
    (C : Scheme.{u}) (g : C ⟶ Spec (.of Ω)) [IsProper g] [Smooth g] [IsCurve Ω g]
    (φ : C ⟶ C) (w : φ ≫ g = g) (hnc : ¬ ∃ y : C, ∀ x : C, φ.base x = y)
    (f : ℕ) (_hf : 0 < f) (hC : Stacks.Frobenius.IsInCharacteristic C p) (Ψ : C ≅ C)
    (_hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC f)
    (ℓ n : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : Ω) ≠ 0) (_hn : 1 ≤ n),
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ((Nat.card (fixedSections g φ) : ℤ) : ZMod (ℓ ^ n)) =
      1 - picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ n +
        ((@degreeOver C C φ _ _ (locallyOfFiniteType_of_isCurve_comp Ω g g φ w)
          (isDominant_of_not_constant Ω g g φ hnc) : ℕ) : ZMod (ℓ ^ n))

end Stacks.EtaleCohomology
