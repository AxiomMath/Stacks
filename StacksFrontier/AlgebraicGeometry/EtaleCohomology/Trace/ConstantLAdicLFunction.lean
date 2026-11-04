module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf

/-!
# `L(X, ℚ_ℓ)`: the L-function of Tag 03UX at a sheaf with trivial stalk Frobenius

Section 23 of the source opens by computing the local factors of the constant sheaf: if `x̄` is a
geometric point of `X`, the Galois module `ℱ_x̄ = ℚ_ℓ` is trivial, so

`det(1 - π_x^* T^{deg x} |_{ℱ_x̄})⁻¹ = 1 / (1 - T^{deg x})`,

and therefore `L(X, ℚ_ℓ)` — the L-function of Tag 03UX, an Euler product over the closed points
of `X` of inverse characteristic series of the geometric Frobenius on the rational stalks — is the
Euler product `∏_{x ∈ |X|} (1 - T^{deg x})⁻¹` that `constantLFunction` records.

This module carries that identification.  The input is exactly the displayed computation: that the
characteristic series of `π_x^*` on the rational stalk at `x` is `1 - T^{deg x}`, which is what
triviality of the Galois module at every geometric point says once the stalk is one-dimensional.
With it, `rationalLFunction_eq_constantLFunction` identifies the two L-functions, and the four
assertions of Tag 03V8 proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve` become assertions about
`LAdicSheaf.rationalLFunction`.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_eq_one_sub_X_pow_of_id`: a trivial Galois module of
  rank one has local factor `1 - T^d`, which is the source's "the Galois module `ℱ_x̄ = ℚ_ℓ` is
  trivial".
* `Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction_eq_constantLFunction`: the L-function of a
  `ℚ_ℓ`-sheaf whose local factors are those of the constant sheaf is `constantLFunction`.
* `Stacks.EtaleCohomology.LAdicSheaf.isRational_rationalLFunction`: part (1) of Tag 03V8 stated
  for `L(X, ℚ_ℓ)` in the form Tag 03UX defines it, for a sheaf whose local factors are those of
  the constant sheaf.

## Why nothing here is registered against Tag 03V8

`htrivial` is not one of Lemma 64.23.1's hypotheses: the source assumes only that `X` is a
smooth, projective, geometrically irreducible curve over a finite field, and the triviality of
the Galois module `ℱ_x̄ = ℚ_ℓ` is the opening *computation* of §23 for the constant sheaf.  The
library has no constant `ℓ`-adic sheaf to run that computation on — an object of `LAdicSheaf`
needs a constructible sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules at every level with the scalar-reduction maps
isomorphisms, and the identification of its geometric stalk together with the triviality of the
action of `π_x^*` there.  So `F` below is an arbitrary `ℚ_ℓ`-sheaf and `htrivial` restricts it;
Tag 03V8's part (1) is instead registered, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve`, on
`isRational_constantLFunction`, whose subject is the defined Euler product `constantLFunction`.

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8), Lemma 64.23.1.
* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX), the L-function.
* [Stacks Project, Tag 03V7](https://stacks.math.columbia.edu/tag/03V7), §23, whose opening
  paragraph is the computation `htrivial` restricts `F` by.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory CategoryTheory.Limits
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Finite k]

/-- **The stalk computation of §23.**  A trivial Galois module of rank one has local factor
`1 - T^d`: if the stalk has a basis indexed by `Fin 1` and the geometric Frobenius acts on it as
the identity, then `det(1 - π_x^* T^d |_{ℱ_x̄}) = 1 - T^d`.  This is the content of "the Galois
module `ℱ_x̄ = ℚ_ℓ` is trivial" in the source. -/
public theorem charPowerSeries_eq_one_sub_X_pow_of_id {Λ : Type*} [CommRing Λ] {M : Type*}
    [AddCommGroup M] [Module Λ M] (b : Module.Basis (Fin 1) Λ M) {φ : M →ₗ[Λ] M}
    (hφ : φ = LinearMap.id) (d : ℕ) :
    charPowerSeries φ d = 1 - (PowerSeries.X : PowerSeries Λ) ^ d := by
  rw [charPowerSeries_eq_localCharSeries b φ d, hφ, LinearMap.toMatrix_id,
    localCharSeries_one_fin_one]

/-- **The opening computation of §23.**  If the geometric Frobenius at every closed point has
characteristic series `1 - T^{deg x}` on the rational stalk — which is what triviality of the
Galois module `ℱ_x̄ = ℚ_ℓ` says — then the L-function of Tag 03UX is the Euler product
`∏_{x ∈ |X|} (1 - T^{deg x})⁻¹`. -/
public theorem LAdicSheaf.rationalLFunction_eq_constantLFunction (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (htrivial : ∀ x : closedPoints X.1,
      charPowerSeries
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
          (residueDegree f x.1)
        = 1 - PowerSeries.X ^ (residueDegree f x.1)) :
    LAdicSheaf.rationalLFunction B X ℓ F f = constantLFunction f (Padic ℓ) := by
  rw [LAdicSheaf.rationalLFunction, constantLFunction]
  refine FrobeniusMatrices.lFunction_congr _ fun x => ?_
  rw [LAdicSheaf.localFactor_frobeniusMatrices, htrivial x,
    localFactor_constantFrobeniusMatrices, localEulerFactor, localCharSeries_one_fin_one]

/-- **Part (1) of Tag 03V8 for `L(X, ℚ_ℓ)` as Tag 03UX defines it.**  The L-function of a
`ℚ_ℓ`-sheaf whose local factors are those of the constant sheaf, on a smooth, projective,
geometrically irreducible curve over a finite field, is a rational function: its product with the
polynomial `(1 - T)(1 - qT)`, whose value at `0` is `1`, is the polynomial
`det(1 - π_X^* T |_{H^1})`.

This carries no Stacks registration: `htrivial` restricts `F` rather than transcribing a
hypothesis of Lemma 64.23.1, as the module docstring explains. -/
public theorem LAdicSheaf.isRational_rationalLFunction (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (htrivial : ∀ x : closedPoints X.1,
      charPowerSeries
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
          (residueDegree f x.1)
        = 1 - PowerSeries.X ^ (residueDegree f x.1))
    (q : ℕ) {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) (Padic ℓ)) (N : ℕ → ℕ)
    (hcount : ∀ n : ℕ, n ≠ 0 →
      N n = ∑ x ∈ (closedPointsDegreeLE f n).filter fun x => residueDegree f x.1 ∣ n,
        residueDegree f x.1)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Padic ℓ) =
      ∑ a : Fin 3, (if Even (curveDeg a) then (1 : Padic ℓ) else -1) *
        ((curveFrobenius q A a) ^ n).trace) :
    ∃ P Q : Polynomial (Padic ℓ), Q.eval 0 ≠ 0 ∧
      LAdicSheaf.rationalLFunction B X ℓ F f * (Q : PowerSeries (Padic ℓ))
        = (P : PowerSeries (Padic ℓ)) := by
  rw [LAdicSheaf.rationalLFunction_eq_constantLFunction B X ℓ F f htrivial]
  exact isRational_constantLFunction q A N hcount hpoint

end Stacks.EtaleCohomology

end
