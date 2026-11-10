module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageTraceFormula

/-!
# Pointwise relations between Frobenius traces pass to finite étale direct images

Let `π : X ⟶ Y` be finite étale and `M`, `N` two lisse ℓ-adic sheaves on `X` whose Frobenius
traces at every point `x` over a point `v` of `Y` with finite residue field are related by
`Tr(π_x ^ k | M) = #κ(x) ^ (a k) · Tr(π_x ^ k | N)` for `k ≥ 1` (for `a = 0`: equal traces, as
for isogenous sheaves; for `a = 1`: `M = N(-1)` a Tate twist). Then the same relation holds for
the direct images at `v`:
`Tr(π_v ^ m | π_* M) = #κ(v) ^ (a m) · Tr(π_v ^ m | π_* N)` for `m ≥ 1`.

## Main results

* `Stacks.EtaleCohomology.natCard_residueField_eq_pow_liftResidueDegree`: `#κ(x) = #κ(v) ^ d_x`
  for a point `x` of `X` over a point `v` with finite residue field.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_of_pointwise`:
  the pointwise relation between the Frobenius traces of `M` and `N` passes to `π_* M` and
  `π_* N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [AlgebraicGeometry.Etale (B.inclusion.map π)] {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

omit [IsFinite (B.inclusion.map π)] [AlgebraicGeometry.IsNoetherian X.obj]
  [AlgebraicGeometry.IsNoetherian Y.obj] in
/-- `#κ(x) = #κ(π(x)) ^ d_x` for a point `x` of `X` over a point with finite residue field. -/
theorem natCard_residueField_eq_pow_liftResidueDegree (x : X.1)
    [Finite (Y.1.residueField ((B.inclusion.map π).base x))] :
    Nat.card (X.1.residueField x) =
      Nat.card (Y.1.residueField ((B.inclusion.map π).base x)) ^
        liftResidueDegree (B.inclusion.map π) x := by
  let : Algebra (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    ((B.inclusion.map π).residueFieldMap x).hom.toAlgebra
  have : Finite (X.1.residueField x) := finite_residueField_of_base_eq π x rfl
  have : Module.Finite (Y.1.residueField ((B.inclusion.map π).base x)) (X.1.residueField x) :=
    Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

/-- **A pointwise relation `Tr(π_x ^ k | M) = #κ(x) ^ (a k) · Tr(π_x ^ k | N)` between Frobenius
traces passes to the direct images along a finite étale `π`.** -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_of_pointwise
    (M N : LAdicSheaf.{u, u + 1} B X ℓ)
    (hM : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (M.level n))
    (hN : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (N.level n)) (a : ℕ)
    (v : Y.1) [Finite (Y.1.residueField v)]
    (h : ∀ (x : X.1), (B.inclusion.map π).base x = v → ∀ (hx : Finite (X.1.residueField x))
      (k : ℕ), 1 ≤ k →
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ M x hx ^ k) =
        (Nat.card (X.1.residueField x) : ℚ_[ℓ]) ^ (a * k) *
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ N x hx ^ k))
    (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B Y ℓ
        (SmallEtale.LAdicSheaf.directImage π M hM) v ‹_› ^ m) =
      (Nat.card (Y.1.residueField v) : ℚ_[ℓ]) ^ (a * m) *
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B Y ℓ
          (SmallEtale.LAdicSheaf.directImage π N hN) v ‹_› ^ m) := by
  classical
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one.mpr hm
  rw [LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum π v M hM e,
    LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum π v N hN e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (B.inclusion.map π).base x = v
  · rw [dite_eq_left hx, dite_eq_left hx]
    by_cases hd : liftResidueDegree (B.inclusion.map π) x ∣ e + 1
    · rw [ite_eq_left hd, ite_eq_left hd]
      have hdpos : 0 < liftResidueDegree (B.inclusion.map π) x := by
        subst hx
        exact liftResidueDegree_pos π x
      have hk : 1 ≤ (e + 1) / liftResidueDegree (B.inclusion.map π) x :=
        (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (Nat.succ_pos e) hd)
      rw [h x hx _ _ hk]
      have hcard : (Nat.card (X.1.residueField x) : ℚ_[ℓ]) ^
          (a * ((e + 1) / liftResidueDegree (B.inclusion.map π) x)) =
          (Nat.card (Y.1.residueField v) : ℚ_[ℓ]) ^ (a * (e + 1)) := by
        subst hx
        rw [natCard_residueField_eq_pow_liftResidueDegree π x, Nat.cast_pow, ← pow_mul]
        congr 1
        rw [mul_comm a, ← mul_assoc, Nat.mul_div_cancel' hd, mul_comm]
      rw [hcard]
      ring
    · rw [ite_eq_right hd, ite_eq_right hd, mul_zero]
  · rw [dite_eq_right hx, dite_eq_right hx, mul_zero]

end Stacks.EtaleCohomology

end
