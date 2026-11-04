module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.ChartRing
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Regularity of the chart ring of a cyclic cover over `k[[π]]`

Let `Q` be a regular ring, `n ≥ 1` invertible in `Q` and `u ∈ Q` a nonzerodivisor with `Q/(u)`
regular. Then `Q[x]/(xⁿ - u)` is regular: away from `x` it is étale over `Q`, and at a prime
containing `x` the element `x` is a nonzerodivisor whose quotient `Q/(u)` is regular
([Stacks, Tag 00NU]).

This applies to the chart ring `(A ⊗_k k[[π]])[x]/(xⁿ - π f)` of the cyclic cover of
[Stacks, Tag 0CEH], for `A` smooth over `k` and `f ∈ A` a unit: `A ⊗_k k[[π]]` is smooth over the
discrete valuation ring `k[[π]]`, hence regular ([Stacks, Tag 07NF]), and its quotient by `π` is
smooth over the residue field `k`.

## Main results

* `Stacks.CyclicCover.etale_away_root`: `Q[x, x⁻¹]/(xⁿ - u)` is étale over `Q`.
* `Stacks.CyclicCover.quotRootEquiv`: `Q[x]/(xⁿ - u, x) ≅ Q/(u)`.
* `Stacks.CyclicCover.isRegularRing_adjoinRoot`: the regularity criterion.
* `Stacks.CyclicCover.isRegularRing_chartRing`: the chart ring over `k[[π]]` with `c = π` is
  regular.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
* [Stacks Project, Tag 00NU](https://stacks.math.columbia.edu/tag/00NU)
* [Stacks Project, Tag 07NF](https://stacks.math.columbia.edu/tag/07NF)
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

universe u

namespace Stacks.CyclicCover

section Criterion

variable {Q : Type u} [CommRing Q] {n : ℕ} (u : Q)

/-- `Q[x, x⁻¹]/(xⁿ - u)` is étale over `Q` when `n` is invertible. -/
theorem etale_away_root (hn : n ≠ 0) (hnu : IsUnit (n : Q)) :
    Algebra.Etale Q (Localization.Away (AdjoinRoot.root (X ^ n - C u))) := by
  have hna : C (n : Q) * C (↑hnu.unit⁻¹ : Q) = 1 := by rw [← C_mul]; simp
  let P : StandardEtalePair Q :=
    { f := X ^ n - C u, monic_f := monic_X_pow_sub_C u hn, g := X,
      cond := ⟨C (↑hnu.unit⁻¹ : Q) * X, 0, n, by
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero]
        linear_combination (C (n : Q) * C (↑hnu.unit⁻¹ : Q)) * pow_sub_one_mul hn (X : Q[X])
          + X ^ n * hna⟩ }
  exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

/-- In `Q[x]/(xⁿ - u)`, the root `x` satisfies `xⁿ = u`. -/
theorem root_pow_eq (hn : n ≠ 0) :
    AdjoinRoot.root (X ^ n - C u) ^ n = AdjoinRoot.of (X ^ n - C u) u := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The map `Q[x]/(xⁿ - u) → Q/(u)`, `x ↦ 0`. -/
def quotRootHom (hn : n ≠ 0) : AdjoinRoot (X ^ n - C u) →+* Q ⧸ Ideal.span {u} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) 0 (by
    simp [zero_pow hn])

/-- `Q[x]/(xⁿ - u, x) ≅ Q/(u)`. -/
def quotRootEquiv (hn : n ≠ 0) :
    AdjoinRoot (X ^ n - C u) ⧸ Ideal.span {AdjoinRoot.root (X ^ n - C u)} ≃+*
      Q ⧸ Ideal.span {u} := by
  refine RingEquiv.ofRingHom
    (Ideal.Quotient.lift _ (quotRootHom u hn) ?_)
    (Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (AdjoinRoot.of _)) ?_) ?_ ?_
  · intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [quotRootHom]
  · intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [RingHom.comp_apply, map_mul, ← root_pow_eq u hn, map_mul, map_pow,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_pow hn, mul_zero]
  · ext a
    simp [quotRootHom]
  · refine Ideal.Quotient.ringHom_ext (AdjoinRoot.ringHom_ext ?_ ?_)
    · ext a; simp [quotRootHom]
    · simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, quotRootHom, AdjoinRoot.lift_root,
        map_zero, RingHom.id_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm

/-- A flat algebra preserves nonzerodivisors of the base. -/
private theorem algebraMap_mem_nonZeroDivisors_of_flat {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Flat R B] {r : R} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R B r ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors hr ?_
  change r • b = r • 0
  rw [smul_zero, Algebra.smul_def, mul_comm, hb]

/-- If `u` is a nonzerodivisor of `Q`, then the root `x` is a nonzerodivisor of `Q[x]/(xⁿ - u)`. -/
theorem root_mem_nonZeroDivisors (hn : n ≠ 0) (hu : u ∈ nonZeroDivisors Q) :
    AdjoinRoot.root (X ^ n - C u) ∈ nonZeroDivisors (AdjoinRoot (X ^ n - C u)) := by
  have := free_adjoinRoot u hn
  have h := algebraMap_mem_nonZeroDivisors_of_flat (B := AdjoinRoot (X ^ n - C u)) hu
  rw [AdjoinRoot.algebraMap_eq, ← root_pow_eq u hn,
    ← pow_sub_one_mul hn (AdjoinRoot.root (X ^ n - C u)), mul_mem_nonZeroDivisors] at h
  exact h.2

/-- **`Q[x]/(xⁿ - u)` is regular** if `Q` is regular, `n` is invertible, `u` is a nonzerodivisor
and `Q/(u)` is regular. Away from `x` the ring is étale over `Q`; at a prime containing `x` it is
regular because `x` is a nonzerodivisor with regular quotient `Q/(u)`. -/
theorem isRegularRing_adjoinRoot [IsRegularRing Q] (hn : n ≠ 0) (hnu : IsUnit (n : Q))
    (hu : u ∈ nonZeroDivisors Q) (hQu : IsRegularRing (Q ⧸ Ideal.span {u})) :
    IsRegularRing (AdjoinRoot (X ^ n - C u)) := by
  set B := AdjoinRoot (X ^ n - C u)
  set x := AdjoinRoot.root (X ^ n - C u)
  have := finite_adjoinRoot u hn
  have : IsNoetherianRing B := IsNoetherianRing.of_finite Q B
  refine { isRegularLocalRing_localization := fun q hq => ?_ }
  by_cases hx : x ∈ q
  · have : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
    refine isRegularLocalRing_of_nonZeroDivisor _ (algebraMap B (Localization.AtPrime q) x)
      (IsLocalization.map_nonZeroDivisors_le q.primeCompl _
        ⟨x, root_mem_nonZeroDivisors u hn hu, rfl⟩) ?_
    set J : Ideal B := Ideal.span {x}
    have hJq : J ≤ q := (Ideal.span_singleton_le_iff_mem _).2 hx
    let 𝔮 : Ideal (B ⧸ J) := q.map (Ideal.Quotient.mk J)
    have h𝔮 : 𝔮.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJq)
    have hcomap : 𝔮.comap (Ideal.Quotient.mk J) = q := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hJq]
    have hloc := isLocalization_atPrime_quotient q (Localization.AtPrime q) J 𝔮 hcomap
    have : IsRegularRing (B ⧸ J) := IsRegularRing.of_ringEquiv (quotRootEquiv u hn).symm
    have hspan : Ideal.span {algebraMap B (Localization.AtPrime q) x} =
        J.map (algebraMap B (Localization.AtPrime q)) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hspan]
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮) _).toRingEquiv
  · have := etale_away_root u hn hnu
    have : IsRegularRing (Localization.Away x) := Algebra.isRegularRing_of_smooth Q _
    have hdisj : Disjoint (↑(Submonoid.powers x) : Set B) ↑q :=
      (Ideal.disjoint_powers_iff_notMem _ hq.isRadical).2 hx
    have hq' : (q.map (algebraMap B (Localization.Away x))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ q hq hdisj
    have hcomap : (q.map (algebraMap B (Localization.Away x))).comap
        (algebraMap B (Localization.Away x)) = q :=
      IsLocalization.comap_map_of_isPrime_disjoint _ _ hq hdisj
    have key : ∀ (I : Ideal B) [I.IsPrime], I = q →
        IsRegularLocalRing (Localization.AtPrime I) →
          IsRegularLocalRing (Localization.AtPrime q) := by
      rintro I _ rfl h
      exact h
    exact key _ hcomap (IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers x)
        (q.map (algebraMap B (Localization.Away x)))).toRingEquiv.symm)

end Criterion

section PowerSeries

variable {k : Type u} [Field k] (A : Type u) [CommRing A] [Algebra k A] [Algebra.Smooth k A]

/-- `A ⊗_k k[[π]]` is a regular ring for `A` smooth over the field `k`. -/
theorem isRegularRing_tensor_powerSeries : IsRegularRing (A ⊗[k] PowerSeries k) := by
  have := Algebra.Smooth.baseChange k A (PowerSeries k)
  have : IsRegularRing (PowerSeries k ⊗[k] A) := Algebra.isRegularRing_of_smooth (PowerSeries k) _
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k (PowerSeries k) A).toRingEquiv

/-- The ideal `(π)` of `k[[π]]` is maximal. -/
theorem span_X_isMaximal : (Ideal.span {(PowerSeries.X : PowerSeries k)}).IsMaximal := by
  have : Ideal.span {(PowerSeries.X : PowerSeries k)} =
      RingHom.ker (PowerSeries.constantCoeff (R := k)) := by
    ext φ
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, PowerSeries.X_dvd_iff]
  rw [this]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨PowerSeries.C a, by simp⟩)

/-- The quotient of `A ⊗_k k[[π]]` by `1 ⊗ π` is a regular ring for `A` smooth over `k`. -/
theorem isRegularRing_tensor_powerSeries_quot :
    IsRegularRing ((A ⊗[k] PowerSeries k) ⧸
      Ideal.span {(1 : A) ⊗ₜ[k] (PowerSeries.X : PowerSeries k)}) := by
  set R := PowerSeries k
  set I : Ideal R := Ideal.span {PowerSeries.X}
  have := span_X_isMaximal (k := k)
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have := Algebra.Smooth.baseChange k A R
  have : Algebra.Smooth (R ⧸ I) ((R ⧸ I) ⊗[R] (R ⊗[k] A)) := Algebra.Smooth.baseChange R _ _
  have : IsRegularRing ((R ⧸ I) ⊗[R] (R ⊗[k] A)) :=
    Stacks.Smooth.RegularRingAscent.isRegularRing_of_formallySmooth (R ⧸ I) _
  have e1 := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R ⊗[k] A) I).toRingEquiv.trans
    (Algebra.TensorProduct.comm R (R ⊗[k] A) (R ⧸ I)).toRingEquiv
  have : IsRegularRing ((R ⊗[k] A) ⧸ I.map (algebraMap R (R ⊗[k] A))) :=
    IsRegularRing.of_ringEquiv e1.symm
  refine IsRegularRing.of_ringEquiv (Ideal.quotientEquiv
    (I.map (algebraMap R (R ⊗[k] A))) (Ideal.span {(1 : A) ⊗ₜ[k] (PowerSeries.X : R)})
    (Algebra.TensorProduct.comm k R A).toRingEquiv ?_)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  simp [R, Algebra.TensorProduct.algebraMap_apply]

/-- The element `1 ⊗ π` is a nonzerodivisor of `A ⊗_k k[[π]]`. -/
theorem tmul_X_mem_nonZeroDivisors :
    (1 : A) ⊗ₜ[k] (PowerSeries.X : PowerSeries k) ∈ nonZeroDivisors (A ⊗[k] PowerSeries k) := by
  set R := PowerSeries k
  have h1 : algebraMap R (R ⊗[k] A) PowerSeries.X ∈ nonZeroDivisors (R ⊗[k] A) :=
    algebraMap_mem_nonZeroDivisors_of_flat (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero)
  set e := (Algebra.TensorProduct.comm k A R).toRingEquiv
  have h2 : e ((1 : A) ⊗ₜ[k] (PowerSeries.X : R)) = algebraMap R (R ⊗[k] A) PowerSeries.X := by
    simp only [e, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul]
    rfl
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  refine e.injective ?_
  rw [map_zero]
  exact mem_nonZeroDivisors_iff_right.1 h1 (e b) (by rw [← h2, ← map_mul, hb, map_zero])

variable {A} {n : ℕ}

/-- **The chart ring `(A ⊗_k k[[π]])[x]/(xⁿ - π f)` is regular** for `A` smooth over `k`, `f` a
unit of `A` and `n` invertible in `k`. -/
theorem isRegularRing_chartRing (hn : (n : k) ≠ 0) {f : A} (hf : IsUnit f) :
    IsRegularRing (chartRing k n f (PowerSeries.X : PowerSeries k)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have := isRegularRing_tensor_powerSeries (k := k) A
  have hu : (f ⊗ₜ[k] (PowerSeries.X : PowerSeries k) : A ⊗[k] PowerSeries k) =
      (f ⊗ₜ[k] 1) * ((1 : A) ⊗ₜ[k] (PowerSeries.X : PowerSeries k)) := by simp
  have hfu : IsUnit (f ⊗ₜ[k] (1 : PowerSeries k) : A ⊗[k] PowerSeries k) :=
    hf.map (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := PowerSeries k))
  refine isRegularRing_adjoinRoot _ hn0 ?_ ?_ ?_
  · simpa using (IsUnit.mk0 _ hn).map (algebraMap k (A ⊗[k] PowerSeries k))
  · rw [hu]
    exact Submonoid.mul_mem _ hfu.mem_nonZeroDivisors (tmul_X_mem_nonZeroDivisors A)
  · rw [hu, Ideal.span_singleton_mul_left_unit hfu]
    exact isRegularRing_tensor_powerSeries_quot A

end PowerSeries

end Stacks.CyclicCover

end
