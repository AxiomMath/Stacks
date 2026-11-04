module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialFiberTestRing
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialTwistLocalization
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialVertexIdeal
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.TwistAwaySelf
public import StacksFrontier.RingTheory.Polynomial.QuotientXPow

/-!
# The fibres of the second and third twists at the vertex

Let `S = k[x, y, z]` be graded by the weights `1`, `2`, `3`, let `S₍z₎` be the degree-zero
localization at `z` and let `𝔪 = (u, v, w)` be its vertex ideal. This file computes the vertex
fibres of the second and third localized twists:

* `S(2)₍z₎ / 𝔪 S(2)₍z₎` has dimension two, its generators `y` and `x²` staying independent;
* `S(3)₍z₎ / 𝔪 S(3)₍z₎` has dimension one, the third twist being free of rank one on `z`.

Together with the two-dimensional fibre of the first twist, this is the dimension count that
rules out an isomorphism `S(1)₍z₎ ⊗ S(2)₍z₎ ≅ S(3)₍z₎`.

## Main results

* `Stacks.WeightedPolynomialSituation.finrank_secondTwistLocalization_quotient_vertexIdeal`:
  the vertex fibre of the second localized twist has dimension two.
* `Stacks.WeightedPolynomialSituation.finrank_thirdTwistLocalization_quotient_vertexIdeal`:
  the vertex fibre of the third localized twist has dimension one.

## Implementation notes

Both fibres are written as the quotient of the localized twist by the submodule `𝔪 · ⊤`, over the
quotient ring `S₍z₎ / 𝔪`, which is a field because the vertex ideal is maximal. The second
dimension count then needs only a spanning family and a test for independence; the third goes
through an explicit `S₍z₎`-linear isomorphism `S₍z₎ ≅ S(3)₍z₎` and Mathlib's identification of
`κ ⊗ M` with `M / 𝔪 M`.

Independence of `y` and `x²` modulo `𝔪` is detected by a ring map from `S₍z₎`-module `S(2)₍z₎`
into `k[X]/(X³) × k[X]/(X³)` sending `x ↦ (X, 0)`, `y ↦ (0, X)` and `z ↦ 1`. It kills `u`, `v`
and `w`, hence the whole of `𝔪 · S(2)₍z₎`, and it sends `y` and `x²` to `(0, X)` and `(X², 0)`,
which are independent over `k` because no scalar multiple of `X` or of `X²` vanishes in
`k[X]/(X³)` (`Polynomial.QuotientXPow.eq_zero_of_algebraMap_mul_gen_pow_eq_zero`).

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

public section

namespace Stacks.WeightedPolynomialSituation

private lemma range_fin2_pair {α : Type*} (a b : α) :
    Set.range (![a, b] : Fin 2 → α) = {a, b} := by
  ext x
  simp [or_comm]

private noncomputable def fiberTestX (E : WeightedPolynomialSituation) : FiberTestRing E :=
  (Polynomial.QuotientXPow.gen E.k 3, 0)

private noncomputable def fiberTestY (E : WeightedPolynomialSituation) : FiberTestRing E :=
  (0, Polynomial.QuotientXPow.gen E.k 3)

private noncomputable def fiberTestZ (E : WeightedPolynomialSituation) : FiberTestRing E := 1

private noncomputable def fiberTestPolynomialMap (E : WeightedPolynomialSituation) :
    E.S →+* FiberTestRing E :=
  (MvPolynomial.aeval ![fiberTestX E, fiberTestY E, fiberTestZ E] :
    E.S →ₐ[E.k] FiberTestRing E).toRingHom

private lemma fiberTestPolynomialMap_z (E : WeightedPolynomialSituation) :
    fiberTestPolynomialMap E E.z = 1 := by
  simp [fiberTestPolynomialMap, WeightedPolynomialSituation.z, fiberTestZ,
    fiberTestX, fiberTestY]

private lemma isUnit_fiberTestPolynomialMap_z (E : WeightedPolynomialSituation) :
    IsUnit (fiberTestPolynomialMap E E.z) := by
  rw [fiberTestPolynomialMap_z]
  exact isUnit_one

private noncomputable def fiberTestLocalizationMap (E : WeightedPolynomialSituation) :
    E.ordinaryLocalization →+* FiberTestRing E :=
  Localization.awayLift (fiberTestPolynomialMap E) E.z (isUnit_fiberTestPolynomialMap_z E)

private noncomputable def fiberTestRingMap (E : WeightedPolynomialSituation) :
    E.R →+* FiberTestRing E :=
  (fiberTestLocalizationMap E).comp (algebraMap E.R E.ordinaryLocalization)

/-- The localization map extends the polynomial map. -/
private lemma fiberTestLocalizationMap_algebraMap (E : WeightedPolynomialSituation) (f : E.S) :
    fiberTestLocalizationMap E (algebraMap E.S E.ordinaryLocalization f) =
      fiberTestPolynomialMap E f := by
  simp [fiberTestLocalizationMap, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- The localization map kills a fraction `a / z ^ j` whose numerator is killed by the
polynomial map. -/
private lemma fiberTestLocalizationMap_mk_eq_zero (E : WeightedPolynomialSituation) (a : E.S)
    (j : ℕ) (ha : fiberTestPolynomialMap E a = 0) :
    fiberTestLocalizationMap E (Localization.mk a
      ⟨E.z ^ j, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) j⟩) = 0 := by
  unfold fiberTestLocalizationMap
  rw [Localization.awayLift_mk (fiberTestPolynomialMap E) E.z a 1
    (by simp [fiberTestPolynomialMap_z]) j]
  simp [ha]

private lemma fiberTestRingMap_const (E : WeightedPolynomialSituation) (a : E.k) :
    fiberTestRingMap E (algebraMap E.k E.R a) = algebraMap E.k (FiberTestRing E) a := by
  change fiberTestLocalizationMap E
    ((algebraMap E.S E.ordinaryLocalization) (algebraMap E.k E.S a)) = _
  simp [fiberTestLocalizationMap_algebraMap, fiberTestPolynomialMap]

private lemma fiberTestRingMap_u (E : WeightedPolynomialSituation) :
    fiberTestRingMap E E.u = 0 :=
  fiberTestLocalizationMap_mk_eq_zero E (E.x ^ 3) 1 (by
    simp [fiberTestPolynomialMap, fiberTestX, fiberTestY, fiberTestZ,
      WeightedPolynomialSituation.x, Polynomial.QuotientXPow.gen_pow_self])

private lemma fiberTestRingMap_v (E : WeightedPolynomialSituation) :
    fiberTestRingMap E E.v = 0 :=
  fiberTestLocalizationMap_mk_eq_zero E (E.x * E.y) 1 (by
    simp [fiberTestPolynomialMap, fiberTestX, fiberTestY, fiberTestZ,
      WeightedPolynomialSituation.x, WeightedPolynomialSituation.y])

private lemma fiberTestRingMap_w (E : WeightedPolynomialSituation) :
    fiberTestRingMap E E.w = 0 :=
  fiberTestLocalizationMap_mk_eq_zero E (E.y ^ 3) 2 (by
    simp [fiberTestPolynomialMap, fiberTestX, fiberTestY, fiberTestZ,
      WeightedPolynomialSituation.y, Polynomial.QuotientXPow.gen_pow_self])

private lemma fiberTestRingMap_eq_zero_of_mem_vertexIdeal (E : WeightedPolynomialSituation)
    (r : E.R) (hr : r ∈ E.vertexIdeal) : fiberTestRingMap E r = 0 := by
  rw [WeightedPolynomialSituation.vertexIdeal] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact fiberTestRingMap_u E
      · exact fiberTestRingMap_v E
      · exact fiberTestRingMap_w E
  | zero => simp
  | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
  | smul a x hx ih => simp [map_mul, ih]

private noncomputable def fiberTestLinearMap (E : WeightedPolynomialSituation) :
    letI : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
    E.secondTwistLocalization →ₗ[E.R] FiberTestRing E := by
  letI : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
  refine { toFun := fun n => fiberTestLocalizationMap E n.1, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    simp
  · intro r x
    change fiberTestLocalizationMap E
        ((algebraMap E.R E.ordinaryLocalization) r * (x : E.ordinaryLocalization)) =
      fiberTestRingMap E r * fiberTestLocalizationMap E (x : E.ordinaryLocalization)
    simp [fiberTestRingMap, map_mul]

private lemma fiberTestLinearMap_eq_zero_of_mem_vertexIdeal_smul_top
    (E : WeightedPolynomialSituation) :
    ∀ (x : E.secondTwistLocalization),
      x ∈ E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization) →
    letI : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
    fiberTestLinearMap E x = 0 := by
  intro x hx
  let : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
  refine Submodule.smul_induction_on
    (p := fun y : E.secondTwistLocalization => fiberTestLinearMap E y = 0) hx ?_ ?_
  · intro r hr n hn
    change fiberTestLinearMap E (r • n) = 0
    rw [(fiberTestLinearMap E).map_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, fiberTestRingMap_eq_zero_of_mem_vertexIdeal E r hr]
    simp
  · intro a b ha hb
    simp [ha, hb]

private noncomputable def secondTwistLocalizationY (E : WeightedPolynomialSituation) :
    E.secondTwistLocalization :=
  ⟨algebraMap E.S E.ordinaryLocalization E.y, by
    rw [secondTwistLocalization_eq_span]
    exact Submodule.subset_span (by simp)⟩

private noncomputable def secondTwistLocalizationX2 (E : WeightedPolynomialSituation) :
    E.secondTwistLocalization :=
  ⟨algebraMap E.S E.ordinaryLocalization (E.x ^ 2), by
    rw [secondTwistLocalization_eq_span]
    exact Submodule.subset_span (by simp)⟩

private lemma fiberTestLinearMap_Y (E : WeightedPolynomialSituation) :
    letI : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
    fiberTestLinearMap E (secondTwistLocalizationY E) = fiberTestY E := by
  change fiberTestLocalizationMap E (algebraMap E.S E.ordinaryLocalization E.y) = _
  simp [fiberTestLocalizationMap_algebraMap, fiberTestPolynomialMap, fiberTestY, fiberTestX,
    fiberTestZ]

private lemma fiberTestLinearMap_X2 (E : WeightedPolynomialSituation) :
    letI : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
    fiberTestLinearMap E (secondTwistLocalizationX2 E) = fiberTestX E ^ 2 := by
  change fiberTestLocalizationMap E (algebraMap E.S E.ordinaryLocalization (E.x ^ 2)) = _
  simp [fiberTestLocalizationMap_algebraMap, fiberTestPolynomialMap, fiberTestY, fiberTestX,
    fiberTestZ]

/-- A `k`-combination of the two generators of the second localized twist that lies in
`𝔪 · S(2)₍z₎` has both coefficients zero. -/
private lemma eq_zero_of_mem_vertexIdeal_smul_top (E : WeightedPolynomialSituation) (a b : E.k)
    (hzmem : (algebraMap E.k E.R a) • secondTwistLocalizationY E +
        (algebraMap E.k E.R b) • secondTwistLocalizationX2 E ∈
      E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization)) :
    a = 0 ∧ b = 0 := by
  let : Algebra E.R (FiberTestRing E) := (fiberTestRingMap E).toAlgebra
  have htest := fiberTestLinearMap_eq_zero_of_mem_vertexIdeal_smul_top E _ hzmem
  have htest' : (algebraMap E.k (FiberTestRing E) a) * fiberTestY E +
      (algebraMap E.k (FiberTestRing E) b) * (fiberTestX E ^ 2) = 0 := by
    simp only [(fiberTestLinearMap E).map_add, (fiberTestLinearMap E).map_smul] at htest
    change fiberTestRingMap E (algebraMap E.k E.R a) *
        fiberTestLinearMap E (secondTwistLocalizationY E) +
      fiberTestRingMap E (algebraMap E.k E.R b) *
        fiberTestLinearMap E (secondTwistLocalizationX2 E) = 0 at htest
    rw [fiberTestRingMap_const E a, fiberTestRingMap_const E b,
      fiberTestLinearMap_Y, fiberTestLinearMap_X2] at htest
    exact htest
  have ha0 : (algebraMap E.k (Polynomial.QuotientXPow E.k 3) a) *
      (Polynomial.QuotientXPow.gen E.k 3) ^ 1 = 0 := by
    have h := congrArg Prod.snd htest'
    simpa [fiberTestY, fiberTestX] using h
  have hb0 : (algebraMap E.k (Polynomial.QuotientXPow E.k 3) b) *
      (Polynomial.QuotientXPow.gen E.k 3) ^ 2 = 0 := by
    have h := congrArg Prod.fst htest'
    simpa [fiberTestY, fiberTestX] using h
  exact ⟨Polynomial.QuotientXPow.eq_zero_of_algebraMap_mul_gen_pow_eq_zero E.k 3
      (by omega : 1 < 3) ha0,
    Polynomial.QuotientXPow.eq_zero_of_algebraMap_mul_gen_pow_eq_zero E.k 3
      (by omega : 2 < 3) hb0⟩

/-- The action of `R ⧸ I` on `M ⧸ I · M` is induced by the action of `R`, in the form in which
the fibre computation rewrites with it. -/
private lemma quotient_mk_ideal_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : R) (y : M) :
    Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) (r • y) =
      (Ideal.Quotient.mk I r) •
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) y :
          M ⧸ (I • (⊤ : Submodule R M))) :=
  Submodule.Quotient.mk_smul (I • ⊤) r y

/-- The two generators of the second localized twist are independent in the vertex fibre. -/
private lemma linearIndependent_secondTwistFiber_pair (E : WeightedPolynomialSituation) :
    letI : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
    LinearIndependent (E.R ⧸ E.vertexIdeal)
      (![Submodule.Quotient.mk
            (p := E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization))
            (secondTwistLocalizationY E),
          Submodule.Quotient.mk
            (p := E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization))
            (secondTwistLocalizationX2 E)] :
        Fin 2 → E.secondTwistLocalization ⧸
          E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization)) := by
  let : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
  let P := E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization)
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hsum : c 0 • (Submodule.Quotient.mk (p := P) (secondTwistLocalizationY E)) +
      c 1 • (Submodule.Quotient.mk (p := P) (secondTwistLocalizationX2 E)) = 0 := by
    simpa using hc
  obtain ⟨a, ha⟩ := (bijective_algebraMap_vertexIdeal_quotient E).2 (c 0)
  obtain ⟨b, hb⟩ := (bijective_algebraMap_vertexIdeal_quotient E).2 (c 1)
  have hA : Ideal.Quotient.mk E.vertexIdeal (algebraMap E.k E.R a) = c 0 :=
    (IsScalarTower.algebraMap_apply E.k E.R (E.R ⧸ E.vertexIdeal) a).symm.trans ha
  have hB : Ideal.Quotient.mk E.vertexIdeal (algebraMap E.k E.R b) = c 1 :=
    (IsScalarTower.algebraMap_apply E.k E.R (E.R ⧸ E.vertexIdeal) b).symm.trans hb
  have hz : (Submodule.Quotient.mk (p := P)
      ((algebraMap E.k E.R a) • secondTwistLocalizationY E +
        (algebraMap E.k E.R b) • secondTwistLocalizationX2 E)) = 0 :=
    (Submodule.Quotient.mk_add P).trans
      (((congrArg₂ (fun u v => u + v)
            (quotient_mk_ideal_smul E.vertexIdeal (algebraMap E.k E.R a)
              (secondTwistLocalizationY E))
            (quotient_mk_ideal_smul E.vertexIdeal (algebraMap E.k E.R b)
              (secondTwistLocalizationX2 E))).trans
        (congrArg₂ (fun u v => u + v)
          (congrArg (fun s => s • Submodule.Quotient.mk (p := P)
            (secondTwistLocalizationY E)) hA)
          (congrArg (fun s => s • Submodule.Quotient.mk (p := P)
            (secondTwistLocalizationX2 E)) hB))).trans hsum)
  obtain ⟨ha', hb'⟩ := eq_zero_of_mem_vertexIdeal_smul_top E a b
    ((Submodule.Quotient.mk_eq_zero P).mp hz)
  cases i using Fin.cases with
  | zero => rw [← ha, ha']; simp
  | succ j => fin_cases j; change c 1 = 0; rw [← hb, hb']; simp

/-- The vertex fiber of the second localized twist has dimension two. -/
theorem finrank_secondTwistLocalization_quotient_vertexIdeal
    (E : WeightedPolynomialSituation) :
    letI : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
    Module.finrank (E.R ⧸ E.vertexIdeal)
      (E.secondTwistLocalization ⧸
        E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization)) = 2 := by
  let : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
  classical
  let K := E.R ⧸ E.vertexIdeal
  let P := E.vertexIdeal • (⊤ : Submodule E.R E.secondTwistLocalization)
  let Q := E.secondTwistLocalization ⧸ P
  change Module.finrank K Q = 2
  let v : Fin 2 → Q := ![Submodule.Quotient.mk (p := P) (secondTwistLocalizationY E),
    Submodule.Quotient.mk (p := P) (secondTwistLocalizationX2 E)]
  have hli : LinearIndependent K v := linearIndependent_secondTwistFiber_pair E
  let g : Fin 2 → E.secondTwistLocalization :=
    ![secondTwistLocalizationY E, secondTwistLocalizationX2 E]
  have hg : Submodule.span E.R (Set.range g) = ⊤ := by
    apply (Submodule.span_val_image_eq_iff E.secondTwistLocalization (Set.range g)).1
    have h := (secondTwistLocalization_eq_span E).symm
    rw [Set.pair_comm] at h
    simpa [g, range_fin2_pair, secondTwistLocalizationY, secondTwistLocalizationX2] using h
  have hspanR : Submodule.span E.R (Set.range v) = ⊤ := by
    calc
      _ = (Submodule.span E.R (Set.range g)).map P.mkQ := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp [v, g]
      _ = ⊤ := by rw [hg, Submodule.map_top, Submodule.range_mkQ]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) :=
    (Submodule.span_eq_top_of_span_eq_top (R := E.R) (S := K) (Set.range v) hspanR).ge
  let B := Module.Basis.mk hli hspan
  rw [Module.finrank_eq_card_basis B]
  decide

private lemma localizedThirdTwist_eq_span (E : WeightedPolynomialSituation) :
    E.localizedTwist 3 =
      Submodule.span E.R {algebraMap E.S (Localization.Away E.z) E.z} := by
  change Stacks.ProjStandardOpenBaseChange.twistAway E.naturalGrading E.z 3 3 = _
  exact Stacks.ProjStandardOpenBaseChange.twistAway_self_eq_span E.naturalGrading E.z 3 (by
    change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (MvPolynomial.X 2) 3
    simpa [WeightedPolynomialSituation.naturalWeight] using
      (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 2))

private noncomputable def thirdTwistLinearEquiv (E : WeightedPolynomialSituation) :
    E.R ≃ₗ[E.R] E.localizedTwist 3 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton E.R _
    (⟨algebraMap E.S (Localization.Away E.z) E.z, by
      rw [localizedThirdTwist_eq_span]
      exact Submodule.subset_span (by simp)⟩ : E.localizedTwist 3))
    ⟨fun r s hrs => HomogeneousLocalization.val_injective (Submonoid.powers E.z)
      ((IsLocalization.Away.algebraMap_isUnit E.z).mul_right_cancel (congrArg Subtype.val hrs)),
    fun m => by
      have hm : (m : Localization (Submonoid.powers E.z)) ∈
          E.R ∙ algebraMap E.S (Localization.Away E.z) E.z := by
        simpa only [localizedThirdTwist_eq_span] using m.property
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
      exact ⟨r, Subtype.ext (by simpa using hr)⟩⟩

/-- The third twist has a one-dimensional fiber at the vertex ideal. -/
theorem finrank_thirdTwistLocalization_quotient_vertexIdeal
    (E : WeightedPolynomialSituation) :
    letI : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
    Module.finrank (E.R ⧸ E.vertexIdeal)
      (E.localizedTwist 3 ⧸
        (E.vertexIdeal • (⊤ : Submodule E.R (E.localizedTwist 3)))) = 1 := by
  let : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
  let K := E.R ⧸ E.vertexIdeal
  let : Field (E.R ⧸ E.vertexIdeal) := Ideal.Quotient.field E.vertexIdeal
  let e : E.localizedTwist 3 ≃ₗ[E.R] E.R := (thirdTwistLinearEquiv E).symm
  let q : TensorProduct E.R K (E.localizedTwist 3) ≃ₗ[K]
      E.localizedTwist 3 ⧸ (E.vertexIdeal • (⊤ : Submodule E.R (E.localizedTwist 3))) :=
    (TensorProduct.quotTensorEquivQuotSMul (E.localizedTwist 3)
      E.vertexIdeal).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let b : TensorProduct E.R K (E.localizedTwist 3) ≃ₗ[K] TensorProduct E.R K E.R :=
    LinearEquiv.baseChange E.R K _ _ e
  let r : TensorProduct E.R K E.R ≃ₗ[K] K :=
    (TensorProduct.rid E.R K).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  simpa only [Module.finrank_self] using (q.symm.trans (b.trans r)).finrank_eq

end Stacks.WeightedPolynomialSituation

end
