module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.PowerSeriesLocalizationNotFlat
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# A nonflat completed principal localization

There is a commutative ring `A`, complete for a principal ideal `(x)`, and an element `f` of
`A` such that the `(x)`-adic completion of `A_f` is not flat over `A`.

The example is `A = R⟦X⟧` with `R = k[y, z, a₀, a₁, …]/(y aᵢ, aᵢ aⱼ)`, `x = X` and `f = z`.

## Main results

* `Stacks.Examples.exists_nonflat_completed_localization`: there is a ring complete for a
  principal ideal whose completed principal localization is not flat over it.

## References

* [Stacks Project, Tag 0ALE](https://stacks.math.columbia.edu/tag/0ALE)
-/

@[expose] public section

namespace Stacks.Examples

private abbrev localizedPowerSeries (R : Type*) [CommRing R] (f : R) :=
  Localization.Away (PowerSeries.C f)

private abbrev localizedCoefficientRing (R : Type*) [CommRing R] (f : R) :=
  Localization.Away f

private noncomputable abbrev localizedPowerSeriesIdeal {R : Type*} [CommRing R] (f : R) :
    Ideal (localizedPowerSeries R f) :=
  (Ideal.span {PowerSeries.X} : Ideal (PowerSeries R)).map
    (algebraMap (PowerSeries R) (localizedPowerSeries R f))

private abbrev localizedPowerSeriesCompletion {R : Type*} [CommRing R] (f : R) :=
  AdicCompletion (localizedPowerSeriesIdeal f) (localizedPowerSeries R f)

private abbrev localizedPowerSeriesLevel {R : Type*} [CommRing R] (f : R) (n : ℕ) :=
  localizedPowerSeries R f ⧸ localizedPowerSeriesIdeal f ^ n

private abbrev coefficientPowerSeries {R : Type*} [CommRing R] (f : R) :=
  PowerSeries (localizedCoefficientRing R f)

private noncomputable abbrev coefficientPowerSeriesIdeal {R : Type*} [CommRing R] (f : R) :
    Ideal (coefficientPowerSeries f) := Ideal.span {PowerSeries.X}

private abbrev coefficientPowerSeriesLevel {R : Type*} [CommRing R] (f : R) (n : ℕ) :=
  coefficientPowerSeries f ⧸ coefficientPowerSeriesIdeal f ^ n

private noncomputable def coefficientMapToLevel {R : Type*} [CommRing R] (f : R)
    (n : ℕ) : localizedCoefficientRing R f →+* localizedPowerSeriesLevel f n := by
  let g : R →+* localizedPowerSeriesLevel f n :=
    (Ideal.Quotient.mk _).comp
      ((algebraMap (PowerSeries R) (localizedPowerSeries R f)).comp PowerSeries.C)
  have hg : IsUnit (g f) := by
    change IsUnit (Ideal.Quotient.mk _
      (algebraMap (PowerSeries R) (localizedPowerSeries R f) (PowerSeries.C f)))
    exact (IsLocalization.Away.algebraMap_isUnit (PowerSeries.C f)).map _
  exact IsLocalization.Away.lift f hg

private theorem coefficientMapToLevel_algebraMap {R : Type*} [CommRing R] (f : R) (n : ℕ)
    (r : R) :
    coefficientMapToLevel f n (algebraMap R (localizedCoefficientRing R f) r) =
      Ideal.Quotient.mk _
        (algebraMap (PowerSeries R) (localizedPowerSeries R f) (PowerSeries.C r)) := by
  simp [coefficientMapToLevel, IsLocalization.Away.lift_eq]

/-- A ring homomorphism out of `R⟦X⟧` is determined by its values on constants and `X`,
provided that `X ^ n` is sent to zero. -/
private theorem powerSeries_ringHom_ext_of_X_pow_eq_zero
    {R D : Type*} [CommRing R] [CommRing D] (n : ℕ) (f g : PowerSeries R →+* D)
    (hC : ∀ r, f (PowerSeries.C r) = g (PowerSeries.C r)) (hX : f PowerSeries.X = g PowerSeries.X)
    (hg : g PowerSeries.X ^ n = 0) : f = g := by
  have hpoly : f.comp Polynomial.coeToPowerSeries.ringHom =
      g.comp Polynomial.coeToPowerSeries.ringHom :=
    Polynomial.ringHom_ext (by simpa using hC) (by simpa using hX)
  ext p
  rw [PowerSeries.eq_X_pow_mul_shift_add_trunc n p]
  simp only [map_add, map_mul, map_pow, hX, hg, zero_mul, zero_add]
  exact DFunLike.congr_fun hpoly (PowerSeries.trunc n p)

/-- The image of an element of an ideal `I` in `R ⧸ I ^ n` has `n`-th power zero. -/
private theorem quotient_mk_pow_eq_zero {R : Type*} [CommRing R] {I : Ideal R} {y : R}
    (hy : y ∈ I) (n : ℕ) : Ideal.Quotient.mk (I ^ n) y ^ n = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hy n)

private theorem localizedPowerSeries_X_pow_eq_zero {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    Ideal.Quotient.mk (localizedPowerSeriesIdeal f ^ n)
      (algebraMap (PowerSeries R) (localizedPowerSeries R f) PowerSeries.X) ^ n = 0 :=
  quotient_mk_pow_eq_zero (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)) n

private noncomputable def powerSeriesMapToLevel {R : Type*} [CommRing R] (f : R)
    (n : ℕ) : PowerSeries (localizedCoefficientRing R f) →+*
      localizedPowerSeriesLevel f n := by
  letI : UniformSpace (localizedCoefficientRing R f) := ⊥
  letI : TopologicalSpace (localizedCoefficientRing R f) := ⊥
  letI : UniformSpace (localizedPowerSeriesLevel f n) := ⊥
  letI : TopologicalSpace (localizedPowerSeriesLevel f n) := ⊥
  letI : DiscreteTopology (localizedCoefficientRing R f) := ⟨rfl⟩
  letI : DiscreteTopology (localizedPowerSeriesLevel f n) := ⟨rfl⟩
  letI : DiscreteUniformity (localizedCoefficientRing R f) := ⟨rfl⟩
  letI : DiscreteUniformity (localizedPowerSeriesLevel f n) := ⟨rfl⟩
  letI : IsUniformAddGroup (localizedCoefficientRing R f) := inferInstance
  letI : IsUniformAddGroup (localizedPowerSeriesLevel f n) := inferInstance
  letI : IsTopologicalRing (localizedCoefficientRing R f) := inferInstance
  letI : IsTopologicalRing (localizedPowerSeriesLevel f n) := inferInstance
  letI : T2Space (localizedPowerSeriesLevel f n) := inferInstance
  letI : CompleteSpace (localizedPowerSeriesLevel f n) := inferInstance
  have hI : IsAdic (⊥ : Ideal (localizedPowerSeriesLevel f n)) :=
    is_bot_adic_iff.mpr inferInstance
  letI : IsLinearTopology (localizedPowerSeriesLevel f n) (localizedPowerSeriesLevel f n) :=
    hI ▸ (⊥ : Ideal (localizedPowerSeriesLevel f n)).isLinearTopology
  have hφ : Continuous (coefficientMapToLevel f n) := continuous_of_discreteTopology
  exact PowerSeries.eval₂Hom hφ
    (IsNilpotent.isTopologicallyNilpotent ⟨n, localizedPowerSeries_X_pow_eq_zero f n⟩)

private theorem powerSeriesMapToLevel_C_X {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    (∀ r, powerSeriesMapToLevel f n (PowerSeries.C r) = coefficientMapToLevel f n r) ∧
      powerSeriesMapToLevel f n PowerSeries.X =
        Ideal.Quotient.mk _ (algebraMap (PowerSeries R) (localizedPowerSeries R f) PowerSeries.X) :=
  ⟨fun r ↦ by simp [powerSeriesMapToLevel, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C],
    by simp [powerSeriesMapToLevel, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]⟩

private noncomputable def localizedPowerSeriesMapToCoefficientLevel
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    localizedPowerSeries R f →+* coefficientPowerSeriesLevel f n := by
  let p : PowerSeries R →+* coefficientPowerSeriesLevel f n :=
    (Ideal.Quotient.mk _).comp (PowerSeries.map (algebraMap R (localizedCoefficientRing R f)))
  have hp : IsUnit (p (PowerSeries.C f)) := by
    simp only [p, RingHom.comp_apply, PowerSeries.map_C]
    exact ((IsLocalization.Away.algebraMap_isUnit f).map PowerSeries.C).map _
  exact IsLocalization.Away.lift (PowerSeries.C f) hp

private theorem localizedPowerSeriesMapToCoefficientLevel_comp_algebraMap
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    (localizedPowerSeriesMapToCoefficientLevel f n).comp
        (algebraMap (PowerSeries R) (localizedPowerSeries R f)) =
      (Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n)).comp
        (PowerSeries.map (algebraMap R (localizedCoefficientRing R f))) :=
  RingHom.ext fun a ↦ by simp [localizedPowerSeriesMapToCoefficientLevel]

private theorem localizedPowerSeriesMapToCoefficientLevel_X
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    localizedPowerSeriesMapToCoefficientLevel f n
        (algebraMap (PowerSeries R) (localizedPowerSeries R f) PowerSeries.X) =
      Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n) PowerSeries.X := by
  simpa [PowerSeries.map_X] using
    DFunLike.congr_fun (localizedPowerSeriesMapToCoefficientLevel_comp_algebraMap f n)
      PowerSeries.X

private noncomputable def coefficientLevelMapFromLocalization
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    localizedPowerSeriesLevel f n →+* coefficientPowerSeriesLevel f n := by
  let g := localizedPowerSeriesMapToCoefficientLevel f n
  let xS : localizedPowerSeries R f :=
    algebraMap (PowerSeries R) (localizedPowerSeries R f) PowerSeries.X
  have hx : (g xS) ^ n = 0 := by
    rw [localizedPowerSeriesMapToCoefficientLevel_X]
    exact quotient_mk_pow_eq_zero (Ideal.mem_span_singleton_self _) n
  have hJ : localizedPowerSeriesIdeal f = Ideal.span {xS} := by
    rw [localizedPowerSeriesIdeal, Ideal.map_span]
    simp [xS]
  have hkill : Ideal.map g (localizedPowerSeriesIdeal f ^ n) ≤ ⊥ := by
    calc
      Ideal.map g (localizedPowerSeriesIdeal f ^ n) = Ideal.map g (Ideal.span {xS} ^ n) := by
        rw [hJ]
      _ = Ideal.span {g (xS ^ n)} := by
        rw [Ideal.span_singleton_pow xS, Ideal.map_span]
        simp only [Set.image_singleton]
      _ ≤ ⊥ := by
        apply Ideal.span_le.mpr
        simp [map_pow, hx]
  exact Ideal.Quotient.lift (localizedPowerSeriesIdeal f ^ n) g (by
    intro y hy
    have hgy : g y ∈ Ideal.map g (localizedPowerSeriesIdeal f ^ n) :=
      Ideal.mem_map_of_mem _ hy
    exact (Submodule.mem_bot _).mp (hkill hgy))

private theorem localizedPowerSeriesMapToCoefficientLevel_compat
    {R : Type*} [CommRing R] (f : R) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (coefficientPowerSeriesIdeal f) hmn).comp
        (localizedPowerSeriesMapToCoefficientLevel f n) =
      localizedPowerSeriesMapToCoefficientLevel f m := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.C f))
  ext a
  simp [localizedPowerSeriesMapToCoefficientLevel, IsLocalization.Away.lift_eq]

private theorem coefficientLevelMapFromLocalization_compat
    {R : Type*} [CommRing R] (f : R) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (coefficientPowerSeriesIdeal f) hmn).comp
      (coefficientLevelMapFromLocalization f n) =
      (coefficientLevelMapFromLocalization f m).comp
        (Ideal.Quotient.factorPow (localizedPowerSeriesIdeal f) hmn) := by
  apply Ideal.Quotient.ringHom_ext
  simpa only [RingHom.comp_assoc, coefficientLevelMapFromLocalization,
    Ideal.Quotient.lift_comp_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_comp_mk] using
      localizedPowerSeriesMapToCoefficientLevel_compat f hmn

private theorem coefficientMapToLevel_compat
    {R : Type*} [CommRing R] (f : R) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (localizedPowerSeriesIdeal f) hmn).comp
        (coefficientMapToLevel f n) = coefficientMapToLevel f m := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp only [RingHom.comp_apply, coefficientMapToLevel_algebraMap]
  exact Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right hmn) _

private theorem powerSeriesMapToLevel_compat
    {R : Type*} [CommRing R] (f : R) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (localizedPowerSeriesIdeal f) hmn).comp
        (powerSeriesMapToLevel f n) = powerSeriesMapToLevel f m := by
  obtain ⟨hC, hX⟩ := powerSeriesMapToLevel_C_X f n
  obtain ⟨hC', hX'⟩ := powerSeriesMapToLevel_C_X f m
  refine powerSeries_ringHom_ext_of_X_pow_eq_zero m _ _ (fun r ↦ ?_) ?_ ?_
  · rw [RingHom.comp_apply, hC, hC']
    exact DFunLike.congr_fun (coefficientMapToLevel_compat f hmn) r
  · rw [RingHom.comp_apply, hX, hX']
    exact Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right hmn) _
  · rw [hX']
    exact localizedPowerSeries_X_pow_eq_zero f m

private noncomputable def coefficientPowerSeriesToCompletion
    {R : Type*} [CommRing R] (f : R) :
    coefficientPowerSeries f →+* localizedPowerSeriesCompletion f :=
  AdicCompletion.liftRingHom (localizedPowerSeriesIdeal f)
    (powerSeriesMapToLevel f)
    (fun {_m _n} hmn ↦ powerSeriesMapToLevel_compat f hmn)

private noncomputable def completionLevelToCoefficientLevel
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    localizedPowerSeriesCompletion f →+* coefficientPowerSeriesLevel f n :=
  (coefficientLevelMapFromLocalization f n).comp
    (AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) n).toRingHom

private theorem completionLevelToCoefficientLevel_compat
    {R : Type*} [CommRing R] (f : R) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (coefficientPowerSeriesIdeal f) hmn).comp
      (completionLevelToCoefficientLevel f n) = completionLevelToCoefficientLevel f m := by
  ext c
  change (Ideal.Quotient.factorPow (coefficientPowerSeriesIdeal f) hmn)
      (coefficientLevelMapFromLocalization f n
        (AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) n c)) =
    coefficientLevelMapFromLocalization f m
      (AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) m c)
  rw [← AdicCompletion.factorPow_evalₐ (localizedPowerSeriesIdeal f) hmn c]
  exact DFunLike.congr_fun (coefficientLevelMapFromLocalization_compat f hmn)
    (AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) n c)

private noncomputable def completionToCoefficientPowerSeries
    {R : Type*} [CommRing R] (f : R) :
    localizedPowerSeriesCompletion f →+* coefficientPowerSeries f :=
  IsAdicComplete.liftRingHom (coefficientPowerSeriesIdeal f)
    (completionLevelToCoefficientLevel f)
    (fun {_m _n} hmn ↦ completionLevelToCoefficientLevel_compat f hmn)

private theorem powerSeriesMapToLevel_comp_coefficientMap
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    (powerSeriesMapToLevel f n).comp
        (PowerSeries.map (algebraMap R (localizedCoefficientRing R f))) =
      (Ideal.Quotient.mk (localizedPowerSeriesIdeal f ^ n)).comp
        (algebraMap (PowerSeries R) (localizedPowerSeries R f)) := by
  obtain ⟨hC, hX⟩ := powerSeriesMapToLevel_C_X f n
  refine powerSeries_ringHom_ext_of_X_pow_eq_zero n _ _ (fun r ↦ ?_) ?_
    (localizedPowerSeries_X_pow_eq_zero f n)
  · simp [hC, coefficientMapToLevel_algebraMap]
  · simp [hX]

private theorem coefficientPowerSeriesToCompletion_commutes
    {R : Type*} [CommRing R] (f : R) (a : PowerSeries R) :
    coefficientPowerSeriesToCompletion f
        (algebraMap (PowerSeries R) (coefficientPowerSeries f) a) =
      algebraMap (PowerSeries R) (localizedPowerSeriesCompletion f) a := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [coefficientPowerSeriesToCompletion, AdicCompletion.evalₐ_liftRingHom]
  rw [IsScalarTower.algebraMap_eq (PowerSeries R) (localizedPowerSeries R f)
    (localizedPowerSeriesCompletion f)]
  simp only [RingHom.comp_apply, AlgHom.commutes]
  exact DFunLike.congr_fun (powerSeriesMapToLevel_comp_coefficientMap f n) a

private theorem completionToCoefficientPowerSeries_projection
    {R : Type*} [CommRing R] (f : R) (n : ℕ)
    (c : localizedPowerSeriesCompletion f) :
    Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n)
        (completionToCoefficientPowerSeries f c) =
      completionLevelToCoefficientLevel f n c := by
  simp [completionToCoefficientPowerSeries, IsAdicComplete.liftRingHom,
    completionLevelToCoefficientLevel, AdicCompletion.mk_ofAlgEquiv_symm,
    AdicCompletion.evalₐ_liftRingHom]

private theorem completionToCoefficientPowerSeries_commutes
    {R : Type*} [CommRing R] (f : R) :
    (completionToCoefficientPowerSeries f).comp
        (algebraMap (PowerSeries R) (localizedPowerSeriesCompletion f)) =
      algebraMap (PowerSeries R) (coefficientPowerSeries f) := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (coefficientPowerSeriesIdeal f)
  intro n a
  change Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n)
      (completionToCoefficientPowerSeries f
        (algebraMap (PowerSeries R) (localizedPowerSeriesCompletion f) a)) =
    Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n)
      (algebraMap (PowerSeries R) (coefficientPowerSeries f) a)
  rw [completionToCoefficientPowerSeries_projection, completionLevelToCoefficientLevel,
    IsScalarTower.algebraMap_eq (PowerSeries R) (localizedPowerSeries R f)
      (localizedPowerSeriesCompletion f)]
  change coefficientLevelMapFromLocalization f n
      (AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) n
        ((algebraMap (localizedPowerSeries R f) (localizedPowerSeriesCompletion f))
          ((algebraMap (PowerSeries R) (localizedPowerSeries R f)) a))) = _
  rw [show AdicCompletion.evalₐ (localizedPowerSeriesIdeal f) n
        ((algebraMap (localizedPowerSeries R f) (localizedPowerSeriesCompletion f))
          ((algebraMap (PowerSeries R) (localizedPowerSeries R f)) a)) =
      Ideal.Quotient.mk (localizedPowerSeriesIdeal f ^ n)
        ((algebraMap (PowerSeries R) (localizedPowerSeries R f)) a) by simp]
  simp only [coefficientLevelMapFromLocalization, Ideal.Quotient.lift_mk]
  exact DFunLike.congr_fun (localizedPowerSeriesMapToCoefficientLevel_comp_algebraMap f n) a

private theorem completionToCoefficientPowerSeries_map_smul
    {R : Type*} [CommRing R] (f : R) (a : PowerSeries R)
    (b : localizedPowerSeriesCompletion f) :
    completionToCoefficientPowerSeries f (a • b) =
      algebraMap (PowerSeries R) (coefficientPowerSeries f) a *
        completionToCoefficientPowerSeries f b := by
  simpa only [Algebra.smul_def, map_mul, RingHom.comp_apply] using
    congrArg (· * completionToCoefficientPowerSeries f b)
      (DFunLike.congr_fun (completionToCoefficientPowerSeries_commutes f) a)

private theorem coefficientLevel_retraction
    {R : Type*} [CommRing R] (f : R) (n : ℕ) :
    (coefficientLevelMapFromLocalization f n).comp (powerSeriesMapToLevel f n) =
      Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n) := by
  have hcoeff : (coefficientLevelMapFromLocalization f n).comp (coefficientMapToLevel f n) =
      (Ideal.Quotient.mk _).comp PowerSeries.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    have h := DFunLike.congr_fun
      (localizedPowerSeriesMapToCoefficientLevel_comp_algebraMap f n) (PowerSeries.C r)
    rw [RingHom.comp_apply, RingHom.comp_apply, PowerSeries.map_C] at h
    rw [RingHom.comp_apply, RingHom.comp_apply, coefficientMapToLevel_algebraMap]
    exact h
  obtain ⟨hC, hX⟩ := powerSeriesMapToLevel_C_X f n
  refine powerSeries_ringHom_ext_of_X_pow_eq_zero n _ _ (fun r ↦ ?_) ?_
    (quotient_mk_pow_eq_zero (Ideal.mem_span_singleton_self _) n)
  · rw [RingHom.comp_apply, hC]
    exact DFunLike.congr_fun hcoeff r
  · rw [RingHom.comp_apply, hX]
    exact localizedPowerSeriesMapToCoefficientLevel_X f n

private theorem coefficientPowerSeries_retraction
    {R : Type*} [CommRing R] (f : R) :
    (completionToCoefficientPowerSeries f).comp
      (coefficientPowerSeriesToCompletion f) = RingHom.id _ := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (coefficientPowerSeriesIdeal f)
  intro n b
  change Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n)
      (completionToCoefficientPowerSeries f (coefficientPowerSeriesToCompletion f b)) =
    Ideal.Quotient.mk (coefficientPowerSeriesIdeal f ^ n) b
  rw [completionToCoefficientPowerSeries_projection]
  simpa [completionLevelToCoefficientLevel, coefficientPowerSeriesToCompletion,
    AdicCompletion.evalₐ_liftRingHom] using
    DFunLike.congr_fun (coefficientLevel_retraction f n) b

/-- There is a ring complete for a principal ideal whose completed principal
localization is not flat over the ring. -/
@[stacks 0ALE]
theorem exists_nonflat_completed_localization :
    ∃ (A : Type*) (_ : CommRing A) (x f : A),
      IsAdicComplete (Ideal.span {x}) A ∧
        ¬ Module.Flat A
          (AdicCompletion
            ((Ideal.span {x}).map (algebraMap A (Localization.Away f)))
            (Localization.Away f)) := by
  let k := ULift.{_} ℚ
  let : Field k := inferInstance
  refine ⟨PowerSeries (nonflatPowerSeriesRing k), inferInstance,
    PowerSeries.X, PowerSeries.C (nonflatPowerSeriesElement k), ?_, ?_⟩
  · infer_instance
  · intro hflat
    let A := PowerSeries (nonflatPowerSeriesRing k)
    let z := nonflatPowerSeriesElement k
    let B := coefficientPowerSeries z
    let E := localizedPowerSeriesCompletion z
    have : Module.Flat A E := hflat
    let i : B →ₗ[A] E := {
      toFun := coefficientPowerSeriesToCompletion z
      map_add' := map_add _
      map_smul' := by
        intro a b
        rw [Algebra.smul_def, map_mul, coefficientPowerSeriesToCompletion_commutes z a]
        simp only [RingHom.id_apply]
        change algebraMap A E a * (coefficientPowerSeriesToCompletion z b) =
          a • (coefficientPowerSeriesToCompletion z b)
        exact (Algebra.smul_def _ _).symm
    }
    let r : E →ₗ[A] B := {
      toFun := completionToCoefficientPowerSeries z
      map_add' := map_add _
      map_smul' := by
        intro a b
        rw [completionToCoefficientPowerSeries_map_smul]
        exact (Algebra.smul_def _ _).symm
    }
    have hri : r.comp i = LinearMap.id :=
      LinearMap.ext fun b ↦ DFunLike.congr_fun (coefficientPowerSeries_retraction z) b
    exact not_flat_powerSeries_map_localizationAway k (Module.Flat.of_retract i r hri)

end Stacks.Examples
