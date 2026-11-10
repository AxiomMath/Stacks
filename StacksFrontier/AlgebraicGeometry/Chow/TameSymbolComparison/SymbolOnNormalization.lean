module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.AlgebraSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.DeterminantNorm
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Normalization
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Invariance
public import Mathlib.RingTheory.Norm.Basic

/-!
# The tame symbol of Stacks 02Q1 read on the normalization

Let `A` be a Noetherian local domain of dimension one with fraction field `F` whose normalization
`A'` is a finite `A`-module. For nonzero `x, y ∈ A'` write `d^A_{A'}(x, y)` for the periodic
determinant over `A` of the two-periodic complex `(A'/xyA', x, y)`
(`Stacks.Chow.normalizationSymbol`, built on `Stacks.Chow.finiteAlgebraSymbol`). This file proves
that the tame symbol `d_A` of Stacks 02Q1 on `F^*`, restricted to the nonzero elements of `A'`, is
`d^A_{A'}` (`Stacks.Chow.tameSymbol_eq_normalizationSymbol`):

* for `a, b ∈ A` nonzero, `d_A(a, b) = d_{A'}(a, b)` by Stacks 02Q4, the inclusion `A → A'` having
  zero kernel and a cokernel of finite length, and `d_{A'}(a, b) = d^A_{A'}(a, b)`;
* both sides are bimultiplicative, and a nonzero element of `A'` becomes an element of `A` after
  multiplication by a nonzero element of `A`.

It also evaluates `d^A_{A'}` on the generators of the nonzero elements of `A'`: the units of `A'`
and the elements `t_𝔪` of `Stacks.Chow.normalizationUniformizer`. Two coprime elements give a
ratio of residue-field determinants of multiplications (Stacks 02PN), which are norms by
`Stacks.Chow.determinantAutomorphism_eq_norm` and `A'/t_𝔪A' ≅ κ(𝔪)`; and
`d^A_{A'}(t_𝔪, t_𝔪) = (-1)^{[κ(𝔪) : κ]}` (Stacks 02PM).

## Main results

* `Stacks.Chow.tameSymbol_eq_normalizationSymbol`.
* `Stacks.Chow.normalizationSymbol_unit_left`, `Stacks.Chow.normalizationSymbol_unit_uniformizer`,
  `Stacks.Chow.normalizationSymbol_uniformizer_of_ne`,
  `Stacks.Chow.normalizationSymbol_uniformizer_self`.

## References

* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 02Q4](https://stacks.math.columbia.edu/tag/02Q4)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing Stacks.Normalization AlgebraicGeometry
  Module.FiniteLength

universe u v

namespace Stacks.Chow

/-! ### The residue field acting on a quotient -/

section ResidueAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A] {S : Type v} [CommRing S] [Algebra A S]

/-- The residue field of `A` acts on `S / I` as soon as `I` contains the image of the maximal
ideal of `A`. -/
@[instance_reducible]
def quotientResidueAlgebra (I : Ideal S) (hI : ∀ a ∈ maximalIdeal A, algebraMap A S a ∈ I) :
    Algebra (ResidueField A) (S ⧸ I) :=
  (Ideal.Quotient.lift (maximalIdeal A) (algebraMap A (S ⧸ I)) fun a ha ↦ by
    rw [IsScalarTower.algebraMap_apply A S (S ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI a ha).toAlgebra

/-- Under `quotientResidueAlgebra`, the residue class of `a ∈ A` acts on `S / I` as the class of
`algebraMap A S a`. -/
theorem quotientResidueAlgebra_algebraMap_residue (I : Ideal S)
    (hI : ∀ a ∈ maximalIdeal A, algebraMap A S a ∈ I) (a : A) :
    letI := quotientResidueAlgebra I hI
    algebraMap (ResidueField A) (S ⧸ I) (residue A a) = Ideal.Quotient.mk I (algebraMap A S a) :=
  rfl

/-- The `A`-action on `S / I` factors through the residue field action `quotientResidueAlgebra`. -/
theorem isScalarTower_quotientResidueAlgebra (I : Ideal S)
    (hI : ∀ a ∈ maximalIdeal A, algebraMap A S a ∈ I) :
    letI := quotientResidueAlgebra I hI
    IsScalarTower A (ResidueField A) (S ⧸ I) :=
  let := quotientResidueAlgebra I hI
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **The residue-field determinant of a multiplication on `S / aS` is a norm.** -/
theorem determinantAutomorphism_singletonQuotientMulEquiv [Module.Finite A S] (a b : S)
    (h : IsCoprime a b) (hL : IsFiniteLength A (singletonQuotient S a))
    (hI : ∀ r ∈ maximalIdeal A, algebraMap A S r ∈ Ideal.span {a}) :
    letI := quotientResidueAlgebra (Ideal.span {a}) hI
    (determinantAutomorphism (singletonQuotientMulEquiv (R := A) a b h) hL : ResidueField A) =
      Algebra.norm (ResidueField A) (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  let := quotientResidueAlgebra (Ideal.span {a}) hI
  have := isScalarTower_quotientResidueAlgebra (Ideal.span {a}) hI
  have : Module.Finite A (S ⧸ Ideal.span {a}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (ResidueField A) (S ⧸ Ideal.span {a}) :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact determinantAutomorphism_eq_norm _ hL _ fun x ↦
    (singletonQuotientMulEquiv_apply a b h x).trans rfl

/-- On a zero quotient the residue-field determinant of a multiplication is `1`. -/
theorem determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit (a b : S)
    (h : IsCoprime a b) (hL : IsFiniteLength A (singletonQuotient S a)) (ha : IsUnit a) :
    determinantAutomorphism (singletonQuotientMulEquiv (R := A) a b h) hL = 1 := by
  have hI : ∀ r ∈ maximalIdeal A, algebraMap A S r ∈ Ideal.span {a} := fun r _ ↦ by
    rw [Ideal.span_singleton_eq_top.mpr ha]; trivial
  have : Subsingleton (S ⧸ Ideal.span {a}) :=
    Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr ha)
  let := quotientResidueAlgebra (Ideal.span {a}) hI
  have := isScalarTower_quotientResidueAlgebra (Ideal.span {a}) hI
  have : Module.Finite (ResidueField A) (S ⧸ Ideal.span {a}) :=
    ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  refine Units.ext ?_
  rw [determinantAutomorphism_eq_det _ hL LinearMap.id (fun _ ↦ Subsingleton.elim _ _),
    LinearMap.det_eq_one_of_subsingleton, Units.val_one]

end ResidueAlgebra

/-- For coprime regular `a, b` in a finite algebra of support dimension one, the symbol
`d^R_S(a, b)` is the ratio of the residue-field determinants of the multiplications by `b` on
`S/aS` and by `a` on `S/bS`. -/
private theorem finiteAlgebraSymbol_isFiniteLength_of_isCoprime {R : Type u} {S : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1) {a b : S} {ha : IsRegular a}
    {hb : IsRegular b} (h : IsCoprime a b) :
    finiteAlgebraSymbol a b ha hb (isFiniteLength_singletonQuotient hdim (a * b) (ha.mul hb)) =
      (determinantAutomorphism (singletonQuotientMulEquiv (R := R) a b h)
        (isFiniteLength_singletonQuotient hdim a ha))⁻¹ *
      determinantAutomorphism (singletonQuotientMulEquiv (R := R) b a h.symm)
        (isFiniteLength_singletonQuotient hdim b hb) :=
  finiteAlgebraSymbol_of_isCoprime _ _ ha hb h _ _ _


/-! ### The symbol `d^A_{A'}` on the normalization -/

section Normalization

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  {F : Type u} [Field F] [Algebra A F] [IsFractionRing A F]

omit [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] in
/-- The map from `A` to its normalization in `F` is injective. -/
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap A ↥(integralClosure A F)) :=
  fun _ _ h ↦ IsFractionRing.injective A F (congrArg Subtype.val h)

/-- A nonzero element of `A`, as a nonzero element of the normalization. -/
def toNormalizationNonZeroDivisors :
    nonZeroDivisors A →* nonZeroDivisors ↥(integralClosure A F) where
  toFun a := ⟨algebraMap A ↥(integralClosure A F) (a : A), mem_nonZeroDivisors_of_ne_zero fun h ↦
    nonZeroDivisors.ne_zero a.2 (algebraMap_integralClosure_injective (h.trans (map_zero _).symm))⟩
  map_one' := Subtype.ext (map_one (algebraMap A ↥(integralClosure A F)))
  map_mul' a b := Subtype.ext (map_mul (algebraMap A ↥(integralClosure A F)) (a : A) (b : A))

section FractionUnit

variable [Ring.DimensionLEOne A]

/-- The unit of `F` attached to a nonzero element of the normalization. -/
def normalizationFractionUnit : nonZeroDivisors ↥(integralClosure A F) →* Fˣ :=
  haveI := Stacks.Normalization.isFractionRing_integralClosure A F
  fractionUnitMap

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- The unit `normalizationFractionUnit x` of `F` is `x` itself, viewed in `F`. -/
theorem coe_normalizationFractionUnit (x : nonZeroDivisors ↥(integralClosure A F)) :
    (normalizationFractionUnit x : F) = ((x : ↥(integralClosure A F)) : F) :=
  have := Stacks.Normalization.isFractionRing_integralClosure A F
  fractionUnitMap_val x

omit [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- For a nonzero element `a` of `A`, `normalizationFractionUnit` recovers the unit of `F` given
by `a`. -/
theorem normalizationFractionUnit_toNormalizationNonZeroDivisors (a : nonZeroDivisors A) :
    normalizationFractionUnit (toNormalizationNonZeroDivisors (F := F) a) =
      (IsLocalization.map_units F (M := nonZeroDivisors A) a).unit :=
  Units.ext (coe_normalizationFractionUnit _)

end FractionUnit

variable [Module.Finite A ↥(integralClosure A F)]

omit [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] in
/-- The normalization has support dimension one over `A`: `A` acts faithfully on it. -/
theorem supportDim_integralClosure (hdim : ringKrullDim A = 1) :
    Module.supportDim A ↥(integralClosure A F) = 1 := by
  have he : Module.annihilator A ↥(integralClosure A F) = Module.annihilator A A := by
    ext a
    simp only [Module.mem_annihilator]
    refine ⟨fun h b ↦ ?_, fun h c ↦ ?_⟩
    · have h1 := h 1
      rw [Algebra.smul_def, mul_one] at h1
      rw [smul_eq_mul, algebraMap_integralClosure_injective (h1.trans (map_zero _).symm), zero_mul]
    · rw [show a = 0 by simpa using h 1, zero_smul]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, he,
    ← Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_self_eq_ringKrullDim, hdim]

/-- **The symbol `d^A_{A'}(x, y)`** of two nonzero elements of the normalization: the periodic
determinant over `A` of the two-periodic complex `(A'/xyA', x, y)`. -/
def normalizationSymbol (hdim : ringKrullDim A = 1)
    (x y : nonZeroDivisors ↥(integralClosure A F)) : (ResidueField A)ˣ :=
  finiteAlgebraSymbol (R := A) (S := ↥(integralClosure A F)) (x : ↥(integralClosure A F))
    (y : ↥(integralClosure A F))
    (isRegular_iff_mem_nonZeroDivisors.mpr x.2) (isRegular_iff_mem_nonZeroDivisors.mpr y.2)
    (isFiniteLength_singletonQuotient (R := A) (S := ↥(integralClosure A F))
      (supportDim_integralClosure (F := F) hdim) ((x : ↥(integralClosure A F)) * y)
      ((isRegular_iff_mem_nonZeroDivisors.mpr x.2).mul (isRegular_iff_mem_nonZeroDivisors.mpr y.2)))

omit [IsDomain A] in
/-- The symbol `d^A_{A'}` is multiplicative in its second argument. -/
theorem normalizationSymbol_mul_right (hdim : ringKrullDim A = 1)
    (x y z : nonZeroDivisors ↥(integralClosure A F)) :
    normalizationSymbol hdim x (y * z) =
      normalizationSymbol hdim x y * normalizationSymbol hdim x z :=
  finiteAlgebraSymbol_mul_right (R := A) (S := ↥(integralClosure A F)) (x : ↥(integralClosure A F))
    (y : ↥(integralClosure A F)) (z : ↥(integralClosure A F)) _ _ _ _ _ _

omit [IsDomain A] in
/-- The symbol `d^A_{A'}` is antisymmetric: `d^A_{A'}(x, y) d^A_{A'}(y, x) = 1`. -/
theorem normalizationSymbol_swap (hdim : ringKrullDim A = 1)
    (x y : nonZeroDivisors ↥(integralClosure A F)) :
    normalizationSymbol hdim x y * normalizationSymbol hdim y x = 1 :=
  finiteAlgebraSymbol_swap (R := A) (S := ↥(integralClosure A F))
    (supportDim_integralClosure (F := F) hdim) (x : ↥(integralClosure A F))
    (y : ↥(integralClosure A F)) _ _ _ _

omit [IsDomain A] in
/-- The symbol `d^A_{A'}` is multiplicative in its first argument. -/
theorem normalizationSymbol_mul_left (hdim : ringKrullDim A = 1)
    (x y z : nonZeroDivisors ↥(integralClosure A F)) :
    normalizationSymbol hdim (x * y) z =
      normalizationSymbol hdim x z * normalizationSymbol hdim y z := by
  rw [eq_inv_of_mul_eq_one_left (normalizationSymbol_swap hdim (x * y) z),
    normalizationSymbol_mul_right, eq_inv_of_mul_eq_one_left (normalizationSymbol_swap hdim x z),
    eq_inv_of_mul_eq_one_left (normalizationSymbol_swap hdim y z), mul_inv]

omit [IsNoetherianRing A] in
/-- Every nonzero element of the normalization becomes an element of `A` after multiplication by
a nonzero element of `A`. -/
theorem exists_toNormalizationNonZeroDivisors_eq_mul
    (x : nonZeroDivisors ↥(integralClosure A F)) :
    ∃ d a : nonZeroDivisors A, toNormalizationNonZeroDivisors a =
      toNormalizationNonZeroDivisors d * x := by
  obtain ⟨d, hd, hdB⟩ := exists_nonZeroDivisor_smul_mem_range A ↥(integralClosure A F) (K := F)
    Subtype.val_injective
  obtain ⟨a, ha⟩ := hdB (x : ↥(integralClosure A F))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    have h2 : algebraMap A ↥(integralClosure A F) d * (x : ↥(integralClosure A F)) = 0 := by
      rw [← Algebra.smul_def]; exact ha.symm
    exact nonZeroDivisors.ne_zero (toNormalizationNonZeroDivisors (F := F) ⟨d, hd⟩ * x).2 h2
  refine ⟨⟨d, hd⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, Subtype.ext ?_⟩
  change algebraMap A ↥(integralClosure A F) a =
    algebraMap A ↥(integralClosure A F) d * (x : ↥(integralClosure A F))
  rw [← Algebra.smul_def]
  exact ha

variable [Ring.DimensionLEOne A]

omit [Ring.DimensionLEOne A] in
/-- **On nonzero elements of `A`, the tame symbol of Stacks 02Q1 is `d^A_{A'}`.** By Stacks 02Q4
the symbol `d_A(a, b)` may be computed on the finite `A`-module `A'`, the inclusion `A → A'` being
injective with cokernel of finite length. -/
theorem tameSymbol_eq_normalizationSymbol_of_mem (hdim : ringKrullDim A = 1)
    (a b : nonZeroDivisors A) :
    tameSymbol (K := F) hdim (IsLocalization.map_units F (M := nonZeroDivisors A) a).unit
        (IsLocalization.map_units F (M := nonZeroDivisors A) b).unit =
      normalizationSymbol hdim (toNormalizationNonZeroDivisors (F := F) a)
        (toNormalizationNonZeroDivisors (F := F) b) := by
  have hdimB := supportDim_integralClosure (F := F) hdim
  have hreg : ∀ c : nonZeroDivisors A, IsRegular (algebraMap A ↥(integralClosure A F) c) :=
    fun c ↦ isRegular_iff_mem_nonZeroDivisors.mpr (toNormalizationNonZeroDivisors (F := F) c).2
  have hsm : ∀ c : nonZeroDivisors A, IsSMulRegular ↥(integralClosure A F) (c : A) :=
    fun c x y h ↦ (hreg c).left (by simpa only [Algebra.smul_def] using h)
  have h1 := (tameSymbol (K := F) hdim).eq_moduleSymbol a b
    (isRegular_iff_mem_nonZeroDivisors.mpr a.2) (isRegular_iff_mem_nonZeroDivisors.mpr b.2)
  refine h1.trans ?_
  have hker : Module.supportDim A (LinearMap.ker (Algebra.linearMap A ↥(integralClosure A F)))
      ≤ 0 := by
    rw [LinearMap.ker_eq_bot.mpr algebraMap_integralClosure_injective,
      Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  have hcoker : Module.supportDim A (↥(integralClosure A F) ⧸
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A F))) ≤ 0 := by
    obtain ⟨d, hd, hdB⟩ := exists_nonZeroDivisor_smul_mem_range A ↥(integralClosure A F) (K := F)
      Subtype.val_injective
    have hL := (Module.isFiniteLength_quotient_range_of_injective
      (LinearMap.lsmul A ↥(integralClosure A F) d) (hsm ⟨d, hd⟩) hdimB).of_surjective
      (f := Submodule.mapQ _ (LinearMap.range (Algebra.linearMap A ↥(integralClosure A F)))
        LinearMap.id (by rintro _ ⟨z, rfl⟩; exact hdB z))
      fun x ↦ Submodule.Quotient.induction_on _ x fun x ↦ ⟨Submodule.Quotient.mk x, rfl⟩
    nontriviality (↥(integralClosure A F) ⧸
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A F)))
    rw [Module.supportDim, support_of_isFiniteLength hL]
    exact Order.krullDim_nonpos_of_subsingleton
  rw [moduleSymbol_eq_of_ker_coker_supportDim_le_zero (Algebra.linearMap A ↥(integralClosure A F))
    a b _ _ (hsm a) (hsm b) _ hdimB hker hcoker,
    moduleSymbol_eq_finiteAlgebraSymbol hdimB a b (hsm a) (hsm b) (hreg a) (hreg b)]
  rfl

omit [Ring.DimensionLEOne A] in
/-- **The tame symbol of Stacks 02Q1, on the nonzero elements of the normalization, is
`d^A_{A'}`.** -/
theorem tameSymbol_eq_normalizationSymbol (hdim : ringKrullDim A = 1)
    (x y : nonZeroDivisors ↥(integralClosure A F)) :
    tameSymbol (K := F) hdim (normalizationFractionUnit x) (normalizationFractionUnit y) =
      normalizationSymbol hdim x y := by
  have hA : ∀ a b : nonZeroDivisors A,
      tameSymbol (K := F) hdim (normalizationFractionUnit (toNormalizationNonZeroDivisors a))
        (normalizationFractionUnit (toNormalizationNonZeroDivisors b)) =
      normalizationSymbol hdim (toNormalizationNonZeroDivisors a)
        (toNormalizationNonZeroDivisors b) := fun a b ↦ by
    rw [normalizationFractionUnit_toNormalizationNonZeroDivisors,
      normalizationFractionUnit_toNormalizationNonZeroDivisors]
    exact tameSymbol_eq_normalizationSymbol_of_mem hdim a b
  have hleft : ∀ (x : nonZeroDivisors ↥(integralClosure A F)) (b : nonZeroDivisors A),
      tameSymbol (K := F) hdim (normalizationFractionUnit x)
        (normalizationFractionUnit (toNormalizationNonZeroDivisors b)) =
      normalizationSymbol hdim x (toNormalizationNonZeroDivisors b) := fun x b ↦ by
    obtain ⟨d, a, hda⟩ := exists_toNormalizationNonZeroDivisors_eq_mul x
    have h := hA a b
    rw [hda, map_mul, (tameSymbol (K := F) hdim).map_mul_left, normalizationSymbol_mul_left,
      hA d b] at h
    exact mul_left_cancel h
  obtain ⟨e, b, heb⟩ := exists_toNormalizationNonZeroDivisors_eq_mul y
  have h := hleft x b
  rw [heb, map_mul, (tameSymbol (K := F) hdim).map_mul_right, normalizationSymbol_mul_right,
    hleft x e] at h
  exact mul_left_cancel h

end Normalization


/-! ### The values of `d^A_{A'}` on the generators -/

section Generators

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  {F : Type u} [Field F] [Algebra A F] [IsFractionRing A F] [Ring.DimensionLEOne A]
  (hA : maximalIdeal A ≠ ⊥)

/-- The maximal ideal of `A` lands in `(t_𝔪)`. -/
theorem algebraMap_mem_span_normalizationUniformizer
    (m : MaximalSpectrum ↥(integralClosure A F)) (r : A) (hr : r ∈ maximalIdeal A) :
    algebraMap A ↥(integralClosure A F) r ∈ Ideal.span {normalizationUniformizer A F hA m} := by
  rw [span_normalizationUniformizer]
  have := liesOver_maximalIdeal A F m.asIdeal
  have h := Ideal.LiesOver.over (p := maximalIdeal A) (P := m.asIdeal)
  rw [h] at hr
  exact hr

/-- `t_𝔪` as a nonzero element of the normalization. -/
def normalizationUniformizerNZD (m : MaximalSpectrum ↥(integralClosure A F)) :
    nonZeroDivisors ↥(integralClosure A F) :=
  ⟨normalizationUniformizer A F hA m, mem_nonZeroDivisors_of_ne_zero fun h ↦
    normalizationUniformizer_ne_zero A F hA m (by rw [h]; rfl)⟩

/-- **The norm from `A'/t_𝔪A'` is the norm from `κ(𝔪)`.** -/
theorem norm_quotient_normalizationUniformizer (m : MaximalSpectrum ↥(integralClosure A F))
    (x : ↥(integralClosure A F)) :
    letI := quotientResidueAlgebra (Ideal.span {normalizationUniformizer A F hA m})
      (algebraMap_mem_span_normalizationUniformizer hA m)
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    Algebra.norm (ResidueField A)
        (Ideal.Quotient.mk (Ideal.span {normalizationUniformizer A F hA m}) x) =
      Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime m.asIdeal) x)) := by
  let := quotientResidueAlgebra (Ideal.span {normalizationUniformizer A F hA m})
    (algebraMap_mem_span_normalizationUniformizer hA m)
  have := isLocalHom_algebraMap_localization A F m.asIdeal
  let e : (↥(integralClosure A F) ⧸ Ideal.span {normalizationUniformizer A F hA m})
      ≃ₐ[ResidueField A] ResidueField (Localization.AtPrime m.asIdeal) :=
    { normalizationQuotientEquiv A F hA m with
      commutes' := fun c ↦ by
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        change normalizationQuotientEquiv A F hA m (Ideal.Quotient.mk _ (algebraMap A _ a)) = _
        rw [normalizationQuotientEquiv_mk, IsLocalRing.ResidueField.algebraMap_residue,
          ← IsScalarTower.algebraMap_apply] }
  rw [← Algebra.norm_eq_of_algEquiv e]
  exact congrArg _ (normalizationQuotientEquiv_mk A F hA m x)

variable [Module.Finite A ↥(integralClosure A F)]

/-- **The residue-field determinant of a multiplication on `A'/t_𝔪A'` is a norm from `κ(𝔪)`.** -/
theorem determinantAutomorphism_normalizationUniformizer
    (m : MaximalSpectrum ↥(integralClosure A F)) (b : ↥(integralClosure A F))
    (h : IsCoprime (normalizationUniformizer A F hA m) b)
    (hL : IsFiniteLength A (singletonQuotient _ (normalizationUniformizer A F hA m))) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    (determinantAutomorphism (singletonQuotientMulEquiv (R := A) _ b h) hL : ResidueField A) =
      Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime m.asIdeal) b)) := by
  rw [determinantAutomorphism_singletonQuotientMulEquiv _ b h hL
    (algebraMap_mem_span_normalizationUniformizer hA m)]
  exact norm_quotient_normalizationUniformizer hA m b

omit [Module.Finite A ↥(integralClosure A F)] in
/-- The length of `A'/t_𝔪A'` over `A` is `[κ(𝔪) : κ]`. -/
theorem moduleLength_quotient_normalizationUniformizer
    (m : MaximalSpectrum ↥(integralClosure A F)) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    moduleLength A (singletonQuotient _ (normalizationUniformizer A F hA m)) =
      Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime m.asIdeal)) := by
  have := isLocalHom_algebraMap_localization A F m.asIdeal
  have := module_finite_residueField_localization A F m.asIdeal
  rw [← moduleLength_eq_finrank A]
  unfold moduleLength
  rw [(normalizationQuotientLinearEquiv A F hA m).length_eq]

/-- A unit is coprime to every element. -/
theorem isCoprime_of_isUnit_left {R : Type*} [CommSemiring R] {u : R} (hu : IsUnit u) (x : R) :
    IsCoprime u x :=
  ⟨↑hu.unit⁻¹, 0, by simp⟩

omit [IsDomain A] [Ring.DimensionLEOne A] in
/-- For a nonzero element `x` of the normalization, `A'/xA'` has finite length over `A`. -/
theorem finiteLength_singletonQuotient_normalization (hdim : ringKrullDim A = 1)
    (x : nonZeroDivisors ↥(integralClosure A F)) :
    IsFiniteLength A (singletonQuotient _ (x : ↥(integralClosure A F))) :=
  isFiniteLength_singletonQuotient (R := A) (S := ↥(integralClosure A F))
    (supportDim_integralClosure (F := F) hdim) (x : ↥(integralClosure A F))
    (isRegular_iff_mem_nonZeroDivisors.mpr x.2)

omit [IsDomain A] [Ring.DimensionLEOne A] in
/-- **`d^A_{A'}(u, y) = det_κ(u on A'/yA')` for a unit `u`.** -/
theorem normalizationSymbol_unit_left (hdim : ringKrullDim A = 1)
    (u y : nonZeroDivisors ↥(integralClosure A F)) (hu : IsUnit (u : ↥(integralClosure A F))) :
    normalizationSymbol hdim u y =
      determinantAutomorphism (singletonQuotientMulEquiv (R := A) (y : ↥(integralClosure A F)) u
        (isCoprime_comm.mp (isCoprime_of_isUnit_left hu _)))
        (finiteLength_singletonQuotient_normalization hdim y) := by
  rw [normalizationSymbol, finiteAlgebraSymbol_isFiniteLength_of_isCoprime (R := A)
      (supportDim_integralClosure (F := F) hdim)
      (isCoprime_of_isUnit_left hu _),
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hu, inv_one, one_mul]

/-- **`d^A_{A'}(t_𝔪, u) = N_{κ(𝔪)/κ}(ū)⁻¹` for a unit `u`.** -/
theorem normalizationSymbol_uniformizer_unit (hdim : ringKrullDim A = 1)
    (m : MaximalSpectrum ↥(integralClosure A F))
    (u : nonZeroDivisors ↥(integralClosure A F)) (hu : IsUnit (u : ↥(integralClosure A F))) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    (normalizationSymbol hdim (normalizationUniformizerNZD hA m) u : ResidueField A) =
      (Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime m.asIdeal)
          (u : ↥(integralClosure A F)))))⁻¹ := by
  have hc := (isCoprime_of_isUnit_left hu
    (normalizationUniformizerNZD hA m : ↥(integralClosure A F))).symm
  rw [normalizationSymbol, finiteAlgebraSymbol_isFiniteLength_of_isCoprime (R := A)
      (supportDim_integralClosure (F := F) hdim) hc,
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hu, mul_one,
    Units.val_inv_eq_inv_val]
  exact congrArg _ (determinantAutomorphism_normalizationUniformizer hA m _ hc _)

/-- **`d^A_{A'}(u, t_𝔪) = N_{κ(𝔪)/κ}(ū)` for a unit `u`.** -/
theorem normalizationSymbol_unit_uniformizer (hdim : ringKrullDim A = 1)
    (m : MaximalSpectrum ↥(integralClosure A F))
    (u : nonZeroDivisors ↥(integralClosure A F)) (hu : IsUnit (u : ↥(integralClosure A F))) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    (normalizationSymbol hdim u (normalizationUniformizerNZD hA m) : ResidueField A) =
      Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime m.asIdeal)
          (u : ↥(integralClosure A F)))) := by
  rw [normalizationSymbol_unit_left hdim u _ hu]
  exact determinantAutomorphism_normalizationUniformizer hA m _ _ _

omit [IsDomain A] [Ring.DimensionLEOne A] in
/-- **`d^A_{A'}(u, v) = 1` for units `u, v`.** -/
theorem normalizationSymbol_unit_unit (hdim : ringKrullDim A = 1)
    (u v : nonZeroDivisors ↥(integralClosure A F)) (hu : IsUnit (u : ↥(integralClosure A F)))
    (hv : IsUnit (v : ↥(integralClosure A F))) :
    normalizationSymbol hdim u v = 1 := by
  rw [normalizationSymbol_unit_left hdim u v hu,
    determinantAutomorphism_singletonQuotientMulEquiv_of_isUnit _ _ _ _ hv]

/-- **`d^A_{A'}(t_𝔪, t_𝔫) = N_{κ(𝔪)/κ}(t̄_𝔫)⁻¹ N_{κ(𝔫)/κ}(t̄_𝔪)` for `𝔪 ≠ 𝔫`.** -/
theorem normalizationSymbol_uniformizer_of_ne (hdim : ringKrullDim A = 1)
    {m n : MaximalSpectrum ↥(integralClosure A F)} (hmn : m ≠ n) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    haveI := isLocalHom_algebraMap_localization A F n.asIdeal
    (normalizationSymbol hdim (normalizationUniformizerNZD hA m)
        (normalizationUniformizerNZD hA n) : ResidueField A) =
      (Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime m.asIdeal)
          (normalizationUniformizer A F hA n))))⁻¹ *
      Algebra.norm (ResidueField A)
        (residue _ (algebraMap _ (Localization.AtPrime n.asIdeal)
          (normalizationUniformizer A F hA m))) := by
  have hc : IsCoprime ((normalizationUniformizerNZD hA m : nonZeroDivisors _) :
      ↥(integralClosure A F)) ((normalizationUniformizerNZD hA n : nonZeroDivisors _) :
      ↥(integralClosure A F)) := isCoprime_normalizationUniformizer A F hA hmn
  rw [normalizationSymbol, finiteAlgebraSymbol_isFiniteLength_of_isCoprime (R := A)
      (supportDim_integralClosure (F := F) hdim) hc,
    Units.val_mul, Units.val_inv_eq_inv_val]
  exact congrArg₂ (· * ·)
    (congrArg _ (determinantAutomorphism_normalizationUniformizer hA m _ hc _))
    (determinantAutomorphism_normalizationUniformizer hA n _ hc.symm _)

/-- **`d^A_{A'}(t_𝔪, t_𝔪) = (-1)^{[κ(𝔪) : κ]}`.** -/
theorem normalizationSymbol_uniformizer_self (hdim : ringKrullDim A = 1)
    (m : MaximalSpectrum ↥(integralClosure A F)) :
    haveI := isLocalHom_algebraMap_localization A F m.asIdeal
    normalizationSymbol hdim (normalizationUniformizerNZD hA m) (normalizationUniformizerNZD hA m) =
      (-1 : (ResidueField A)ˣ) ^
        Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime m.asIdeal)) := by
  rw [normalizationSymbol, finiteAlgebraSymbol_self]
  exact congrArg _ (moduleLength_quotient_normalizationUniformizer hA m)

end Generators

end Stacks.Chow

end
