module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.AdjoinDegreeOneGraded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-one chart of `Sym_R(M ⊕ R)`

Let `M` be a module over a commutative ring `R`. The symmetric algebra `Sym_R(M ⊕ R)` is graded
by its symmetric powers, and the generator `T = ι (0, 1)` coming from the second summand is
homogeneous of degree one. This file computes the degree-zero part of the homogeneous
localization of `Sym_R(M ⊕ R)` at `T`:

`(Sym_R(M ⊕ R)_T)_0 ≅ Sym_R(M)`,

the generator `m` of `Sym_R(M)` corresponding to the fraction `ι (m, 0) / T`.

Under the identification `Sym_R(M ⊕ R) = Sym_R(M)[T]` of
`StacksFrontier.LinearAlgebra.SymmetricAlgebra.AdjoinDegreeOne` — graded by
`SymmetricAlgebra.map_symmetricPower_eq_polyDegreePart` — this is the statement that the standard
open `D₊(T)` of `Proj(Sym_R(M)[T])` is the affine space `Spec(Sym_R M)`, which is the inclusion
`j : C ⟶ E` of Stacks 0FEF read over an affine base.

The grading is the symmetric-power grading
`SymPow.symmetricPower n R (M × R) = (LinearMap.range (SymmetricAlgebra.ι R (M × R))) ^ n`, and
`M` is an arbitrary module: not finitely generated, not free, with no basis chosen. For `M` free,
`Sym_R(M ⊕ R)` is a polynomial algebra, and its chart at any variable is
`Stacks.SymmetricAway.chartAlgEquiv`.

## Main definitions

* `Stacks.SymAdjoinChart.adjoinedGen`: the degree-one generator `T = ι (0, 1)`.
* `Stacks.SymAdjoinChart.prodChartRing`: the chart `(Sym_R(M ⊕ R)_T)_0`, with the `R`-algebra
  structure it carries through the degree-zero part of the grading.
* `Stacks.SymAdjoinChart.mkChart`: the fraction `a / T ^ n` for `a` homogeneous of degree `n`.
* `Stacks.SymAdjoinChart.dehomogenize`: the `R`-algebra map `Sym_R(M ⊕ R) ⟶ Sym_R(M)` sending the
  generator at `(m, r)` to `ι m + r`, hence `T` to `1`.
* `Stacks.SymAdjoinChart.toChart`: the comparison map `Sym_R(M) ⟶ (Sym_R(M ⊕ R)_T)_0`.
* `Stacks.SymAdjoinChart.prodChartAlgEquiv`: **the identification
  `Sym_R(M) ≅ (Sym_R(M ⊕ R)_T)_0`.**

## Main results

* `Stacks.SymAdjoinChart.val_toChartFull_of_mem` and
  `Stacks.SymAdjoinChart.toChartFull_eq_mkChart`: the comparison map, extended to all of
  `Sym_R(M ⊕ R)`, sends a homogeneous element of degree `n` to the fraction `a / T ^ n`.
* `Stacks.SymAdjoinChart.toChart_surjective`: the fractions `ι (m, 0) / T` generate the chart.
* `Stacks.SymAdjoinChart.chartSpecialize_toChart`: they are algebraically independent.
* `Stacks.SymAdjoinChart.prodChartAlgEquiv_symm_comp_fromZeroRingHom`: the identification is
  compatible with the structure maps over `R`, the one of the chart taken through the degree-zero
  part of the grading.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/
@[expose] public noncomputable section

open HomogeneousLocalization SymmetricAlgebra

namespace Stacks.SymAdjoinChart

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree-one generator adjoined to `Sym_R(M)` by passing to `Sym_R(M ⊕ R)`. -/
def adjoinedGen : SymmetricAlgebra R (M × R) := SymmetricAlgebra.ι R (M × R) (0, 1)

/-- The adjoined generator is homogeneous of degree one. -/
theorem adjoinedGen_mem_one :
    adjoinedGen R M ∈ SymPow.symmetricPower 1 R (M × R) :=
  ι_mem_symmetricPower_one (0, 1)

/-- The degree-zero part of the localization of `Sym_R(M ⊕ R)` at the adjoined generator. -/
abbrev prodChartRing : Type (max u v) :=
  HomogeneousLocalization.Away (fun n : ℕ => SymPow.symmetricPower n R (M × R)) (adjoinedGen R M)

/-- The coefficient ring acts on the chart through the degree-zero part of the grading. -/
instance algebraProdChartRing : Algebra R (prodChartRing R M) :=
  ((algebraMap (SymPow.symmetricPower 0 R (M × R)) (prodChartRing R M)).comp
    (algebraMap R (SymPow.symmetricPower 0 R (M × R)))).toAlgebra

/-! ### Inverting the generator in the ordinary localization -/

/-- The inverse of the adjoined generator in the localization away from it. -/
def invGen : Localization.Away (adjoinedGen R M) :=
  Localization.mk 1 ⟨adjoinedGen R M, 1, pow_one _⟩

/-- The powers of the inverse of the adjoined generator. -/
theorem invGen_pow (n : ℕ) :
    invGen R M ^ n = Localization.mk 1
      (⟨adjoinedGen R M ^ n, n, rfl⟩ : Submonoid.powers (adjoinedGen R M)) := by
  rw [invGen, Localization.mk_pow, one_pow]
  congr 1

/-- The inverse of the adjoined generator is a right inverse of it. -/
theorem algebraMap_adjoinedGen_mul_invGen :
    algebraMap (SymmetricAlgebra R (M × R)) (Localization.Away (adjoinedGen R M))
        (adjoinedGen R M) * invGen R M = 1 := by
  rw [invGen, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨adjoinedGen R M, 1, pow_one _⟩ :
    Submonoid.powers (adjoinedGen R M))

/-- A fraction whose denominator is a power of the adjoined generator, rewritten using the
inverse of that generator. -/
theorem localization_mk_eq (a : SymmetricAlgebra R (M × R)) (n : ℕ) :
    Localization.mk a (⟨adjoinedGen R M ^ n, n, rfl⟩ :
        Submonoid.powers (adjoinedGen R M)) =
      algebraMap (SymmetricAlgebra R (M × R)) _ a * invGen R M ^ n := by
  rw [invGen_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]

/-! ### The fractions of the chart -/

/-- The fraction `a / T ^ n`, for `a` in the `n`-th symmetric power of `M ⊕ R`. -/
def mkChart (n : ℕ) (a : SymmetricAlgebra R (M × R))
    (ha : a ∈ SymPow.symmetricPower n R (M × R)) : prodChartRing R M :=
  Away.mk _ (adjoinedGen_mem_one R M) n a (by simpa using ha)

/-- **The fraction `a / T ^ n`, read in the ordinary localization.** -/
theorem val_mkChart (n : ℕ) (a : SymmetricAlgebra R (M × R))
    (ha : a ∈ SymPow.symmetricPower n R (M × R)) :
    (mkChart R M n a ha).val =
      algebraMap (SymmetricAlgebra R (M × R)) _ a * invGen R M ^ n := by
  change Localization.mk a (⟨adjoinedGen R M ^ n, n, rfl⟩ :
    Submonoid.powers (adjoinedGen R M)) = _
  rw [localization_mk_eq]

/-- A scalar of the chart, read in the ordinary localization. -/
theorem val_algebraMap_prodChartRing (r : R) :
    (algebraMap R (prodChartRing R M) r).val =
      algebraMap (SymmetricAlgebra R (M × R)) (Localization.Away (adjoinedGen R M))
        (algebraMap R (SymmetricAlgebra R (M × R)) r) := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

/-! ### Dehomogenization -/

/-- Dehomogenization: the `R`-algebra map `Sym_R(M ⊕ R) ⟶ Sym_R(M)` sending the generator at
`(m, r)` to `ι m + r`, so that the adjoined generator goes to `1`. -/
def dehomogenize : SymmetricAlgebra R (M × R) →ₐ[R] SymmetricAlgebra R M :=
  lift (LinearMap.coprod (ι R M) (LinearMap.toSpanSingleton R (SymmetricAlgebra R M) 1))

/-- Dehomogenization sends the generator at `(m, r)` to `ι m + r • 1`. -/
@[simp]
theorem dehomogenize_ι (m : M) (r : R) :
    dehomogenize R M (ι R (M × R) (m, r)) = ι R M m + r • 1 :=
  lift_ι_apply _ _

/-- Dehomogenization sends the adjoined generator to `1`. -/
@[simp]
theorem dehomogenize_adjoinedGen : dehomogenize R M (adjoinedGen R M) = 1 := by
  rw [adjoinedGen, dehomogenize_ι, map_zero, one_smul, zero_add]

/-! ### The comparison map -/

/-- The generator map of the chart: `(m, r) ↦ ι (m, r) / T`. -/
def genToChart : M × R →ₗ[R] prodChartRing R M where
  toFun mr := mkChart R M 1 (ι R (M × R) mr) (ι_mem_symmetricPower_one mr)
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, val_mkChart, val_mkChart, val_mkChart, map_add,
      map_add, add_mul]
  map_smul' r x := by
    apply HomogeneousLocalization.val_injective
    change (mkChart R M 1 (ι R (M × R) (r • x)) _).val =
      (algebraMap R (prodChartRing R M) r *
        mkChart R M 1 (ι R (M × R) x) (ι_mem_symmetricPower_one x)).val
    rw [HomogeneousLocalization.val_mul, val_mkChart, val_mkChart,
      val_algebraMap_prodChartRing, map_smul, Algebra.smul_def, map_mul, mul_assoc]

/-- The comparison map on all of `Sym_R(M ⊕ R)`: the generator at `(m, r)` goes to
`ι (m, r) / T`, so that the adjoined generator goes to `1`. -/
def toChartFull : SymmetricAlgebra R (M × R) →ₐ[R] prodChartRing R M :=
  lift (genToChart R M)

/-- The comparison map on `Sym_R(M ⊕ R)` sends the generator at `mr` to the fraction
`ι mr / T`. -/
@[simp]
theorem toChartFull_ι (mr : M × R) :
    toChartFull R M (ι R (M × R) mr) =
      mkChart R M 1 (ι R (M × R) mr) (ι_mem_symmetricPower_one mr) :=
  lift_ι_apply (genToChart R M) mr

/-- **The comparison map `Sym_R(M) ⟶ (Sym_R(M ⊕ R)_T)_0`**: the generator `m` goes to the
fraction `ι (m, 0) / T`. -/
def toChart : SymmetricAlgebra R M →ₐ[R] prodChartRing R M :=
  (toChartFull R M).comp (inlAlgHom R M)

/-- The comparison map sends the generator `m` to the fraction `ι (m, 0) / T`. -/
@[simp]
theorem toChart_ι (m : M) :
    toChart R M (ι R M m) =
      mkChart R M 1 (ι R (M × R) (m, 0)) (ι_mem_symmetricPower_one (m, 0)) := by
  rw [toChart, AlgHom.comp_apply, inlAlgHom_ι, toChartFull_ι]

/-- **The comparison map sends a homogeneous element of degree `n` to the fraction `a / T ^ n`**,
read in the ordinary localization. -/
theorem val_toChartFull_of_mem (n : ℕ) (a : SymmetricAlgebra R (M × R))
    (ha : a ∈ SymPow.symmetricPower n R (M × R)) :
    (toChartFull R M a).val =
      algebraMap (SymmetricAlgebra R (M × R)) _ a * invGen R M ^ n := by
  rw [SymPow.symmetricPower] at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [AlgHom.commutes, val_algebraMap_prodChartRing, pow_zero, mul_one]
  | add x y i hx hy ihx ihy =>
      rw [map_add, HomogeneousLocalization.val_add, ihx, ihy, map_add, add_mul]
  | mem_mul m hm i x hx ih =>
      obtain ⟨mr, rfl⟩ := hm
      rw [map_mul, HomogeneousLocalization.val_mul, ih, toChartFull_ι, val_mkChart, map_mul,
        Nat.succ_eq_add_one, pow_add]
      ring

/-- **The comparison map sends a homogeneous element of degree `n` to the fraction
`a / T ^ n`.** -/
theorem toChartFull_eq_mkChart (n : ℕ) (a : SymmetricAlgebra R (M × R))
    (ha : a ∈ SymPow.symmetricPower n R (M × R)) :
    toChartFull R M a = mkChart R M n a ha := by
  apply HomogeneousLocalization.val_injective
  rw [val_toChartFull_of_mem R M n a ha, val_mkChart]

/-- The comparison map factors through dehomogenization. -/
theorem toChart_dehomogenize (a : SymmetricAlgebra R (M × R)) :
    toChart R M (dehomogenize R M a) = toChartFull R M a := by
  have key : (toChart R M).comp (dehomogenize R M) = toChartFull R M := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun mr => ?_)
    obtain ⟨m, r⟩ := mr
    change toChart R M (dehomogenize R M (ι R (M × R) (m, r))) =
      toChartFull R M (ι R (M × R) (m, r))
    rw [dehomogenize_ι, Algebra.smul_def, mul_one, map_add, AlgHom.commutes, toChart_ι,
      toChartFull_ι]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, val_mkChart, val_mkChart,
      val_algebraMap_prodChartRing, ι_prod_eq R M m r, map_add, add_mul, Algebra.smul_def,
      map_mul, mul_assoc, ← adjoinedGen, pow_one, algebraMap_adjoinedGen_mul_invGen, mul_one]
  exact AlgHom.congr_fun key a

/-- **The chart is generated by the fractions `ι (m, 0) / T`.** -/
theorem toChart_surjective : Function.Surjective (toChart R M) := by
  intro z
  obtain ⟨n, a, ha, hz⟩ :=
    Away.mk_surjective (fun n : ℕ => SymPow.symmetricPower n R (M × R))
      (adjoinedGen_mem_one R M) z
  have ha' : a ∈ SymPow.symmetricPower n R (M × R) := by simpa using ha
  refine ⟨dehomogenize R M a, ?_⟩
  rw [toChart_dehomogenize, toChartFull_eq_mkChart R M n a ha']
  exact hz

/-! ### Dehomogenization inverts the comparison map -/

/-- The inverse of the comparison map: dehomogenization extended to the chart, which exists
because dehomogenization sends the adjoined generator to the unit `1`. -/
def chartSpecialize : prodChartRing R M →+* SymmetricAlgebra R M :=
  (Localization.awayLift (dehomogenize R M).toRingHom (adjoinedGen R M)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)).comp
    (algebraMap (prodChartRing R M) (Localization.Away (adjoinedGen R M)))

/-- The inverse of the comparison map sends the fraction `a / T ^ n` to the dehomogenization
of `a`. -/
theorem chartSpecialize_mkChart (n : ℕ) (a : SymmetricAlgebra R (M × R))
    (ha : a ∈ SymPow.symmetricPower n R (M × R)) :
    chartSpecialize R M (mkChart R M n a ha) = dehomogenize R M a := by
  rw [chartSpecialize, RingHom.comp_apply]
  change Localization.awayLift _ _ _ (Localization.mk a (⟨adjoinedGen R M ^ n, n, rfl⟩ :
    Submonoid.powers (adjoinedGen R M))) = _
  rw [Localization.awayLift_mk (dehomogenize R M).toRingHom (adjoinedGen R M) a 1 (by simp) n,
    one_pow, mul_one]
  rfl

/-- A scalar is homogeneous of degree zero. -/
theorem algebraMap_mem_symmetricPower_zero (r : R) :
    algebraMap R (SymmetricAlgebra R (M × R)) r ∈ SymPow.symmetricPower 0 R (M × R) := by
  rw [SymPow.symmetricPower, pow_zero]
  exact Submodule.algebraMap_mem r

/-- A scalar is the fraction `algebraMap r / T ^ 0`. -/
theorem algebraMap_eq_mkChart (r : R) :
    algebraMap R (prodChartRing R M) r =
      mkChart R M 0 (algebraMap R (SymmetricAlgebra R (M × R)) r)
        (algebraMap_mem_symmetricPower_zero R M r) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mkChart, pow_zero, mul_one, val_algebraMap_prodChartRing]

/-- **The fractions `ι (m, 0) / T` are algebraically independent.** -/
theorem chartSpecialize_toChart (q : SymmetricAlgebra R M) :
    chartSpecialize R M (toChart R M q) = q := by
  induction q using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes, algebraMap_eq_mkChart, chartSpecialize_mkChart, AlgHom.commutes]
  | ι m => rw [toChart_ι, chartSpecialize_mkChart, dehomogenize_ι, zero_smul, add_zero]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **The degree-one chart of `Sym_R(M ⊕ R)` is `Sym_R(M)`.** Localizing `Sym_R(M ⊕ R)`
homogeneously at the adjoined degree-one generator `T` and taking the degree-zero part returns
the symmetric algebra of `M`, the generator `m` corresponding to the fraction `ι (m, 0) / T`. -/
@[sga "6 IX 3.3" "special case"]
def prodChartAlgEquiv : SymmetricAlgebra R M ≃ₐ[R] prodChartRing R M :=
  AlgEquiv.ofBijective (toChart R M)
    ⟨fun a b h => by
        rw [← chartSpecialize_toChart R M a, ← chartSpecialize_toChart R M b, h],
      toChart_surjective R M⟩

/-- The chart identification is the comparison map `Stacks.SymAdjoinChart.toChart`. -/
@[simp]
theorem prodChartAlgEquiv_apply (q : SymmetricAlgebra R M) :
    prodChartAlgEquiv R M q = toChart R M q := rfl

/-- The inverse of the chart identification is `Stacks.SymAdjoinChart.chartSpecialize`. -/
@[simp]
theorem prodChartAlgEquiv_symm_apply (z : prodChartRing R M) :
    (prodChartAlgEquiv R M).symm z = chartSpecialize R M z := by
  refine (prodChartAlgEquiv R M).injective ?_
  rw [AlgEquiv.apply_symm_apply, prodChartAlgEquiv_apply]
  obtain ⟨q, rfl⟩ := toChart_surjective R M z
  rw [chartSpecialize_toChart]

/-- The inverse of the comparison map fixes the scalars of `R`. -/
theorem chartSpecialize_algebraMap (r : R) :
    chartSpecialize R M (algebraMap R (prodChartRing R M) r) =
      algebraMap R (SymmetricAlgebra R M) r := by
  rw [← prodChartAlgEquiv_symm_apply, AlgEquiv.commutes]

/-- The structure map of the chart over the coefficient ring factors through the degree-zero
part of the grading. -/
theorem algebraMap_prodChartRing_eq (r : R) :
    algebraMap R (prodChartRing R M) r =
      HomogeneousLocalization.fromZeroRingHom (fun n : ℕ => SymPow.symmetricPower n R (M × R)) _
        (algebraMap R (SymPow.symmetricPower 0 R (M × R)) r) := rfl

/-- The structure map of the chart over the coefficient ring, taken through the degree-zero
part of the grading and followed by the inverse of the chart identification, is the structure
map of `Sym_R(M)`. -/
theorem prodChartAlgEquiv_symm_comp_fromZeroRingHom :
    ((prodChartAlgEquiv R M).symm.toRingEquiv.toRingHom).comp
        ((HomogeneousLocalization.fromZeroRingHom
            (fun n : ℕ => SymPow.symmetricPower n R (M × R))
            (Submonoid.powers (adjoinedGen R M))).comp
          (algebraMap R (SymPow.symmetricPower 0 R (M × R)))) =
      algebraMap R (SymmetricAlgebra R M) :=
  RingHom.ext fun r => (prodChartAlgEquiv R M).symm.commutes r

end Stacks.SymAdjoinChart

end
