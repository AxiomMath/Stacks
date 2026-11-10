module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChange
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra

/-!
# The standard affine chart of `Proj` commutes with base change

Let `A` be a graded `R`-algebra with grading `𝒜 : ℕ → Submodule R A`, let `S` be an `R`-algebra
and let `a : A` be homogeneous of degree `d`. The base change `S ⊗[R] A` is graded by
`Stacks.ProjBaseChange.grading`, the element `1 ⊗ₜ a` is homogeneous of the same degree, and the
standard affine chart of `Proj (S ⊗[R] A)` attached to `1 ⊗ₜ a` is the ring
`Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`.

This file proves that this chart is the base change of the chart of `Proj A` attached to `a`:
the canonical ring homomorphism `S ⊗[R] Away 𝒜 a ⟶ Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)` is an isomorphism.
Equivalently, the square of affine schemes

```
Spec (Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)) ⟶ Spec (Away 𝒜 a)
          |                              |
          v                              v
       Spec S                    ⟶     Spec R
```

is cartesian. This is the chart-level content of the base-change statement for `Proj`, which is
Stacks tag 01NO.

## Main definitions

* `Stacks.ProjBaseChange.awayBaseChange` is the comparison homomorphism
  `S ⊗[R] Away 𝒜 a →+* Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`.
* `Stacks.ProjBaseChange.awayBaseChangeEquiv` is the same map as a ring isomorphism.
* `Stacks.ProjBaseChange.divPow` is the fraction `y / aⁿ`.
* `Stacks.ProjBaseChange.mulPowNum` is multiplication of a numerator by `a ^ k`.

## Main results

* `Stacks.ProjBaseChange.awayBaseChange_bijective`: the comparison homomorphism is bijective.
* `Stacks.ProjBaseChange.isPushout_awayMap`: the square of rings is a pushout.
* `Stacks.ProjBaseChange.isPullback_Spec_awayMap`: the square of affine schemes is cartesian.

## Implementation notes

The `R`-algebra structure on `HomogeneousLocalization 𝒜 x` is installed so that its scalar
multiplication is the one Mathlib already has (which acts on numerators); only the `algebraMap`
field is new, so no scalar action is duplicated.

No `R`-algebra structure is installed on the base-changed chart: it carries an `S`-algebra
structure, and the `R`-algebra structure obtained from it along `R → S` is a `local instance`
used only to build `awayBaseChange` out of the universal property of the tensor product. No
statement of this file mentions it.

Both halves of the bijectivity come from one presentation. Every element of `S ⊗[R] Away 𝒜 a` is
of the form `tensorDivPow n u` for some `n` and some `u : S ⊗[R] 𝒜 (n • d)`, that is, can be
written over a single denominator `aⁿ` (`exists_tensorDivPow`); and `awayBaseChange` sends
`tensorDivPow n u` to the fraction whose numerator is the image of `u` in `S ⊗[R] A` and whose
denominator is `(1 ⊗ₜ a)ⁿ` (`awayBaseChange_tensorDivPow`). Surjectivity is then the surjectivity
of `Submodule.toBaseChange`, and injectivity is the fact that an annihilation by a power of
`1 ⊗ₜ a` in `S ⊗[R] A` can be read back inside the homogeneous parts, which is
`DirectSum.toBaseChange_injective`: the grading decomposes `A` into `R`-module summands, so no
flatness hypothesis on `S` is needed.

No `@[stacks]` attribute is attached. Tag 01NO is the cartesianness of the base-change square for
the whole of `Proj`, of which this is the statement on one standard affine chart.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct HomogeneousLocalization

universe u

namespace HomogeneousLocalization

section AlgebraBase

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] {𝒜 : ι → Submodule R A} [GradedRing 𝒜] {x : Submonoid A}

/-- The image of the base ring of a graded algebra lies in the degree-zero part. -/
theorem algebraMap_mem_graded_zero (r : R) : algebraMap R A r ∈ 𝒜 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (SetLike.one_mem_graded 𝒜)

/-- Acting by a scalar of the base ring on a homogeneous fraction is multiplication by the
degree-zero fraction `r / 1`. This is the compatibility that turns the scalar multiplication
Mathlib already has on `HomogeneousLocalization 𝒜 x` into an algebra structure. -/
theorem smul_eq_fromZeroRingHom_mul (r : R) (y : HomogeneousLocalization 𝒜 x) :
    r • y = fromZeroRingHom 𝒜 x (algebraMap R ↥(𝒜 0) r) * y :=
  Algebra.smul_def r y

/-- The structure map of `HomogeneousLocalization.instAlgebra`: a scalar `r` of the base ring
becomes the degree-zero fraction `r / 1`. -/
theorem algebraMap_base_apply (r : R) :
    algebraMap R (HomogeneousLocalization 𝒜 x) r =
      fromZeroRingHom 𝒜 x (algebraMap R ↥(𝒜 0) r) := rfl

/-- The scalar tower relating the base ring, the degree-zero part and the fractions. -/
instance : IsScalarTower R ↥(𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq fun _ ↦ rfl

end AlgebraBase

end HomogeneousLocalization

namespace Stacks.ProjBaseChange

/-! ### Vanishing of a fraction with a homogeneous denominator -/

section AwayMkZero

variable {ι B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [AddCommMonoid ι]
  [DecidableEq ι] (ℬ : ι → τ) [GradedRing ℬ] {f : B} {e : ι} (hf : f ∈ ℬ e)

/-- Two fractions with the same denominator and equal numerators are equal. The membership
proofs are not part of the data, so no hypothesis relating them is needed. -/
theorem awayMk_congr (n : ℕ) {w w' : B} (h : w = w') (hw : w ∈ ℬ (n • e))
    (hw' : w' ∈ ℬ (n • e)) : Away.mk ℬ hf n w hw = Away.mk ℬ hf n w' hw' := by
  subst h; rfl

/-- A fraction with denominator `fⁿ` vanishes exactly when some power of `f` annihilates its
numerator. -/
theorem awayMk_eq_zero_iff (n : ℕ) (w : B) (hw : w ∈ ℬ (n • e)) :
    Away.mk ℬ hf n w hw = 0 ↔ ∃ k : ℕ, f ^ k * w = 0 := by
  rw [← (HomogeneousLocalization.val_injective (𝒜 := ℬ) (x := Submonoid.powers f)).eq_iff,
    Away.val_mk, HomogeneousLocalization.val_zero, ← Localization.mk_zero 1,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨⟨c, k, rfl⟩, hc⟩
    exact ⟨k, by simpa using hc⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨f ^ k, k, rfl⟩, by simpa using hk⟩

end AwayMkZero

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]
  {d : ℕ} {a : A}

/-! ### The comparison homomorphism -/

section Comparison

/-- The `R`-algebra structure on the base-changed chart obtained from its `S`-algebra structure
along `R → S`. It is a `local instance`: it is needed only to build
`Stacks.ProjBaseChange.awayBaseChange` out of the universal property of the tensor product, and
no statement of this file mentions it. -/
@[instance_reducible]
def chartAlgebraBase : Algebra R (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) :=
  ((algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))).comp (algebraMap R S)).toAlgebra

attribute [local instance] chartAlgebraBase

/-- The structure map of the base-changed chart over `S`, read as a homomorphism of
`R`-algebras. The compatibility holds by the very definition of
`Stacks.ProjBaseChange.chartAlgebraBase`. -/
def toChartₐ : S →ₐ[R] Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) where
  __ := algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
  commutes' _ := rfl

/-- The chart-level base change map, as a homomorphism of `R`-algebras. The compatibility with
the two structure maps is the degree-zero part of `Stacks.ProjBaseChange.includeRight`. -/
def awayMapₐ : Away 𝒜 a →ₐ[R] Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) where
  __ := awayMap 𝒜 S a
  commutes' r := by
    refine (congrArg (fun g ↦ g (algebraMap R ↥(𝒜 0) r))
      (AlgebraicGeometry.Proj.awayMap_comp_fromZeroRingHom (includeRight 𝒜 S) a)).trans ?_
    refine congrArg (fromZeroRingHom (grading 𝒜 S) (Submonoid.powers ((1 : S) ⊗ₜ[R] a)))
      (Subtype.ext ?_)
    change (1 : S) ⊗ₜ[R] algebraMap R A r = algebraMap S (S ⊗[R] A) (algebraMap R S r)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      Algebra.algebraMap_eq_smul_one (R := R) (A := S), Algebra.algebraMap_eq_smul_one (R := R),
      TensorProduct.smul_tmul]

/-- The degree-zero scalar `s ⊗ₜ 1` of the base-changed grading is the image of `s` under the
structure map of the base-changed chart. -/
theorem algebraMap_eq_fromZeroRingHom_tmulOne (s : S) :
    algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) s =
      fromZeroRingHom (grading 𝒜 S) (Submonoid.powers ((1 : S) ⊗ₜ[R] a)) (tmulOne 𝒜 S s) := by
  rw [HomogeneousLocalization.algebraMap_base_apply]
  refine congrArg _ (Subtype.ext ?_)
  change algebraMap S (S ⊗[R] A) s = s ⊗ₜ[R] (1 : A)
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- The degree-zero scalar attached to `1` is `1`. -/
theorem tmulOne_one : tmulOne 𝒜 S 1 = 1 :=
  Subtype.ext (Algebra.TensorProduct.one_def (R := R) (A := S) (B := A)).symm

/-- **The comparison homomorphism of the chart-level base change.** It sends `s ⊗ₜ (y / aⁿ)` to
`(s ⊗ₜ y) / (1 ⊗ₜ a)ⁿ`. -/
def awayBaseChange : S ⊗[R] Away 𝒜 a →+* Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  (Algebra.TensorProduct.productMap (toChartₐ 𝒜 S) (awayMapₐ 𝒜 S)).toRingHom

/-- The comparison homomorphism on a pure tensor `s ⊗ₜ z`: the image of the degree-zero scalar
of `s`, times the image of `z` under `awayMap`. -/
theorem awayBaseChange_tmul (s : S) (z : Away 𝒜 a) :
    awayBaseChange 𝒜 S (s ⊗ₜ[R] z) =
      fromZeroRingHom (grading 𝒜 S) (Submonoid.powers ((1 : S) ⊗ₜ[R] a)) (tmulOne 𝒜 S s) *
        awayMap 𝒜 S a z := by
  rw [← algebraMap_eq_fromZeroRingHom_tmulOne]
  exact Algebra.TensorProduct.productMap_apply_tmul (toChartₐ 𝒜 S) (awayMapₐ 𝒜 S) s z

end Comparison

/-! ### Fractions with a single denominator -/

section Presentation

variable (ha : a ∈ 𝒜 d)

/-- The fraction `y / aⁿ`, as an `R`-linear map from the degree-`n • d` part of `𝒜` to the chart
`Away 𝒜 a`. -/
def divPow (n : ℕ) : ↥(𝒜 (n • d)) →ₗ[R] Away 𝒜 a where
  toFun y := Away.mk 𝒜 ha n y y.2
  map_add' y z := awayMk_add 𝒜 ha n y.2 z.2
  map_smul' r y := by
    refine Eq.trans ?_ (Algebra.smul_def r (Away.mk 𝒜 ha n (y : A) y.2)).symm
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.algebraMap_base_apply,
      show (fromZeroRingHom 𝒜 (Submonoid.powers a) (algebraMap R ↥(𝒜 0) r)).val =
        Localization.mk (algebraMap R A r) 1 from rfl,
      Away.val_mk, Away.val_mk, Localization.mk_mul, one_mul]
    congr 1
    change r • (y : A) = algebraMap R A r * (y : A)
    rw [Algebra.smul_def]

/-- `divPow 𝒜 ha n y` is the fraction `y / aⁿ`. -/
@[simp]
theorem divPow_apply (n : ℕ) (y : ↥(𝒜 (n • d))) :
    divPow 𝒜 ha n y = Away.mk 𝒜 ha n y y.2 := rfl

/-- Multiplication of a numerator by `a ^ k`, as an `R`-linear map from the degree-`n • d` part
of `𝒜` to the degree-`(n + k) • d` part. -/
def mulPowNum (k n : ℕ) : ↥(𝒜 (n • d)) →ₗ[R] ↥(𝒜 ((n + k) • d)) where
  toFun y := ⟨a ^ k * y, by
    rw [add_smul, add_comm]
    exact SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) y.2⟩
  map_add' y z := Subtype.ext (by simpa using mul_add (a ^ k) (y : A) (z : A))
  map_smul' r y := Subtype.ext (by simp)

/-- `mulPowNum 𝒜 ha k n y` is `a ^ k * y`. -/
@[simp]
theorem coe_mulPowNum (k n : ℕ) (y : ↥(𝒜 (n • d))) :
    (mulPowNum 𝒜 ha k n y : A) = a ^ k * y := rfl

/-- Multiplying numerator and denominator by `a ^ k` does not change the fraction. -/
theorem divPow_mulPowNum (k n : ℕ) (y : ↥(𝒜 (n • d))) :
    divPow 𝒜 ha (n + k) (mulPowNum 𝒜 ha k n y) = divPow 𝒜 ha n y := by
  apply HomogeneousLocalization.val_injective
  rw [divPow_apply, divPow_apply, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [coe_mulPowNum, OneMemClass.coe_one]; ring⟩

/-- Fractions with the single denominator `aⁿ`, inside the base change `S ⊗[R] Away 𝒜 a`. -/
def tensorDivPow (n : ℕ) : S ⊗[R] ↥(𝒜 (n • d)) →ₗ[R] S ⊗[R] Away 𝒜 a :=
  LinearMap.lTensor S (divPow 𝒜 ha n)

/-- `tensorDivPow 𝒜 S ha n` sends `s ⊗ₜ y` to `s ⊗ₜ (y / aⁿ)`. -/
@[simp]
theorem tensorDivPow_tmul (n : ℕ) (s : S) (y : ↥(𝒜 (n • d))) :
    tensorDivPow 𝒜 S ha n (s ⊗ₜ[R] y) = s ⊗ₜ[R] Away.mk 𝒜 ha n y y.2 := by
  rw [tensorDivPow, LinearMap.lTensor_tmul, divPow_apply]

/-- Raising the denominator by `a ^ k` does not change the element of the base change. -/
theorem tensorDivPow_lTensor_mulPowNum (k n : ℕ) (u : S ⊗[R] ↥(𝒜 (n • d))) :
    tensorDivPow 𝒜 S ha (n + k) (LinearMap.lTensor S (mulPowNum 𝒜 ha k n) u) =
      tensorDivPow 𝒜 S ha n u := by
  induction u with
  | tmul s y =>
      simp only [tensorDivPow, LinearMap.lTensor_tmul]
      rw [divPow_mulPowNum]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- An element written over `aⁿ` can be rewritten over `a ^ N` for any `N ≥ n`. -/
theorem exists_tensorDivPow_of_le {n N : ℕ} (h : n ≤ N) (u : S ⊗[R] ↥(𝒜 (n • d))) :
    ∃ w : S ⊗[R] ↥(𝒜 (N • d)), tensorDivPow 𝒜 S ha N w = tensorDivPow 𝒜 S ha n u := by
  induction N, h using Nat.le_induction with
  | base => exact ⟨u, rfl⟩
  | succ N _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨LinearMap.lTensor S (mulPowNum 𝒜 ha 1 N) w,
        (tensorDivPow_lTensor_mulPowNum 𝒜 S ha 1 N w).trans hw⟩

/-- **Every element of the base change of a chart can be written over a single denominator.** -/
theorem exists_tensorDivPow (z : S ⊗[R] Away 𝒜 a) :
    ∃ (n : ℕ) (u : S ⊗[R] ↥(𝒜 (n • d))), tensorDivPow 𝒜 S ha n u = z := by
  induction z with
  | tmul s z =>
      obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective 𝒜 ha z
      exact ⟨n, s ⊗ₜ[R] ⟨y, hy⟩, tensorDivPow_tmul 𝒜 S ha n s ⟨y, hy⟩⟩
  | add z z' hz hz' =>
      obtain ⟨n, u, rfl⟩ := hz
      obtain ⟨m, v, rfl⟩ := hz'
      obtain ⟨w, hw⟩ := exists_tensorDivPow_of_le 𝒜 S ha (le_max_left n m) u
      obtain ⟨w', hw'⟩ := exists_tensorDivPow_of_le 𝒜 S ha (le_max_right n m) v
      exact ⟨max n m, w + w', by rw [map_add, hw, hw']⟩

end Presentation

/-! ### The comparison homomorphism is an isomorphism -/

section Bijective

variable (ha : a ∈ 𝒜 d)

/-- The comparison homomorphism takes a fraction with denominator `aⁿ` to the fraction with the
same numerator, read in `S ⊗[R] A`, and denominator `(1 ⊗ₜ a)ⁿ`. -/
theorem awayBaseChange_tensorDivPow (n : ℕ) (u : S ⊗[R] ↥(𝒜 (n • d))) :
    awayBaseChange 𝒜 S (tensorDivPow 𝒜 S ha n u) =
      Away.mk (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        ((𝒜 (n • d)).toBaseChange S u : S ⊗[R] A) ((𝒜 (n • d)).toBaseChange S u).2 := by
  induction u with
  | tmul s y =>
      have hnum : (s ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] (y : A)) =
          ((𝒜 (n • d)).toBaseChange S (s ⊗ₜ[R] y) : S ⊗[R] A) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Submodule.coe_toBaseChange_tmul]
        simp
      rw [tensorDivPow_tmul, awayBaseChange_tmul, awayMap_mk 𝒜 S ha n (y : A) y.2]
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk,
        val_fromZeroRingHom, Localization.mk_mul, one_mul]
      exact congrArg (Localization.mk · _) hnum
  | add u v hu hv =>
      rw [map_add, map_add, hu, hv,
        ← awayMk_add (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
          ((𝒜 (n • d)).toBaseChange S u).2 ((𝒜 (n • d)).toBaseChange S v).2]
      exact awayMk_congr (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        (by rw [map_add, Submodule.coe_add]) _ _

/-- Pushing a homogeneous part into `S ⊗[R] A` turns multiplication by `a ^ k` into
multiplication by `(1 ⊗ₜ a) ^ k`. -/
theorem toBaseChange_lTensor_mulPowNum (k n : ℕ) (u : S ⊗[R] ↥(𝒜 (n • d))) :
    ((𝒜 ((n + k) • d)).toBaseChange S (LinearMap.lTensor S (mulPowNum 𝒜 ha k n) u) :
        S ⊗[R] A) =
      ((1 : S) ⊗ₜ[R] a) ^ k * ((𝒜 (n • d)).toBaseChange S u : S ⊗[R] A) := by
  induction u with
  | tmul s y => simp [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
  | add u v hu hv => simp only [map_add, Submodule.coe_add, hu, hv, mul_add]

/-- **The degreewise injectivity input.** If a power of `1 ⊗ₜ a` annihilates the image of `u` in
`S ⊗[R] A`, then the same power of `a` already annihilates `u` inside the homogeneous parts. The
grading decomposes `A` into `R`-module summands, so this needs no flatness. -/
theorem lTensor_mulPowNum_eq_zero (k n : ℕ) (u : S ⊗[R] ↥(𝒜 (n • d)))
    (h : ((1 : S) ⊗ₜ[R] a) ^ k * ((𝒜 (n • d)).toBaseChange S u : S ⊗[R] A) = 0) :
    LinearMap.lTensor S (mulPowNum 𝒜 ha k n) u = 0 := by
  refine DirectSum.toBaseChange_injective 𝒜 (S := S) ((n + k) • d) ?_
  rw [map_zero]
  exact Subtype.ext ((toBaseChange_lTensor_mulPowNum 𝒜 S ha k n u).trans h)

include ha in
/-- **The chart-level comparison homomorphism is bijective:** the standard affine chart of `Proj`
commutes with base change. -/
theorem awayBaseChange_bijective : Function.Bijective (awayBaseChange 𝒜 S (a := a)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, u, rfl⟩ := exists_tensorDivPow 𝒜 S ha z
    rw [awayBaseChange_tensorDivPow 𝒜 S ha n u] at hz
    obtain ⟨k, hk⟩ := (awayMk_eq_zero_iff (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n _ _).mp hz
    rw [← tensorDivPow_lTensor_mulPowNum 𝒜 S ha k n u,
      lTensor_mulPowNum_eq_zero 𝒜 S ha k n u hk, map_zero]
  · intro w
    obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) w
    obtain ⟨u, hu⟩ := (𝒜 (n • d)).toBaseChange_surjective S ⟨x, hx⟩
    refine ⟨tensorDivPow 𝒜 S ha n u, ?_⟩
    rw [awayBaseChange_tensorDivPow 𝒜 S ha n u]
    exact awayMk_congr (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n (congrArg Subtype.val hu) _ _

include ha in
/-- **The standard affine chart of `Proj` commutes with base change,** as a ring isomorphism. -/
def awayBaseChangeEquiv :
    S ⊗[R] Away 𝒜 a ≃+* Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  RingEquiv.ofBijective (awayBaseChange 𝒜 S) (awayBaseChange_bijective 𝒜 S ha)

/-- The ring isomorphism `awayBaseChangeEquiv` is the comparison homomorphism. -/
@[simp]
theorem awayBaseChangeEquiv_apply (z : S ⊗[R] Away 𝒜 a) :
    awayBaseChangeEquiv 𝒜 S ha z = awayBaseChange 𝒜 S z := rfl

end Bijective

/-! ### The base-change square of charts -/

section Square

variable (ha : a ∈ 𝒜 d)

include ha in
/-- **The base-change square of charts is a pushout of rings.** -/
theorem isPushout_awayMap :
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R (Away 𝒜 a)))
      (CommRingCat.ofHom (algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))))
      (CommRingCat.ofHom (awayMap 𝒜 S a)) := by
  refine (CommRingCat.isPushout_tensorProduct R S (Away 𝒜 a)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (awayBaseChangeEquiv 𝒜 S ha).toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_)
    change awayBaseChange 𝒜 S (s ⊗ₜ[R] 1) = _
    rw [awayBaseChange_tmul, map_one, mul_one]
    exact (algebraMap_eq_fromZeroRingHom_tmulOne 𝒜 S s).symm
  · rw [Iso.refl_hom, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_)
    change awayBaseChange 𝒜 S (1 ⊗ₜ[R] z) = _
    rw [awayBaseChange_tmul, tmulOne_one, map_one, one_mul]
    rfl

include ha in
/-- **The base-change square of charts is cartesian:** `Spec` of the base-changed chart is the
fibre product of `Spec` of the chart with `Spec S` over `Spec R`. -/
theorem isPullback_Spec_awayMap :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)))))
      (Spec.map (CommRingCat.ofHom (awayMap 𝒜 S a)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 a)))) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_awayMap 𝒜 S ha)

end Square

end Stacks.ProjBaseChange

end
