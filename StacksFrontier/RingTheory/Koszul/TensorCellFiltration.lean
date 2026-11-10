module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksFrontier.RingTheory.Koszul.BaseCellFiltration
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of a differential graded algebra with a Koszul algebra is orthogonal to the
acyclic modules

Let `R` be a commutative ring, let `A` be a differential graded `R`-algebra and let `K` be the
Koszul algebra of a functional `φ : Rʳ → R` — the exterior algebra `⋀[R] Rʳ` with contraction by
`φ` as its differential and with the `k`-th exterior power in cohomological degree `-k`. The
tensor product `A ⊗_R K` of Tag 065W, viewed as a right differential graded `A`-module by
restricting along `a ↦ a ⊗ 1`, is orthogonal on the left to the acyclic differential graded
`A`-modules.

The reason is the exterior grading of the second factor: the cells of `A ⊗_R K` over `A` are the
wedge monomials `1 ⊗ ξ_s` for `s ⊆ {1, …, r}`, the cell of exterior degree `m` sits in degree
`-m`, there are none above exterior degree `r`, and the tensor differential lowers the exterior
degree by one. That is a triangular cell decomposition in the sense of
`DifferentialGradedModule.GradedCellData`, and
`DifferentialGradedModule.leftOrthogonal_acyclic_of_cellCoords` turns it into orthogonality.

Taking `A` to be the Koszul algebra `K_n` of `f₁ⁿ, …, f_rⁿ` and `K` to be the Koszul algebra
`K_t` of `f₁ᵗ, …, f_rᵗ` gives `K_n ⊗_R K_t` over `K_n`. That is the left-orthogonality input of
Tag 0GZJ, where it is what makes the derived tensor product over the base ring computable by the
honest tensor product; the companion statement over `R` in degree zero is
`Koszul.leftOrthogonal_acyclic_powAlgebra_baseModule`.

## Main definitions

* `DifferentialGradedAlgebra.koszulSignPow`: multiplication by `(-1)^(m · p)` on the degree-`p`
  part of a differential graded algebra, the twist the cell coordinates have to carry.
* `Koszul.cellSplit`: a tensor product of the algebra with a direct sum of copies of the base
  ring, identified with the direct sum of copies of the algebra.
* `Koszul.koszulCellCoords`, `Koszul.koszulCellBlock` and `Koszul.koszulLower`: the cell
  coordinates of the Koszul algebra, grouped by exterior degree, and the matrix of its
  differential from one exterior degree to the next.
* `Koszul.tensorModule`: the tensor product `A ⊗_R K`, as a right differential graded
  `A`-module.
* `Koszul.tensorCellEquiv` and `Koszul.tensorCellCoords`: the cell coordinates of `A ⊗_R K`, on
  the tensor product of the carriers and on the differential graded module.
* `Koszul.gradedCellDataTensorModule`: the triangular cell decomposition of `A ⊗_R K` by
  exterior degree.

## Main results

* `Koszul.koszulCellBlock_d`: the Koszul differential strictly lowers the exterior degree, read
  in cell coordinates.
* `Koszul.tensorCellCoords_mulTensorOne`: the cell coordinates are compatible with the right
  action of `A`.
* `Koszul.tensorModule_mem_grading_iff`: an element of `A ⊗_R K` is homogeneous of degree `n`
  exactly when its coordinate on each cell of exterior degree `m` has degree `n + m`.
* `Koszul.leftOrthogonal_acyclic_tensorModule`: `A ⊗_R K` over `A` is orthogonal on the left to
  the acyclic modules.
* `Koszul.leftOrthogonal_acyclic_powAlgebra_tensorModule`: the same for `K_n ⊗_R K_t` over
  `K_n`.

## Implementation notes

*The coordinates carry a sign.* The `s`-th coordinate of `a ⊗ ξ_s` is not `a` but
`(-1)^(|s| · deg a) a`. Without that twist the coordinates are not compatible with the right
action: the action on the tensor product carries the Koszul sign `(-1)^((deg a - |s|) · deg b)`
while the action on a direct sum of shifts of the regular module carries `(-1)^(deg a · deg b)`,
and the two differ by exactly the twist. The twist is `DifferentialGradedAlgebra.koszulSignPow`,
an involution preserving each homogeneous piece, and it commutes with the differential up to the
sign `(-1)^(|s|)` that the shift of the cell already carries, so the triangularity of the
differential comes out with the sign
`DifferentialGradedModule.gradedCellDataOfCellCoords` asks for.

*Both triangularity properties come from one lemma.* `Koszul.koszulCellBlock_d` says that the
coordinates of exterior degree `m` of a contraction are obtained from the coordinates of
exterior degree `m + 1` of its argument; it is a restatement of
`Koszul.exteriorDecompose_contraction_of`, and it is transported to the tensor product by
`Koszul.cellBlockTensor_map_d`, which is where the second half of the tensor differential is
seen to drop a whole exterior degree.

*Two spellings of the Koszul algebra.* The carrier of the Koszul differential graded algebra is
the exterior algebra, but the two are not the same term, and a pure tensor whose second factor is
typed at the exterior algebra while the grading is typed at the differential graded algebra is
not type correct at the transparency `rw` uses. Everything below is therefore spelled at the
carrier of the differential graded algebra: `Koszul.koszulCellCoords` is
`Koszul.exteriorCellCoords` restated there, and the few facts proved about the exterior algebra
itself are bridged across by `exact`.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W), the tensor product of
  differential graded algebras.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P), the shape
  of the filtration this reproduces.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ), where `K_n ⊗_R K_t` over
  `K_n` is used.
-/

@[expose] public noncomputable section

open scoped DirectSum ExteriorAlgebra TensorProduct

universe u v w w'

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)

/-- The sign `(-1)^n`, cast to `ℤ`, at a natural number. -/
theorem negOnePow_natCast_val (m : ℕ) : (((m : ℤ)).negOnePow : ℤ) = (-1 : ℤ) ^ m := by
  simpa only [Int.cast_id, Int.natAbs_natCast] using Int.coe_negOnePow ℤ (m : ℤ)

/-- The signs `(-1)^(m·p)` are multiplicative in `p`. -/
theorem negOnePow_natMul_add (m : ℕ) (p q : ℤ) :
    (((m : ℤ) * (p + q)).negOnePow : ℤ)
      = (((m : ℤ) * q).negOnePow : ℤ) * (((m : ℤ) * p).negOnePow : ℤ) := by
  rw [mul_add, Int.negOnePow_add, Units.val_mul]
  ring

/-- The sign `(-1)^(m·p)` squares to one. -/
theorem negOnePow_natMul_self (m : ℕ) (p : ℤ) :
    (((m : ℤ) * p).negOnePow : ℤ) * (((m : ℤ) * p).negOnePow : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- **Multiplication by `(-1)^(m·p)` on the degree-`p` part of `A`.** This is the twist by the
parity of `m` that the cell coordinates of `A ⊗_R K` carry: it is
`DifferentialGradedAlgebra.koszulSign` iterated `m` times. -/
def koszulSignPow (m : ℕ) : A.A →ₗ[R] A.A :=
  (DirectSum.toModule R ℤ A.A fun p ↦
      ((((m : ℤ) * p).negOnePow : ℤ) • (A.grading p).subtype)) ∘ₗ
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

/-- On an element of degree `p`, the twist is multiplication by `(-1)^(m·p)`. -/
theorem koszulSignPow_apply_coe (m : ℕ) (p : ℤ) (a : A.grading p) :
    A.koszulSignPow m a = (((m : ℤ) * p).negOnePow : ℤ) • (a : A.A) := by
  simp [koszulSignPow, DirectSum.toModule_lof]

/-- On an element `a` of the degree-`p` piece, the twist is multiplication by `(-1)^(m·p)`. -/
theorem koszulSignPow_apply_of_mem (m : ℕ) {p : ℤ} {a : A.A} (ha : a ∈ A.grading p) :
    A.koszulSignPow m a = (((m : ℤ) * p).negOnePow : ℤ) • a :=
  A.koszulSignPow_apply_coe m p ⟨a, ha⟩

/-- The twist is an involution. -/
theorem koszulSignPow_koszulSignPow (m : ℕ) (a : A.A) :
    A.koszulSignPow m (A.koszulSignPow m a) = a := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | @homogeneous p x =>
      rw [A.koszulSignPow_apply_coe m p x, map_zsmul, A.koszulSignPow_apply_coe m p x, smul_smul,
        negOnePow_natMul_self, one_smul]

/-- The twist preserves each homogeneous piece. -/
theorem koszulSignPow_mem (m : ℕ) {p : ℤ} {a : A.A} (ha : a ∈ A.grading p) :
    A.koszulSignPow m a ∈ A.grading p := by
  rw [A.koszulSignPow_apply_of_mem m ha]
  exact zsmul_mem ha _

/-- The twist of `a` has degree `p` exactly when `a` has degree `p`. -/
theorem koszulSignPow_mem_iff (m : ℕ) (p : ℤ) (a : A.A) :
    A.koszulSignPow m a ∈ A.grading p ↔ a ∈ A.grading p := by
  refine ⟨fun h => ?_, fun h => A.koszulSignPow_mem m h⟩
  simpa only [A.koszulSignPow_koszulSignPow] using A.koszulSignPow_mem m h

/-- The twist of `a` vanishes exactly when `a` does. -/
theorem koszulSignPow_eq_zero_iff (m : ℕ) (a : A.A) : A.koszulSignPow m a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  simpa only [A.koszulSignPow_koszulSignPow, map_zero] using congrArg (A.koszulSignPow m) h

/-- The twist, as a linear automorphism of the algebra. -/
def koszulSignPowEquiv (m : ℕ) : A.A ≃ₗ[R] A.A :=
  LinearEquiv.ofLinearMap (A.koszulSignPow m) (A.koszulSignPow m)
    (LinearMap.ext fun a => A.koszulSignPow_koszulSignPow m a)
    (LinearMap.ext fun a => A.koszulSignPow_koszulSignPow m a)

/-- The linear automorphism `koszulSignPowEquiv` acts as `koszulSignPow`. -/
@[simp] theorem koszulSignPowEquiv_apply (m : ℕ) (a : A.A) :
    A.koszulSignPowEquiv m a = A.koszulSignPow m a := rfl

/-- Moving the twist past a right multiplication by a homogeneous element costs the sign of that
element's degree. -/
theorem koszulSignPow_mul_of_mem (m : ℕ) {q : ℤ} (z : A.A) {a : A.A} (ha : a ∈ A.grading q) :
    A.koszulSignPow m (z * a)
      = (((m : ℤ) * q).negOnePow : ℤ) • (A.koszulSignPow m z * a) := by
  induction z using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul, smul_add]
  | @homogeneous p x =>
      have hxa : (x : A.A) * a ∈ A.grading (p + q) := SetLike.mul_mem_graded x.property ha
      rw [A.koszulSignPow_apply_of_mem m hxa, A.koszulSignPow_apply_coe m p x, smul_mul_assoc,
        smul_smul, negOnePow_natMul_add]

/-- Moving the twist past the differential costs the sign `(-1)^m`. -/
theorem koszulSignPow_d (m : ℕ) (a : A.A) :
    A.koszulSignPow m (A.d a) = ((-1 : ℤ) ^ m) • A.d (A.koszulSignPow m a) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | @homogeneous p x =>
      have hdx : A.d (x : A.A) ∈ A.grading (p + 1) := A.d_mem p x x.property
      rw [A.koszulSignPow_apply_of_mem m hdx, A.koszulSignPow_apply_coe m p x, map_zsmul,
        smul_smul, negOnePow_natMul_add, mul_one, negOnePow_natCast_val]

end DifferentialGradedAlgebra

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-! ### Splitting off a direct sum from a tensor product -/

/-- **The components of `TensorProduct.directSumRight`**: the `j`-th one is the contraction of the
second factor against its `j`-th component. -/
theorem tensorDirectSumRight_apply {ι : Type v} [DecidableEq ι] (M : Type w) [AddCommMonoid M]
    [Module R M] (N : ι → Type w') [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (Y : M ⊗[R] (⨁ i, N i)) (j : ι) :
    (TensorProduct.directSumRight R R M N Y) j
      = TensorProduct.map LinearMap.id (DirectSum.component R ι N j) Y := by
  induction Y using TensorProduct.inductionOn with
  | tmul a y =>
      induction y using DirectSum.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, DirectSum.zero_apply, map_zero]
      | of i b =>
          rw [← DirectSum.lof_eq_of R, TensorProduct.directSumRight_tmul_lof,
            TensorProduct.map_tmul, LinearMap.id_apply, ← DirectSum.apply_eq_component,
            DirectSum.lof_eq_of, DirectSum.lof_eq_of]
          by_cases hij : j = i
          · subst hij
            rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
          · rw [DirectSum.of_eq_of_ne _ _ _ hij, DirectSum.of_eq_of_ne _ _ _ hij,
              TensorProduct.tmul_zero]
      | add y z hy hz =>
          rw [TensorProduct.tmul_add, map_add, DirectSum.add_apply, hy, hz, map_add]
  | add Y Z hY hZ => rw [map_add, DirectSum.add_apply, hY, hZ, map_add]

variable (A : DifferentialGradedAlgebra.{u, u} R)

/-- **A tensor product of the algebra with a direct sum of copies of the base ring**, identified
with the direct sum of copies of the algebra. -/
def cellSplit (ι : Type u) [DecidableEq ι] :
    (A.A ⊗[R] (⨁ (_ : ι), R)) ≃ₗ[R] (⨁ (_ : ι), A.A) :=
  (TensorProduct.directSumRight R R A.A (fun _ : ι => R)).trans
    (DirectSum.congrLinearEquiv fun _ => TensorProduct.rid R A.A)

/-- The `j`-th component of `cellSplit` is the contraction of the second factor against its `j`-th
component, followed by the identification `A ⊗_R R ≅ A`. -/
theorem cellSplit_apply {ι : Type u} [DecidableEq ι] (Z : A.A ⊗[R] (⨁ (_ : ι), R)) (j : ι) :
    (cellSplit A ι Z) j
      = TensorProduct.rid R A.A
          (TensorProduct.map LinearMap.id (DirectSum.component R ι (fun _ : ι => R) j) Z) := by
  rw [cellSplit, LinearEquiv.trans_apply]
  exact congrArg (TensorProduct.rid R A.A) (tensorDirectSumRight_apply A.A (fun _ : ι => R) Z j)

/-- The `j`-th component of `cellSplit` on a pure tensor `a ⊗ v` is `v j • a`. -/
theorem cellSplit_tmul {ι : Type u} [DecidableEq ι] (a : A.A) (v : ⨁ (_ : ι), R) (j : ι) :
    (cellSplit A ι (a ⊗ₜ[R] v)) j = (v j) • a := by
  rw [cellSplit_apply A (a ⊗ₜ[R] v) j, TensorProduct.map_tmul, LinearMap.id_apply,
    ← DirectSum.apply_eq_component, TensorProduct.rid_tmul]

/-- An element vanishes exactly when every component of its image under `cellSplit` does. -/
theorem cellSplit_eq_zero_iff {ι : Type u} [DecidableEq ι] (Z : A.A ⊗[R] (⨁ (_ : ι), R)) :
    (∀ j : ι, (cellSplit A ι Z) j = 0) ↔ Z = 0 := by
  refine ⟨fun h => (cellSplit A ι).map_eq_zero_iff.1 (DirectSum.ext fun j => ?_), fun h j => ?_⟩
  · rw [h j, DirectSum.zero_apply]
  · rw [h, map_zero, DirectSum.zero_apply]

/-! ### The cells of the Koszul algebra -/

variable {r : ℕ}

/-- The cell coordinates of a homogeneous element of the exterior algebra are concentrated in its
own exterior degree. -/
theorem exteriorCellCoords_coe {m : ℕ} (y : ↥(⋀[R]^m (Fin r → R))) :
    exteriorCellCoords R r (y : ExteriorAlgebra R (Fin r → R))
      = DirectSum.lof R ℕ (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), R) m
          (exteriorCellEquiv R r m y) := by
  refine DirectSum.ext fun m' => ?_
  rw [exteriorCellCoords_apply, exteriorDecompose_coe, DirectSum.lof_eq_of]
  by_cases hm : m' = m
  · subst hm
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ hm, DirectSum.of_eq_of_ne _ _ _ hm, map_zero]

variable (φ : Module.Dual R (Fin r → R))

/-- `𝒦` abbreviates the Koszul algebra of the functional `φ` in this section. -/
local notation "𝒦" => cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ

/-- **The cell coordinates of the Koszul algebra of `φ`**, spelled at the carrier of the
differential graded algebra rather than at the exterior algebra. The two carriers are the same
type, but only the former makes the pure tensors of `A ⊗_R K` below well typed without unfolding
the Koszul algebra. -/
def koszulCellCoords : (𝒦).A ≃ₗ[R] ⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), R :=
  exteriorCellCoords R r

/-- **The cell coordinates of exterior degree `m`** of an element of the Koszul algebra. -/
def koszulCellBlock (m : ℕ) :
    (𝒦).A →ₗ[R] (⨁ (_ : exteriorCellIndex.{u} r m), R) :=
  (DirectSum.component R ℕ (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), R) m) ∘ₗ
    (koszulCellCoords φ).toLinearMap

/-- The cell coordinates of exterior degree `m` are the `m`-th component of the cell
coordinates. -/
theorem koszulCellBlock_apply (m : ℕ) (b : (𝒦).A) :
    koszulCellBlock φ m b = (koszulCellCoords φ b) m := rfl

/-- The cell coordinates of exterior degree `m` of `b` vanish exactly when the component of `b` in
the `m`-th exterior power does. -/
theorem koszulCellBlock_eq_zero_iff (m : ℕ) (b : (𝒦).A) :
    koszulCellBlock φ m b = 0 ↔ exteriorDecompose R (Fin r → R) b m = 0 :=
  exteriorCellCoords_eq_zero_iff b m

/-- **An element of the Koszul algebra is homogeneous of degree `q` exactly when its cell
coordinates of exterior degree `m` vanish whenever `q + m ≠ 0`**: the cell of exterior degree `m`
sits in degree `-m`. -/
theorem mem_koszulGrading_iff (q : ℤ) (b : (𝒦).A) :
    b ∈ (𝒦).grading q ↔ ∀ m : ℕ, q + (m : ℤ) ≠ 0 → koszulCellBlock φ m b = 0 :=
  (mem_cohomologicalExteriorGrade_iff_exteriorDecompose q b).trans <|
    forall₂_congr fun m _ => (koszulCellBlock_eq_zero_iff φ m b).symm

/-- The cell coordinates of a homogeneous element of degree `q` vanish on every cell of exterior
degree `m` with `q + m ≠ 0`. -/
theorem koszulCellBlock_apply_eq_zero_of_mem {q : ℤ} {b : (𝒦).A} (hb : b ∈ (𝒦).grading q)
    {m : ℕ} (hqm : q + (m : ℤ) ≠ 0) (j : exteriorCellIndex.{u} r m) :
    (koszulCellBlock φ m b) j = 0 := by
  rw [(mem_koszulGrading_iff φ q b).1 hb m hqm, DirectSum.zero_apply]

/-- The element of the Koszul algebra with prescribed cell coordinates in one exterior degree and
none in the others. -/
def koszulBlockSection (m : ℕ) :
    (⨁ (_ : exteriorCellIndex.{u} r m), R) →ₗ[R] (𝒦).A :=
  (koszulCellCoords φ).symm.toLinearMap ∘ₗ
    (DirectSum.lof R ℕ (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), R) m)

/-- The cell coordinates of `koszulBlockSection φ m v` are `v` in exterior degree `m` and zero
elsewhere. -/
theorem koszulCellCoords_koszulBlockSection (m : ℕ)
    (v : ⨁ (_ : exteriorCellIndex.{u} r m), R) :
    koszulCellCoords φ (koszulBlockSection φ m v)
      = DirectSum.lof R ℕ (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), R) m v :=
  (koszulCellCoords φ).apply_symm_apply _

/-- The cell coordinates of exterior degree `m` of `koszulBlockSection φ m v` are `v`. -/
theorem koszulCellBlock_koszulBlockSection_self (m : ℕ)
    (v : ⨁ (_ : exteriorCellIndex.{u} r m), R) :
    koszulCellBlock φ m (koszulBlockSection φ m v) = v := by
  rw [koszulCellBlock_apply, koszulCellCoords_koszulBlockSection, DirectSum.lof_eq_of,
    DirectSum.of_eq_same]

/-- The cell coordinates of `koszulBlockSection φ m v` in an exterior degree `m' ≠ m` vanish. -/
theorem koszulCellBlock_koszulBlockSection_ne {m m' : ℕ} (h : m' ≠ m)
    (v : ⨁ (_ : exteriorCellIndex.{u} r m), R) :
    koszulCellBlock φ m' (koszulBlockSection φ m v) = 0 := by
  rw [koszulCellBlock_apply, koszulCellCoords_koszulBlockSection, DirectSum.lof_eq_of,
    DirectSum.of_eq_of_ne _ _ _ h]

/-- **The Koszul differential strictly lowers the exterior degree**, read in cell coordinates on
the exterior algebra. -/
@[ega "III 1.1.1" "i_f has degree −1"]
theorem exteriorCellCoords_contraction (m : ℕ) (b : ExteriorAlgebra R (Fin r → R)) :
    exteriorCellCoords R r (contraction φ b) m
      = exteriorCellCoords R r (contraction φ
          ((exteriorDecompose R (Fin r → R) b (m + 1) : ↥(⋀[R]^(m + 1) (Fin r → R))) :
            ExteriorAlgebra R (Fin r → R))) m := by
  have h := exteriorDecompose_contraction_of φ (exteriorDecompose R (Fin r → R) b) m
  rw [LinearEquiv.symm_apply_apply] at h
  rw [exteriorCellCoords_apply, exteriorCellCoords_apply, h]

/-- **The Koszul differential strictly lowers the exterior degree**, read in cell coordinates: the
coordinates of exterior degree `m` of `d b` depend only on the coordinates of exterior degree
`m + 1` of `b`. -/
theorem koszulCellBlock_d (m : ℕ) (b : (𝒦).A) :
    koszulCellBlock φ m ((𝒦).d b)
      = koszulCellBlock φ m
          ((𝒦).d (koszulBlockSection φ (m + 1) (koszulCellBlock φ (m + 1) b))) := by
  have hb : koszulCellBlock φ (m + 1) b
      = exteriorCellEquiv R r (m + 1) (exteriorDecompose R (Fin r → R) b (m + 1)) :=
    exteriorCellCoords_apply b (m + 1)
  have hsec : koszulBlockSection φ (m + 1) (koszulCellBlock φ (m + 1) b)
      = ((exteriorDecompose R (Fin r → R) b (m + 1) : ↥(⋀[R]^(m + 1) (Fin r → R))) :
          ExteriorAlgebra R (Fin r → R)) := by
    refine (koszulCellCoords φ).injective ?_
    rw [koszulCellCoords_koszulBlockSection, hb]
    exact (exteriorCellCoords_coe (exteriorDecompose R (Fin r → R) b (m + 1))).symm
  exact (exteriorCellCoords_contraction φ m b).trans
    (congrArg (fun y : (𝒦).A => koszulCellBlock φ m ((𝒦).d y)) hsec.symm)

/-- **The matrix of the Koszul differential from exterior degree `m + 1` to exterior degree
`m`.** -/
def koszulLower (m : ℕ) :
    (⨁ (_ : exteriorCellIndex.{u} r (m + 1)), R) →ₗ[R]
      (⨁ (_ : exteriorCellIndex.{u} r m), R) :=
  (koszulCellBlock φ m) ∘ₗ (𝒦).d ∘ₗ (koszulBlockSection φ (m + 1))

/-- The cell coordinates of exterior degree `m` of `d b` are the image under `koszulLower φ m` of
the cell coordinates of exterior degree `m + 1` of `b`. -/
theorem koszulCellBlock_d_eq_koszulLower (m : ℕ) (b : (𝒦).A) :
    koszulCellBlock φ m ((𝒦).d b) = koszulLower φ m (koszulCellBlock φ (m + 1) b) :=
  koszulCellBlock_d φ m b

/-- **A wedge monomial** of the Koszul algebra: the element whose cell coordinate at the cell `j`
of exterior degree `m` is one and whose other cell coordinates vanish. -/
def koszulMonomial (m : ℕ) (j : exteriorCellIndex.{u} r m) : (𝒦).A :=
  koszulBlockSection φ m (DirectSum.of (fun _ : exteriorCellIndex.{u} r m => R) j 1)

/-- The cell coordinates of exterior degree `m` of the wedge monomial at `j` are the basis vector
at `j`. -/
theorem koszulCellBlock_koszulMonomial_self (m : ℕ) (j : exteriorCellIndex.{u} r m) :
    koszulCellBlock φ m (koszulMonomial φ m j)
      = DirectSum.of (fun _ : exteriorCellIndex.{u} r m => R) j 1 :=
  koszulCellBlock_koszulBlockSection_self φ m _

/-- A wedge monomial of exterior degree `m` has no cell coordinates in exterior degree `m' ≠ m`. -/
theorem koszulCellBlock_koszulMonomial_ne {m m' : ℕ} (h : m' ≠ m)
    (j : exteriorCellIndex.{u} r m) :
    koszulCellBlock φ m' (koszulMonomial φ m j) = 0 :=
  koszulCellBlock_koszulBlockSection_ne φ h _

/-- A wedge monomial of exterior degree `m` is homogeneous of degree `-m`. -/
theorem koszulMonomial_mem (m : ℕ) (j : exteriorCellIndex.{u} r m) :
    koszulMonomial φ m j ∈ (𝒦).grading (-(m : ℤ)) := by
  rw [mem_koszulGrading_iff]
  intro m' hm'
  exact koszulCellBlock_koszulMonomial_ne φ (by omega) j

/-! ### The cell coordinates of `A ⊗_R K` -/

/-- The twist by the parity of the exterior degree, on the cells of a single exterior degree. -/
def cellTwistBlock (ι : Type u) (m : ℕ) : (⨁ (_ : ι), A.A) ≃ₗ[R] (⨁ (_ : ι), A.A) :=
  DirectSum.congrLinearEquiv fun _ => A.koszulSignPowEquiv m

/-- `cellTwistBlock` applies the twist `koszulSignPow m` to each component. -/
theorem cellTwistBlock_apply {ι : Type u} (m : ℕ) (y : ⨁ (_ : ι), A.A) (j : ι) :
    (cellTwistBlock A ι m y) j = A.koszulSignPow m (y j) := rfl

/-- The tensor product of the algebra with the cell coordinates of the Koszul algebra,
regrouped by exterior degree. -/
def cellBlocks (s : ℕ) :
    (A.A ⊗[R] (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} s m), R)) ≃ₗ[R]
      (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} s m), A.A) :=
  (TensorProduct.directSumRight R R A.A
      (fun m : ℕ => ⨁ (_ : exteriorCellIndex.{u} s m), R)).trans
    (DirectSum.congrLinearEquiv fun m => cellSplit A (exteriorCellIndex.{u} s m))

/-- The block of exterior degree `m` of the second tensor factor. -/
def cellBlockTensor (m : ℕ) :
    (A.A ⊗[R] (𝒦).A) →ₗ[R] (A.A ⊗[R] (⨁ (_ : exteriorCellIndex.{u} r m), R)) :=
  TensorProduct.map LinearMap.id (koszulCellBlock φ m)

/-- **The cell coordinates of exterior degree `m` of `A ⊗_R K`**, as a linear map: the coordinate
of a pure tensor `a ⊗ ξ_s` on the cell `s` is `(-1)^(m · deg a) a`. -/
def cellCoordsBlock (m : ℕ) :
    (A.A ⊗[R] (𝒦).A) →ₗ[R] (⨁ (_ : exteriorCellIndex.{u} r m), A.A) :=
  (cellTwistBlock A (exteriorCellIndex.{u} r m) m).toLinearMap ∘ₗ
    (cellSplit A (exteriorCellIndex.{u} r m)).toLinearMap ∘ₗ cellBlockTensor A φ m

/-- **The cell coordinates of `A ⊗_R K`**, on the plain tensor product of the carriers. -/
def tensorCellEquiv :
    (A.A ⊗[R] (𝒦).A) ≃ₗ[R] (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), A.A) :=
  ((TensorProduct.congr (LinearEquiv.refl R A.A) (koszulCellCoords φ)).trans
      (cellBlocks A r)).trans
    (DirectSum.congrLinearEquiv fun m => cellTwistBlock A (exteriorCellIndex.{u} r m) m)

/-- The component of exterior degree `m` of `tensorCellEquiv` is `cellCoordsBlock A φ m`. -/
theorem tensorCellEquiv_apply (X : A.A ⊗[R] (𝒦).A) (m : ℕ) :
    (tensorCellEquiv A φ X) m = cellCoordsBlock A φ m X := by
  have h1 : (TensorProduct.congr (LinearEquiv.refl R A.A) (koszulCellCoords φ)) X
      = TensorProduct.map LinearMap.id (koszulCellCoords φ).toLinearMap X := rfl
  have h2 : TensorProduct.map LinearMap.id
        (DirectSum.component R ℕ (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), R) m)
        (TensorProduct.map LinearMap.id (koszulCellCoords φ).toLinearMap X)
      = cellBlockTensor A φ m X := by
    rw [cellBlockTensor, koszulCellBlock, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp]
  change cellTwistBlock A _ m ((cellBlocks A r
      ((TensorProduct.congr (LinearEquiv.refl R A.A) (koszulCellCoords φ)) X)) m) = _
  rw [h1]
  change cellTwistBlock A _ m (cellSplit A _
      ((TensorProduct.directSumRight R R A.A
          (fun m : ℕ => ⨁ (_ : exteriorCellIndex.{u} r m), R)
        (TensorProduct.map LinearMap.id (koszulCellCoords φ).toLinearMap X)) m)) = _
  rw [tensorDirectSumRight_apply, h2]
  rfl

/-- The coordinate of `a ⊗ b` on the cell `j` of exterior degree `m` is the twist by `m` of
`b_j • a`, where `b_j` is the coordinate of `b` on that cell. -/
theorem cellCoordsBlock_tmul (m : ℕ) (a : A.A) (b : (𝒦).A)
    (j : exteriorCellIndex.{u} r m) :
    (cellCoordsBlock A φ m (a ⊗ₜ[R] b)) j
      = A.koszulSignPow m (((koszulCellBlock φ m b) j) • a) := by
  rw [cellCoordsBlock]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [cellBlockTensor, TensorProduct.map_tmul, LinearMap.id_apply, cellTwistBlock_apply,
    cellSplit_tmul]

/-- The cell coordinates of exterior degree `m` of `X` vanish exactly when the block of exterior
degree `m` of its second factor does. -/
theorem cellCoordsBlock_eq_zero_iff (m : ℕ) (X : A.A ⊗[R] (𝒦).A) :
    cellCoordsBlock A φ m X = 0 ↔ cellBlockTensor A φ m X = 0 := by
  rw [cellCoordsBlock]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [(cellTwistBlock A (exteriorCellIndex.{u} r m) m).map_eq_zero_iff,
    (cellSplit A (exteriorCellIndex.{u} r m)).map_eq_zero_iff]

/-! ### The module `A ⊗_R K` over `A` -/

/-- **The tensor product of a differential graded algebra `A` with the Koszul algebra of a
functional on `Rʳ`, as a right differential graded `A`-module.** The action is restriction along
`a ↦ a ⊗ 1`. For `A = K_n` and the functional cutting out `K_t` this is `K_n ⊗_R K_t` over
`K_n`. -/
def tensorModule : DifferentialGradedModule.{u, u, u} A :=
  restrictScalars (tensorInclLeft A (𝒦)) (regularModule (tensorProduct A (𝒦)))

/-- The carrier of `tensorModule A φ` is the graded tensor product of `A` and the Koszul
algebra. -/
theorem tensorModule_M : (tensorModule A φ).M = (A.grading ᵍ⊗[R] (𝒦).grading) := rfl

/-- The grading of `tensorModule A φ` is the tensor product grading. -/
theorem tensorModule_grading (n : ℤ) :
    (tensorModule A φ).grading n = tensorProductGrading A (𝒦) n := rfl

/-- The differential of `tensorModule A φ` is the tensor product differential. -/
theorem tensorModule_d : (tensorModule A φ).d = tensorProductDifferential A (𝒦) := rfl

/-- **The cell coordinates of `A ⊗_R K` over `A`.** -/
def tensorCellCoords :
    (A.grading ᵍ⊗[R] (𝒦).grading) ≃ₗ[R]
      (⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), A.A) :=
  (GradedTensorProduct.of R A.grading (𝒦).grading).symm.trans (tensorCellEquiv A φ)

/-- The component of exterior degree `m` of the cell coordinates of `X` is
`cellCoordsBlock A φ m X`. -/
theorem tensorCellCoords_of (X : A.A ⊗[R] (𝒦).A) (m : ℕ) :
    (tensorCellCoords A φ (GradedTensorProduct.of R A.grading (𝒦).grading X)) m
      = cellCoordsBlock A φ m X :=
  tensorCellEquiv_apply A φ X m

/-- The coordinate of `a ⊗ b` on the cell `j` of exterior degree `m` is the twist by `m` of
`b_j • a`, where `b_j` is the coordinate of `b` on that cell. -/
theorem tensorCellCoords_tmul (a : A.A) (b : (𝒦).A) (m : ℕ)
    (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ (a ᵍ⊗ₜ[R] b)) m) j
      = A.koszulSignPow m (((koszulCellBlock φ m b) j) • a) := by
  have hof : (GradedTensorProduct.of R A.grading (𝒦).grading) (a ⊗ₜ[R] b)
      = (a ᵍ⊗ₜ[R] b) := rfl
  have h : ((tensorCellCoords A φ (a ᵍ⊗ₜ[R] b)) m) j = (cellCoordsBlock A φ m (a ⊗ₜ[R] b)) j := by
    rw [← hof]
    exact congrArg (fun y : ⨁ (_ : exteriorCellIndex.{u} r m), A.A => y j)
      (tensorCellCoords_of A φ (a ⊗ₜ[R] b) m)
  rw [h, cellCoordsBlock_tmul]

/-- The cell coordinates commute with multiplication by an integer. -/
theorem tensorCellCoords_zsmul (t : ℤ) (x : A.grading ᵍ⊗[R] (𝒦).grading) (m : ℕ)
    (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ (t • x)) m) j = t • (((tensorCellCoords A φ x) m) j) := by
  rw [← Int.cast_smul_eq_zsmul R t x, map_smul, DFinsupp.smul_apply, DFinsupp.smul_apply,
    Int.cast_smul_eq_zsmul]

/-! ### Compatibility of the cell coordinates with the right action -/

/-- **The right action of `a` on `A ⊗_R K`**, as an `R`-linear endomorphism: multiplication by
`a ⊗ 1`. -/
def mulTensorOne (a : A.A) :
    (A.grading ᵍ⊗[R] (𝒦).grading) →ₗ[R] (A.grading ᵍ⊗[R] (𝒦).grading) :=
  LinearMap.mulRight R (a ᵍ⊗ₜ[R] (1 : (𝒦).A))

/-- `mulTensorOne A φ a` is right multiplication by `a ⊗ 1`. -/
theorem mulTensorOne_apply (a : A.A) (x : A.grading ᵍ⊗[R] (𝒦).grading) :
    mulTensorOne A φ a x = x * (a ᵍ⊗ₜ[R] (1 : (𝒦).A)) := rfl

/-- **The cell coordinates are compatible with the right action of a homogeneous element.** The
twist by the parity of the exterior degree is what makes this hold: the right action on the
tensor product carries the Koszul sign of the exterior degree against the degree of the scalar,
and the twist absorbs it. -/
theorem tensorCellCoords_mulTensorOne_of_mem (α : ℤ) {a : A.A} (ha : a ∈ A.grading α)
    (x : A.grading ᵍ⊗[R] (𝒦).grading) (m : ℕ) (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ (mulTensorOne A φ a x)) m) j
      = ((tensorCellCoords A φ x) m) j * a := by
  obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective x
  induction X using TensorProduct.inductionOn with
  | add X Y hX hY =>
      simp only [map_add, DirectSum.add_apply, add_mul]
      rw [hX, hY]
  | tmul b c =>
      induction c using DirectSum.Decomposition.inductionOn (𝒦).grading with
      | zero =>
          simp only [TensorProduct.tmul_zero, map_zero, DirectSum.zero_apply, zero_mul]
      | add c c' hc hc' =>
          simp only [TensorProduct.tmul_add, map_add, DirectSum.add_apply, add_mul]
          rw [hc, hc']
      | @homogeneous q c =>
          have hof : (GradedTensorProduct.of R A.grading (𝒦).grading)
              (b ⊗ₜ[R] (c : (𝒦).A)) = (b ᵍ⊗ₜ[R] (c : (𝒦).A)) := rfl
          have hmul : mulTensorOne A φ a (b ᵍ⊗ₜ[R] (c : (𝒦).A))
              = ((q * α).negOnePow : ℤ) • ((b * a) ᵍ⊗ₜ[R] (c : (𝒦).A)) := by
            have h := GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading (𝒦).grading b c
              ⟨a, ha⟩ (1 : (𝒦).A)
            rw [mul_one, show ((-1 : ℤˣ) ^ (q * α)) = (q * α).negOnePow from rfl] at h
            simpa only [Units.smul_def, mulTensorOne_apply] using h
          rw [hof, hmul, tensorCellCoords_zsmul, tensorCellCoords_tmul, tensorCellCoords_tmul]
          simp only [map_smul]
          rw [A.koszulSignPow_mul_of_mem m b ha, smul_mul_assoc]
          by_cases hqm : q + (m : ℤ) = 0
          · have hq : ((q * α).negOnePow : ℤ) = (((m : ℤ) * α).negOnePow : ℤ) := by
              rw [show q = -(m : ℤ) by omega, show -(m : ℤ) * α = -((m : ℤ) * α) by ring,
                Int.negOnePow_neg]
            rw [hq, smul_comm, smul_smul, negOnePow_natMul_self, one_smul]
          · rw [koszulCellBlock_apply_eq_zero_of_mem φ c.property hqm j, zero_smul, smul_zero,
              zero_smul]

/-- **The cell coordinates are compatible with the right action of `A`**: the coordinates of
`x · (a ⊗ 1)` are those of `x` multiplied on the right by `a`. -/
theorem tensorCellCoords_mulTensorOne (a : A.A) (x : A.grading ᵍ⊗[R] (𝒦).grading) (m : ℕ)
    (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ (mulTensorOne A φ a x)) m) j
      = ((tensorCellCoords A φ x) m) j * a := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero =>
      rw [show mulTensorOne A φ 0 x = 0 by
        rw [mulTensorOne_apply, tmul_zero_left' A (𝒦), mul_zero]]
      simp only [map_zero, DirectSum.zero_apply, mul_zero]
  | add a a' hna hna' =>
      rw [show mulTensorOne A φ (a + a') x = mulTensorOne A φ a x + mulTensorOne A φ a' x by
        rw [mulTensorOne_apply, mulTensorOne_apply, mulTensorOne_apply,
          tmul_add_left A (𝒦), mul_add]]
      simp only [map_add, DirectSum.add_apply]
      rw [hna, hna', mul_add]
  | @homogeneous α a => exact tensorCellCoords_mulTensorOne_of_mem A φ α a.property x m j

/-! ### Compatibility of the cell coordinates with the grading -/

/-- The element of `A ⊗_R K` whose only nonzero cell coordinate is `a` on the cell `j` of exterior
degree `m` is the twist of `a` tensored with the wedge monomial at `j`. -/
theorem tensorCellCoords_symm_of_of (m : ℕ) (j : exteriorCellIndex.{u} r m) (a : A.A) :
    (tensorCellCoords A φ).symm
        (DirectSum.of (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), A.A) m
          (DirectSum.of (fun _ : exteriorCellIndex.{u} r m => A.A) j a))
      = (A.koszulSignPow m a) ᵍ⊗ₜ[R] koszulMonomial φ m j := by
  refine (LinearEquiv.symm_apply_eq _).2 (DirectSum.ext fun m' => DirectSum.ext fun j' => ?_).symm
  rw [tensorCellCoords_tmul]
  by_cases hm : m' = m
  · subst hm
    rw [koszulCellBlock_koszulMonomial_self, DirectSum.of_eq_same]
    by_cases hj : j' = j
    · subst hj
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same, one_smul,
        A.koszulSignPow_koszulSignPow]
    · rw [DirectSum.of_eq_of_ne _ _ _ hj, DirectSum.of_eq_of_ne _ _ _ hj, zero_smul, map_zero]
  · rw [koszulCellBlock_koszulMonomial_ne φ hm, DirectSum.of_eq_of_ne _ _ _ hm,
      DirectSum.zero_apply, DirectSum.zero_apply, zero_smul, map_zero]

/-- The element of `A ⊗_R K` whose only nonzero cell coordinate is an element of degree `n + m` on
a cell of exterior degree `m` is homogeneous of degree `n`. -/
theorem tensorCellCoords_symm_of_of_mem (n : ℤ) (m : ℕ) (j : exteriorCellIndex.{u} r m)
    {a : A.A} (ha : a ∈ A.grading (n + (m : ℤ))) :
    (tensorCellCoords A φ).symm
        (DirectSum.of (fun m => ⨁ (_ : exteriorCellIndex.{u} r m), A.A) m
          (DirectSum.of (fun _ : exteriorCellIndex.{u} r m => A.A) j a))
      ∈ tensorProductGrading A (𝒦) n := by
  rw [tensorCellCoords_symm_of_of]
  have h := tmul_mem_total A (𝒦) (n + (m : ℤ)) (-(m : ℤ)) (A.koszulSignPow m a)
    (koszulMonomial φ m j) (A.koszulSignPow_mem m ha) (koszulMonomial_mem φ m j)
  rwa [show n + (m : ℤ) + -(m : ℤ) = n by ring] at h

/-- An element of `A ⊗_R K` whose coordinate on each cell of exterior degree `m` has degree
`n + m` is homogeneous of degree `n`, stated for the inverse of the cell coordinates. -/
theorem tensorCellCoords_symm_mem_grading (n : ℤ)
    (y : ⨁ (m : ℕ), ⨁ (_ : exteriorCellIndex.{u} r m), A.A)
    (hy : ∀ (m : ℕ) (j : exteriorCellIndex.{u} r m), (y m) j ∈ A.grading (n + (m : ℤ))) :
    (tensorCellCoords A φ).symm y ∈ tensorProductGrading A (𝒦) n := by
  classical
  rw [← DirectSum.sum_support_of y, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [← DirectSum.sum_support_of (y m), map_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact tensorCellCoords_symm_of_of_mem A φ n m j (hy m j)

/-- If the coordinate of `x` on each cell of exterior degree `m` has degree `n + m`, then `x` is
homogeneous of degree `n`. -/
theorem mem_tensorProductGrading_of_coords (n : ℤ) (x : A.grading ᵍ⊗[R] (𝒦).grading)
    (h : ∀ (m : ℕ) (j : exteriorCellIndex.{u} r m),
      ((tensorCellCoords A φ x) m) j ∈ A.grading (n + (m : ℤ))) :
    x ∈ tensorProductGrading A (𝒦) n := by
  have hx := tensorCellCoords_symm_mem_grading A φ n (tensorCellCoords A φ x) h
  rwa [LinearEquiv.symm_apply_apply] at hx

/-- If `x` is homogeneous of degree `n`, then its coordinate on each cell of exterior degree `m`
has degree `n + m`. -/
theorem coords_mem_of_mem_tensorProductGrading (n : ℤ) (x : A.grading ᵍ⊗[R] (𝒦).grading)
    (hx : x ∈ tensorProductGrading A (𝒦) n) (m : ℕ) (j : exteriorCellIndex.{u} r m) :
    ((tensorCellCoords A φ x) m) j ∈ A.grading (n + (m : ℤ)) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hz
      by_cases hqm : q + (m : ℤ) = 0
      · rw [tensorCellCoords_tmul, show n + (m : ℤ) = p by omega]
        exact A.koszulSignPow_mem m (Submodule.smul_mem _ _ ha)
      · rw [tensorCellCoords_tmul, koszulCellBlock_apply_eq_zero_of_mem φ hb hqm j, zero_smul,
          map_zero]
        exact Submodule.zero_mem _
  | zero =>
      rw [map_zero (tensorCellCoords A φ), DirectSum.zero_apply, DirectSum.zero_apply]
      exact Submodule.zero_mem _
  | add z w _ _ ihz ihw =>
      rw [map_add (tensorCellCoords A φ), DirectSum.add_apply, DirectSum.add_apply]
      exact Submodule.add_mem _ ihz ihw
  | smul t z _ ih =>
      rw [map_smul (tensorCellCoords A φ), DFinsupp.smul_apply, DFinsupp.smul_apply]
      exact Submodule.smul_mem _ t ih

/-- **An element of `A ⊗_R K` is homogeneous of degree `n` exactly when all of its cell
coordinates are**: the coordinate on a cell of exterior degree `m` must have degree `n + m`,
because that cell sits in degree `-m`. -/
theorem tensorModule_mem_grading_iff (n : ℤ) (x : (tensorModule A φ).M) :
    x ∈ (tensorModule A φ).grading n ↔ ∀ (m : ℕ) (j : exteriorCellIndex.{u} r m),
      ((tensorCellCoords A φ x) m) j ∈ A.grading (n + (m : ℤ)) :=
  ⟨fun hx m j => coords_mem_of_mem_tensorProductGrading A φ n x hx m j,
    fun h => mem_tensorProductGrading_of_coords A φ n x h⟩

/-- There are no cells above exterior degree `r`. -/
theorem tensorModule_coords_eq_zero (x : (tensorModule A φ).M) (m : ℕ) (hm : r + 1 ≤ m) :
    (tensorCellCoords A φ x) m = 0 := by
  have : IsEmpty (exteriorCellIndex.{u} r m) := isEmpty_exteriorCellIndex r (by omega)
  exact DirectSum.ext fun j => isEmptyElim j

/-! ### Compatibility of the cell coordinates with the differential -/

/-- The differential of `A ⊗_R K` is `d ⊗ 1 + σ ⊗ d`, where `σ` is the Koszul sign on `A`. -/
theorem tensorModule_d_of (X : A.A ⊗[R] (𝒦).A) :
    (tensorModule A φ).d (GradedTensorProduct.of R A.grading (𝒦).grading X)
      = GradedTensorProduct.of R A.grading (𝒦).grading
          (TensorProduct.map A.d LinearMap.id X
            + TensorProduct.map (koszulSign A) (𝒦).d X) := rfl

/-- On the cell coordinates of a fixed exterior degree, the first half of the tensor differential
is the differential of the algebra, with the sign of that exterior degree. -/
theorem cellCoordsBlock_map_d (m : ℕ) (X : A.A ⊗[R] (𝒦).A)
    (j : exteriorCellIndex.{u} r m) :
    (cellCoordsBlock A φ m (TensorProduct.map A.d LinearMap.id X)) j
      = ((-1 : ℤ) ^ m) • A.d ((cellCoordsBlock A φ m X) j) := by
  induction X using TensorProduct.inductionOn with
  | tmul a b =>
      have h1 : A.koszulSignPow m (((koszulCellBlock φ m b) j) • A.d a)
          = ((-1 : ℤ) ^ m) • A.d (A.koszulSignPow m (((koszulCellBlock φ m b) j) • a)) := by
        simp only [map_smul, A.koszulSignPow_d]
        rw [smul_comm]
      rw [TensorProduct.map_tmul, LinearMap.id_apply, cellCoordsBlock_tmul,
        cellCoordsBlock_tmul, h1]
  | add X Y hX hY =>
      rw [map_add, map_add, DirectSum.add_apply, hX, hY, map_add (cellCoordsBlock A φ m),
        DirectSum.add_apply, map_add A.d, smul_add]

/-- The second half of the tensor differential lowers the exterior degree by one. -/
theorem cellBlockTensor_map_d (m : ℕ) (X : A.A ⊗[R] (𝒦).A) :
    cellBlockTensor A φ m (TensorProduct.map (koszulSign A) (𝒦).d X)
      = TensorProduct.map (koszulSign A) (koszulLower φ m) (cellBlockTensor A φ (m + 1) X) := by
  induction X using TensorProduct.inductionOn with
  | tmul a b =>
      rw [TensorProduct.map_tmul, cellBlockTensor, cellBlockTensor, TensorProduct.map_tmul,
        TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.id_apply, TensorProduct.map_tmul,
        koszulCellBlock_d_eq_koszulLower]
  | add X Y hX hY =>
      rw [map_add, map_add, hX, hY, map_add (cellBlockTensor A φ (m + 1)), map_add]

/-- If the block of exterior degree `m + 1` of `X` vanishes, then the cell coordinates of exterior
degree `m` of the second half of the tensor differential of `X` vanish. -/
theorem cellCoordsBlock_map_d_eq_zero (m : ℕ) (X : A.A ⊗[R] (𝒦).A)
    (h : cellBlockTensor A φ (m + 1) X = 0) :
    cellCoordsBlock A φ m (TensorProduct.map (koszulSign A) (𝒦).d X) = 0 := by
  rw [cellCoordsBlock_eq_zero_iff, cellBlockTensor_map_d, h, map_zero]

/-- The cell coordinates of exterior degree `m` of the differential of `X` are the sum of those of
the two halves of the tensor differential. -/
theorem tensorCellCoords_d_of_block (X : A.A ⊗[R] (𝒦).A) (m : ℕ) :
    (tensorCellCoords A φ
        ((tensorModule A φ).d (GradedTensorProduct.of R A.grading (𝒦).grading X))) m
      = cellCoordsBlock A φ m (TensorProduct.map A.d LinearMap.id X)
        + cellCoordsBlock A φ m (TensorProduct.map (koszulSign A) (𝒦).d X) := by
  rw [tensorModule_d_of, map_add (GradedTensorProduct.of R A.grading (𝒦).grading),
    map_add (tensorCellCoords A φ), DirectSum.add_apply, tensorCellCoords_of,
    tensorCellCoords_of]

/-- On a cell of exterior degree `k`, the differential of `A ⊗_R K` is the differential of the
algebra with the sign of `k`, provided the coordinates of exterior degree `k + 1` vanish. -/
private theorem tensorCellCoords_d_apply_of_coords_eq_zero (X : A.A ⊗[R] (𝒦).A) (k : ℕ)
    (j : exteriorCellIndex.{u} r k)
    (h1 : (tensorCellCoords A φ (GradedTensorProduct.of R A.grading (𝒦).grading X)) (k + 1)
      = 0) :
    ((tensorCellCoords A φ
        ((tensorModule A φ).d (GradedTensorProduct.of R A.grading (𝒦).grading X))) k) j
      = ((-1 : ℤ) ^ k) • A.d (((tensorCellCoords A φ
          (GradedTensorProduct.of R A.grading (𝒦).grading X)) k) j) := by
  have hcb1 : cellBlockTensor A φ (k + 1) X = 0 :=
    (cellCoordsBlock_eq_zero_iff A φ (k + 1) X).1
      ((tensorCellCoords_of A φ X (k + 1)).symm.trans h1)
  rw [tensorCellCoords_d_of_block, DirectSum.add_apply, cellCoordsBlock_map_d,
    cellCoordsBlock_map_d_eq_zero A φ k X hcb1, DirectSum.zero_apply, add_zero,
    tensorCellCoords_of]

/-- **The differential preserves the vanishing of the high cell coordinates.** -/
theorem tensorCellCoords_d_eq_zero (X : A.A ⊗[R] (𝒦).A) (m : ℕ)
    (h0 : (tensorCellCoords A φ (GradedTensorProduct.of R A.grading (𝒦).grading X)) m = 0)
    (h1 : (tensorCellCoords A φ (GradedTensorProduct.of R A.grading (𝒦).grading X)) (m + 1)
      = 0) :
    (tensorCellCoords A φ
        ((tensorModule A φ).d (GradedTensorProduct.of R A.grading (𝒦).grading X))) m = 0 := by
  refine DirectSum.ext fun j => ?_
  rw [tensorCellCoords_d_apply_of_coords_eq_zero A φ X m j h1, h0]
  simp

/-- **On the top cell coordinate the differential is the differential of the algebra**, with the
sign of the exterior degree. -/
theorem tensorCellCoords_d_apply (X : A.A ⊗[R] (𝒦).A) (k : ℕ)
    (j : exteriorCellIndex.{u} r k)
    (h1 : (tensorCellCoords A φ (GradedTensorProduct.of R A.grading (𝒦).grading X)) (k + 1)
      = 0) :
    ((tensorCellCoords A φ
        ((tensorModule A φ).d (GradedTensorProduct.of R A.grading (𝒦).grading X))) k) j
      = ((-1 : ℤ) ^ k) • A.d (((tensorCellCoords A φ
          (GradedTensorProduct.of R A.grading (𝒦).grading X)) k) j) :=
  tensorCellCoords_d_apply_of_coords_eq_zero A φ X k j h1

/-! ### The cell decomposition and orthogonality -/

/-- **The triangular cell decomposition of `A ⊗_R K` over `A`, by exterior degree.** The cells of
exterior degree `m` are the wedge monomials `1 ⊗ ξ_s` with `|s| = m`, each in degree `-m`; there
are none above exterior degree `r`, and the tensor differential lowers the exterior degree, so it
is lower triangular for this decomposition. -/
def gradedCellDataTensorModule : GradedCellData (tensorModule A φ) := by
  refine gradedCellDataOfCellCoords (I := exteriorCellIndex.{u} r) (fun m _ => (m : ℤ)) (r + 1)
    (tensorCellCoords A φ) ?_ (tensorModule_mem_grading_iff A φ)
    (tensorModule_coords_eq_zero A φ) ?_ ?_
  · intro a x m
    refine DirectSum.ext fun j => ?_
    rw [DFinsupp.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact tensorCellCoords_mulTensorOne A φ a x m j
  · intro k x hk m hm
    obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective x
    exact tensorCellCoords_d_eq_zero A φ X m (hk m hm) (hk (m + 1) (by omega))
  · intro k x hk j
    obtain ⟨X, rfl⟩ := (GradedTensorProduct.of R A.grading (𝒦).grading).surjective x
    rw [Int.natAbs_natCast]
    exact tensorCellCoords_d_apply A φ X k j (hk (k + 1) (by omega))

/-- **The tensor product of a differential graded algebra `A` with the Koszul algebra of a
functional on `Rʳ`, viewed as a right differential graded `A`-module, is orthogonal on the left to
the acyclic modules.** -/
theorem leftOrthogonal_acyclic_tensorModule :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (tensorModule A φ)) :=
  leftOrthogonal_acyclic_of_gradedCellData (gradedCellDataTensorModule A φ)

/-- **`K_n ⊗_R K_t`, viewed as a right differential graded `K_n`-module, is orthogonal on the left
to the acyclic modules.** This is `Koszul.leftOrthogonal_acyclic_tensorModule` for the functional
cutting out `K_t` over the algebra `K_n`. -/
theorem leftOrthogonal_acyclic_powAlgebra_tensorModule (f : Fin r → R) (n t : ℕ) :
    (acyclic' (powAlgebra f n)).leftOrthogonal
      ((toHomotopyCategory (powAlgebra f n)).obj
        (restrictScalars (tensorInclLeft (powAlgebra f n) (powAlgebra f t))
          (regularModule (tensorProduct (powAlgebra f n) (powAlgebra f t))))) :=
  leftOrthogonal_acyclic_tensorModule (powAlgebra f n) (seqDual fun i => f i ^ t)

end Koszul

end
