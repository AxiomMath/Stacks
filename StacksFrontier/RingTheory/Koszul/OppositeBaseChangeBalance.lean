module

public import StacksFrontier.RingTheory.Koszul.BaseChangeBalance
public import StacksFrontier.RingTheory.Koszul.OppositeTensorCellFiltration

/-!
# One plain tensor product, read on the graded opposite algebra

Let `R` be a commutative ring and let `(A, d)` and `(C, d)` be differential graded `R`-algebras.
The tensor product `A ⊗_R C` of Tag 065W has two presentations as a right differential graded
module over the graded opposite `A^opp`: the tensor product `A^opp ⊗_R C` read over `A^opp`
through `a ↦ a ⊗ 1`, which is `DifferentialGraded.absLeftSource (oppAlgebra A) C`, and the graded
opposite of `A ⊗_R C` read over `A^opp` through the graded opposite of `a ↦ a ⊗ 1`, which is
`DifferentialGraded.oppLeftSource` below and is the presentation `Koszul.oppTensorModule` uses.
The two tensor products `A^opp ⊗_R C` and `(A ⊗_R C)^opp` are genuinely different differential
graded algebras, so the two presentations have to be compared by hand; this file compares them,
and the comparison is an isomorphism of right differential graded `A^opp`-modules whose
underlying map is the identification of the underlying graded modules, with no sign.

Transporting `DifferentialGraded.tensorObjIsoOfBaseChange` across that isomorphism gives the
identification of plain tensor products `(A ⊗_R C) ⊗_{A^opp} N = C ⊗_R N` in the second
presentation, which is the spelling in which the left orthogonality of
`Koszul.leftOrthogonal_acyclic_oppTensorModule` is available.

## Main definitions

* `DifferentialGraded.oppLeftSource`: `A ⊗_R C`, as a right differential graded `A^opp`-module
  through the graded opposite of `a ↦ a ⊗ 1`.
* `DifferentialGraded.oppLeftEquiv`: the identification of the underlying graded module of
  `A^opp ⊗_R C` with that of `A ⊗_R C`, and `DifferentialGraded.oppLeftBridgeEquiv`: its
  composite with the identification of the underlying graded module of `(A ⊗_R C)^opp`.
* `DifferentialGraded.oppLeftBridgeHom` and `DifferentialGraded.oppLeftBridgeInv`: the two
  homomorphisms of differential graded `A^opp`-modules it produces.

## Main results

* `DifferentialGraded.oppLeftEquiv_mul_tmul_one_of_mem`: the right action of a homogeneous
  element of `A^opp` on `A^opp ⊗_R C` becomes left multiplication by `a ⊗ 1` on `A ⊗_R C`, up to
  the Koszul sign the graded opposite of `A ⊗_R C` acts by.
* `DifferentialGraded.oppLeftBridgeIso`: **the comparison of the two presentations**,
  `A^opp ⊗_R C ≅ (A ⊗_R C)^opp` as right differential graded `A^opp`-modules.
* `Koszul.oppTensorModuleIso`: the comparison at the Koszul algebra of a functional on `Rʳ`.
* `Koszul.oppTensorObjIso_oppTensorModule_baseModule`: **the comparison of the two plain tensor
  products** in the presentation `Koszul.oppTensorModule` uses, and
  `Koszul.oppTensorObjIso_powBaseTensorRestrictedModule`: the same for `K_N ⊗_R K_t` as a left
  differential graded `K_N`-module.

## Implementation notes

*Why the comparison carries no sign.* For `a` of degree `α` and a pure tensor `y ⊗ c` with `y` of
degree `ξ` and `c` of degree `γ`, the right action of `A^opp` on `A^opp ⊗_R C` is
`(y ⊗ c)(a ⊗ 1) = (-1)^(γ α) (y ⋅ᵒᵖᵖ a) ⊗ c` by Tag 065W, and
`y ⋅ᵒᵖᵖ a = (-1)^(ξ α) (a y)` under the identification of the underlying graded modules of
`A^opp` and `A`. The right action of `A^opp` on `(A ⊗_R C)^opp` is
`(-1)^((ξ + γ) α) (a ⊗ 1)(y ⊗ c) = (-1)^((ξ + γ) α) (a y) ⊗ c`, left multiplication by `a ⊗ 1`
carrying no sign because `1` has degree zero. The two signs are equal, so the identification of
the underlying graded modules is already a homomorphism of modules.

*The graded opposite is opaque.* `DifferentialGradedAlgebra.opposite` is built by choice from a
nonemptiness statement, so the underlying type of `oppAlgebra X` is reachable only through the
linear equivalence `DifferentialGradedAlgebra.Opposite.equiv` and the formulas recorded alongside
it. Every statement below is therefore pushed across those equivalences, and the comparison is
assembled from the linear equivalence `DifferentialGraded.oppLeftBridgeEquiv` rather than by
rewriting one spelling into the other.

*Transporting the balance.* The relative tensor product with a fixed bimodule has no
presentation, only a universal property, so the comparison of plain tensor products is obtained
by applying the functor `DifferentialGraded.Bimodule.tensorCompFunctor` of Tag 09LM to the
comparison of the two presentations.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W) is the tensor product of
  differential graded algebras, [Tag 09JG](https://stacks.math.columbia.edu/tag/09JG) the graded
  opposite algebra and [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) the relative tensor
  product with a bimodule.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is where the comparison
  is used.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] (A C : DifferentialGradedAlgebra.{u, u} R)

/-! ### The second presentation and the identification of underlying graded modules -/

/-- `A ⊗_R C` of Tag 065W, read as a right differential graded module over the graded opposite of
`A` through the graded opposite of `a ↦ a ⊗ 1`. This is the presentation
`Koszul.oppTensorModule` uses, and the companion of
`DifferentialGraded.absLeftSource (oppAlgebra A) C`. -/
abbrev oppLeftSource : DifferentialGradedModule.{u, u, u} (oppAlgebra A) :=
  restrictScalars (oppHom (tensorInclLeft A C)) (regularModule (oppAlgebra (tensorProduct A C)))

/-- The identification of the underlying graded module of `A^opp ⊗_R C` with that of `A ⊗_R C`:
the identification of the underlying graded module of `A^opp` with that of `A`, tensored with the
identity of `C`. -/
def oppLeftEquiv :
    ((oppAlgebra A).grading ᵍ⊗[R] C.grading) ≃ₗ[R] (A.grading ᵍ⊗[R] C.grading) :=
  ((GradedTensorProduct.of R (oppAlgebra A).grading C.grading).symm.trans
    (TensorProduct.congr (opposite R A).equiv (LinearEquiv.refl R C.A))).trans
    (GradedTensorProduct.of R A.grading C.grading)

/-- `oppLeftEquiv` sends `x ⊗ c` to the image of `x` in `A`, tensored with `c`. -/
theorem oppLeftEquiv_tmul (x : (oppAlgebra A).A) (c : C.A) :
    oppLeftEquiv A C ((x ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      (((opposite R A).equiv x) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) := rfl

/-- The inverse of `oppLeftEquiv` sends `x ⊗ c` to the image of `x` in `A^opp`, tensored with
`c`. -/
theorem oppLeftEquiv_symm_tmul (x : A.A) (c : C.A) :
    (oppLeftEquiv A C).symm ((x ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) =
      (((opposite R A).equiv.symm x) ᵍ⊗ₜ[R] c :
        (oppAlgebra A).grading ᵍ⊗[R] C.grading) := rfl

/-- The identification preserves the total grading: it is the identity on the second factor and
preserves every homogeneous component of the first. -/
theorem oppLeftEquiv_mem_grading (n : ℤ)
    (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading (oppAlgebra A) C n) :
    oppLeftEquiv A C x ∈ tensorProductGrading A C n := by
  refine tensorProductGrading_induction (oppAlgebra A) C n
    (motive := fun z => oppLeftEquiv A C z ∈ tensorProductGrading A C n)
    (by simp) (fun z w hz hw => by simpa only [map_add] using Submodule.add_mem _ hz hw)
    (fun r z hz => by simpa only [map_smul] using Submodule.smul_mem _ r hz) ?_ x hx
  intro p q y c hy hc hpq
  rw [oppLeftEquiv_tmul]
  exact hpq ▸ tmul_mem_total A C p q _ c (((opposite R A).mem_grading_iff p y).1 hy) hc

/-- The inverse identification preserves the total grading. -/
theorem oppLeftEquiv_symm_mem_grading (n : ℤ) (y : A.grading ᵍ⊗[R] C.grading)
    (hy : y ∈ tensorProductGrading A C n) :
    (oppLeftEquiv A C).symm y ∈ tensorProductGrading (oppAlgebra A) C n := by
  refine tensorProductGrading_induction A C n
    (motive := fun z => (oppLeftEquiv A C).symm z ∈
      tensorProductGrading (oppAlgebra A) C n)
    (by simp) (fun z w hz hw => by simpa only [map_add] using Submodule.add_mem _ hz hw)
    (fun r z hz => by simpa only [map_smul] using Submodule.smul_mem _ r hz) ?_ y hy
  intro p q b c hb hc hpq
  rw [oppLeftEquiv_symm_tmul]
  refine hpq ▸ tmul_mem_total (oppAlgebra A) C p q _ c ?_ hc
  exact ((opposite R A).mem_grading_iff p _).2 (by rwa [LinearEquiv.apply_symm_apply])

/-- The identification commutes with the two tensor differentials: the graded opposite of `A` has
the same differential as `A`, and the signs in the two tensor differentials are read off the same
degrees. -/
theorem oppLeftEquiv_map_d (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading) :
    oppLeftEquiv A C ((tensorProduct (oppAlgebra A) C).d x) =
      (tensorProduct A C).d (oppLeftEquiv A C x) := by
  induction x using gradedTensor_induction with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul y c =>
      induction y using DirectSum.Decomposition.inductionOn (oppAlgebra A).grading with
      | zero => rw [tmul_zero_left' (oppAlgebra A) C]; simp
      | add y y' hy hy' =>
          rw [tmul_add_left (oppAlgebra A) C, map_add, map_add, map_add, map_add, hy, hy']
      | @homogeneous p y =>
          have hey : (opposite R A).equiv (y : (oppAlgebra A).A) ∈ A.grading p :=
            ((opposite R A).mem_grading_iff p _).1 y.property
          rw [tensorProductDifferential_tmul (oppAlgebra A) C p y c, oppLeftEquiv_tmul,
            tensorProductDifferential_tmul A C p ⟨_, hey⟩ c]
          simp only [map_add, ← Int.cast_smul_eq_zsmul R, map_smul, oppLeftEquiv_tmul,
            (opposite R A).map_d]

/-- Under the identification of the underlying graded modules, the image of a scalar under the
graded opposite of `a ↦ a ⊗ 1` is the pure tensor `a ⊗ 1`. -/
theorem oppTensorInclLeft_equiv (a : (oppAlgebra A).A) :
    (opposite R (tensorProduct A C)).equiv
        ((oppHom (tensorInclLeft A C)).toAlgebraHom a) =
      ((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : C.A)) : A.grading ᵍ⊗[R] C.grading) := by
  rw [oppHom_apply, LinearEquiv.apply_symm_apply, tensorInclLeft_toAlgebraHom]
  rfl

/-! ### Compatibility with the right action of the graded opposite algebra -/

/-- **The right action of `A^opp` on `A^opp ⊗_R C` is left multiplication by `a ⊗ 1` on
`A ⊗_R C`, up to the Koszul sign of the total degree against the degree of the scalar.** This is
the sign the graded opposite of `A ⊗_R C` acts by, so this is the identity that makes the
identification of the underlying graded modules a homomorphism of modules. Right multiplication
by `a ⊗ 1` contributes the sign of the degree of the second factor against the degree of the
scalar, the graded opposite of `A` contributes the sign of the degree of the first factor, and
the two together are the sign of the total degree. -/
theorem oppLeftEquiv_mul_tmul_one_of_mem {n α : ℤ}
    (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading (oppAlgebra A) C n)
    (a : (oppAlgebra A).A) (ha : a ∈ (oppAlgebra A).grading α) :
    oppLeftEquiv A C
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      (n * α).negOnePow •
        ((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : C.A) : A.grading ᵍ⊗[R] C.grading) *
          oppLeftEquiv A C x) := by
  have hone : (1 : C.A) ∈ C.grading 0 := SetLike.one_mem_graded C.grading
  have hea : (opposite R A).equiv a ∈ A.grading α := ((opposite R A).mem_grading_iff α a).1 ha
  refine tensorProductGrading_induction (oppAlgebra A) C n
    (motive := fun z => oppLeftEquiv A C
        (z * ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      (n * α).negOnePow •
        ((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : C.A) : A.grading ᵍ⊗[R] C.grading) *
          oppLeftEquiv A C z))
    (by simp) ?_ ?_ ?_ x hx
  · intro z w hz hw
    simp only [add_mul, map_add, hz, hw, mul_add, smul_add]
  · intro t z hz
    have hsc : ∀ (u : ℤˣ) (w : A.grading ᵍ⊗[R] C.grading), t • (u • w) = u • (t • w) := by
      intro u w
      rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
        ← Int.cast_smul_eq_zsmul R, smul_comm]
    rw [Algebra.smul_mul_assoc, map_smul, hz, map_smul, Algebra.mul_smul_comm, hsc]
  · intro p q y c hy hc hpq
    subst hpq
    have hey : (opposite R A).equiv y ∈ A.grading p := ((opposite R A).mem_grading_iff p y).1 hy
    have hprod := tmul_mul (oppAlgebra A) C p q α 0 ⟨y, hy⟩ ⟨c, hc⟩ ⟨a, ha⟩ ⟨1, hone⟩
    have hprod' := tmul_mul A C α 0 p q ⟨_, hea⟩ ⟨1, hone⟩ ⟨_, hey⟩ ⟨c, hc⟩
    have hya : (opposite R A).equiv (y * a)
        = (p * α).negOnePow • ((opposite R A).equiv a * (opposite R A).equiv y) :=
      (opposite R A).map_mul_of_mem p α y a hy ha
    have hL : oppLeftEquiv A C
        (((y ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) *
          ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
        ((q * α).negOnePow * (p * α).negOnePow) •
          ((((opposite R A).equiv a * (opposite R A).equiv y) ᵍ⊗ₜ[R] c) :
            A.grading ᵍ⊗[R] C.grading) := by
      rw [hprod, mul_one, map_zsmul_unit, oppLeftEquiv_tmul, hya, units_smul_tmul_left,
        smul_smul]
    have hR : ((((opposite R A).equiv a) ᵍ⊗ₜ[R] (1 : C.A) : A.grading ᵍ⊗[R] C.grading) *
          oppLeftEquiv A C ((y ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading))) =
        ((((opposite R A).equiv a * (opposite R A).equiv y) ᵍ⊗ₜ[R] c) :
          A.grading ᵍ⊗[R] C.grading) := by
      rw [oppLeftEquiv_tmul, hprod', zero_mul, Int.negOnePow_zero, one_smul, one_mul]
    rw [hL, hR]
    congr 1
    rw [← Int.negOnePow_add]
    congr 1
    ring

/-! ### The comparison of the two presentations -/

/-- The identification of the underlying graded module of `A^opp ⊗_R C` with that of
`(A ⊗_R C)^opp`: the identification `DifferentialGraded.oppLeftEquiv` of both with that of
`A ⊗_R C`. -/
def oppLeftBridgeEquiv :
    ((oppAlgebra A).grading ᵍ⊗[R] C.grading) ≃ₗ[R] (oppAlgebra (tensorProduct A C)).A :=
  (oppLeftEquiv A C).trans (opposite R (tensorProduct A C)).equiv.symm

/-- `oppLeftBridgeEquiv` is `oppLeftEquiv` followed by the identification of the underlying
graded module of `A ⊗_R C` with that of `(A ⊗_R C)^opp`. -/
theorem oppLeftBridgeEquiv_apply (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading) :
    oppLeftBridgeEquiv A C x =
      (opposite R (tensorProduct A C)).equiv.symm (oppLeftEquiv A C x) := rfl

/-- The inverse of `oppLeftBridgeEquiv` is the identification of `(A ⊗_R C)^opp` with `A ⊗_R C`
followed by the inverse of `oppLeftEquiv`. -/
theorem oppLeftBridgeEquiv_symm_apply (z : (oppAlgebra (tensorProduct A C)).A) :
    (oppLeftBridgeEquiv A C).symm z =
      (oppLeftEquiv A C).symm ((opposite R (tensorProduct A C)).equiv z) := rfl

/-- The identification preserves the grading (proved before its use in the action lemmas). -/
private theorem oppLeftBridgeEquiv_mem_grading_aux (n : ℤ)
    (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading (oppAlgebra A) C n) :
    oppLeftBridgeEquiv A C x ∈ (oppAlgebra (tensorProduct A C)).grading n := by
  refine ((opposite R (tensorProduct A C)).mem_grading_iff n _).2 ?_
  rw [oppLeftBridgeEquiv_apply, LinearEquiv.apply_symm_apply]
  exact oppLeftEquiv_mem_grading A C n x hx

/-- **The identification carries the right action of a homogeneous element of `A^opp`**, which is
`DifferentialGraded.oppLeftEquiv_mul_tmul_one_of_mem` read through the identification of the
underlying graded module of `(A ⊗_R C)^opp` with that of `A ⊗_R C`. -/
theorem oppLeftBridgeEquiv_smul_of_mem {n α : ℤ} (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading (oppAlgebra A) C n)
    (a : (oppAlgebra A).A) (ha : a ∈ (oppAlgebra A).grading α) :
    oppLeftBridgeEquiv A C
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      oppLeftBridgeEquiv A C x * (oppHom (tensorInclLeft A C)).toAlgebraHom a := by
  have h1 := oppLeftBridgeEquiv_mem_grading_aux A C n x hx
  have h2 : (oppHom (tensorInclLeft A C)).toAlgebraHom a
      ∈ (oppAlgebra (tensorProduct A C)).grading α :=
    (oppHom (tensorInclLeft A C)).map_grading α a ha
  refine (opposite R (tensorProduct A C)).equiv.injective ?_
  rw [(opposite R (tensorProduct A C)).map_mul_of_mem n α _ _ h1 h2,
    oppTensorInclLeft_equiv A C a, oppLeftBridgeEquiv_apply, LinearEquiv.apply_symm_apply,
    oppLeftBridgeEquiv_apply, LinearEquiv.apply_symm_apply,
    oppLeftEquiv_mul_tmul_one_of_mem A C x hx a ha]

/-- **The identification carries the right action of the graded opposite algebra.** Both sides
are additive in the scalar and in the element, so this follows from
`DifferentialGraded.oppLeftBridgeEquiv_smul_of_mem` by decomposing both into homogeneous
pieces. -/
theorem oppLeftBridgeEquiv_smul (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (a : (oppAlgebra A).A) :
    oppLeftBridgeEquiv A C
        (x * ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      oppLeftBridgeEquiv A C x * (oppHom (tensorInclLeft A C)).toAlgebraHom a := by
  induction a using DirectSum.Decomposition.inductionOn (oppAlgebra A).grading with
  | zero => simp [tmul_zero_left' (oppAlgebra A) C]
  | add a b hA hB =>
      rw [tmul_add_left (oppAlgebra A) C, mul_add, map_add, hA, hB, map_add, mul_add]
  | @homogeneous α a =>
      induction x using DirectSum.Decomposition.inductionOn
        (tensorProduct (oppAlgebra A) C).grading with
      | zero => simp
      | add x y hX hY => rw [add_mul, map_add, hX, hY, map_add, add_mul]
      | @homogeneous n x => exact oppLeftBridgeEquiv_smul_of_mem A C x.1 x.2 a.1 a.2

/-- The identification preserves the grading. -/
theorem oppLeftBridgeEquiv_mem_grading (n : ℤ) (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading)
    (hx : x ∈ tensorProductGrading (oppAlgebra A) C n) :
    oppLeftBridgeEquiv A C x ∈ (oppAlgebra (tensorProduct A C)).grading n :=
  oppLeftBridgeEquiv_mem_grading_aux A C n x hx

/-- The identification commutes with the differentials. -/
theorem oppLeftBridgeEquiv_map_d (x : (oppAlgebra A).grading ᵍ⊗[R] C.grading) :
    oppLeftBridgeEquiv A C ((tensorProduct (oppAlgebra A) C).d x) =
      (oppAlgebra (tensorProduct A C)).d (oppLeftBridgeEquiv A C x) := by
  refine (opposite R (tensorProduct A C)).equiv.injective ?_
  rw [oppLeftBridgeEquiv_apply, LinearEquiv.apply_symm_apply,
    (opposite R (tensorProduct A C)).map_d, oppLeftBridgeEquiv_apply,
    LinearEquiv.apply_symm_apply]
  exact oppLeftEquiv_map_d A C x

/-- The inverse identification carries the right action of the graded opposite algebra. -/
theorem oppLeftBridgeEquiv_symm_smul (z : (oppAlgebra (tensorProduct A C)).A)
    (a : (oppAlgebra A).A) :
    (oppLeftBridgeEquiv A C).symm (z * (oppHom (tensorInclLeft A C)).toAlgebraHom a) =
      (oppLeftBridgeEquiv A C).symm z *
        ((a ᵍ⊗ₜ[R] (1 : C.A)) : (oppAlgebra A).grading ᵍ⊗[R] C.grading) := by
  refine (oppLeftBridgeEquiv A C).injective ?_
  rw [LinearEquiv.apply_symm_apply, oppLeftBridgeEquiv_smul A C, LinearEquiv.apply_symm_apply]

/-- The inverse identification preserves the grading. -/
theorem oppLeftBridgeEquiv_symm_mem_grading (n : ℤ) (z : (oppAlgebra (tensorProduct A C)).A)
    (hz : z ∈ (oppAlgebra (tensorProduct A C)).grading n) :
    (oppLeftBridgeEquiv A C).symm z ∈ tensorProductGrading (oppAlgebra A) C n := by
  rw [oppLeftBridgeEquiv_symm_apply]
  exact oppLeftEquiv_symm_mem_grading A C n _
    (((opposite R (tensorProduct A C)).mem_grading_iff n z).1 hz)

/-- The inverse identification commutes with the differentials. -/
theorem oppLeftBridgeEquiv_symm_map_d (z : (oppAlgebra (tensorProduct A C)).A) :
    (oppLeftBridgeEquiv A C).symm ((oppAlgebra (tensorProduct A C)).d z) =
      (tensorProduct (oppAlgebra A) C).d ((oppLeftBridgeEquiv A C).symm z) := by
  refine (oppLeftBridgeEquiv A C).injective ?_
  rw [LinearEquiv.apply_symm_apply, oppLeftBridgeEquiv_map_d, LinearEquiv.apply_symm_apply]

/-- The comparison `A^opp ⊗_R C → (A ⊗_R C)^opp`, as a homomorphism of right differential graded
`A^opp`-modules. -/
def oppLeftBridgeHom : absLeftSource (oppAlgebra A) C ⟶ oppLeftSource A C where
  toFun := (oppLeftBridgeEquiv A C).toLinearMap
  map_smul x a := by
    rw [absLeftSource_op_smul (oppAlgebra A) C x a,
      restrictRegular_op_smul (oppAlgebra (tensorProduct A C))
        (oppHom (tensorInclLeft A C)) a _]
    exact oppLeftBridgeEquiv_smul A C x a
  map_grading n x hx := oppLeftBridgeEquiv_mem_grading A C n x hx
  map_d := LinearMap.ext fun x => oppLeftBridgeEquiv_map_d A C x

/-- The comparison `(A ⊗_R C)^opp → A^opp ⊗_R C`, as a homomorphism of right differential graded
`A^opp`-modules. -/
def oppLeftBridgeInv : oppLeftSource A C ⟶ absLeftSource (oppAlgebra A) C where
  toFun := (oppLeftBridgeEquiv A C).symm.toLinearMap
  map_smul z a := by
    rw [restrictRegular_op_smul (oppAlgebra (tensorProduct A C))
        (oppHom (tensorInclLeft A C)) a z,
      absLeftSource_op_smul (oppAlgebra A) C _ a]
    exact oppLeftBridgeEquiv_symm_smul A C z a
  map_grading n z hz := oppLeftBridgeEquiv_symm_mem_grading A C n z hz
  map_d := LinearMap.ext fun z => oppLeftBridgeEquiv_symm_map_d A C z

/-- **The two presentations of `A ⊗_R C` as a right differential graded module over the graded
opposite of `A` agree.** The tensor product `A^opp ⊗_R C` read over `A^opp` through `a ↦ a ⊗ 1`
and the graded opposite of `A ⊗_R C` read over `A^opp` through the graded opposite of
`a ↦ a ⊗ 1` are isomorphic, by the identification of their underlying graded modules. -/
def oppLeftBridgeIso : absLeftSource (oppAlgebra A) C ≅ oppLeftSource A C where
  hom := oppLeftBridgeHom A C
  inv := oppLeftBridgeInv A C
  hom_inv_id :=
    DifferentialGradedModule.Hom.ext
      (LinearMap.ext fun x => (oppLeftBridgeEquiv A C).symm_apply_apply x)
  inv_hom_id :=
    DifferentialGradedModule.Hom.ext
      (LinearMap.ext fun z => (oppLeftBridgeEquiv A C).apply_symm_apply z)

end DifferentialGraded

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} (A B : DifferentialGradedAlgebra.{u, u} R)
  (φ : Module.Dual R (Fin r → R))

/-- **The two presentations of `A ⊗_R K` as a left differential graded `A`-module agree**, where
`K` is the Koszul algebra of a functional on `Rʳ`: the tensor product of the graded opposite of
`A` with `K`, read over the graded opposite of `A`, is `Koszul.oppTensorModule`. -/
def oppTensorModuleIso : tensorModule (oppAlgebra A) φ ≅ oppTensorModule A φ :=
  oppLeftBridgeIso A (cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ)

/-- **The two plain tensor products of Tag 0GZJ agree, in the presentation of `A ⊗_R K` as a left
differential graded `A`-module.** For a differential graded `(A^opp, B)`-bimodule `N`, the
relative tensor product over `A^opp` of `Koszul.oppTensorModule` with `N` is the relative tensor
product over `R` placed in degree zero of `K` with `N`. This is
`Koszul.tensorObjIso_tensorModule_baseModule` over the graded opposite of `A`, transported along
`Koszul.oppTensorModuleIso`, and it is the spelling in which the left orthogonality of
`Koszul.leftOrthogonal_acyclic_oppTensorModule` is available. -/
def oppTensorObjIso_oppTensorModule_baseModule (N : Bimodule (oppAlgebra A) B) :
    Bimodule.tensorObj N (oppTensorModule A φ) ≅
      Bimodule.tensorObj (absBaseBimodule (oppAlgebra A) B N) (baseModule φ) :=
  (tensorCompFunctor N).mapIso (oppTensorModuleIso A φ).symm ≪≫
    tensorObjIso_tensorModule_baseModule (oppAlgebra A) B φ N

/-- **The two plain tensor products with `K_N ⊗_R K_t`, read as a left differential graded
`K_N`-module, agree.** This is `Koszul.oppTensorObjIso_oppTensorModule_baseModule` on the module
`Koszul.powBaseTensorRestrictedModule`, the companion of
`Koszul.leftOrthogonal_acyclic_powBaseTensorRestrictedModule`. -/
def oppTensorObjIso_powBaseTensorRestrictedModule (f : Fin r → R) (t N : ℕ)
    (M : Bimodule (oppAlgebra (powAlgebra f N)) B) :
    Bimodule.tensorObj M (powBaseTensorRestrictedModule f t N) ≅
      Bimodule.tensorObj (absBaseBimodule (oppAlgebra (powAlgebra f N)) B M)
        (baseModule (seqDual fun i => f i ^ t)) :=
  oppTensorObjIso_oppTensorModule_baseModule (powAlgebra f N) B
    (seqDual fun i => f i ^ t) M

end Koszul

end
