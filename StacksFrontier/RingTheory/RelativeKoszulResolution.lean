module

public import StacksFrontier.RingTheory.Koszul.Variables
public import StacksFrontier.RingTheory.MvPolynomialTwoCopy
public import StacksFrontier.RingTheory.Koszul.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The relative Koszul resolution

Let `A` be a commutative ring, `E` a type, `T = A[E]` and `S = T[E]`.  Write `C : T → S` for
the coefficient inclusion and `diagShift : T → S` for the ring map `X e ↦ X e + C (X e)`; the
augmentation `S → T` at `0` is a retraction of both.  For a `T`-module `V` the complex
`𝒦_• ⊗_T V`, where `𝒦_•` is the Koszul complex of the variables of `S` and the tensor product
is taken over `T` acting on `𝒦_•` through `C`, is a resolution of `V` once it is regarded as a
`T`-module through `diagShift`; its terms are free over `T` as soon as `V` is free over `A`.
This is the Koszul resolution of the diagonal.

## Main definitions

* `MvPolynomial.relKoszulComplex`: The relative Koszul complex `𝒦_• ⊗_T V`, as a complex of
  `T`-modules through `diagShift`.
* `MvPolynomial.relKoszulPi`: Its augmentation to `V` concentrated in degree zero.
* `MvPolynomial.relKoszulMap`: The chain map induced by a `T`-linear map of modules.
* `MvPolynomial.relKoszulResolution`: The relative Koszul complex as a projective resolution
  of `V` when `V` is free over `A`.

## Main results

* `MvPolynomial.relKoszulPi_quasiIso`: The augmentation is a quasi-isomorphism.
* `MvPolynomial.projective_relKoszulTerm`: The terms are projective `T`-modules when `V` is free
  over `A`.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace MvPolynomial

variable (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
  (V : Type max u v) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
  [IsScalarTower A (MvPolynomial E A) V]

/-! ### The complex -/

/-- The degree-`j` term of the relative Koszul complex of `V`. -/
abbrev relKoszulType (j : ℕ) : Type max u v :=
  (⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A)))
    ⊗[MvPolynomial E A] V

/-- The degree-`j` term of the relative Koszul complex of `V`, as a `T`-module through
`diagShift`. -/
abbrev relKoszulTerm (j : ℕ) : ModuleCat.{max u v} (MvPolynomial E A) :=
  (ModuleCat.restrictScalars (diagShift A E)).obj
    (ModuleCat.of (MvPolynomial E (MvPolynomial E A)) (relKoszulType A E V j))

/-- The differential of the relative Koszul complex. -/
def relKoszulDiff (j : ℕ) :
    relKoszulType A E V (j + 1) →ₗ[MvPolynomial E (MvPolynomial E A)] relKoszulType A E V j :=
  TensorProduct.AlgebraTensorModule.map
    (Koszul.d (variableKoszulDual (MvPolynomial E A) E) j) LinearMap.id

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The differential of the relative Koszul complex is the Koszul differential on the first
factor of a pure tensor. -/
@[simp]
lemma relKoszulDiff_tmul (j : ℕ)
    (ω : ⋀[MvPolynomial E (MvPolynomial E A)]^(j + 1)
      (E →₀ MvPolynomial E (MvPolynomial E A))) (v : V) :
    relKoszulDiff A E V j (ω ⊗ₜ v) =
      (Koszul.d (variableKoszulDual (MvPolynomial E A) E) j ω) ⊗ₜ v := rfl

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- Two consecutive differentials of the relative Koszul complex compose to zero. -/
lemma relKoszulDiff_comp_relKoszulDiff (j : ℕ) :
    (relKoszulDiff A E V j).comp (relKoszulDiff A E V (j + 1)) = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v =>
    simp only [LinearMap.comp_apply, relKoszulDiff_tmul, LinearMap.zero_apply]
    rw [show Koszul.d (variableKoszulDual (MvPolynomial E A) E) j
        (Koszul.d (variableKoszulDual (MvPolynomial E A) E) (j + 1) ω) = 0 from
      LinearMap.congr_fun (Koszul.d_comp_d (variableKoszulDual (MvPolynomial E A) E) j) ω]
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy => simp only [map_add, hx, hy, add_zero, LinearMap.zero_apply]

/-- The relative Koszul complex of `V`. -/
def relKoszulComplex : ChainComplex (ModuleCat.{max u v} (MvPolynomial E A)) ℕ :=
  ChainComplex.of (relKoszulTerm A E V)
    (fun j => (ModuleCat.restrictScalars (diagShift A E)).map
      (ModuleCat.ofHom (relKoszulDiff A E V j)))
    (fun j => by
      have h : (ModuleCat.ofHom (relKoszulDiff A E V (j + 1))) ≫
          (ModuleCat.ofHom (relKoszulDiff A E V j)) = 0 := by
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
        exact relKoszulDiff_comp_relKoszulDiff A E V j
      rw [← Functor.map_comp, h, Functor.map_zero])

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The differential `j + 1 → j` of `relKoszulComplex` is `relKoszulDiff` with scalars
restricted along `diagShift`. -/
lemma relKoszulComplex_d (j : ℕ) :
    (relKoszulComplex A E V).d (j + 1) j =
      (ModuleCat.restrictScalars (diagShift A E)).map
        (ModuleCat.ofHom (relKoszulDiff A E V j)) :=
  ChainComplex.of_d (relKoszulTerm A E V)
    (fun j => (ModuleCat.restrictScalars (diagShift A E)).map
      (ModuleCat.ofHom (relKoszulDiff A E V j))) j

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The differential `j + 1 → j` of `relKoszulComplex` acts on elements as `relKoszulDiff`. -/
lemma relKoszulComplex_d_apply (j : ℕ) (z : relKoszulType A E V (j + 1)) :
    ((relKoszulComplex A E V).d (j + 1) j) z = relKoszulDiff A E V j z :=
  ConcreteCategory.congr_hom (relKoszulComplex_d A E V j) z

/-! ### The contracting homotopy -/

/-- The contraction of the relative Koszul complex, additive only. -/
def relKoszulContract (j : ℕ) :
    relKoszulType A E V j →ₗ[MvPolynomial E A] relKoszulType A E V (j + 1) :=
  LinearMap.rTensor V (variableKoszulChosenContract (MvPolynomial E A) E j)

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The contraction of the relative Koszul complex is `variableKoszulChosenContract` on the
first factor of a pure tensor. -/
@[simp]
lemma relKoszulContract_tmul (j : ℕ)
    (ω : ⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A)))
    (v : V) :
    relKoszulContract A E V j (ω ⊗ₜ v) =
      (variableKoszulChosenContract (MvPolynomial E A) E j ω) ⊗ₜ v :=
  LinearMap.rTensor_tmul _ _ _ _

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The homotopy identity in positive degree. -/
lemma relKoszulContract_homotopy (q : ℕ) (z : relKoszulType A E V (q + 1)) :
    relKoszulDiff A E V (q + 1) (relKoszulContract A E V (q + 1) z) +
      relKoszulContract A E V q (relKoszulDiff A E V q z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v =>
    rw [relKoszulContract_tmul, relKoszulDiff_tmul, relKoszulDiff_tmul,
      relKoszulContract_tmul, ← TensorProduct.add_tmul,
      variableKoszulChosenContract_homotopy (MvPolynomial E A) E q ω]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]

/-! ### The augmentation -/

/-- The augmentation `S → T` of the second polynomial ring, as a `T`-linear map through the
coefficient inclusion. -/
def relAugLinear : MvPolynomial E (MvPolynomial E A) →ₗ[MvPolynomial E A] MvPolynomial E A where
  toFun := MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A)
  map_add' := map_add _
  map_smul' t s := by
    have h : (t • s : MvPolynomial E (MvPolynomial E A)) = MvPolynomial.C t * s := by
      rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    change MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A)
        (t • s) = (RingHom.id (MvPolynomial E A)) t •
      MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A) s
    rw [h, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply, smul_eq_mul]

omit [LinearOrder E] in
/-- `relAugLinear` evaluates a polynomial over `T` at `0`. -/
@[simp]
lemma relAugLinear_apply (s : MvPolynomial E (MvPolynomial E A)) :
    relAugLinear A E s =
      MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A) s := rfl

/-- The augmentation `⋀⁰ → T` of the Koszul complex of the variables of `S`, as a `T`-linear
map. -/
def relKoszulAugDegZero :
    (⋀[MvPolynomial E (MvPolynomial E A)]^0 (E →₀ MvPolynomial E (MvPolynomial E A)))
      →ₗ[MvPolynomial E A] MvPolynomial E A :=
  (relAugLinear A E).comp
    ((variableKoszulAug (MvPolynomial E A) E).restrictScalars (MvPolynomial E A))

/-- The augmentation of the relative Koszul complex, as a map linear over the coefficient
inclusion. -/
def relKoszulAug : relKoszulType A E V 0 →ₗ[MvPolynomial E A] V :=
  (TensorProduct.lid (MvPolynomial E A) V).toLinearMap.comp
    (LinearMap.rTensor V (relKoszulAugDegZero A E))

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The augmentation sends `ω ⊗ v` to `relKoszulAugDegZero ω • v`. -/
@[simp]
lemma relKoszulAug_tmul
    (ω : ⋀[MvPolynomial E (MvPolynomial E A)]^0 (E →₀ MvPolynomial E (MvPolynomial E A)))
    (v : V) :
    relKoszulAug A E V (ω ⊗ₜ v) = relKoszulAugDegZero A E ω • v := by
  rw [relKoszulAug, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  exact TensorProduct.lid_tmul _ _


/-- The unit of the relative Koszul complex. -/
def relKoszulUnit : V →ₗ[MvPolynomial E A] relKoszulType A E V 0 where
  toFun v := (variableKoszulUnit (MvPolynomial E A) E 1) ⊗ₜ v
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_smul' t v := by
    change (variableKoszulUnit (MvPolynomial E A) E 1) ⊗ₜ (t • v) =
      t • ((variableKoszulUnit (MvPolynomial E A) E 1) ⊗ₜ v)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]

omit [LinearOrder E] in
/-- The unit of the Koszul complex of the variables at `t` is `t` times its value at `1`. -/
lemma variableKoszulUnit_eq_smul (t : MvPolynomial E A) :
    variableKoszulUnit (MvPolynomial E A) E t =
      t • variableKoszulUnit (MvPolynomial E A) E 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The unit of the relative Koszul complex sends `t • v` to `variableKoszulUnit t ⊗ v`. -/
@[simp]
lemma relKoszulUnit_smul (t : MvPolynomial E A) (v : V) :
    relKoszulUnit A E V (t • v) = (variableKoszulUnit (MvPolynomial E A) E t) ⊗ₜ v := by
  show (variableKoszulUnit (MvPolynomial E A) E 1) ⊗ₜ (t • v) = _
  rw [← TensorProduct.smul_tmul, ← variableKoszulUnit_eq_smul]

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The homotopy identity in degree zero. -/
lemma relKoszulContract_homotopy_zero (z : relKoszulType A E V 0) :
    relKoszulDiff A E V 0 (relKoszulContract A E V 0 z) +
      relKoszulUnit A E V (relKoszulAug A E V z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v =>
    rw [relKoszulContract_tmul, relKoszulDiff_tmul, relKoszulAug_tmul, relKoszulUnit_smul,
      ← TensorProduct.add_tmul]
    congr 1
    exact variableKoszulChosenContract_homotopy_zero_augmented (MvPolynomial E A) E ω
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The unit is a section of the augmentation. -/
@[simp]
lemma relKoszulAug_relKoszulUnit (v : V) : relKoszulAug A E V (relKoszulUnit A E V v) = v := by
  show relKoszulAug A E V ((variableKoszulUnit (MvPolynomial E A) E 1) ⊗ₜ v) = v
  rw [relKoszulAug_tmul]
  have h : relKoszulAugDegZero A E (variableKoszulUnit (MvPolynomial E A) E 1) = 1 := by
    rw [relKoszulAugDegZero, LinearMap.comp_apply]
    show relAugLinear A E (variableKoszulAug (MvPolynomial E A) E
      (variableKoszulUnit (MvPolynomial E A) E 1)) = 1
    rw [variableKoszulAug_unit, relAugLinear_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
  rw [h, one_smul]

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The augmentation of the relative Koszul complex is surjective. -/
lemma relKoszulAug_surjective : Function.Surjective (relKoszulAug A E V) :=
  fun v => ⟨relKoszulUnit A E V v, relKoszulAug_relKoszulUnit A E V v⟩

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The augmentation vanishes on the image of the differential `1 → 0`. -/
lemma relKoszulAug_relKoszulDiff (z : relKoszulType A E V 1) :
    relKoszulAug A E V (relKoszulDiff A E V 0 z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v =>
    rw [relKoszulDiff_tmul, relKoszulAug_tmul]
    rw [show relKoszulAugDegZero A E
        (Koszul.d (variableKoszulDual (MvPolynomial E A) E) 0 ω) = 0 from
      variableKoszulAug_d_zero (MvPolynomial E A) E ω]
    exact zero_smul _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- In positive degree, an element of the relative Koszul complex is a boundary if and only if it
is a cycle. -/
lemma relKoszul_mem_range_iff (q : ℕ) (z : relKoszulType A E V (q + 1)) :
    (∃ y, relKoszulDiff A E V (q + 1) y = z) ↔ relKoszulDiff A E V q z = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (relKoszulDiff_comp_relKoszulDiff A E V q) y
  · intro hdz
    have h := relKoszulContract_homotopy A E V q z
    rw [hdz, map_zero, add_zero] at h
    exact ⟨relKoszulContract A E V (q + 1) z, h⟩

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- In degree zero, an element of the relative Koszul complex is a boundary if and only if its
augmentation vanishes. -/
lemma relKoszul_mem_range_iff_aug_eq_zero (z : relKoszulType A E V 0) :
    (∃ y, relKoszulDiff A E V 0 y = z) ↔ relKoszulAug A E V z = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact relKoszulAug_relKoszulDiff A E V y
  · intro hdz
    have h := relKoszulContract_homotopy_zero A E V z
    rw [hdz, map_zero, add_zero] at h
    exact ⟨relKoszulContract A E V 0 z, h⟩

/-! ### The resolution -/

omit [LinearOrder E] in
/-- The augmentation `S → T` is a retraction of `diagShift`. -/
lemma relAugLinear_diagShift (t : MvPolynomial E A) :
    relAugLinear A E (diagShift A E t) = t := by
  have h : (MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A))
        (0 : E → MvPolynomial E A)).comp (diagShift A E) =
      RingHom.id (MvPolynomial E A) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      show MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A)
        (diagShift A E (MvPolynomial.C a)) = _
      simp [diagShift]
    · intro e
      show MvPolynomial.eval₂Hom (RingHom.id (MvPolynomial E A)) (0 : E → MvPolynomial E A)
        (diagShift A E (MvPolynomial.X e)) = _
      simp [diagShift]
  exact DFunLike.congr_fun h t

omit [LinearOrder E] in
/-- `relKoszulAugDegZero` is `T`-linear for the action of `T` through `diagShift`. -/
lemma relKoszulAugDegZero_diagShift_smul (t : MvPolynomial E A)
    (ω : ⋀[MvPolynomial E (MvPolynomial E A)]^0 (E →₀ MvPolynomial E (MvPolynomial E A))) :
    relKoszulAugDegZero A E (diagShift A E t • ω) = t * relKoszulAugDegZero A E ω := by
  show relAugLinear A E ((exteriorPower.zeroEquiv _ _) (diagShift A E t • ω)) =
    t * relAugLinear A E ((exteriorPower.zeroEquiv _ _) ω)
  rw [map_smul, smul_eq_mul, relAugLinear_apply, relAugLinear_apply, map_mul]
  congr 1
  exact relAugLinear_diagShift A E t

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The augmentation is `T`-linear for the action of `T` through `diagShift`. -/
lemma relKoszulAug_diagShift_smul (t : MvPolynomial E A) (z : relKoszulType A E V 0) :
    relKoszulAug A E V (diagShift A E t • z) = t • relKoszulAug A E V z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v =>
    rw [show diagShift A E t • (ω ⊗ₜ[MvPolynomial E A] v) = (diagShift A E t • ω) ⊗ₜ v from
      TensorProduct.smul_tmul' _ _ _]
    rw [relKoszulAug_tmul, relKoszulAug_tmul, relKoszulAugDegZero_diagShift_smul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The augmentation of the relative Koszul complex, as a morphism of `T`-modules. -/
def relKoszulAugHom : relKoszulTerm A E V 0 ⟶ ModuleCat.of (MvPolynomial E A) V :=
  (ModuleCat.homEquiv (M := relKoszulTerm A E V 0)
      (N := ModuleCat.of (MvPolynomial E A) V)).symm
    { toFun := fun z => relKoszulAug A E V z
      map_add' := fun a b => map_add (relKoszulAug A E V) a b
      map_smul' := fun t z => relKoszulAug_diagShift_smul A E V t z }

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The differential `1 → 0` followed by the augmentation is zero. -/
lemma relKoszulAugHom_comp_d :
    (relKoszulComplex A E V).d 1 0 ≫ relKoszulAugHom A E V = 0 := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun z => ?_
  show relKoszulAug A E V (((relKoszulComplex A E V).d 1 0) z) = 0
  exact (congrArg (relKoszulAug A E V) (relKoszulComplex_d_apply A E V 0 z)).trans
    (relKoszulAug_relKoszulDiff A E V z)

/-- The augmentation of the relative Koszul complex, as a map to the complex concentrated in
degree zero. -/
def relKoszulPi : relKoszulComplex A E V ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v} (MvPolynomial E A))).obj
      (ModuleCat.of (MvPolynomial E A) V) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨relKoszulAugHom A E V, relKoszulAugHom_comp_d A E V⟩

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The degree-zero component of `relKoszulPi` is `relKoszulAugHom`. -/
@[simp]
lemma relKoszulPi_f_zero : (relKoszulPi A E V).f 0 = relKoszulAugHom A E V :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := relKoszulComplex A E V)
    (X := ModuleCat.of (MvPolynomial E A) V) (relKoszulAugHom A E V)
    (relKoszulAugHom_comp_d A E V)

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The differential `1 → 0` of `relKoszulComplex` acts on elements as `relKoszulDiff`. -/
lemma relKoszulComplex_d_one_zero (z : relKoszulType A E V 1) :
    ((relKoszulComplex A E V).d 1 0) z = relKoszulDiff A E V 0 z :=
  relKoszulComplex_d_apply A E V 0 z

/-- Two linear maps agreeing with functions `F`, `G` have `range f = ker g` once `F`'s image is
the zero set of `G`. -/
private theorem range_eq_ker_of_forall_exists_iff {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (F : M → N) (G : N → P) (hf : ∀ y, f y = F y)
    (hg : ∀ z, g z = G z) (h : ∀ z, (∃ y, F y = z) ↔ G z = 0) :
    LinearMap.range f = LinearMap.ker g :=
  Submodule.ext fun z => by simp only [LinearMap.mem_range, LinearMap.mem_ker, hf, hg]; exact h z

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The image of the differential `1 → 0` is the kernel of the augmentation. -/
lemma relKoszulComplex_range_eq_ker_zero :
    LinearMap.range ((relKoszulComplex A E V).d 1 0).hom =
      LinearMap.ker (relKoszulAugHom A E V).hom :=
  range_eq_ker_of_forall_exists_iff _ _ _ _ (relKoszulComplex_d_one_zero A E V) (fun _ => rfl)
    (relKoszul_mem_range_iff_aug_eq_zero A E V)

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The relative Koszul complex is exact in each positive degree. -/
lemma relKoszulComplex_range_eq_ker_succ (q : ℕ) :
    LinearMap.range ((relKoszulComplex A E V).d (q + 2) (q + 1)).hom =
      LinearMap.ker ((relKoszulComplex A E V).d (q + 1) q).hom :=
  range_eq_ker_of_forall_exists_iff _ _ _ _ (relKoszulComplex_d_apply A E V (q + 1))
    (relKoszulComplex_d_apply A E V q) (relKoszul_mem_range_iff A E V q)

omit [Module A V] [IsScalarTower A (MvPolynomial E A) V] in
/-- The augmentation of the relative Koszul complex to `V` in degree zero is a
quasi-isomorphism. -/
lemma relKoszulPi_quasiIso : QuasiIso (relKoszulPi A E V) := by
  refine ⟨fun j ↦ ?_⟩
  cases j with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    exact ⟨.moduleCat_of_range_eq_ker _ _ (relKoszulComplex_range_eq_ker_zero A E V),
      (ModuleCat.epi_iff_surjective _).2 (relKoszulAug_surjective A E V)⟩
  | succ q =>
    rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
    exact (HomologicalComplex.exactAt_iff' (relKoszulComplex A E V)
      (i := q + 2) (j := q + 1) (k := q) (by simp) (by simp)).2
      (.moduleCat_of_range_eq_ker _ _ (relKoszulComplex_range_eq_ker_succ A E V q))

/-! ### Functoriality in the module -/

section Functoriality

variable {V} {V' : Type max u v} [AddCommGroup V'] [Module A V']
  [Module (MvPolynomial E A) V'] [IsScalarTower A (MvPolynomial E A) V']

/-- The map of relative Koszul terms induced by a `T`-linear map. -/
def relKoszulMapTerm (f : V →ₗ[MvPolynomial E A] V') (j : ℕ) :
    relKoszulType A E V j →ₗ[MvPolynomial E (MvPolynomial E A)] relKoszulType A E V' j :=
  TensorProduct.AlgebraTensorModule.map LinearMap.id f

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] [Module A V']
  [IsScalarTower A (MvPolynomial E A) V'] in
/-- `relKoszulMapTerm f` sends `ω ⊗ v` to `ω ⊗ f v`. -/
@[simp]
lemma relKoszulMapTerm_tmul (f : V →ₗ[MvPolynomial E A] V') (j : ℕ)
    (ω : ⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A)))
    (v : V) :
    relKoszulMapTerm A E f j (ω ⊗ₜ v) = ω ⊗ₜ (f v) := rfl

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] [Module A V']
  [IsScalarTower A (MvPolynomial E A) V'] in
/-- The maps `relKoszulMapTerm f` commute with the differentials. -/
lemma relKoszulMapTerm_comm (f : V →ₗ[MvPolynomial E A] V') (j : ℕ) :
    (relKoszulMapTerm A E f j).comp (relKoszulDiff A E V j) =
      (relKoszulDiff A E V' j).comp (relKoszulMapTerm A E f (j + 1)) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The chain map of relative Koszul complexes induced by a `T`-linear map. -/
def relKoszulMap (f : V →ₗ[MvPolynomial E A] V') :
    relKoszulComplex A E V ⟶ relKoszulComplex A E V' where
  f j := (ModuleCat.restrictScalars (diagShift A E)).map
    (ModuleCat.ofHom (relKoszulMapTerm A E f j))
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    have h1 : (relKoszulComplex A E V').d (j + 1) j (relKoszulMapTerm A E f (j + 1) z)
        = relKoszulDiff A E V' j (relKoszulMapTerm A E f (j + 1) z) :=
      relKoszulComplex_d_apply A E V' j _
    have h2 : (relKoszulComplex A E V).d (j + 1) j z = relKoszulDiff A E V j z :=
      relKoszulComplex_d_apply A E V j z
    change (relKoszulComplex A E V').d (j + 1) j (relKoszulMapTerm A E f (j + 1) z) =
      relKoszulMapTerm A E f j ((relKoszulComplex A E V).d (j + 1) j z)
    rw [h1, congrArg (relKoszulMapTerm A E f j) h2]
    exact LinearMap.congr_fun (relKoszulMapTerm_comm A E f j).symm z

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] [Module A V']
  [IsScalarTower A (MvPolynomial E A) V'] in
/-- The augmentation commutes with the degree-zero map induced by `f`. -/
lemma relKoszulAug_relKoszulMapTerm (f : V →ₗ[MvPolynomial E A] V')
    (z : relKoszulType A E V 0) :
    relKoszulAug A E V' (relKoszulMapTerm A E f 0 z) = f (relKoszulAug A E V z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω v => rw [relKoszulMapTerm_tmul, relKoszulAug_tmul, relKoszulAug_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [LinearOrder E] [Module A V] [IsScalarTower A (MvPolynomial E A) V] [Module A V']
  [IsScalarTower A (MvPolynomial E A) V'] in
/-- The chain map induced by a `T`-linear map lifts that map. -/
lemma relKoszulMap_pi (f : V →ₗ[MvPolynomial E A] V') :
    relKoszulMap A E f ≫ relKoszulPi A E V' =
      relKoszulPi A E V ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} (MvPolynomial E A))).map
          (ModuleCat.ofHom f) := by
  apply (ChainComplex.toSingle₀Equiv (relKoszulComplex A E V) _).injective
  apply Subtype.ext
  show (relKoszulMap A E f ≫ relKoszulPi A E V').f 0 =
    (relKoszulPi A E V ≫ (ChainComplex.single₀ (ModuleCat.{max u v} (MvPolynomial E A))).map
      (ModuleCat.ofHom f)).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relKoszulPi_f_zero,
    relKoszulPi_f_zero, ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun z => ?_
  show relKoszulAug A E V' (relKoszulMapTerm A E f 0 z) = f (relKoszulAug A E V z)
  exact relKoszulAug_relKoszulMapTerm A E f z

end Functoriality

/-! ### The comparison with the Koszul complex over `T` -/

/-- The `T`-linear map `(E →₀ T) → (E →₀ S)` induced by the coefficient inclusion. -/
def coeffFinsuppMap : (E →₀ MvPolynomial E A) →ₗ[MvPolynomial E A]
    (E →₀ MvPolynomial E (MvPolynomial E A)) :=
  Finsupp.mapRange.linearMap
    (Algebra.linearMap (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A)))

/-- The `S`-dual sending the `e`-th basis vector to the image of the `e`-th variable of `T`. -/
def coeffVariableDual : Module.Dual (MvPolynomial E (MvPolynomial E A))
    (E →₀ MvPolynomial E (MvPolynomial E A)) :=
  Finsupp.linearCombination _ fun e => MvPolynomial.C (MvPolynomial.X e : MvPolynomial E A)

/-- The `S`-dual sending the `e`-th basis vector to `diagShift` of the `e`-th variable. -/
def diagShiftVariableDual : Module.Dual (MvPolynomial E (MvPolynomial E A))
    (E →₀ MvPolynomial E (MvPolynomial E A)) :=
  Finsupp.linearCombination _ fun e => diagShift A E (MvPolynomial.X e)

omit [LinearOrder E] in
/-- `diagShift` sends the variable `X e` to `X e + C (X e)`. -/
lemma diagShift_X (e : E) :
    diagShift A E (MvPolynomial.X e) =
      (MvPolynomial.X e : MvPolynomial E (MvPolynomial E A)) +
        MvPolynomial.C (MvPolynomial.X e) := by
  simp [diagShift]

omit [LinearOrder E] in
/-- The sum of `variableKoszulDual` and `coeffVariableDual` is `diagShiftVariableDual`. -/
lemma variableKoszulDual_add_coeffVariableDual :
    variableKoszulDual (MvPolynomial E A) E + coeffVariableDual A E =
      diagShiftVariableDual A E := by
  refine Finsupp.lhom_ext' fun e => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    variableKoszulDual, coeffVariableDual, diagShiftVariableDual,
    Finsupp.linearCombination_single, one_smul, diagShift_X]

omit [LinearOrder E] in
/-- `coeffVariableDual` restricted along `coeffFinsuppMap` is the image in `S` of the
variable dual over `T`. -/
lemma coeffVariableDual_coeffFinsuppMap (w : E →₀ MvPolynomial E A) :
    coeffVariableDual A E (coeffFinsuppMap A E w) =
      algebraMap (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A))
        (variableKoszulDual A E w) := by
  classical
  show (Finsupp.linearCombination _ fun e => MvPolynomial.C (MvPolynomial.X e : MvPolynomial E A))
      (Finsupp.mapRange (algebraMap (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A)))
        (map_zero _) w) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  show (w.sum fun e t => MvPolynomial.C t * MvPolynomial.C (MvPolynomial.X e)) = _
  rw [show variableKoszulDual A E w = w.sum fun e t => t * MvPolynomial.X e from by
    rw [variableKoszulDual, Finsupp.linearCombination_apply]; rfl]
  rw [map_finsuppSum]
  refine Finset.sum_congr rfl fun e _ => ?_
  show MvPolynomial.C (w e) * MvPolynomial.C (MvPolynomial.X e) =
    algebraMap (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A))
      (w e * MvPolynomial.X e)
  rw [map_mul, MvPolynomial.algebraMap_eq]

/-- The base-change map from the Koszul terms over `T` to those over `S`. -/
def koszulBaseChange (j : ℕ) :
    (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) →ₗ[MvPolynomial E A]
      (⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A))) :=
  Koszul.baseChangeMap (coeffFinsuppMap A E) j

omit [LinearOrder E] in
/-- `koszulBaseChange` intertwines the Koszul differential of the variables of `T` with the
Koszul differential of `coeffVariableDual`. -/
lemma koszulBaseChange_d (j : ℕ) (ω : ⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) :
    koszulBaseChange A E j (Koszul.d (variableKoszulDual A E) j ω) =
      Koszul.d (coeffVariableDual A E) j (koszulBaseChange A E (j + 1) ω) :=
  Koszul.baseChangeMap_d (coeffFinsuppMap A E) (variableKoszulDual A E)
    (coeffVariableDual A E) (coeffVariableDual_coeffFinsuppMap A E) j ω

omit [LinearOrder E] in
/-- The Koszul differential of the variables of `S` is the difference of the Koszul
differentials of `diagShiftVariableDual` and `coeffVariableDual`. -/
lemma koszul_d_variableKoszulDual_eq (j : ℕ)
    (ξ : ⋀[MvPolynomial E (MvPolynomial E A)]^(j + 1)
      (E →₀ MvPolynomial E (MvPolynomial E A))) :
    Koszul.d (variableKoszulDual (MvPolynomial E A) E) j ξ =
      Koszul.d (diagShiftVariableDual A E) j ξ - Koszul.d (coeffVariableDual A E) j ξ := by
  have h := Koszul.d_add (variableKoszulDual (MvPolynomial E A) E) (coeffVariableDual A E) j
  rw [variableKoszulDual_add_coeffVariableDual] at h
  have h' := LinearMap.congr_fun h ξ
  rw [LinearMap.add_apply] at h'
  rw [h']
  abel

/-! ### Coordinates on the terms -/

/-- The degree-`j` term of the relative Koszul complex is `A`-linearly isomorphic to
`{s : Finset E // s.card = j} →₀ T ⊗[A] V`, by an isomorphism that is `T`-linear for the action
of `T` through `diagShift` and sends `b s ⊗ v` to `single s (1 ⊗ v)`, where `b` is the
exterior-power basis. -/
theorem exists_relKoszulCoordEquiv (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (V : Type max u v) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
    [IsScalarTower A (MvPolynomial E A) V] :
    ∃ e : (MvPolynomial.relKoszulType A E V j) ≃ₗ[A]
        ({s : Finset E // s.card = j} →₀ (MvPolynomial E A ⊗[A] V)),
      (∀ (t : MvPolynomial E A) (x : MvPolynomial.relKoszulType A E V j),
          e (MvPolynomial.diagShift A E t • x) = t • e x) ∧
      (∀ (s : {s : Finset E // s.card = j}) (v : V),
          e (((Finsupp.basisSingleOne (R := MvPolynomial E (MvPolynomial E A))
              (ι := E)).exteriorPower j s) ⊗ₜ v) = Finsupp.single s (1 ⊗ₜ v)) := by
  classical
  let b : Module.Basis {s : Finset E // s.card = j} (MvPolynomial E (MvPolynomial E A))
      (⋀[MvPolynomial E (MvPolynomial E A)]^j (E →₀ MvPolynomial E (MvPolynomial E A))) :=
    (Finsupp.basisSingleOne (R := MvPolynomial E (MvPolynomial E A)) (ι := E)).exteriorPower j
  let e₁ : (relKoszulType A E V j) ≃ₗ[MvPolynomial E (MvPolynomial E A)]
      ({s : Finset E // s.card = j} →₀
        (MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V)) :=
    (TensorProduct.AlgebraTensorModule.congr b.repr
      (LinearEquiv.refl (MvPolynomial E A) V)).trans
      (TensorProduct.finsuppLeft (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A))
        (MvPolynomial E (MvPolynomial E A)) V {s : Finset E // s.card = j})
  have he₁ : ∀ (s : {s : Finset E // s.card = j}) (v : V),
      e₁ (b s ⊗ₜ v) = Finsupp.single s (1 ⊗ₜ v) := by
    intro s v
    show TensorProduct.finsuppLeft (MvPolynomial E A) (MvPolynomial E (MvPolynomial E A))
      (MvPolynomial E (MvPolynomial E A)) V {s : Finset E // s.card = j}
      (b.repr (b s) ⊗ₜ v) = _
    rw [Module.Basis.repr_self]
    refine Finsupp.ext fun i => ?_
    rw [TensorProduct.finsuppLeft_apply_tmul_apply]
    by_cases h : s = i
    · rw [h, Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne' h, Finsupp.single_eq_of_ne' h, TensorProduct.zero_tmul]
  have hsingle : ∀ (s : {s : Finset E // s.card = j})
      (x : MvPolynomial E (MvPolynomial E A) ⊗[MvPolynomial E A] V),
      Finsupp.mapRange.linearEquiv (TwoCopy.fullEquiv A E V) (Finsupp.single s x) =
        Finsupp.single s (TwoCopy.fullEquiv A E V x) := fun _ _ =>
    Finsupp.mapRange_single (hf := map_zero (TwoCopy.fullEquiv A E V))
  refine ⟨(e₁.restrictScalars A).trans
    (Finsupp.mapRange.linearEquiv (TwoCopy.fullEquiv A E V)), fun t x => ?_, fun s v => ?_⟩
  · have h : e₁ (diagShift A E t • x) = diagShift A E t • e₁ x := e₁.map_smul _ x
    show Finsupp.mapRange.linearEquiv (TwoCopy.fullEquiv A E V) (e₁ (diagShift A E t • x)) =
      t • Finsupp.mapRange.linearEquiv (TwoCopy.fullEquiv A E V) (e₁ x)
    rw [h]
    exact Finsupp.ext fun i => TwoCopy.fullEquiv_smul A E V t (e₁ x i)
  · show Finsupp.mapRange.linearEquiv (TwoCopy.fullEquiv A E V) (e₁ (b s ⊗ₜ v)) =
      Finsupp.single s (1 ⊗ₜ v)
    rw [he₁ s v, hsingle, TwoCopy.fullEquiv_one_tmul]

/-- **The terms of the relative Koszul complex are projective.** With `T = A[E]` and `S = T[E]`,
the degree-`j` term of the relative Koszul complex of a `T`-module `V`, regarded as a
`T`-module through `diagShift`, is a projective object of `ModuleCat T` as soon as `V` is a free
`A`-module. -/
theorem projective_relKoszulTerm (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (V : Type max u v) [AddCommGroup V] [Module A V] [Module (MvPolynomial E A) V]
    [IsScalarTower A (MvPolynomial E A) V] [Module.Free A V] :
    CategoryTheory.Projective (MvPolynomial.relKoszulTerm A E V j) := by
  obtain ⟨e, hsmul, -⟩ := exists_relKoszulCoordEquiv A E j V
  have e' : (relKoszulTerm A E V j) ≃ₗ[MvPolynomial E A]
      ({s : Finset E // s.card = j} →₀ (MvPolynomial E A ⊗[A] V)) :=
    { toFun := e.toFun
      map_add' := e.map_add'
      map_smul' := hsmul
      invFun := e.invFun
      left_inv := e.left_inv
      right_inv := e.right_inv }
  have : Module.Projective (MvPolynomial E A) (relKoszulTerm A E V j) :=
    Module.Projective.of_equiv' e'.symm
  infer_instance

/-- **The relative Koszul resolution.**  For a `T`-module `V` which is free over `A`, the Koszul
complex of the variables of `S = T[E]`, tensored over `T` with `V` and regarded as a `T`-module
through `diagShift`, is a projective resolution of `V`. -/
def relKoszulResolution [Module.Free A V] :
    ProjectiveResolution (ModuleCat.of (MvPolynomial E A) V) where
  complex := relKoszulComplex A E V
  projective j := projective_relKoszulTerm A E j V
  π := relKoszulPi A E V
  quasiIso := relKoszulPi_quasiIso A E V

end MvPolynomial

end
