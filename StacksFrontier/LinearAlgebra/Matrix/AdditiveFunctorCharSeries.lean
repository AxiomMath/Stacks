module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace
public import StacksFrontier.LinearAlgebra.Matrix.CharSeriesTraceDetection

/-!
# Characteristic series and traces through an additive functor

Let `R` be a ring, `Λ` a commutative ring and `Φ : Mod_R ⥤ Mod_Λ` an additive functor, and let
`O` be a free `R`-module of rank one with a basis `b` of `Φ(O)` over `Λ` of rank `r`. Right
multiplication by `s ∈ R` on `O` is `R`-linear, and the transpose of the matrix of its image
under `Φ` is a ring homomorphism `φ : R →+* M_r(Λ)` (`Stacks.CharSeriesTraceDetection.functorRep`).

For an endomorphism `F` of the free module `n → O` with matrix `A ∈ M_n(R)`
(`F(v) = v ⬝ A`), the matrix of `Φ(F)` in the basis induced by `b` is the transpose of the
block matrix `φ(A)`, so that

`det(1 - Φ(F) T) = det(1 - φ(A) T)`,

and for a finite projective module `P`, a retract of `n → O`, and an endomorphism `f` of `P`
with matrix `A` of `i ∘ f ∘ p`, both `det(1 - Φ(f) T)` and the traces `Tr(f ^ m) ∈ R^♮` are read
off `A`. This is the dictionary that turns the characteristic series of `π_X^*` on
`RΓ_c(Z_k̄, F) ≅ Φ(Q)` and the traces of its powers on a perfect `R`-complex `Q` into the two
sides of the key lemma `Stacks.CharSeriesTraceDetection.coeff_det_eq_of_trace_pow`.

## Main results

* `Stacks.CharSeriesTraceDetection.freeModuleTrace_eq_trq` and
  `Stacks.CharSeriesTraceDetection.projectiveModuleTrace_pow_eq_trq`: traces of powers.
* `Stacks.CharSeriesTraceDetection.charSeries_functor_map_eq_det`: `det(1 - Φ(F) T)` on a free
  module.
* `Stacks.CharSeriesTraceDetection.charSeries_functor_map_retract`: on a retract of a free
  module.
-/

@[expose] public noncomputable section

open CategoryTheory Matrix PowerSeries
open CategoryTheory.FilteredDerived

universe u v v' w

namespace Stacks.CharSeriesTraceDetection

/-! ### The matrix of an endomorphism of a free left module -/

section EndMatrix

variable {R : Type u} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix `A` of an endomorphism `F` of the free left module `n → R`, with `F(v) = v ⬝ A`:
its `i`-th row is `F(eᵢ)`. -/
def endMatrix (F : (n → R) →ₗ[R] (n → R)) : Matrix n n R :=
  Matrix.of fun i j => F (Pi.single i 1) j

omit [Fintype n] in
/-- The `(i, j)` entry of `endMatrix F` is the `j`-th coordinate of `F(eᵢ)`. -/
theorem endMatrix_apply (F : (n → R) →ₗ[R] (n → R)) (i j : n) :
    endMatrix F i j = F (Pi.single i 1) j := rfl

/-- An endomorphism `F` of `n → R` acts by `F(v) = v ⬝ endMatrix F`. -/
theorem apply_eq_vecMul (F : (n → R) →ₗ[R] (n → R)) (v : n → R) : F v = v ᵥ* endMatrix F := by
  have hv : v = ∑ i, v i • Pi.single i (1 : R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  ext j
  simp [map_sum, map_smul, Matrix.vecMul, dotProduct, endMatrix, Finset.sum_apply]

/-- The matrix of `F ∘ G` is the product `endMatrix G * endMatrix F`. -/
theorem endMatrix_comp (F G : (n → R) →ₗ[R] (n → R)) :
    endMatrix (F ∘ₗ G) = endMatrix G * endMatrix F := by
  ext i j
  rw [endMatrix_apply, LinearMap.comp_apply, apply_eq_vecMul F]
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, endMatrix]

omit [Fintype n] in
/-- The matrix of the identity is the identity matrix. -/
theorem endMatrix_id : endMatrix (LinearMap.id : (n → R) →ₗ[R] (n → R)) = 1 := by
  ext i j
  simp [endMatrix, Pi.single_apply, Matrix.one_apply, eq_comm]

/-- The matrix of `F ^ m` is the `m`-th power of the matrix of `F`. -/
theorem endMatrix_pow (F : Module.End R (n → R)) (m : ℕ) :
    endMatrix (F ^ m) = endMatrix F ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, endMatrix_id]
  | succ m ih => rw [pow_succ, Module.End.mul_eq_comp, endMatrix_comp, ih, pow_succ']

/-- The trace of an endomorphism of `n → R` is the class of the trace of its matrix. -/
theorem freeModuleTrace_eq_trq (F : Module.End R (n → R)) :
    freeModuleTrace R n F = trq n (endMatrix F) := by
  classical
  rw [freeModuleTrace_apply, trq_apply, Matrix.trace]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, endMatrix_apply, standardBasisVector]
  exact congrArg (fun v => F v i)
    (by ext k; rcases eq_or_ne k i with rfl | h <;> simp [*])

end EndMatrix

/-! ### A rank one free module -/

section RankOne

variable {R : Type u} [Ring R] {O : Type v} [AddCommGroup O] [Module R O] (eO : R ≃ₗ[R] O)

/-- Right multiplication by `s` on a free module `O` of rank one, `x ↦ x ⬝ s` in the
coordinate `eO`. -/
def rightMul (s : R) : O →ₗ[R] O where
  toFun x := eO (eO.symm x * s)
  map_add' x y := by rw [map_add, add_mul, map_add]
  map_smul' c x := by
    rw [map_smul, smul_eq_mul, mul_assoc, ← smul_eq_mul, map_smul, RingHom.id_apply]

/-- `rightMul eO s` sends `x` to `eO (eO.symm x * s)`. -/
theorem rightMul_apply (s : R) (x : O) : rightMul eO s x = eO (eO.symm x * s) := rfl

/-- Right multiplication by `s * t` is right multiplication by `s` followed by `t`. -/
theorem rightMul_mul (s t : R) : rightMul eO (s * t) = rightMul eO t ∘ₗ rightMul eO s := by
  ext x
  simp [rightMul_apply, mul_assoc]

/-- Right multiplication by `1` is the identity. -/
theorem rightMul_one : rightMul eO 1 = LinearMap.id := by
  ext x
  simp [rightMul_apply]

/-- Right multiplication is additive in the scalar. -/
theorem rightMul_add (s t : R) : rightMul eO (s + t) = rightMul eO s + rightMul eO t := by
  ext x
  simp [rightMul_apply, mul_add]

/-- Right multiplication by `0` is the zero map. -/
theorem rightMul_zero : rightMul eO 0 = 0 := by
  ext x
  simp [rightMul_apply]

/-- The coordinates `n → R ≃ n → O`. -/
def piRankOne (n : Type*) : (n → R) ≃ₗ[R] (n → O) := LinearEquiv.piCongrRight fun _ => eO

/-- `piRankOne eO n` sends `Pi.single i x` to `Pi.single i (eO x)`. -/
theorem piRankOne_single (n : Type*) [DecidableEq n] (i : n) (x : R) :
    piRankOne eO n (Pi.single i x) = Pi.single i (eO x) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [piRankOne]
  · simp [piRankOne, h]

/-- The matrix of an endomorphism of `n → O`, `F(v) = v ⬝ A` in the coordinate `eO`. -/
def endMatrixO {n : Type*} [Fintype n] [DecidableEq n] (F : (n → O) →ₗ[R] (n → O)) :
    Matrix n n R :=
  endMatrix ((piRankOne eO n).symm.toLinearMap ∘ₗ F ∘ₗ (piRankOne eO n).toLinearMap)

/-- The `(i, j)` entry of `endMatrixO eO F` is the `eO`-coordinate of the `j`-th component of
`F(Pi.single i (eO 1))`. -/
theorem endMatrixO_apply {n : Type*} [Fintype n] [DecidableEq n] (F : (n → O) →ₗ[R] (n → O))
    (i j : n) : endMatrixO eO F i j = eO.symm (F (Pi.single i (eO 1)) j) := by
  rw [endMatrixO, endMatrix_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change (piRankOne eO n).symm (F (piRankOne eO n (Pi.single i 1))) j = _
  rw [piRankOne_single]
  simp [piRankOne]

/-- `F` maps the `i`-th summand to the `j`-th summand by right multiplication by its matrix
entry `A i j`. -/
theorem proj_comp_comp_single {n : Type*} [Fintype n] [DecidableEq n]
    (F : (n → O) →ₗ[R] (n → O)) (i j : n) :
    LinearMap.proj j ∘ₗ F ∘ₗ LinearMap.single R (fun _ => O) i =
      rightMul eO (endMatrixO eO F i j) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, rightMul_apply, endMatrixO_apply]
  have hx : x = eO.symm x • eO 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hx]
  rw [LinearMap.single_apply, Pi.single_smul', map_smul, Pi.smul_apply, ← eO.apply_symm_apply
    (F (Pi.single i (eO 1)) j), ← map_smul, smul_eq_mul, LinearEquiv.apply_symm_apply]

end RankOne

/-! ### Through an additive functor -/

section Functor

variable {R : Type u} [Ring R] {Λ : Type w} [CommRing Λ]
  (Φ : ModuleCat.{v} R ⥤ ModuleCat.{v'} Λ) [Φ.Additive] {O : ModuleCat.{v} R} (eO : R ≃ₗ[R] O)
  {r : ℕ} (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ))

/-- Right multiplication by `s` on `O`, as a morphism of `R`-modules. -/
abbrev rightMulHom (s : R) : O ⟶ O := ModuleCat.ofHom (rightMul eO s)

/-- `rightMulHom eO (s * t)` is the composite `rightMulHom eO s ≫ rightMulHom eO t`. -/
theorem rightMulHom_mul (s t : R) :
    rightMulHom eO (s * t) = rightMulHom eO s ≫ rightMulHom eO t := by
  ext1
  exact rightMul_mul eO s t

/-- The matrix of `Φ(x ↦ x ⬝ s)` in the basis `b`. -/
def functorMatrix (s : R) : Matrix (Fin r) (Fin r) Λ :=
  LinearMap.toMatrix' (b.conj (Φ.map (rightMulHom eO s)).hom)

omit [Φ.Additive] in
/-- The matrix of `Φ(x ↦ x ⬝ (s * t))` is the product of the matrices for `t` and for `s`, in
that order. -/
theorem functorMatrix_mul (s t : R) :
    functorMatrix Φ eO b (s * t) = functorMatrix Φ eO b t * functorMatrix Φ eO b s := by
  rw [functorMatrix, rightMulHom_mul, Φ.map_comp, ModuleCat.hom_comp, LinearEquiv.conj_comp,
    LinearMap.toMatrix'_comp]
  rfl

/-- **The representation `φ : R →+* M_r(Λ)` attached to `Φ` and the basis `b` of `Φ(O)`**: the
transpose of the matrix of `Φ` of right multiplication. -/
def functorRep : R →+* Matrix (Fin r) (Fin r) Λ where
  toFun s := (functorMatrix Φ eO b s)ᵀ
  map_one' := by
    have h : rightMulHom eO (1 : R) = 𝟙 O := by
      ext1
      exact rightMul_one eO
    rw [functorMatrix, h, Φ.map_id, ModuleCat.hom_id, LinearEquiv.conj_id, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  map_mul' s t := by
    rw [functorMatrix_mul, Matrix.transpose_mul]
  map_zero' := by
    have h : rightMulHom eO (0 : R) = 0 := by
      ext1
      exact rightMul_zero eO
    rw [functorMatrix, h, Φ.map_zero, ModuleCat.hom_zero, map_zero, map_zero, Matrix.transpose_zero]
  map_add' s t := by
    have h : rightMulHom eO (s + t) = rightMulHom eO s + rightMulHom eO t := by
      ext1
      exact rightMul_add eO s t
    rw [functorMatrix, h, Φ.map_add, ModuleCat.hom_add, map_add, map_add, Matrix.transpose_add]
    rfl

/-- The `(a, c)` entry of `φ(s)` is the `c`-th `b`-coordinate of `Φ(x ↦ x ⬝ s)` applied to the
`a`-th basis vector. -/
theorem functorRep_apply (s : R) (a c : Fin r) :
    functorRep Φ eO b s a c = b ((Φ.map (rightMulHom eO s)).hom (b.symm (Pi.single a 1))) c := by
  simp [functorRep, functorMatrix, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply]

/-- **The characteristic series of `Φ(x ↦ x ⬝ s)` is that of `φ(s)`**:
`det(1 - Φ(x ↦ x ⬝ s) T ^ d) = det(1 - φ(s) T ^ d)`. -/
theorem charSeries_functor_map_rightMulHom [Module.Finite Λ (Φ.obj O)]
    [Module.Projective Λ (Φ.obj O)] (s : R) (d : ℕ) :
    ProjectiveDeterminant.charSeries (Φ.map (rightMulHom eO s)).hom d =
      (1 - (X : PowerSeries Λ) ^ d • (functorRep Φ eO b s).map (C (R := Λ))).det := by
  rw [ProjectiveDeterminant.charSeries_eq_det_matrix (Module.Basis.ofEquivFun b),
    ← Matrix.det_transpose]
  congr 1
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, ← Matrix.transpose_map]
  congr 3

variable (n : Type) [Fintype n] [DecidableEq n]

/-- The free module `n → O`. -/
abbrev freeObj (O : ModuleCat.{v} R) (n : Type) : ModuleCat.{v} R := ModuleCat.of R (n → O)

/-- The inclusion of the `i`-th summand of `n → O`. -/
abbrev freeι (O : ModuleCat.{v} R) (i : n) : O ⟶ freeObj O n :=
  ModuleCat.ofHom (LinearMap.single R (fun _ => O) i)

/-- The projection onto the `j`-th summand of `n → O`. -/
abbrev freeπ (O : ModuleCat.{v} R) (j : n) : freeObj O n ⟶ O := ModuleCat.ofHom (LinearMap.proj j)

/-- The projections and inclusions of the summands of `n → O` sum to the identity. -/
theorem sum_freeπ_comp_freeι : ∑ j, freeπ n O j ≫ freeι n O j = 𝟙 _ := by
  ext1
  refine LinearMap.ext fun v => ?_
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
  exact Finset.univ_sum_single v

omit [Fintype n] in
/-- The inclusion of the `i`-th summand followed by the projection onto the `j`-th is the
identity if `i = j` and zero otherwise. -/
theorem freeι_comp_freeπ (i j : n) :
    freeι n O i ≫ freeπ n O j = if i = j then 𝟙 O else 0 := by
  ext1
  refine LinearMap.ext fun x => ?_
  by_cases h : i = j
  · subst h
    simp
  · rw [ite_eq_right h]
    simp [Ne.symm h]

/-- `Φ(n → O) ≅ n → Φ(O)`, by the images of the projections. -/
def functorFreeEquiv : Φ.obj (freeObj O n) ≃ₗ[Λ] (n → Φ.obj O) where
  toFun x j := (Φ.map (freeπ n O j)).hom x
  invFun y := ∑ j, (Φ.map (freeι n O j)).hom (y j)
  map_add' x y := by
    ext j
    simp
  map_smul' c x := by
    ext j
    simp
  left_inv x := by
    have h := congrArg (fun g => (Φ.map g).hom x) (sum_freeπ_comp_freeι (O := O) n)
    simp only [Φ.map_sum, ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply, Φ.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, Φ.map_id, ModuleCat.hom_id,
      LinearMap.id_apply] at h
    exact h
  right_inv y := by
    ext k
    simp only [map_sum]
    have h : ∀ j, (Φ.map (freeπ n O k)).hom ((Φ.map (freeι n O j)).hom (y j)) =
        if j = k then y j else 0 := fun j => by
      have := congrArg (fun g => (Φ.map g).hom (y j)) (freeι_comp_freeπ (O := O) n j k)
      simp only [Φ.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      split_ifs <;> simp
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The identification `(n → Fin r → Λ) ≃ (Fin r × n → Λ)`. -/
def blockFunEquiv : (n → Fin r → Λ) ≃ₗ[Λ] (Fin r × n → Λ) where
  toFun v p := v p.2 p.1
  invFun w j a := w (a, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis of `Φ(n → O)` indexed by `Fin r × n` induced by `b`. -/
def functorFreeBasis : Module.Basis (Fin r × n) Λ (Φ.obj (freeObj O n)) :=
  Module.Basis.ofEquivFun
    (functorFreeEquiv Φ n ≪≫ₗ LinearEquiv.piCongrRight (fun _ => b) ≪≫ₗ blockFunEquiv n)

/-- The `(a, j)` coordinate of `x` in `functorFreeBasis Φ b n` is the `a`-th `b`-coordinate of
the image of `x` under `Φ` of the `j`-th projection. -/
theorem functorFreeBasis_repr (x : Φ.obj (freeObj O n)) (a : Fin r) (j : n) :
    (functorFreeBasis Φ b n).repr x (a, j) = b ((Φ.map (freeπ n O j)).hom x) a := rfl

/-- The `(c, i)` vector of `functorFreeBasis Φ b n` is the image of the `c`-th vector of `b`
under `Φ` of the `i`-th inclusion. -/
theorem functorFreeBasis_apply (c : Fin r) (i : n) :
    functorFreeBasis Φ b n (c, i) = (Φ.map (freeι n O i)).hom (b.symm (Pi.single c 1)) := by
  rw [functorFreeBasis, Module.Basis.coe_ofEquivFun]
  change ∑ j, (Φ.map (freeι n O j)).hom
      (b.symm (fun a => (Pi.single (c, i) (1 : Λ) : Fin r × n → Λ) (a, j))) = _
  rw [Finset.sum_eq_single i]
  · congr 2
    ext a
    by_cases h : a = c
    · subst h
      simp
    · simp [h]
  · intro j _ hj
    have : (fun a => (Pi.single (c, i) (1 : Λ) : Fin r × n → Λ) (a, j)) = 0 := by
      ext a
      simp [hj]
    rw [this, map_zero, map_zero]
  · simp

/-- **The matrix of `Φ(F)` is the transpose of the block matrix `φ(A)`**, for an endomorphism
`F` of `n → O` with matrix `A`. -/
theorem toMatrix_functor_map (F : freeObj O n ⟶ freeObj O n) :
    LinearMap.toMatrix (functorFreeBasis Φ b n) (functorFreeBasis Φ b n) (Φ.map F).hom =
      (blockMap (functorRep Φ eO b) n (endMatrixO eO F.hom))ᵀ := by
  ext ⟨a, j⟩ ⟨c, i⟩
  rw [LinearMap.toMatrix_apply, functorFreeBasis_repr, functorFreeBasis_apply,
    Matrix.transpose_apply]
  have h : freeι n O i ≫ F ≫ freeπ n O j = rightMulHom eO (endMatrixO eO F.hom i j) := by
    ext1
    exact proj_comp_comp_single eO F.hom i j
  have h' := congrArg (fun g => (Φ.map g).hom (b.symm (Pi.single c 1))) h
  simp only [Φ.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  rw [h']
  simp only [blockMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply,
    functorRep_apply]

/-- **`det(1 - Φ(F) T) = det(1 - φ(A) T)`** for an endomorphism `F` of `n → O` with matrix
`A`. -/
theorem charSeries_functor_map_eq_det [Module.Finite Λ (Φ.obj (freeObj O n))]
    [Module.Projective Λ (Φ.obj (freeObj O n))] (F : freeObj O n ⟶ freeObj O n) :
    ProjectiveDeterminant.charSeries (Φ.map F).hom 1 =
      (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) n (endMatrixO eO F.hom)).map
        (C (R := Λ))).det := by
  rw [ProjectiveDeterminant.charSeries_eq_det_matrix (functorFreeBasis Φ b n),
    toMatrix_functor_map Φ eO b n F, pow_one, ← Matrix.det_transpose]
  congr 1
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_map,
    Matrix.transpose_transpose]

end Functor

/-! ### Retracts of free modules -/

section Retract

variable {R : Type u} [Ring R] {Λ : Type w} [CommRing Λ]
  (Φ : ModuleCat.{v} R ⥤ ModuleCat.{v'} Λ) [Φ.Additive] {O : ModuleCat.{v} R} (eO : R ≃ₗ[R] O)
  {r : ℕ} (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ)) (n : Type) [Fintype n] [DecidableEq n]
  {P : ModuleCat.{v} R} (p : freeObj O n ⟶ P) (i : P ⟶ freeObj O n) (hpi : i ≫ p = 𝟙 P)

omit [Φ.Additive] [Fintype n] [DecidableEq n] in
include hpi in
/-- If `i ≫ p = 𝟙 P`, then `Φ(p) ∘ Φ(i)` is the identity of `Φ(P)`. -/
lemma functor_map_comp_eq_id : (Φ.map p).hom.comp (Φ.map i).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← Φ.map_comp, hpi, Φ.map_id, ModuleCat.hom_id]

omit [Fintype n] [DecidableEq n] in
include b hpi in
/-- The image under `Φ` of a retract of `n → O` is finite over `Λ`. -/
theorem functor_obj_finite_of_retract [Finite n] : Module.Finite Λ (Φ.obj P) := by
  classical
  have := Fintype.ofFinite n
  have := Module.Finite.of_basis (functorFreeBasis Φ b n)
  refine Module.Finite.of_surjective (Φ.map p).hom fun y => ⟨(Φ.map i).hom y, ?_⟩
  have := congrArg (fun g => g y) (functor_map_comp_eq_id Φ n p i hpi)
  simpa using this

omit [Fintype n] [DecidableEq n] in
include b hpi in
/-- The image under `Φ` of a retract of `n → O` is projective over `Λ`. -/
theorem functor_obj_projective_of_retract [Finite n] : Module.Projective Λ (Φ.obj P) := by
  classical
  have := Fintype.ofFinite n
  have := Module.Projective.of_basis (functorFreeBasis Φ b n)
  exact Module.Projective.of_split (Φ.map i).hom (Φ.map p).hom
    (functor_map_comp_eq_id Φ n p i hpi)

include hpi in
/-- **`det(1 - Φ(f) T) = det(1 - φ(A) T)`** for an endomorphism `f` of a retract `P` of `n → O`,
where `A` is the matrix of `i ∘ f ∘ p`. -/
theorem charSeries_functor_map_retract [Module.Finite Λ (Φ.obj (freeObj O n))]
    [Module.Projective Λ (Φ.obj (freeObj O n))] [Module.Finite Λ (Φ.obj P)]
    [Module.Projective Λ (Φ.obj P)] (f : P ⟶ P) :
    ProjectiveDeterminant.charSeries (Φ.map f).hom 1 =
      (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) n
        (endMatrixO eO (p ≫ f ≫ i).hom)).map (C (R := Λ))).det := by
  rw [ProjectiveDeterminant.charSeries_retract (Φ.map i).hom (Φ.map p).hom
    (functor_map_comp_eq_id Φ n p i hpi) (Φ.map f).hom 1,
    ← charSeries_functor_map_eq_det Φ eO b n (p ≫ f ≫ i)]
  congr 1
  simp only [Φ.map_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]

include hpi in
/-- **The traces of the powers of an endomorphism of a retract `P` of `n → O`** are the traces
of the powers of the matrix `A` of `i ∘ f ∘ p`. -/
theorem projectiveModuleTrace_pow_eq_trq [Module.Finite R P] [Module.Projective R P]
    (f : P ⟶ P) {m : ℕ} (hm : 0 < m) :
    Stacks.Trace.projectiveModuleTrace R P (f.hom ^ m) =
      trq n (endMatrixO eO (p ≫ f ≫ i).hom ^ m) := by
  let e := piRankOne eO n
  let p' : (n → R) →ₗ[R] P := p.hom ∘ₗ e.toLinearMap
  let i' : P →ₗ[R] (n → R) := e.symm.toLinearMap ∘ₗ i.hom
  have hpi' : p'.comp i' = LinearMap.id := by
    ext x
    have := congrArg (fun g => g.hom x) hpi
    simpa [p', i'] using this
  rw [projectiveModuleTrace_eq_of_split R P (f.hom ^ m) p' i' hpi',
    freeModuleTrace_eq_trq, endMatrixO, ← endMatrix_pow]
  congr 2
  have key : ∀ k : ℕ, i' ∘ₗ ((f.hom ^ (k + 1)) ∘ₗ p') = (i' ∘ₗ (f.hom ∘ₗ p')) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (i' ∘ₗ (f.hom ∘ₗ p')), ← ih, Module.End.mul_eq_comp, pow_succ,
        Module.End.mul_eq_comp]
      refine LinearMap.ext fun x => ?_
      have h := congrArg (fun g => g (f.hom (p' x))) hpi'
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
      rw [h]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [zero_add, key k]
  congr 1

end Retract

/-! ### Block diagonal matrices -/

section BlockDiagonal

variable {R : Type u} [Ring R] {Λ : Type w} [CommRing Λ] {r : ℕ}
  (φ : R →+* Matrix (Fin r) (Fin r) Λ) {J : Type*} [Fintype J] [DecidableEq J] {k : J → ℕ}
  (A : ∀ j, Matrix (Fin (k j)) (Fin (k j)) R)

/-- The determinant of a block diagonal matrix with blocks of varying sizes is the product of
the determinants of its blocks. -/
theorem det_blockDiagonal'_eq_prod {S : Type*} [CommRing S] {m' : J → Type*}
    [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (d : ∀ j, Matrix (m' j) (m' j) S) :
    (Matrix.blockDiagonal' d).det = ∏ j, (d j).det := by
  let : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J) (Fintype.equivFin J).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun j _ => ?_
  let e : m' j ≃ {a : Σ j, m' j // a.1 = j} :=
    { toFun := fun x => ⟨⟨j, x⟩, rfl⟩
      invFun := fun a => cast (congrArg m' a.2) a.1.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨j', y⟩, h⟩ => by subst h; rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext x y
  simp [Matrix.toSquareBlock_def, e, Matrix.blockDiagonal'_apply_eq]

/-- The reindexing `Fin r × (Σ j, Fin (k j)) ≃ Σ j, Fin r × Fin (k j)`. -/
def blockSigmaEquiv (r : ℕ) (k : J → ℕ) : Fin r × (Σ j, Fin (k j)) ≃ Σ j, Fin r × Fin (k j) where
  toFun x := ⟨x.2.1, (x.1, x.2.2)⟩
  invFun y := (y.2.1, ⟨y.1, y.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexed by `blockSigmaEquiv`, the block matrix `φ` of a block diagonal matrix is the block
diagonal matrix of the block matrices `φ` of its blocks. -/
theorem submatrix_blockMap_blockDiagonal' :
    (blockMap φ (Σ j, Fin (k j)) (Matrix.blockDiagonal' A)).submatrix
        (blockSigmaEquiv r k).symm (blockSigmaEquiv r k).symm =
      Matrix.blockDiagonal' fun j => blockMap φ (Fin (k j)) (A j) := by
  ext ⟨i, a, x⟩ ⟨i', a', y⟩
  simp only [Matrix.submatrix_apply, blockSigmaEquiv, Equiv.coe_fn_symm_mk, blockMap,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply,
    Matrix.blockDiagonal'_apply]
  by_cases h : i = i'
  · subst h
    simp
  · simp [h]

/-- **The characteristic series of a block diagonal matrix** is the product of those of its
blocks. -/
theorem det_one_sub_X_smul_blockMap_blockDiagonal' :
    (1 - (X : PowerSeries Λ) • (blockMap φ (Σ j, Fin (k j)) (Matrix.blockDiagonal' A)).map
      (C (R := Λ))).det =
      ∏ j, (1 - (X : PowerSeries Λ) • (blockMap φ (Fin (k j)) (A j)).map (C (R := Λ))).det := by
  rw [← det_blockDiagonal'_eq_prod, ← Matrix.det_submatrix_equiv_self (blockSigmaEquiv r k).symm]
  congr 1
  have hN := submatrix_blockMap_blockDiagonal' φ A
  ext ⟨i, a, x⟩ ⟨i', a', y⟩
  have hpq := congrFun (congrFun hN ⟨i, a, x⟩) ⟨i', a', y⟩
  simp only [Matrix.submatrix_apply] at hpq
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hpq,
    Matrix.blockDiagonal'_apply]
  by_cases h : i = i'
  · subst h
    simp [Matrix.one_apply, blockSigmaEquiv, Prod.ext_iff]
  · simp [Matrix.one_apply, blockSigmaEquiv, h]

/-- **The traces of the powers of a block diagonal matrix** are the sums of those of its
blocks. -/
theorem trq_blockDiagonal'_pow (m : ℕ) :
    trq (Σ j, Fin (k j)) (Matrix.blockDiagonal' A ^ m) = ∑ j, trq (Fin (k j)) (A j ^ m) := by
  rw [← Matrix.blockDiagonal'_pow, trq_apply, Matrix.trace_blockDiagonal', map_sum]
  rfl

end BlockDiagonal

end Stacks.CharSeriesTraceDetection
