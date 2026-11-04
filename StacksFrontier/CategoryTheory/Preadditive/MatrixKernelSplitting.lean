module

public import StacksFrontier.CategoryTheory.Limits.BiproductMatrixFunctor
public import StacksFrontier.RingTheory.Fitting.KernelRankStratum
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Morphisms of free objects given by matrices, and their split kernels

Let `O` be an object of a preadditive category with finite biproducts. A matrix with entries in
a commutative ring `R` mapping to `End O` gives a morphism `O^n ⟶ O^m` of biproducts, and
matrix multiplication becomes composition. A free kernel splitting of a matrix
(`Matrix.HasFreeKernelSplittingKernelRankStratum`) makes `O^r ⟶ O^n` a kernel of the
corresponding morphism, and this kernel is preserved by every additive functor.

## Main definitions

* `CategoryTheory.matrixHomMatrixKernelSplitting`: the morphism `O^n ⟶ O^m` of an `m × n` matrix.

## Main results

* `CategoryTheory.matrixHom_mul_matrixKernelSplitting`: the morphism of a product is the composite.
* `CategoryTheory.exists_isLimit_kernelFork_of_hasFreeKernelSplitting_matrixKernelSplitting`: a
  free kernel splitting gives a kernel, preserved by every additive functor.
* `CategoryTheory.injective_mulVec_of_mono_matrixKernelSplitting`: a monomorphism `O^r ⟶ O^n` has
  an injective matrix when `R → End O` is injective.
* `CategoryTheory.app_kernel_matrixHom_eq_zero_matrixKernelSplitting`: if `N A = x · 1`, a central
  endomorphism acting on `O` as `x` vanishes on the kernel of `A`.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] (O : C)
  {R : Type w} [CommRing R] (ψ : R →+* End O)

/-- The `n`-fold biproduct `O^n`. -/
abbrev freeObjMatrixKernelSplitting (n : ℕ) : C := ⨁ fun _ : Fin n => O

/-- The morphism `O^n ⟶ O^m` of an `m × n` matrix `M` with entries in `R`, acting through
`ψ : R → End O`: its component from the `j`th summand to the `i`th is `ψ (M i j)`. -/
def matrixHomMatrixKernelSplitting {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    freeObjMatrixKernelSplitting O n ⟶ freeObjMatrixKernelSplitting O m :=
  biproduct.matrix fun j i => (ψ (M i j) : O ⟶ O)

variable {O ψ}

/-- The component of the morphism of `M` from the `j`th summand to the `i`th is `ψ (M i j)`. -/
@[reassoc (attr := simp)]
theorem ι_matrixHom_π_matrixKernelSplitting {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (j : Fin n)
    (i : Fin m) :
    biproduct.ι _ j ≫ matrixHomMatrixKernelSplitting O ψ M ≫ biproduct.π _ i =
      (ψ (M i j) : O ⟶ O) := by
  simp [matrixHomMatrixKernelSplitting]

/-- Two morphisms `O^n ⟶ O^m` are equal if all their components agree. -/
theorem matrixHom_ext_matrixKernelSplitting {m n : ℕ}
    {f g : freeObjMatrixKernelSplitting O n ⟶ freeObjMatrixKernelSplitting O m}
    (h : ∀ j i, biproduct.ι _ j ≫ f ≫ biproduct.π _ i = biproduct.ι _ j ≫ g ≫ biproduct.π _ i) :
    f = g :=
  biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun i => by
    simpa only [Category.assoc] using h j i

/-- **Matrix multiplication is composition**, in the opposite order. -/
theorem matrixHom_mul_matrixKernelSplitting {l m n : ℕ} (M : Matrix (Fin l) (Fin m) R)
    (N : Matrix (Fin m) (Fin n) R) :
    matrixHomMatrixKernelSplitting O ψ (M * N) =
      matrixHomMatrixKernelSplitting O ψ N ≫ matrixHomMatrixKernelSplitting O ψ M := by
  refine matrixHom_ext_matrixKernelSplitting fun j i => ?_
  rw [ι_matrixHom_π_matrixKernelSplitting, Matrix.mul_apply, map_sum, Category.assoc,
    ← Category.assoc, matrixHomMatrixKernelSplitting, biproduct.ι_matrix,
    matrixHomMatrixKernelSplitting, biproduct.matrix_π, biproduct.lift_desc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, End.mul_def]

/-- The identity matrix gives the identity morphism. -/
theorem matrixHom_one_matrixKernelSplitting {n : ℕ} :
    matrixHomMatrixKernelSplitting O ψ (1 : Matrix (Fin n) (Fin n) R) = 𝟙 _ := by
  refine matrixHom_ext_matrixKernelSplitting fun j i => ?_
  rw [ι_matrixHom_π_matrixKernelSplitting, Category.id_comp, biproduct.ι_π, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [End.one_def]
  · rw [if_neg h, dif_neg (Ne.symm h), map_zero]

/-- The zero matrix gives the zero morphism. -/
theorem matrixHom_zero_matrixKernelSplitting {m n : ℕ} :
    matrixHomMatrixKernelSplitting O ψ (0 : Matrix (Fin m) (Fin n) R) = 0 := by
  refine matrixHom_ext_matrixKernelSplitting fun j i => ?_
  simp

/-- The morphism of a sum of matrices is the sum of their morphisms. -/
theorem matrixHom_add_matrixKernelSplitting {m n : ℕ} (M N : Matrix (Fin m) (Fin n) R) :
    matrixHomMatrixKernelSplitting O ψ (M + N) =
      matrixHomMatrixKernelSplitting O ψ M + matrixHomMatrixKernelSplitting O ψ N := by
  refine matrixHom_ext_matrixKernelSplitting fun j i => ?_
  simp [Preadditive.add_comp, Preadditive.comp_add]

/-- A matrix is determined by its morphism when `ψ` is injective. -/
theorem matrixHom_injective_matrixKernelSplitting (hψ : Function.Injective ψ) {m n : ℕ} :
    Function.Injective (matrixHomMatrixKernelSplitting O ψ (m := m) (n := n)) := by
  intro M N h
  ext i j
  apply hψ
  have := ι_matrixHom_π_matrixKernelSplitting (ψ := ψ) M j i
  rw [h, ι_matrixHom_π_matrixKernelSplitting] at this
  exact this.symm

/-- **A free kernel splitting gives a kernel.** If `V U = 1`, `A U = 0` and `W A + U V = 1`, then
`U : O^r ⟶ O^n` is a kernel of `A : O^n ⟶ O^m`. -/
def isLimitKernelForkOfSplittingMatrixKernelSplitting {K P Q : C} {u : K ⟶ P} {v : P ⟶ K}
    {w : Q ⟶ P} {d : P ⟶ Q}
    (h₁ : u ≫ v = 𝟙 K) (h₂ : u ≫ d = 0) (h₃ : d ≫ w + v ≫ u = 𝟙 P) :
    IsLimit (KernelFork.ofι u h₂) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x ≫ v)
    (fun x hx => by
      rw [Category.assoc, ← add_zero (x ≫ v ≫ u), ← zero_comp (f := w), ← hx, Category.assoc,
        ← Preadditive.comp_add, add_comm, h₃, Category.comp_id])
    (fun x hx m hm => by rw [← hm, Category.assoc, h₁, Category.comp_id])

/-- **An additive functor preserves the kernel of a free kernel splitting**: the three identities
survive. -/
def isLimitMapKernelForkOfSplittingMatrixKernelSplitting {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D)
    [F.Additive] {K P Q : C} {u : K ⟶ P} {v : P ⟶ K} {w : Q ⟶ P} {d : P ⟶ Q}
    (h₁ : u ≫ v = 𝟙 K) (h₂ : u ≫ d = 0) (h₃ : d ≫ w + v ≫ u = 𝟙 P) :
    IsLimit (KernelFork.ofι (f := F.map d) (F.map u) (by rw [← F.map_comp, h₂, F.map_zero])) :=
  isLimitKernelForkOfSplittingMatrixKernelSplitting (w := F.map w) (v := F.map v)
    (by rw [← F.map_comp, h₁, F.map_id])
    (by rw [← F.map_comp, h₂, F.map_zero])
    (by rw [← F.map_comp, ← F.map_comp, ← F.map_add, h₃, F.map_id])

/-- **A free kernel splitting of `A` makes `O^r` a kernel of the morphism of `A`**, through the
morphism of the first matrix of the splitting; any additive functor preserves it. -/
theorem exists_isLimit_kernelFork_of_hasFreeKernelSplitting_matrixKernelSplitting {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (h : A.HasFreeKernelSplittingKernelRankStratum r) :
    ∃ (u : freeObjMatrixKernelSplitting O r ⟶ freeObjMatrixKernelSplitting O n)
      (hu : u ≫ matrixHomMatrixKernelSplitting O ψ A = 0),
      ∀ {D : Type u} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive],
        Nonempty (IsLimit (KernelFork.ofι (f := F.map (matrixHomMatrixKernelSplitting O ψ A))
          (F.map u) (by rw [← F.map_comp, hu, F.map_zero]))) := by
  obtain ⟨U, V, W, h₁, h₂, h₃⟩ := h
  have e₁ : matrixHomMatrixKernelSplitting O ψ U ≫ matrixHomMatrixKernelSplitting O ψ V = 𝟙 _ := by
    rw [← matrixHom_mul_matrixKernelSplitting, h₁, matrixHom_one_matrixKernelSplitting]
  have e₂ : matrixHomMatrixKernelSplitting O ψ U ≫ matrixHomMatrixKernelSplitting O ψ A = 0 := by
    rw [← matrixHom_mul_matrixKernelSplitting, h₂, matrixHom_zero_matrixKernelSplitting]
  have e₃ : matrixHomMatrixKernelSplitting O ψ A ≫ matrixHomMatrixKernelSplitting O ψ W +
      matrixHomMatrixKernelSplitting O ψ V ≫ matrixHomMatrixKernelSplitting O ψ U = 𝟙 _ := by
    rw [← matrixHom_mul_matrixKernelSplitting, ← matrixHom_mul_matrixKernelSplitting,
      ← matrixHom_add_matrixKernelSplitting, h₃, matrixHom_one_matrixKernelSplitting]
  exact ⟨matrixHomMatrixKernelSplitting O ψ U, e₂, fun F _ =>
    ⟨isLimitMapKernelForkOfSplittingMatrixKernelSplitting F e₁ e₂ e₃⟩⟩

/-- Every morphism `O^n ⟶ O^m` is the morphism of a matrix when `ψ` is surjective. -/
theorem exists_matrixHom_eq_matrixKernelSplitting (hψ : Function.Surjective ψ) {m n : ℕ}
    (f : freeObjMatrixKernelSplitting O n ⟶ freeObjMatrixKernelSplitting O m) :
    ∃ M : Matrix (Fin m) (Fin n) R, matrixHomMatrixKernelSplitting O ψ M = f := by
  choose c hc using fun (i : Fin m) (j : Fin n) =>
    hψ (biproduct.ι (fun _ : Fin n => O) j ≫ f ≫ biproduct.π (fun _ : Fin m => O) i)
  exact ⟨Matrix.of c, matrixHom_ext_matrixKernelSplitting fun j i => by
    rw [ι_matrixHom_π_matrixKernelSplitting, Matrix.of_apply, hc]⟩

/-- **A monomorphism `O^r ⟶ O^n` has injective matrix**, when `ψ : R → End O` is injective. -/
theorem injective_mulVec_of_mono_matrixKernelSplitting (hψ : Function.Injective ψ) {n r : ℕ}
    (J : Matrix (Fin n) (Fin r) R) [Mono (matrixHomMatrixKernelSplitting O ψ J)] :
    Function.Injective J.mulVec := by
  intro x y hxy
  let X : Matrix (Fin r) (Fin 1) R := Matrix.of fun i _ => x i
  let Y : Matrix (Fin r) (Fin 1) R := Matrix.of fun i _ => y i
  have hXY : J * X = J * Y := by
    ext i k
    have := congrFun hxy i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, X, Y] using this
  have hm : matrixHomMatrixKernelSplitting O ψ X = matrixHomMatrixKernelSplitting O ψ Y := by
    rw [← cancel_mono (matrixHomMatrixKernelSplitting O ψ J),
      ← matrixHom_mul_matrixKernelSplitting, ← matrixHom_mul_matrixKernelSplitting, hXY]
  have := matrixHom_injective_matrixKernelSplitting hψ hm
  funext i
  simpa [X, Y] using congrFun (congrFun this i) 0

/-- A matrix killed by composition is zero, when `ψ` is injective. -/
theorem mul_eq_zero_of_matrixHom_comp_matrixKernelSplitting (hψ : Function.Injective ψ) {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) R) (N : Matrix (Fin m) (Fin n) R)
    (h : matrixHomMatrixKernelSplitting O ψ N ≫ matrixHomMatrixKernelSplitting O ψ M = 0) :
    M * N = 0 :=
  matrixHom_injective_matrixKernelSplitting hψ
    (by rw [matrixHom_mul_matrixKernelSplitting, h, matrixHom_zero_matrixKernelSplitting])

section Functor

variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D] (F : C ⥤ D)
  [F.Additive] {O' : D} (e : F.obj O ≅ O')

/-- An additive functor carries `O^n` to `O'^n` when it carries `O` to `O'`. -/
def freeObjMapIsoMatrixKernelSplitting (n : ℕ) :
    F.obj (freeObjMatrixKernelSplitting O n) ≅ freeObjMatrixKernelSplitting O' n :=
  F.mapBiproduct _ ≪≫ biproduct.mapIso fun _ => e

/-- **An additive functor carries the morphism of a matrix to the morphism of the image
matrix**, for any ring map `θ` compatible with conjugation by `e`. -/
theorem freeObjMapIso_inv_map_matrixHom_matrixKernelSplitting {R' : Type*} [CommRing R']
    (ψ' : R' →+* End O')
    (θ : R →+* R') (hθ : ∀ a, (ψ' (θ a) : O' ⟶ O') = e.inv ≫ F.map (ψ a : O ⟶ O) ≫ e.hom)
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (freeObjMapIsoMatrixKernelSplitting F e n).inv ≫
        F.map (matrixHomMatrixKernelSplitting O ψ M) ≫
          (freeObjMapIsoMatrixKernelSplitting F e m).hom =
      matrixHomMatrixKernelSplitting O' ψ' (M.map θ) := by
  have key := Functor.mapBiproduct_inv_map_matrix F
    (fun (j : Fin n) (i : Fin m) => (ψ (M i j) : O ⟶ O))
  simp only [freeObjMapIsoMatrixKernelSplitting, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
    biproduct.mapIso_hom, Category.assoc, matrixHomMatrixKernelSplitting]
  rw [reassoc_of% key]
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun i => ?_
  simp [hθ]

end Functor

section Central

variable (η : End (𝟭 C)) {x : R} (hη : η.app O = ψ x)
include hη

/-- **An endomorphism of the identity functor acting on `O` as `ψ x` acts on `O^n` as the scalar
matrix `x · 1`.** -/
theorem app_freeObj_eq_matrixHom_smul_one_matrixKernelSplitting (n : ℕ) :
    η.app (freeObjMatrixKernelSplitting O n) =
      matrixHomMatrixKernelSplitting O ψ (x • (1 : Matrix (Fin n) (Fin n) R)) := by
  classical
  refine matrixHom_ext_matrixKernelSplitting fun j i => ?_
  have hnat : biproduct.ι (fun _ : Fin n => O) j ≫ η.app (freeObjMatrixKernelSplitting O n) =
      η.app O ≫ biproduct.ι (fun _ : Fin n => O) j := η.naturality _
  rw [reassoc_of% hnat, ι_matrixHom_π_matrixKernelSplitting, hη, biproduct.ι_π,
    Matrix.smul_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [dif_neg h, if_neg (Ne.symm h), comp_zero, smul_zero, map_zero]

/-- **A scalar `x` with `N A = x · 1` kills the kernel of `A`**: an endomorphism of the identity
functor acting on `O` as `ψ x` is zero on the kernel of the morphism of `A`. -/
theorem app_kernel_matrixHom_eq_zero_matrixKernelSplitting {m n : ℕ} {A : Matrix (Fin m) (Fin n) R}
    [HasKernel (matrixHomMatrixKernelSplitting O ψ A)] {N : Matrix (Fin n) (Fin m) R}
    (hN : N * A = x • (1 : Matrix (Fin n) (Fin n) R)) :
    η.app (kernel (matrixHomMatrixKernelSplitting O ψ A)) = 0 := by
  rw [← cancel_mono (kernel.ι (matrixHomMatrixKernelSplitting O ψ A)), zero_comp]
  have hnat : η.app (kernel (matrixHomMatrixKernelSplitting O ψ A)) ≫
        kernel.ι (matrixHomMatrixKernelSplitting O ψ A) =
      kernel.ι (matrixHomMatrixKernelSplitting O ψ A) ≫
        η.app (freeObjMatrixKernelSplitting O n) :=
    (η.naturality _).symm
  rw [hnat, app_freeObj_eq_matrixHom_smul_one_matrixKernelSplitting η hη, ← hN,
    matrixHom_mul_matrixKernelSplitting, kernel.condition_assoc, zero_comp]

end Central

end CategoryTheory
