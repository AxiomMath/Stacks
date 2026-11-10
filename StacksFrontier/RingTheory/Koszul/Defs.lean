module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The Koszul complex and Koszul regularity

Let `R` be a commutative ring and `E` an `R`-module. A functional `φ : E →ₗ[R] R`
contracts the exterior algebra `⋀(E)`, and this contraction is an antiderivation of
degree `-1` squaring to zero. The resulting chain complex, with `⋀ⁿ E` in homological
degree `n`, is the Koszul complex of `φ` (Stacks 0622). For a finite sequence
`f₁, …, f_r ∈ R` one takes `E = Rʳ` and the functional `eᵢ ↦ fᵢ`, giving the Koszul
complex `K_•(f₁, …, f_r)` of the sequence (Stacks 0623), optionally tensored with a
coefficient module `M`.

The sequence is *Koszul-regular* when the Koszul complex is acyclic away from degree
`0`, and *`H₁`-regular* when only its first homology vanishes; both notions have a
version with coefficients in `M` (Stacks 062E).

## Main definitions

* `Koszul.contraction`: contraction of `⋀(E)` by a functional on `E`, with
  `Koszul.contraction_ιMulti` its value on a product of vectors.
* `Koszul.d`: the Koszul differential `⋀^(n+1) E →ₗ[R] ⋀ⁿ E`.
* `Koszul.complex`: the Koszul complex of a functional.
* `Koszul.seqDual`, `Koszul.seqComplex`, `Koszul.seqComplexTensor`: the functional and
  the Koszul complex of a finite sequence of ring elements, with and without
  coefficients.
* `Koszul.IsKoszulRegularOn`, `Koszul.IsH1RegularOn`, `Koszul.IsKoszulRegular`,
  `Koszul.IsH1Regular`: the four regularity predicates.
-/

open scoped ExteriorAlgebra TensorProduct
open CategoryTheory

namespace Koszul

universe u v w

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- The recurrence `ιMulti (n + 1) v = ι (v 0) * ιMulti n (Fin.tail v)` for the
alternating map defining the exterior powers. -/
theorem ιMulti_succ_apply (n : ℕ) (v : Fin (n + 1) → E) :
    ExteriorAlgebra.ιMulti R (n + 1) v
      = ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ιMulti R n (Fin.tail v) :=
  ExteriorAlgebra.ιMulti_succ_apply v

/-- A wedge of `n` vectors lies in the `n`-th exterior power. -/
theorem ιMulti_mem (n : ℕ) (w : Fin n → E) : ExteriorAlgebra.ιMulti R n w ∈ ⋀[R]^n E := by
  rw [← exteriorPower.ιMulti_span_fixedDegree]
  exact Submodule.subset_span ⟨w, rfl⟩

/-- The image of `ExteriorAlgebra.ι` lies in the first exterior power. -/
theorem ι_mem_one (x : E) : ExteriorAlgebra.ι R x ∈ ⋀[R]^1 E := by simp

/-- The Koszul differential attached to `φ : E →ₗ[R] R`: the degree `-1`
antiderivation of `⋀(E)` given by contraction with `φ`, determined by
`φ ⌟ (x ∧ y) = φ x • y - x ∧ (φ ⌟ y)` for `x : E`. -/
noncomputable abbrev contraction (φ : Module.Dual R E) :
    ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E := CliffordAlgebra.contractLeft φ

/-- Contraction lowers the exterior degree by one: it maps `⋀^(n+1) E` into `⋀ⁿ E`. -/
theorem contraction_mem (φ : Module.Dual R E) (n : ℕ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ⋀[R]^(n + 1) E) : contraction φ x ∈ ⋀[R]^n E := by
  have key : ∀ (n : ℕ) (v : Fin (n + 1) → E),
      contraction φ (ExteriorAlgebra.ιMulti R (n + 1) v) ∈ ⋀[R]^n E := by
    intro n
    induction n with
    | zero =>
      intro v
      rw [ιMulti_succ_apply, contraction, CliffordAlgebra.contractLeft_ι_mul,
        ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one, mul_zero, sub_zero]
      have := ExteriorAlgebra.gradedAlgebra R E
      exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)
    | succ m ih =>
      intro v
      rw [ιMulti_succ_apply, contraction, CliffordAlgebra.contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (ιMulti_mem (m + 1) _)) ?_
      have := ExteriorAlgebra.gradedAlgebra R E
      have h := SetLike.mul_mem_graded (ι_mem_one (v 0)) (ih (Fin.tail v))
      rwa [Nat.add_comm 1 m] at h
  rw [← exteriorPower.ιMulti_span_fixedDegree] at hx
  exact (Submodule.span_le (p := (⋀[R]^n E).comap (contraction φ))).mpr
    (by rintro _ ⟨v, rfl⟩; exact key n v) hx

/-- Contraction of a product of `q + 1` vectors in the exterior algebra is the alternating sum
of the products with one factor removed, weighted by the value of the functional at the removed
factor. -/
theorem contraction_ιMulti (φ : Module.Dual R E) (q : ℕ) (v : Fin (q + 1) → E) :
    contraction φ (ExteriorAlgebra.ιMulti R (q + 1) v) =
      ∑ k : Fin (q + 1), ((-1 : R) ^ k.val * φ (v k)) •
        ExteriorAlgebra.ιMulti R q (v ∘ k.succAbove) := by
  induction q with
  | zero =>
    simp [ExteriorAlgebra.ιMulti, Koszul.contraction,
      CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  | succ q ih =>
    rw [Koszul.ιMulti_succ_apply, Koszul.contraction,
      CliffordAlgebra.contractLeft_ι_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Function.comp_def,
      ← Fin.tail_def]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Koszul.ιMulti_succ_apply]
    simp only [Fin.val_succ, pow_succ, mul_smul,
      mul_neg, neg_mul, mul_smul_comm, Fin.succ_succAbove_zero,
      Fin.succ_succAbove_succ, Fin.tail_def, mul_one, neg_smul]

/-- The graded Koszul differential `⋀^(n+1) E →ₗ[R] ⋀ⁿ E`, the restriction of
`Koszul.contraction φ` to exterior powers. -/
noncomputable def d (φ : Module.Dual R E) (n : ℕ) : (⋀[R]^(n + 1) E) →ₗ[R] (⋀[R]^n E) :=
  LinearMap.codRestrict _ (contraction φ ∘ₗ (⋀[R]^(n + 1) E).subtype)
    (fun x => contraction_mem φ n x.2)

/-- As an element of `⋀(E)`, the Koszul differential of `x` is the contraction of `x` by `φ`. -/
@[simp]
theorem d_apply_coe (φ : Module.Dual R E) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    ((d φ n x : ⋀[R]^n E) : ExteriorAlgebra R E) = contraction φ (x : ExteriorAlgebra R E) :=
  rfl

/-- The Koszul differential squares to zero: `d φ n ∘ d φ (n + 1) = 0`. -/
theorem d_comp_d (φ : Module.Dual R E) (n : ℕ) : (d φ n).comp (d φ (n + 1)) = 0 :=
  LinearMap.ext fun x => Subtype.ext <|
    CliffordAlgebra.contractLeft_contractLeft φ (x : ExteriorAlgebra R E)

/-- The Koszul complex `K_•(φ)` of a functional `φ : E →ₗ[R] R`: the chain complex of
`R`-modules with `⋀ⁿ E` in degree `n` and the contraction differential. -/
noncomputable def complex (φ : Module.Dual R E) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n E))
    (fun n => ModuleCat.ofHom (d φ n))
    (fun n => by
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        d_comp_d])

/-- The differential of `Koszul.complex φ` from degree `n + 1` to degree `n` is `Koszul.d φ n`. -/
theorem complex_d (φ : Module.Dual R E) (n : ℕ) :
    (complex φ).d (n + 1) n = ModuleCat.ofHom (d φ n) :=
  ChainComplex.of_d (fun n => ModuleCat.of R (⋀[R]^n E)) (fun n => ModuleCat.ofHom (d φ n)) n

variable {r : ℕ}

/-- The functional `Rʳ →ₗ[R] R` attached to a sequence `f₁, …, f_r` of elements of `R`,
namely `v ↦ ∑ i, vᵢ * fᵢ`; it sends the `i`-th standard basis vector to `fᵢ`. -/
@[stacks 0623]
noncomputable def seqDual (f : Fin r → R) : Module.Dual R (Fin r → R) :=
  Fintype.linearCombination R f

/-- `Koszul.seqDual f` sends `v` to `∑ i, vᵢ * fᵢ`. -/
theorem seqDual_apply (f v : Fin r → R) : seqDual f v = ∑ i, v i * f i := by
  simp [seqDual, Fintype.linearCombination_apply, smul_eq_mul]

/-- `Koszul.seqDual f` sends `c` times the `i`-th standard basis vector to `c * fᵢ`. -/
theorem seqDual_apply_single (f : Fin r → R) (i : Fin r) (c : R) :
    seqDual f (Pi.single i c) = c * f i := by
  simp [seqDual, smul_eq_mul]

/-- `Koszul.seqDual f` sends the `i`-th standard basis vector to `fᵢ`. -/
@[simp] theorem seqDual_single (f : Fin r → R) (i : Fin r) :
    seqDual f (Pi.single i 1) = f i := by
  rw [seqDual_apply_single, one_mul]

/-- `Koszul.seqDual f` is the combination `∑ i, fᵢ • prᵢ` of the coordinate projections of
`Rʳ` weighted by the `fᵢ`. -/
theorem seqDual_eq_sum_smul_proj (f : Fin r → R) :
    seqDual f = ∑ i, f i • (LinearMap.proj i : (Fin r → R) →ₗ[R] R) := by
  refine LinearMap.ext fun v => ?_
  simp [seqDual_apply, LinearMap.sum_apply, mul_comm]

/-- The Koszul complex `K_•(f₁, …, f_r)` of a sequence of elements of `R`: the Koszul
complex of the functional `Koszul.seqDual f` on `Rʳ`. -/
@[stacks 0623, ega "III 1.1.1"]
noncomputable def seqComplex (f : Fin r → R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  complex (seqDual f)

/-- The differential of `Koszul.seqComplex f` from degree `n + 1` to degree `n` is
`Koszul.d (Koszul.seqDual f) n`. -/
theorem seqComplex_d (f : Fin r → R) (n : ℕ) :
    (seqComplex f).d (n + 1) n = ModuleCat.ofHom (d (seqDual f) n) :=
  complex_d (seqDual f) n

/-- The Koszul complex of a sequence of length `r` vanishes in degrees above `r`: there are no
nonzero alternating forms of degree larger than the rank. -/
theorem seqComplex_isZero_of_lt (f : Fin r → R) (j : ℕ) (hj : r < j) :
    Limits.IsZero ((seqComplex f).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (⋀[R]^j (Fin r → R))
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (Pi.basisFun R (Fin r)) (Pi.basisFun R (Fin r)).span_eq j
  simpa using hj

/-- The Koszul complex of `f₁, …, f_r` with coefficients in an `R`-module `M`, that is
`K_•(f₁, …, f_r) ⊗_R M`: in degree `n` it is `⋀ⁿ(Rʳ) ⊗[R] M`, with differential
`d ⊗ id`. -/
noncomputable def seqComplexTensor (f : Fin r → R) (M : Type w)
    [AddCommGroup M] [Module R M] : ChainComplex (ModuleCat.{max u w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] M))
    (fun n => ModuleCat.ofHom (LinearMap.rTensor M (d (seqDual f) n)))
    (fun n => by
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        ← LinearMap.rTensor_comp, d_comp_d, LinearMap.rTensor_zero])

/-- The differential of `Koszul.seqComplexTensor f M` from degree `n + 1` to degree `n` is
`Koszul.d (Koszul.seqDual f) n ⊗ id_M`. -/
theorem seqComplexTensor_d (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    (seqComplexTensor f M).d (n + 1) n = ModuleCat.ofHom (LinearMap.rTensor M (d (seqDual f) n)) :=
  ChainComplex.of_d (fun n => ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] M))
    (fun n => ModuleCat.ofHom (LinearMap.rTensor M (d (seqDual f) n))) n

/-- A sequence `f₁, …, f_r` is `M`-Koszul-regular if `Hᵢ(K_•(f) ⊗_R M) = 0` for all
`i ≠ 0`. -/
@[stacks 062E "(1)"]
def IsKoszulRegularOn (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  ∀ i ≠ 0, Limits.IsZero ((seqComplexTensor f M).homology i)

/-- A sequence `f₁, …, f_r` is `M`-`H₁`-regular if `H₁(K_•(f) ⊗_R M) = 0`. -/
@[stacks 062E "(2)"]
def IsH1RegularOn (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  Limits.IsZero ((seqComplexTensor f M).homology 1)

/-- A sequence `f₁, …, f_r` is Koszul-regular if `Hᵢ(K_•(f)) = 0` for all `i ≠ 0`. -/
@[stacks 062E "(3)"]
def IsKoszulRegular (f : Fin r → R) : Prop :=
  ∀ i ≠ 0, Limits.IsZero ((seqComplex f).homology i)

/-- A sequence `f₁, …, f_r` is `H₁`-regular if `H₁(K_•(f)) = 0`. -/
@[stacks 062E "(4)"]
def IsH1Regular (f : Fin r → R) : Prop :=
  Limits.IsZero ((seqComplex f).homology 1)

/-- The right unitor `- ⊗[R] R ≅ -` is natural: `g ∘ rid = rid ∘ (g ⊗ id)`. -/
theorem rid_toModuleIso_naturality {A B : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (g : A →ₗ[R] B) :
    (TensorProduct.rid R A).toModuleIso.hom ≫ ModuleCat.ofHom g
      = ModuleCat.ofHom (LinearMap.rTensor R g) ≫ (TensorProduct.rid R B).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun x y => ?_
  simp

/-- Taking coefficients in `R` itself changes nothing: `K_•(f) ⊗_R R ≅ K_•(f)`,
degreewise the right unitor `⋀ⁿ(Rʳ) ⊗[R] R ≃ₗ[R] ⋀ⁿ(Rʳ)`. -/
noncomputable def seqComplexTensorSelfIso (f : Fin r → R) :
    seqComplexTensor f R ≅ seqComplex f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.rid R (⋀[R]^n (Fin r → R))).toModuleIso)
    (fun i j hij => by
      obtain rfl : j + 1 = i := hij
      rw [seqComplexTensor_d, seqComplex_d]
      exact rid_toModuleIso_naturality (d (seqDual f) j))

/-- The homology of `K_•(f) ⊗_R R` agrees with that of `K_•(f)`. -/
noncomputable def homologySelfIso (f : Fin r → R) (i : ℕ) :
    (seqComplexTensor f R).homology i ≅ (seqComplex f).homology i :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (seqComplexTensorSelfIso f)

/-- A sequence is `R`-`H₁`-regular if and only if it is `H₁`-regular. -/
theorem isH1RegularOn_self_iff (f : Fin r → R) : IsH1RegularOn f R ↔ IsH1Regular f :=
  ⟨fun h => h.of_iso (homologySelfIso f 1).symm, fun h => h.of_iso (homologySelfIso f 1)⟩

/-- A sequence is `R`-Koszul-regular if and only if it is Koszul-regular. -/
theorem isKoszulRegularOn_self_iff (f : Fin r → R) : IsKoszulRegularOn f R ↔ IsKoszulRegular f :=
  ⟨fun h i hi => (h i hi).of_iso (homologySelfIso f i).symm,
    fun h i hi => (h i hi).of_iso (homologySelfIso f i)⟩

end Koszul
