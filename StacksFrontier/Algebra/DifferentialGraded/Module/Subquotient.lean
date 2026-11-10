module

public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Kernels and cokernels of homomorphisms of differential graded modules

Let `f : M ⟶ N` be a homomorphism of right differential graded modules over a differential
graded algebra `(A, d)`. Its kernel and its image are right `A`-submodules which are homogeneous
— they contain every graded component of each of their elements — and stable under the
differential. Consequently the kernel, and the quotient of `N` by the image, carry differential
graded module structures, and the inclusion of the kernel and the projection onto the quotient
are homomorphisms of differential graded modules.

## Main definitions

* `DifferentialGradedModule.Hom.ker` and `DifferentialGradedModule.Hom.range`: the kernel and
  the image of `f`, as right `A`-submodules.
* `DifferentialGradedModule.Hom.kernelGrading`, `DifferentialGradedModule.Hom.kernelD`,
  `DifferentialGradedModule.Hom.kernelObj` and `DifferentialGradedModule.Hom.kernelι`: the
  kernel as a differential graded module and its inclusion into `M`.
* `DifferentialGradedModule.Hom.cokernelGrading`, `DifferentialGradedModule.Hom.cokernelD`,
  `DifferentialGradedModule.Hom.cokernelObj` and `DifferentialGradedModule.Hom.cokernelπ`: the
  quotient of `N` by the image and the projection onto it.

## Main results

* `DifferentialGradedModule.Hom.kernelι_comp`: the kernel inclusion followed by `f` vanishes.
* `DifferentialGradedModule.Hom.comp_cokernelπ`: `f` followed by the cokernel projection
  vanishes.

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
  {M N : DifferentialGradedModule.{u, v, w} A}

/-- The kernel of a homomorphism of differential graded modules, as a right `A`-submodule of the
source. -/
def Hom.ker (f : Hom M N) : Submodule (MulOpposite A.A) M.M where
  carrier := {x | f.toFun x = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [show c • x = (MulOpposite.op c.unop) • x from rfl, f.map_smul, hx, smul_zero]

/-- An element lies in the kernel of `f` exactly when `f` sends it to zero. -/
theorem Hom.mem_ker (f : Hom M N) (x : M.M) : x ∈ f.ker ↔ f.toFun x = 0 := Iff.rfl

/-- The image of a homomorphism of differential graded modules, as a right `A`-submodule of the
target. -/
def Hom.range (f : Hom M N) : Submodule (MulOpposite A.A) N.M where
  carrier := {y | ∃ x, f.toFun x = y}
  add_mem' := by rintro a b ⟨x, rfl⟩ ⟨z, rfl⟩; exact ⟨x + z, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c y ⟨x, rfl⟩
    exact ⟨(MulOpposite.op c.unop) • x, by rw [f.map_smul]; rfl⟩

/-- An element lies in the image of `f` exactly when it is a value of `f`. -/
theorem Hom.mem_range (f : Hom M N) (y : N.M) : y ∈ f.range ↔ ∃ x, f.toFun x = y := Iff.rfl

/-- The image of `f`, with scalars restricted to `R`, is the range of the underlying linear
map. -/
theorem Hom.range_restrictScalars (f : Hom M N) :
    (f.range).restrictScalars R = LinearMap.range f.toFun := by
  ext y
  rw [Submodule.restrictScalars_mem, Hom.mem_range, LinearMap.mem_range]

/-- A homomorphism commutes with taking graded components. -/
private theorem Hom.map_decompose (f : Hom M N) (x : M.M) (n : ℤ) :
    f.toFun (DirectSum.decompose M.grading x n : M.M) =
      (DirectSum.decompose N.grading (f.toFun x) n : N.M) :=
  (DirectSum.coe_decompose_apply_map M.grading N.grading f.toFun
    (fun i y hy => f.map_grading i y hy) x n).symm

/-- A homomorphism commutes with the differentials. -/
private theorem Hom.map_d_apply (f : Hom M N) (x : M.M) : f.toFun (M.d x) = N.d (f.toFun x) := by
  simpa using LinearMap.congr_fun f.map_d x

/-- The kernel is homogeneous: every graded component of an element of the kernel is again in
the kernel. -/
theorem Hom.decompose_mem_ker (f : Hom M N) (n : ℤ) (x : M.M)
    (hx : x ∈ (f.ker).restrictScalars R) :
    (DirectSum.decompose M.grading x n : M.M) ∈ (f.ker).restrictScalars R := by
  rw [Submodule.restrictScalars_mem, Hom.mem_ker] at hx ⊢
  rw [f.map_decompose, hx]
  simp

/-- The image is homogeneous: every graded component of an element of the image is again in the
image. -/
theorem Hom.decompose_mem_range (f : Hom M N) (n : ℤ) (y : N.M)
    (hy : y ∈ (f.range).restrictScalars R) :
    (DirectSum.decompose N.grading y n : N.M) ∈ (f.range).restrictScalars R := by
  rw [Hom.range_restrictScalars, LinearMap.mem_range] at hy ⊢
  obtain ⟨x, rfl⟩ := hy
  exact ⟨_, f.map_decompose x n⟩

/-- The differential maps the kernel into itself. -/
theorem Hom.d_mem_ker (f : Hom M N) (x : M.M) (hx : x ∈ (f.ker).restrictScalars R) :
    M.d x ∈ (f.ker).restrictScalars R := by
  rw [Submodule.restrictScalars_mem, Hom.mem_ker] at hx ⊢
  rw [f.map_d_apply, hx, map_zero]

/-- The differential maps the image into itself. -/
theorem Hom.d_mem_range (f : Hom M N) (y : N.M) (hy : y ∈ (f.range).restrictScalars R) :
    N.d y ∈ (f.range).restrictScalars R := by
  rw [Hom.range_restrictScalars, LinearMap.mem_range] at hy ⊢
  obtain ⟨x, rfl⟩ := hy
  exact ⟨M.d x, f.map_d_apply x⟩

/-- The grading of the kernel of `f`: the grading induced on it by that of the source. -/
noncomputable def Hom.kernelGrading (f : Hom M N) (n : ℤ) : Submodule R ↥f.ker :=
  Submodule.inducedGrading M.grading ((f.ker).restrictScalars R) n

/-- The kernel of `f` is a graded submodule of the source. -/
@[instance_reducible]
noncomputable def Hom.kernelDecomposition (f : Hom M N) :
    DirectSum.Decomposition f.kernelGrading :=
  Submodule.inducedGrading.decomposition M.grading ((f.ker).restrictScalars R)
    (fun n m hm => f.decompose_mem_ker n m hm)

/-- The differential of the kernel of `f`, the restriction of that of the source. -/
def Hom.kernelD (f : Hom M N) : ↥f.ker →ₗ[R] ↥f.ker :=
  LinearMap.restrict M.d (p := (f.ker).restrictScalars R) (q := (f.ker).restrictScalars R)
    (fun x hx => f.d_mem_ker x hx)

/-- The differential of the kernel of `f` is computed in the source. -/
@[simp] theorem Hom.kernelD_coe_apply (f : Hom M N) (x : ↥f.ker) :
    ((f.kernelD x : ↥f.ker) : M.M) = M.d (x : M.M) := rfl

/-- The kernel of `f` as a differential graded module. -/
@[implicit_reducible]
noncomputable def Hom.kernelObj (f : Hom M N) : DifferentialGradedModule.{u, v, w} A where
  M := ↥f.ker
  grading := f.kernelGrading
  decomposition := f.kernelDecomposition
  smul_mem n m x a hx ha := M.smul_mem n m x.val a hx ha
  d := f.kernelD
  d_comp_d := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero,
      Hom.kernelD_coe_apply] using LinearMap.congr_fun M.d_comp_d (x : M.M)
  d_mem n x hx := M.d_mem n x.val hx
  leibniz n m x a hx ha := Subtype.ext (M.leibniz n m x.val a hx ha)

/-- The grading of `f.kernelObj` is `f.kernelGrading`. -/
@[simp] theorem Hom.kernelObj_grading (f : Hom M N) : (f.kernelObj).grading = f.kernelGrading :=
  rfl

/-- The inclusion of the kernel of `f` into the source. -/
def Hom.kernelι (f : Hom M N) : f.kernelObj ⟶ M where
  toFun := ((f.ker).restrictScalars R).subtype
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := by ext x; rfl

/-- The kernel inclusion sends an element of the kernel to itself, as an element of the
source. -/
@[simp] theorem Hom.kernelι_toFun_apply (f : Hom M N) (x : ↥f.ker) :
    (f.kernelι).toFun x = (x : M.M) := rfl

/-- The kernel inclusion followed by `f` is zero. -/
theorem Hom.kernelι_comp (f : Hom M N) : f.kernelι ≫ f = 0 :=
  Hom.ext (LinearMap.ext fun x => x.2)

/-- The grading of the cokernel of `f`: the grading induced on the quotient by that of the
target. -/
noncomputable def Hom.cokernelGrading (f : Hom M N) (n : ℤ) :
    Submodule R (N.M ⧸ (f.range).restrictScalars R) :=
  Submodule.quotientGrading N.grading ((f.range).restrictScalars R) n

/-- The quotient of the target by the image of `f` is graded. -/
@[instance_reducible]
noncomputable def Hom.cokernelDecomposition (f : Hom M N) :
    DirectSum.Decomposition f.cokernelGrading :=
  Submodule.quotientGrading.decomposition N.grading ((f.range).restrictScalars R)
    (fun n y hy => f.decompose_mem_range n y hy)

/-- The differential induced on the quotient of the target by the image of `f`. -/
def Hom.cokernelD (f : Hom M N) : (N.M ⧸ f.range) →ₗ[R] (N.M ⧸ f.range) :=
  Submodule.mapQ ((f.range).restrictScalars R) ((f.range).restrictScalars R) N.d
    (fun y hy => f.d_mem_range y hy)

/-- The differential of the cokernel of `f` sends the class of `y` to the class of `N.d y`. -/
@[simp] theorem Hom.cokernelD_mk (f : Hom M N) (y : N.M) :
    f.cokernelD (Submodule.Quotient.mk (p := f.range) y) =
      Submodule.Quotient.mk (p := f.range) (N.d y) := rfl

/-- The quotient of the target of `f` by its image, as a differential graded module. -/
@[implicit_reducible]
noncomputable def Hom.cokernelObj (f : Hom M N) : DifferentialGradedModule.{u, v, w} A where
  M := N.M ⧸ f.range
  isScalarTower := by
    constructor
    intro r a ybar
    induction ybar using Submodule.Quotient.induction_on with
    | _ y => exact congrArg (Submodule.Quotient.mk (p := f.range)) (smul_assoc r a y)
  grading := f.cokernelGrading
  decomposition := f.cokernelDecomposition
  smul_mem := by
    rintro n m _ a ⟨y, hyN, rfl⟩ ha
    exact ⟨(MulOpposite.op a) • y, N.smul_mem n m y a hyN ha, rfl⟩
  d := f.cokernelD
  d_comp_d := by
    apply LinearMap.ext
    intro ybar
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (f.range) ybar
    have hdd := LinearMap.congr_fun N.d_comp_d y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    change f.cokernelD (f.cokernelD (Submodule.Quotient.mk (p := f.range) y)) = 0
    rw [Hom.cokernelD_mk, Hom.cokernelD_mk, hdd]
    simp
  d_mem := by
    rintro n _ ⟨y, hyN, rfl⟩
    exact ⟨N.d y, N.d_mem n y hyN, rfl⟩
  leibniz := by
    rintro n m _ a ⟨y, hyN, rfl⟩ ha
    change f.cokernelD ((MulOpposite.op a) • (Submodule.Quotient.mk (p := f.range) y)) =
      (MulOpposite.op a) • f.cokernelD (Submodule.Quotient.mk (p := f.range) y) +
        (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a)) • Submodule.Quotient.mk (p := f.range) y)
    rw [← Submodule.Quotient.mk_smul, Hom.cokernelD_mk, Hom.cokernelD_mk,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, N.leibniz n m y a hyN ha]

/-- The underlying module of `f.cokernelObj` is the quotient of the target by the image of
`f`. -/
@[simp] theorem Hom.cokernelObj_M (f : Hom M N) : (f.cokernelObj).M = (N.M ⧸ f.range) := rfl

/-- The projection of the target of `f` onto the quotient by its image. -/
def Hom.cokernelπ (f : Hom M N) : N ⟶ f.cokernelObj where
  toFun := ((f.range).restrictScalars R).mkQ
  map_smul := by
    intro x a
    change Submodule.Quotient.mk (p := f.range) ((MulOpposite.op a) • x) =
      (MulOpposite.op a) • Submodule.Quotient.mk (p := f.range) x
    rw [Submodule.Quotient.mk_smul]
  map_grading _ x hx := ⟨x, hx, rfl⟩
  map_d := LinearMap.ext fun _ => rfl

/-- The cokernel projection sends an element of the target to its class. -/
@[simp] theorem Hom.cokernelπ_toFun_apply (f : Hom M N) (y : N.M) :
    (f.cokernelπ).toFun y = Submodule.Quotient.mk (p := f.range) y := rfl

/-- `f` followed by the cokernel projection is zero. -/
theorem Hom.comp_cokernelπ (f : Hom M N) : f ≫ f.cokernelπ = 0 := by
  refine Hom.ext (LinearMap.ext fun x => ?_)
  change Submodule.Quotient.mk (p := f.range) (f.toFun x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

end DifferentialGradedModule
