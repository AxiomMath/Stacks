module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DirectSum.GradedSubmodule

/-! # Differential graded submodules

Let `M` be a right differential graded module over a differential graded algebra `(A, d)`. A
right `A`-submodule of `M` which is *homogeneous* — it contains every graded component of each of
its elements — and *stable under the differential* is again a differential graded `A`-module, and
its inclusion into `M` is a homomorphism of differential graded modules.
`DifferentialGradedModule.GradedSub` is that data, and
`DifferentialGradedModule.GradedSub.obj` the differential graded module it carries.

## Main definitions

* `DifferentialGradedModule.GradedSub`: a homogeneous, differential-stable right `A`-submodule.
* `DifferentialGradedModule.GradedSub.obj`: it, as a differential graded `A`-module.
* `DifferentialGradedModule.GradedSub.ι`: the inclusion into the ambient module.
* `DifferentialGradedModule.GradedSub.incl`: the inclusion of one such submodule into a larger
  one.
* `DifferentialGradedModule.GradedSub.gradedHomOfRestrict`: a map of *graded* right `A`-modules
  between two such submodules, from an ambient `R`-linear map carrying one into the other.

## Main results

* `DifferentialGradedModule.GradedSub.mem_obj_grading`: homogeneity in the submodule is
  homogeneity in the ambient module.
* `DifferentialGradedModule.GradedSub.ι_injective` and
  `DifferentialGradedModule.GradedSub.incl_injective`: the inclusions are injective.
* `DifferentialGradedModule.GradedSub.isAdmissibleMono_incl`: an inclusion with a graded
  retraction is an admissible monomorphism.

## Implementation notes

*The two hypotheses are stated at the ambient module.* `decompose_mem` and `d_mem` quantify over
`x : M.M` with `x ∈ carrier`, not over elements of the subtype: the grading and the differential
of the ambient module are what they talk about, and a binder at the subtype would need its
`Module` instances to synthesize below default transparency, which they do not. The conversions
into the `restrictScalars R` form that `Submodule.inducedGrading` takes are
`Submodule.restrictScalars_mem`, which is definitional.

*The grading and the decomposition are named separately*, with their types written in terms of
the submodule over the opposite algebra, so that the `R`-module structure the object carries is
the one restricted from the right `A`-action rather than an unrelated copy. This is the pattern of
`DifferentialGradedModule.Hom.kernelObj`, whose implementation notes say more.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI), differential graded
  modules.
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible
  monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {M : DifferentialGradedModule A}

/-- **A differential graded submodule of `M`**: a right `A`-submodule which contains every
graded component of each of its elements and is stable under the differential. -/
structure GradedSub (M : DifferentialGradedModule A) where
  /-- The underlying right `A`-submodule. -/
  carrier : Submodule (MulOpposite A.A) M.M
  /-- Homogeneity: every graded component of an element of the submodule is in the submodule. -/
  decompose_mem : ∀ (n : ℤ) (x : M.M), x ∈ carrier →
    (DirectSum.decompose M.grading x n : M.M) ∈ carrier
  /-- Stability under the differential. -/
  d_mem : ∀ x : M.M, x ∈ carrier → M.d x ∈ carrier

namespace GradedSub

variable (S : GradedSub M)

/-- Membership in the submodule, read after restricting scalars to `R`. -/
theorem mem_restrictScalars {x : M.M} : x ∈ (S.carrier).restrictScalars R ↔ x ∈ S.carrier :=
  Submodule.restrictScalars_mem _ _ _

/-- The grading of a differential graded submodule: the one induced by the grading of the
ambient module. -/
def grading (n : ℤ) : Submodule R ↥S.carrier :=
  Submodule.inducedGrading M.grading ((S.carrier).restrictScalars R) n

/-- A differential graded submodule is a graded submodule, so it inherits the direct-sum
decomposition. -/
@[instance_reducible]
def decomposition : DirectSum.Decomposition S.grading :=
  Submodule.inducedGrading.decomposition M.grading ((S.carrier).restrictScalars R)
    (fun n x hx => S.decompose_mem n x hx)

/-- The differential of a differential graded submodule: the restriction of that of the ambient
module. -/
def d : ↥S.carrier →ₗ[R] ↥S.carrier :=
  LinearMap.restrict M.d (p := (S.carrier).restrictScalars R)
    (q := (S.carrier).restrictScalars R) (fun x hx => S.d_mem x hx)

/-- The differential of a differential graded submodule, read in the ambient module, is the
differential of the ambient module. -/
@[simp] theorem d_coe_apply (x : ↥S.carrier) : ((S.d x : ↥S.carrier) : M.M) = M.d (x : M.M) :=
  rfl

/-- **A differential graded submodule, as a differential graded module.** -/
@[implicit_reducible]
def obj : DifferentialGradedModule A where
  M := ↥S.carrier
  grading := S.grading
  decomposition := S.decomposition
  smul_mem := by
    intro n m x a hx ha
    change (x : M.M) ∈ M.grading n at hx
    change (MulOpposite.op a • x : M.M) ∈ M.grading (n + m)
    exact M.smul_mem n m x.val a hx ha
  d := S.d
  d_comp_d := by
    ext x
    have hdd := LinearMap.congr_fun M.d_comp_d (x : M.M)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero,
      d_coe_apply] using hdd
  d_mem := by
    intro n x hx
    change (x : M.M) ∈ M.grading n at hx
    change (M.d (x : M.M)) ∈ M.grading (n + 1)
    exact M.d_mem n x.val hx
  leibniz := by
    intro n m x a hx ha
    change (x : M.M) ∈ M.grading n at hx
    exact Subtype.ext (M.leibniz n m x.val a hx ha)

/-- The grading of `DifferentialGradedModule.GradedSub.obj` is
`DifferentialGradedModule.GradedSub.grading`. -/
@[simp] theorem obj_grading : S.obj.grading = S.grading := rfl

/-- **The inclusion of a differential graded submodule into the ambient module.** -/
def ι : S.obj ⟶ M where
  toFun := ((S.carrier).restrictScalars R).subtype
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := by ext x; rfl

/-- The inclusion of a differential graded submodule sends an element to itself, read in the
ambient module. -/
@[simp] theorem ι_toFun_apply (x : ↥S.carrier) : (S.ι).toFun x = (x : M.M) := rfl

/-- The inclusion of a differential graded submodule is injective. -/
theorem ι_injective : Function.Injective (S.ι).toFun := fun _ _ h => Subtype.ext h

/-- An element of a differential graded submodule lies in it, read in the ambient module. -/
theorem ι_mem (x : ↥S.carrier) : (S.ι).toFun x ∈ S.carrier := x.2

/-- **Homogeneity in a differential graded submodule is homogeneity in the ambient module.** -/
theorem mem_obj_grading {n : ℤ} {x : S.obj.M} :
    x ∈ S.obj.grading n ↔ (S.ι).toFun x ∈ M.grading n := Submodule.mem_inducedGrading

/-- **The inclusion of one differential graded submodule into a larger one.** -/
def incl {S T : GradedSub M} (h : S.carrier ≤ T.carrier) : S.obj ⟶ T.obj where
  toFun := LinearMap.restrict LinearMap.id (p := (S.carrier).restrictScalars R)
    (q := (T.carrier).restrictScalars R) (fun _ hx => h hx)
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := by ext x; rfl

/-- The inclusion into a larger differential graded submodule, followed by the inclusion of that
one into the ambient module, is the inclusion of the smaller one. -/
@[simp] theorem incl_ι {S T : GradedSub M} (h : S.carrier ≤ T.carrier) (x : S.obj.M) :
    (T.ι).toFun ((incl h).toFun x) = (S.ι).toFun x := rfl

/-- An inclusion of differential graded submodules is injective. -/
theorem incl_injective {S T : GradedSub M} (h : S.carrier ≤ T.carrier) :
    Function.Injective (incl h).toFun := fun x y he =>
  S.ι_injective ((incl_ι h x).symm.trans ((congrArg (T.ι).toFun he).trans (incl_ι h y)))

/-- **A map of graded right `A`-modules between two differential graded submodules**, from an
`R`-linear endomorphism of the ambient module which commutes with the right `A`-action, preserves
degrees, and carries the source submodule into the target one; it need not commute with the
differential. -/
def gradedHomOfRestrict {S T : GradedSub M} (f : M.M →ₗ[R] M.M)
    (hsmul : ∀ (x : M.M) (a : A.A), f (MulOpposite.op a • x) = MulOpposite.op a • f x)
    (hgrading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → f x ∈ M.grading n)
    (hmem : ∀ x : M.M, x ∈ S.carrier → f x ∈ T.carrier) : GradedHom S.obj T.obj where
  toFun := LinearMap.restrict f (p := (S.carrier).restrictScalars R)
    (q := (T.carrier).restrictScalars R) (fun x hx => hmem x hx)
  map_smul _ a := Subtype.ext (hsmul _ a)
  map_grading n _ hx := hgrading n _ hx

/-- The map `DifferentialGradedModule.GradedSub.gradedHomOfRestrict f`, followed by the inclusion
of the target, is `f` applied after the inclusion of the source. -/
@[simp] theorem gradedHomOfRestrict_ι {S T : GradedSub M} (f : M.M →ₗ[R] M.M)
    (hsmul hgrading hmem) (x : S.obj.M) :
    (T.ι).toFun ((gradedHomOfRestrict (S := S) (T := T) f hsmul hgrading hmem).toFun x)
      = f ((S.ι).toFun x) := rfl

/-- **An inclusion of differential graded submodules with a graded retraction is an admissible
monomorphism.** The retraction is given by an endomorphism `f` of the ambient module as in
`DifferentialGradedModule.GradedSub.gradedHomOfRestrict`, which must carry the larger submodule
into the smaller one and fix the smaller one pointwise. -/
theorem isAdmissibleMono_incl {S T : GradedSub M} (h : S.carrier ≤ T.carrier)
    (f : M.M →ₗ[R] M.M)
    (hsmul : ∀ (x : M.M) (a : A.A), f (MulOpposite.op a • x) = MulOpposite.op a • f x)
    (hgrading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → f x ∈ M.grading n)
    (hmem : ∀ x : M.M, x ∈ T.carrier → f x ∈ S.carrier)
    (hfix : ∀ x : M.M, x ∈ S.carrier → f x = x) :
    IsAdmissibleMono (incl h) :=
  ⟨gradedHomOfRestrict (S := T) (T := S) f hsmul hgrading hmem,
    fun x => S.ι_injective (by
      rw [gradedHomOfRestrict_ι, incl_ι]
      exact hfix _ (S.ι_mem x))⟩

end GradedSub

end DifferentialGradedModule

end
