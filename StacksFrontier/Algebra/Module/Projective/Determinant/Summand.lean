module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import StacksFrontier.Algebra.Module.Projective.Determinant.Graded

/-!
# The determinant line is a direct summand of the exterior algebra

Let `R` be a commutative ring and `M` a finite projective `R`-module. The determinant line
`ProjectiveDeterminant.submodule` is the supremum, inside `⋀_R(M)`, of the rank-stratum summands
`ProjectiveDeterminant.component R M n`, the `n`-th of which is the image of `⋀ⁿ_R M` under
multiplication by the idempotent cutting out the rank-`n` stratum. This file produces the
splitting: a linear projection of the exterior algebra onto the determinant line which is the
identity on it, and the same one degree at a time.

## Why a splitting is what is needed

Construction (3) of Stacks 01BH — `M ↦ ℱ_M`, the sheafification of `V ↦ 𝒪_X(V) ⊗_R M` — does
**not** carry an injection of modules to a monomorphism of sheaves of modules: base change along
`R → 𝒪_X(V)` is not left exact. It does carry a *split* injection to a split monomorphism, which
is `Stacks.AssociatedSheaf.isSplitMono_associatedSheafFunctor_map`
(`StacksFrontier/Topology/Sheaves/Modules/AssociatedSheaf/FreeRetract.lean`), and that lemma
consumes a `CategoryTheory.Retract` of modules. So recognising `ℱ_{det M}` as a subsheaf of
`ℱ_{⋀ M}`, which a local description of the determinant of a sheaf of modules needs, requires
`det M` as a direct summand of `⋀_R(M)` rather than merely as a submodule of it.

## The projection

The exterior powers are an internal grading of the exterior algebra
(`ExteriorAlgebra.gradedAlgebra`), so there is a degreewise projection
`ProjectiveDeterminant.gradeProj n : ⋀_R(M) →ₗ[R] ⋀_R(M)`, the identity on `⋀ⁿ_R M` and zero on
every other exterior power. Multiplying its value by the rank-`n` idempotent lands in
`component R M n`, and summing over a finite set of degrees covering the rank strata gives the
projection onto the determinant line: on `component R M n` the `n`-th term of the sum is the
identity, because the idempotent acts as the identity there, and every other term vanishes
because `component R M m ≤ ⋀ᵐ_R M`.

Only finitely many degrees may be used, which is what `exists_finset_rankLocus_cover` provides:
the rank strata are clopen and cover `Spec R`, which is quasi-compact, so finitely many of them
already do, and the idempotents of the remaining degrees vanish.

## Main definitions

* `ProjectiveDeterminant.gradeProj`: the projection of the exterior algebra onto its degree-`n`
  part, as an endomorphism of the exterior algebra.
* `ProjectiveDeterminant.componentProj`: the projection of `⋀ⁿ_R M` onto `component R M n`.
* `ProjectiveDeterminant.submoduleProj`: the projection of the exterior algebra onto the
  determinant line, for a finite set of degrees covering the rank strata.

## Main results

* `ProjectiveDeterminant.componentRetract`: **each rank-stratum summand is a direct summand of
  the exterior power containing it.**
* `ProjectiveDeterminant.componentRetractExteriorAlgebra`: the same inside the whole exterior
  algebra.
* `ProjectiveDeterminant.submoduleRetract`: **the determinant line is a direct summand of the
  exterior algebra.**

## References

* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ProjectiveDeterminant

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### The degreewise projection of the exterior algebra -/

/-- The projection of `⋀_R(M)` onto its degree-`n` part, read as an endomorphism of `⋀_R(M)`.
The exterior powers are an internal grading of the exterior algebra
(`ExteriorAlgebra.gradedAlgebra`), so the decomposition of an element into homogeneous parts is a
linear equivalence and this is one of its components followed by the inclusion. -/
def gradeProj (n : ℕ) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  (⋀[R]^n M).subtype ∘ₗ DirectSum.component R ℕ (fun i : ℕ => ↥(⋀[R]^i M)) n ∘ₗ
    (DirectSum.decomposeLinearEquiv fun i : ℕ => ⋀[R]^i M).toLinearMap

/-- The degree-`n` projection lands in the degree-`n` exterior power. -/
lemma gradeProj_mem (n : ℕ) (x : ExteriorAlgebra R M) : gradeProj n x ∈ ⋀[R]^n M :=
  (DirectSum.decompose (fun i : ℕ => ⋀[R]^i M) x n).2

/-- The degree-`n` projection is the identity on the degree-`n` exterior power. -/
lemma gradeProj_of_mem_same {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    gradeProj n x = x :=
  DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[R]^i M) hx

/-- The degree-`n` projection kills every other exterior power. -/
lemma gradeProj_of_mem_ne {m n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^m M) (hmn : m ≠ n) :
    gradeProj n x = 0 :=
  DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[R]^i M) hx hmn

/-! ### The rank-stratum summand inside its exterior power -/

variable [Module.Finite R M] [Module.Projective R M]

/-- Multiplication by the rank-`n` idempotent carries the degree-`n` exterior power into the
`n`-th rank-stratum summand of the determinant line. -/
lemma rankIdempotent_smul_mem_component {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    rankIdempotent (R := R) (M := M) n • x ∈ component (R := R) (M := M) n :=
  Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- **The projection of `⋀ⁿ_R M` onto the `n`-th rank-stratum summand of the determinant
line**, namely multiplication by the rank-`n` idempotent. -/
def componentProj (n : ℕ) : ↥(⋀[R]^n M) →ₗ[R] ↥(component (R := R) (M := M) n) :=
  LinearMap.codRestrict _
    (rankIdempotent (R := R) (M := M) n • (⋀[R]^n M).subtype)
    fun x => rankIdempotent_smul_mem_component x.2

/-- **Each rank-stratum summand of the determinant line is a direct summand of the exterior
power containing it.** The projection is multiplication by the rank-`n` idempotent, which is the
identity on the summand it cuts out. -/
def componentRetract (n : ℕ) :
    Retract (ModuleCat.of R ↥(component (R := R) (M := M) n)) (ModuleCat.of R ↥(⋀[R]^n M)) where
  i := ModuleCat.ofHom (Submodule.inclusion (component_le_exteriorPower n))
  r := ModuleCat.ofHom (componentProj n)
  retract := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change rankIdempotent (R := R) (M := M) n • (x : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M)
    exact rankIdempotent_smul_eq_self_of_mem_component x.2

/-- The projection of the exterior algebra onto the `n`-th rank-stratum summand: project to
degree `n`, then multiply by the rank-`n` idempotent. -/
def componentProjExteriorAlgebra (n : ℕ) :
    ExteriorAlgebra R M →ₗ[R] ↥(component (R := R) (M := M) n) :=
  LinearMap.codRestrict _
    (rankIdempotent (R := R) (M := M) n • gradeProj (R := R) (M := M) n)
    fun x => rankIdempotent_smul_mem_component (gradeProj_mem n x)

/-- **Each rank-stratum summand of the determinant line is a direct summand of the whole
exterior algebra.** It is a direct summand of the exterior power containing it, and that
exterior power is a direct summand of the exterior algebra, the grading supplying the
projection. -/
def componentRetractExteriorAlgebra (n : ℕ) :
    Retract (ModuleCat.of R ↥(component (R := R) (M := M) n))
      (ModuleCat.of R (ExteriorAlgebra R M)) where
  i := ModuleCat.ofHom ((component (R := R) (M := M) n).subtype)
  r := ModuleCat.ofHom (componentProjExteriorAlgebra n)
  retract := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change rankIdempotent (R := R) (M := M) n • gradeProj n (x : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M)
    rw [gradeProj_of_mem_same (component_le_exteriorPower n x.2)]
    exact rankIdempotent_smul_eq_self_of_mem_component x.2

/-! ### The determinant line inside the exterior algebra -/

variable (R M)

/-- A finite set of degrees whose rank strata cover `Spec R`. The rank strata of a finite
projective module are clopen and cover the spectrum, which is quasi-compact. -/
def coverDegrees : Finset ℕ :=
  (exists_finset_rankLocus_cover (R := R) (M := M)).choose

/-- The rank strata of the degrees in `ProjectiveDeterminant.coverDegrees` cover `Spec R`. -/
lemma coverDegrees_spec : (Set.univ : Set (PrimeSpectrum R)) ⊆
    ⋃ n ∈ coverDegrees R M, rankLocus (R := R) M n :=
  (exists_finset_rankLocus_cover (R := R) (M := M)).choose_spec

/-- The determinant line is the supremum of the rank-stratum summands of the finitely many
degrees in `ProjectiveDeterminant.coverDegrees`. -/
lemma submodule_eq_iSup_coverDegrees :
    submodule (R := R) (M := M) = ⨆ n : coverDegrees R M, component (R := R) (M := M) n :=
  submodule_eq_iSup_finset_cover (coverDegrees_spec R M)

variable {R M}

/-- The sum, over the degrees of `ProjectiveDeterminant.coverDegrees`, of the projections onto
the rank-stratum summands, as an endomorphism of the exterior algebra. -/
def submoduleProjAux : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  ∑ n ∈ coverDegrees R M, rankIdempotent (R := R) (M := M) n • gradeProj (R := R) (M := M) n

/-- `ProjectiveDeterminant.submoduleProjAux` evaluated at an element, as the sum of its
degreewise terms. -/
lemma submoduleProjAux_apply (x : ExteriorAlgebra R M) :
    submoduleProjAux x = ∑ n ∈ coverDegrees R M,
      rankIdempotent (R := R) (M := M) n • gradeProj (R := R) (M := M) n x :=
  LinearMap.sum_apply _ _ x

/-- `ProjectiveDeterminant.submoduleProjAux` lands in the determinant line: its degree-`n` term
lies in the rank-`n` stratum summand, and each summand lies in the determinant line. -/
lemma submoduleProjAux_mem (x : ExteriorAlgebra R M) :
    submoduleProjAux x ∈ submodule (R := R) (M := M) := by
  rw [submoduleProjAux_apply]
  refine Submodule.sum_mem _ fun n _ => component_le_submodule n ?_
  exact rankIdempotent_smul_mem_component (gradeProj_mem n x)

/-- The sum of the degreewise projections is the identity on the determinant line: on the `n`-th
rank-stratum summand the `n`-th term is the identity, because the rank-`n` idempotent acts as the
identity there, and every other term vanishes, because the summand sits in degree `n`. -/
lemma submoduleProjAux_of_mem {x : ExteriorAlgebra R M} (hx : x ∈ submodule (R := R) (M := M)) :
    submoduleProjAux x = x := by
  classical
  rw [submodule_eq_iSup_coverDegrees] at hx
  refine Submodule.iSup_induction _ (motive := fun y => submoduleProjAux y = y) hx ?_
    (map_zero _) ?_
  · intro n z hz
    rw [submoduleProjAux_apply, Finset.sum_eq_single_of_mem (n : ℕ) n.2]
    · rw [gradeProj_of_mem_same (component_le_exteriorPower _ hz)]
      exact rankIdempotent_smul_eq_self_of_mem_component hz
    · intro m _ hmn
      rw [gradeProj_of_mem_ne (component_le_exteriorPower _ hz) (Ne.symm hmn), smul_zero]
  · intro a b ha hb
    rw [map_add, ha, hb]

/-- **The projection of the exterior algebra onto the determinant line.** Each term projects to
a degree, multiplies by the idempotent of that degree and so lands in the corresponding
rank-stratum summand; the sum over a covering set of degrees therefore lands in the determinant
line. -/
def submoduleProj : ExteriorAlgebra R M →ₗ[R] ↥(submodule (R := R) (M := M)) :=
  LinearMap.codRestrict _ submoduleProjAux submoduleProjAux_mem

/-- **The determinant line is a direct summand of the exterior algebra.** -/
def submoduleRetract :
    Retract (ModuleCat.of R ↥(submodule (R := R) (M := M)))
      (ModuleCat.of R (ExteriorAlgebra R M)) where
  i := ModuleCat.ofHom ((submodule (R := R) (M := M)).subtype)
  r := ModuleCat.ofHom submoduleProj
  retract := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact submoduleProjAux_of_mem x.2

end ProjectiveDeterminant

end
