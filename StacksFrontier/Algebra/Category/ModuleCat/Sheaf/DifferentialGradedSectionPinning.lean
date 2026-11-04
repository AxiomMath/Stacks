module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule

/-!
# The sections of a sheaf of differential graded algebras, pinned degreewise

The differential graded algebra `A(U) = ⨁ₙ Aⁿ(U)` of sections and the differential graded
`A(U)`-module `M(U) = ⨁ₙ Mⁿ(U)` carry their degree in the element: the degree-`n` part of each is
the `n`-th summand of a direct sum. This file identifies that summand with the group of sections
of the degree-`n` piece and records that the identification carries each piece of structure —
the differential, the multiplication, the unit, the right action, a homomorphism of modules, and
the restriction maps of the site — to the corresponding structure of `A` and `M`.

The identification is the inverse of `Stacks.ExternalGrading.intSummandEquiv`, so it reads a
homogeneous element off as its own coordinate, and every statement below is proved by replacing a
homogeneous element by the summand of its coordinate and then applying the computation rule of
the structure map on a summand.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.sectionDegree`: the degree-`n` part of `A(U)` is
  `Aⁿ(U)`.
* `SheafOfModules.DifferentialGradedModule.sectionModuleDegree`: the degree-`n` part of `M(U)`
  is `Mⁿ(U)`.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.sectionDegree_d`, `sectionDegree_mul`,
  `sectionDegree_one` and `sectionRestriction_degree`: the identification carries the
  differential, the multiplication, the unit and the restriction homomorphisms of `A(U)` to
  those of `A`.
* `SheafOfModules.DifferentialGradedModule.sectionModuleDegree_d`, `sectionModuleDegree_mul`,
  `sectionModuleDegree_naturality` and `sectionModuleRestriction_degree`: the same for `M(U)`.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- An element of the `n`-th summand whose underlying element is `of T n w` has coordinate `w`. -/
private theorem intSummandEquiv_symm_eq_of_coe_eq {ι : Type*} [DecidableEq ι] (T : ι → Type a)
    [∀ i, AddCommGroup (T i)] {n : ι} (z : Stacks.ExternalGrading.intSummand T n) (w : T n)
    (hz : (z : DirectSum ι T) = DirectSum.of T n w) :
    (Stacks.ExternalGrading.intSummandEquiv T n).symm z = w :=
  (Stacks.ExternalGrading.intSummandEquiv T n).symm_apply_eq.2 (Subtype.ext hz)

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ)

/-- **The degree-`n` part of the algebra of sections is the group of sections of `Aⁿ` over
`U`.** -/
def sectionDegree (n : ℤ) :
    (A.sectionAlgebra U).grading n ≃+ (A.complex.X n).val.obj U :=
  (Stacks.ExternalGrading.intSummandEquiv (A.toGradedAlgebra.sectionsPiece U) n).symm

/-- A homogeneous element of the algebra of sections is the summand of the section it names. -/
theorem coe_eq_of_sectionDegree (n : ℤ) (x : (A.sectionAlgebra U).grading n) :
    (x : (A.sectionAlgebra U).A) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n (A.sectionDegree U n x) :=
  (Stacks.ExternalGrading.of_coord_eq (A.toGradedAlgebra.sectionsPiece U) x).symm

/-- A homogeneous element of the algebra of sections is read off by `sectionDegree`. -/
theorem sectionDegree_eq_of_coe_eq (n : ℤ) (z : (A.sectionAlgebra U).grading n)
    (w : A.toGradedAlgebra.sectionsPiece U n)
    (hz : (z : (A.sectionAlgebra U).A) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n w) :
    A.sectionDegree U n z = w := by
  exact intSummandEquiv_symm_eq_of_coe_eq _ z w hz

/-- **The identification carries the differential of `A(U)` to the differential of `A`.** -/
theorem sectionDegree_d (n : ℤ) (x : (A.sectionAlgebra U).grading n) :
    A.sectionDegree U (n + 1) ⟨(A.sectionAlgebra U).d (x : (A.sectionAlgebra U).A),
        (A.sectionAlgebra U).d_mem n (x : (A.sectionAlgebra U).A) x.2⟩ =
      (A.complex.d n (n + 1)).val.app U (A.sectionDegree U n x) := by
  refine A.sectionDegree_eq_of_coe_eq U (n + 1) _ _ ?_
  show (A.sectionAlgebra U).d (x : (A.sectionAlgebra U).A) = _
  rw [A.coe_eq_of_sectionDegree U n x, A.sectionAlgebra_d_of U n]

/-- **The identification carries the multiplication of `A(U)` to the multiplication of `A`.** -/
theorem sectionDegree_mul (n i : ℤ) (x : (A.sectionAlgebra U).grading n)
    (y : (A.sectionAlgebra U).grading i) (z : (A.sectionAlgebra U).grading (n + i))
    (hz : (z : (A.sectionAlgebra U).A) =
      (x : (A.sectionAlgebra U).A) * (y : (A.sectionAlgebra U).A)) :
    A.sectionDegree U (n + i) z =
      (A.mul n i).app U (A.sectionDegree U n x) (A.sectionDegree U i y) := by
  refine A.sectionDegree_eq_of_coe_eq U (n + i) z _ ?_
  rw [hz, A.coe_eq_of_sectionDegree U n x, A.coe_eq_of_sectionDegree U i y]
  exact GradedAlgebra.of_mul_of_eq A.toGradedAlgebra U n i _ _

/-- **The identification carries the unit of `A(U)` to the unit section of `A`.** -/
theorem sectionDegree_one (z : (A.sectionAlgebra U).grading 0)
    (hz : (z : (A.sectionAlgebra U).A) = 1) : A.sectionDegree U 0 z = A.one.eval U := by
  refine A.sectionDegree_eq_of_coe_eq U 0 z _ ?_
  rw [hz]
  exact (DirectSum.of_zero_one (A.toGradedAlgebra.sectionsPiece U)).symm

variable {U}

/-- **The identification carries the restriction homomorphisms of the algebras of sections to
the restriction maps of `A`.** -/
theorem sectionRestriction_degree {V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ)
    (x : (A.sectionAlgebra V).grading n) :
    A.sectionDegree U n ⟨(A.sectionRestriction a).toAlgebraHom (x : (A.sectionAlgebra V).A),
        (A.sectionRestriction a).map_grading n (x : (A.sectionAlgebra V).A) x.2⟩ =
      (A.complex.X n).val.map a (A.sectionDegree V n x) := by
  refine A.sectionDegree_eq_of_coe_eq U n _ _ ?_
  show (A.sectionRestriction a).toAlgebraHom (x : (A.sectionAlgebra V).A) = _
  rw [A.coe_eq_of_sectionDegree V n x, A.sectionRestriction_of a n]
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R} (M : DifferentialGradedModule.{t, a, a} A)
  (U : Cᵒᵖ)

/-- **The degree-`n` part of the module of sections is the group of sections of `Mⁿ` over
`U`.** -/
def sectionModuleDegree (n : ℤ) :
    (M.sectionModule U).grading n ≃+ (M.complex.X n).val.obj U :=
  (Stacks.ExternalGrading.intSummandEquiv (M.sectionsPiece U) n).symm

/-- A homogeneous element of the module of sections is the summand of the section it names. -/
theorem coe_eq_of_sectionModuleDegree (n : ℤ) (x : (M.sectionModule U).grading n) :
    (x : (M.sectionModule U).M) =
      DirectSum.of (M.sectionsPiece U) n (M.sectionModuleDegree U n x) :=
  (Stacks.ExternalGrading.of_coord_eq (M.sectionsPiece U) x).symm

/-- A homogeneous element of the module of sections is read off by `sectionModuleDegree`. -/
theorem sectionModuleDegree_eq_of_coe_eq (n : ℤ) (z : (M.sectionModule U).grading n)
    (w : M.sectionsPiece U n)
    (hz : (z : (M.sectionModule U).M) = DirectSum.of (M.sectionsPiece U) n w) :
    M.sectionModuleDegree U n z = w := by
  exact intSummandEquiv_symm_eq_of_coe_eq _ z w hz

/-- **The identification carries the differential of `M(U)` to the differential of `M`.** -/
theorem sectionModuleDegree_d (n : ℤ) (x : (M.sectionModule U).grading n) :
    M.sectionModuleDegree U (n + 1) ⟨(M.sectionModule U).d (x : (M.sectionModule U).M),
        (M.sectionModule U).d_mem n (x : (M.sectionModule U).M) x.2⟩ =
      (M.complex.d n (n + 1)).val.app U (M.sectionModuleDegree U n x) := by
  refine M.sectionModuleDegree_eq_of_coe_eq U (n + 1) _ _ ?_
  show (M.sectionModule U).d (x : (M.sectionModule U).M) = _
  rw [M.coe_eq_of_sectionModuleDegree U n x, M.sectionModule_d_of U n]
  rfl

/-- **The identification carries the right action on `M(U)` to the right action of `A` on
`M`.** -/
theorem sectionModuleDegree_mul (n i : ℤ) (x : (M.sectionModule U).grading n)
    (y : (A.sectionAlgebra U).grading i) (z : (M.sectionModule U).grading (n + i))
    (hz : (z : (M.sectionModule U).M) =
      MulOpposite.op (y : (A.sectionAlgebra U).A) • (x : (M.sectionModule U).M)) :
    M.sectionModuleDegree U (n + i) z =
      (M.mul n i).app U (M.sectionModuleDegree U n x) (A.sectionDegree U i y) := by
  refine M.sectionModuleDegree_eq_of_coe_eq U (n + i) z _ ?_
  rw [hz, M.coe_eq_of_sectionModuleDegree U n x, A.coe_eq_of_sectionDegree U i y]
  show M.act U (DirectSum.of (M.sectionsPiece U) n (M.sectionModuleDegree U n x))
      (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i (A.sectionDegree U i y)) = _
  rw [act_of, actOn_of]

/-- **The identification is natural in the differential graded module.** -/
theorem sectionModuleDegree_naturality {N : DifferentialGradedModule.{t, a, a} A} (f : M ⟶ N)
    (n : ℤ) (x : (M.sectionModule U).grading n) :
    N.sectionModuleDegree U n ⟨(sectionMap f U).toFun (x : (M.sectionModule U).M),
        (sectionMap f U).map_grading n (x : (M.sectionModule U).M) x.2⟩ =
      (f.toHomologicalComplex.f n).val.app U (M.sectionModuleDegree U n x) := by
  refine N.sectionModuleDegree_eq_of_coe_eq U n _ _ ?_
  show sectionMapAdd f U (x : (M.sectionModule U).M) = _
  rw [M.coe_eq_of_sectionModuleDegree U n x, sectionMapAdd_of]
  rfl

variable {U}

/-- **The identification carries restriction of sections to the restriction maps of `M`.** -/
theorem sectionModuleRestriction_degree {V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ)
    (x : (M.sectionModule V).grading n) :
    M.sectionModuleDegree U n ⟨(M.sectionModuleRestriction a).toFun
          (x : (M.sectionModule V).M),
        (M.sectionModuleRestriction a).map_grading n (x : (M.sectionModule V).M) x.2⟩ =
      (M.complex.X n).val.map a (M.sectionModuleDegree V n x) := by
  refine M.sectionModuleDegree_eq_of_coe_eq U n _ _ ?_
  show M.sectionRestrictAdd a (x : (M.sectionModule V).M) = _
  rw [M.coe_eq_of_sectionModuleDegree V n x, sectionRestrictAdd_of]
  rfl

end DifferentialGradedModule

end SheafOfModules

end
