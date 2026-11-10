module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalNullHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# Local null-homotopy of a map which vanishes in the derived category

Let `(C, O)` be a ringed site and `U` an object of `C`. A map `α : E ⟶ F` of complexes of
`O|_U`-modules whose source is strictly perfect and whose image in `D(O|_U)` is zero becomes
null-homotopic after restriction along the arrows of a covering sieve of `U`.

This is part (2) of Stacks 08FR. By the calculus of left fractions, `α` vanishing in the derived
category means that it is killed by postcomposition with some quasi-isomorphism `t : F ⟶ G` of
the homotopy category, so `α` factors up to homotopy through the shifted cone of `t`, which is
acyclic; Stacks 08FP (1) then makes that factor locally null-homotopic.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero`: a map out of
  a strictly perfect complex which is zero in the derived category is locally null-homotopic.

## References

* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d

namespace AlgebraicGeometry.RingedSite

section Abelian

variable {A : Type*} [Category A] [Abelian A]

/-- A map of cochain complexes in an abelian category is a quasi-isomorphism if and only if
its mapping cone is acyclic. -/
private theorem quasiIso_iff_acyclic_mappingCone {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

/-- A shift of an acyclic cochain complex is acyclic. -/
private theorem acyclic_shift (K : CochainComplex A ℤ) (hK : K.Acyclic) (a : ℤ) :
    (K⟦a⟧).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  simpa [CochainComplex] using
    (IsZero.of_iso (hK (i + a)).isZero_homology
      ((CochainComplex.ShiftSequence.shiftIso A a i (i + a) (add_comm a i)).app K))

end Abelian

variable (X : RingedSite.{u, u, 0}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d}
  (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- Let `(C, O)` be a ringed site and `U` an object of `C`. Let
`α : E ⟶ F` be a map of complexes of `O|_U`-modules with `E` strictly perfect, and suppose the
image of `α` in `D(O|_U)` is zero. Then there is a covering sieve of `U` such that the
restriction of `α` along each of its arrows is homotopic to zero. -/
@[stacks 08FR "local_null_homotopy", sga "6 I 4.1" "special case"]
theorem exists_coveringSieve_homotopy_zero_of_derived_zero
    {E F : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) (α : E ⟶ F)
    (hα : DerivedCategory.Q.map α = 0) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0) := by
  let M := SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
  let q := HomotopyCategory.quotient M (ComplexShape.up ℤ)
  have hα₀ : DerivedCategory.Qh.map (q.map α) = 0 := by
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso M).hom.app F)).1
    rw [DerivedCategory.quotientCompQhIso_hom_naturality]
    simp [hα]
  obtain ⟨Z, s, hs, hαs⟩ := (MorphismProperty.map_eq_iff_postcomp
    (L := DerivedCategory.Qh) (W := HomotopyCategory.quasiIso M (ComplexShape.up ℤ))
    (q.map α) 0).1 (by rw [hα₀, Functor.map_zero])
  obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t, rfl⟩ := q.map_surjective s
  let T := (CochainComplex.mappingCone.triangleh t).invRotate
  have hC' : (T.obj₁.as).Acyclic := by
    change (((q.obj (CochainComplex.mappingCone t))⟦(-1 : ℤ)⟧).as).Acyclic
    rw [HomotopyCategory.shift_quotient_obj]
    exact acyclic_shift _ ((quasiIso_iff_acyclic_mappingCone t).1
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).1 hs)) (-1)
  obtain ⟨β₀, hβ₀⟩ := Triangle.coyoneda_exact₂ T
    (inv_rot_of_distTriang _ (HomotopyCategory.mappingCone_triangleh_distinguished t)) (q.map α)
    (by
      change q.map α ≫ (CochainComplex.mappingCone.triangleh t).mor₁ = 0
      exact (by simpa using hαs : q.map α ≫ q.map t = 0))
  obtain ⟨β, hβ⟩ := q.map_surjective β₀
  obtain ⟨j, hj⟩ := q.map_surjective T.mor₁
  have hfactor : Homotopy α (β ≫ j) :=
    HomotopyCategory.homotopyOfEq _ _ (show q.map α = q.map β ≫ q.map j by
      rw [hβ, hj]
      exact hβ₀)
  obtain ⟨S, hS, hnull⟩ :=
    exists_coveringSieve_homotopy_zero_of_acyclic (X := X) (U := U) (α := β) hE hC'
  refine ⟨S, hS, fun f hf ↦ ?_⟩
  obtain ⟨hβf⟩ := hnull f hf
  let R :=
    SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk f)
  let RV := R.mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨(R.mapHomotopy hfactor).trans ((Homotopy.ofEq (RV.map_comp β j)).trans
    ((hβf.compRight (RV.map j)).trans (Homotopy.ofEq (by exact zero_comp))))⟩

end AlgebraicGeometry.RingedSite

end
