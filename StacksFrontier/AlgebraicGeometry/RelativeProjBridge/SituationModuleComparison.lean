module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.SectionModule
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionModule
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison

/-!
# The two relative-`Proj` substrates have the same graded modules of local sections

Let `A` be a sheaf of graded algebras on a scheme `S` and `ℳ` a left graded module over it, with
quasi-coherent homogeneous pieces. This file converts `ℳ` into a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule` over
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra`, and compares its graded
modules of local sections with those of `ℳ` over the relative `Proj` situation
`Stacks.AlgebraicGeometry.RelativeProjBridge.situationOfGradedAlgebra`. The two modules of
sections over an open are the same additive group `⨁_{n ∈ ℤ} Γ(ℳₙ, U)`, with the same graded
scalar action, the same grading and the same decomposition; the identity is semilinear along the
comparison `Stacks.AlgebraicGeometry.RelativeProjBridge.situationSectionRingEquiv` of the
section rings and natural in the open.

## Main definitions

* `toSheafGradedModule`: a left graded module over a sheaf of graded algebras, as a
  `SheafGradedModule` over `toSheafGradedAlgebra`.
* `situationSectionModuleEquiv`: the identity additive equivalence between the two graded
  modules of local sections over an open.

## Main results

* `gSMul_situationOfGradedModule`: the two graded scalar actions agree.
* `situationSectionModuleEquiv_of`: the comparison is the identity on a homogeneous section.
* `situationSectionModuleEquiv_smul`: the comparison is semilinear along the comparison of the
  section rings.
* `situationSectionModuleEquiv_mem_grading`, `situationSectionModuleEquiv_symm_mem`: it
  preserves degrees in both directions.
* `situationSectionModuleEquiv_res`: it is natural in the open.
* `sectionModuleGrading_situationOfGradedModule`, `grading_situationOfGradedAlgebra`: the two
  internal gradings of the module of sections, and those of the section ring, are the same
  subgroups.
* `sectionModuleDecomposition_situationOfGradedModule`: the two direct-sum decompositions of the
  module of sections are the same decomposition.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped DirectSum Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {S : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf}
  (hcomm : IsCommutative A) (hneg : VanishesInNegativeDegrees A)
  (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} A)
  (hqcM : ∀ n : ℤ, ((ℳ.piece n : S.Modules)).IsQuasicoherent)

/-! ### The graded module on the other substrate -/

/-- A left graded module over a sheaf of graded algebras on a scheme, with quasi-coherent
homogeneous pieces, as graded module data over
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra`: every field is the
corresponding field of the left graded module, read over `op U`. -/
def toSheafGradedModule : SheafGradedModule (toSheafGradedAlgebra A hcomm hneg hqc) where
  piece n := ℳ.piece n
  smul i j :=
    { app U := ℳ.smul i j (op U)
      map_smul_left U r x y := ℳ.smul_smul_left i j (op U) r x y
      map_smul_right U r x y := ℳ.smul_smul_right i j (op U) r x y
      naturality h x y := ℳ.smul_naturality i j (homOfLE h).op x y }
  one_smul j U x := ℳ.one_smul j (op U) x
  mul_smul i j k U a b x := ℳ.mul_smul i j k (op U) a b x
  isQuasicoherent n := hqcM n

/-- The homogeneous pieces of `toSheafGradedModule hcomm hneg hqc ℳ hqcM` are those of `ℳ`. -/
theorem toSheafGradedModule_piece (n : ℤ) :
    (toSheafGradedModule hcomm hneg hqc ℳ hqcM).piece n = ℳ.piece n := rfl

/-- The homogeneous action of `toSheafGradedModule hcomm hneg hqc ℳ hqcM` over `U` is that of `ℳ`
over `op U`. -/
theorem toSheafGradedModule_smul_app (i j : ℤ) (U : S.Opens) :
    ((toSheafGradedModule hcomm hneg hqc ℳ hqcM).smul i j).app U = ℳ.smul i j (op U) := rfl

/-! ### The comparison of the graded modules of sections -/

/-- **The two graded scalar actions of homogeneous sections on homogeneous sections are the same
action.** -/
theorem gSMul_situationOfGradedModule (U : S.Opens) :
    (toSheafGradedModule hcomm hneg hqc ℳ hqcM).instGSMul U =
      Stacks.RelativeProj.Situation.sectionModuleGSMul
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U :=
  rfl

/-- The graded module structure on the homogeneous sections of `ℳ` over an open `U : S.Opens`,
over the homogeneous sections of `A`. -/
instance gmoduleSituationOfGradedModule (U : S.Opens) :
    DirectSum.Gmodule ((situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U)
      (Stacks.RelativeProj.Situation.sectionModulePieces
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) :=
  Stacks.RelativeProj.Situation.sectionModuleGmodule
    (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U

/-- The module structure on the graded module of sections of `ℳ` over an open `U : S.Opens`, over
the graded ring of sections of `A`. -/
instance moduleSituationOfGradedModule (U : S.Opens) :
    Module ((situationOfGradedAlgebra A hcomm hneg hqc).sectionRing U)
      (Stacks.RelativeProj.Situation.sectionModule
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) :=
  Stacks.RelativeProj.Situation.sectionModuleModule
    (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U

/-- The action of a homogeneous scalar of degree `i` on a homogeneous section of degree `j` of the
module of sections over `situationOfGradedAlgebra` is the homogeneous section of degree `i + j`
given by the action of `ℳ`. -/
theorem of_smul_of_situation (U : S.Opens) (i : ℕ) (j : ℤ)
    (a : (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U i)
    (x : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModulePieces U j) :
    DirectSum.of ((situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U) i a •
        DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) j x =
      DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) ((i : ℤ) + j)
        (ℳ.smul (i : ℤ) j (op U) a x) :=
  Stacks.RelativeProj.Situation.sectionModule_of_smul_of
    (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U a x

/-- The restriction of a homogeneous section of the module of sections over
`situationOfGradedAlgebra` is the homogeneous section given by the restriction map of the
corresponding piece of `ℳ`. -/
theorem sectionModuleRestrict_of_situation {U V : S.Opens} (h : U ≤ V) (n : ℤ)
    (x : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModulePieces V n) :
    Stacks.RelativeProj.Situation.sectionModuleRestrict
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ h
        (DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ V) n x) =
      DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) n
        ((ℳ.piece n).val.map (homOfLE h).op x) :=
  Stacks.RelativeProj.Situation.sectionModuleRestrict_of
    (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ h x

/-- **The two graded modules of local sections over an open are the same additive group**, by the
identity: both are `⨁_{n ∈ ℤ} Γ(ℳₙ, U)` on the same homogeneous pieces. -/
def situationSectionModuleEquiv (U : S.Opens) :
    (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModule U ≃+
      Stacks.RelativeProj.Situation.sectionModule
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U :=
  AddEquiv.refl _

/-- The comparison `situationSectionModuleEquiv` is the identity on a homogeneous section. -/
theorem situationSectionModuleEquiv_of (U : S.Opens) (n : ℤ)
    (x : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModulePieces U n) :
    situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U (DirectSum.of _ n x) =
      DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) n x := rfl

/-- The inverse of `situationSectionModuleEquiv` is the identity on a homogeneous section. -/
theorem situationSectionModuleEquiv_symm_of (U : S.Opens) (n : ℤ)
    (x : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModulePieces U n) :
    (situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U).symm
        (DirectSum.of (Stacks.RelativeProj.Situation.sectionModulePieces
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U) n x) =
      DirectSum.of ((toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModulePieces U) n x := rfl

/-! ### Semilinearity -/

/-- **The comparison of the graded modules of sections is semilinear along the comparison of the
graded rings of sections.** -/
theorem situationSectionModuleEquiv_smul (U : S.Opens)
    (w : (toSheafGradedAlgebra A hcomm hneg hqc).sectionRing U)
    (z : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModule U) :
    situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U (w • z) =
      situationSectionRingEquiv A hcomm hneg hqc U w •
        situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U z := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of i a =>
      induction z using DirectSum.induction_on with
      | zero => simp
      | of j x =>
          rw [situationSectionRingEquiv_of, SheafGradedModule.of_smul_of,
            situationSectionModuleEquiv_of, situationSectionModuleEquiv_of]
          exact (of_smul_of_situation hcomm hneg hqc ℳ hqcM U i j a x).symm
      | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
  | add w₁ w₂ h₁ h₂ => rw [add_smul, map_add, h₁, h₂, map_add, add_smul]

/-! ### Compatibility with the gradings -/

/-- The comparison preserves degrees. -/
theorem situationSectionModuleEquiv_mem_grading (U : S.Opens) (n : ℤ)
    {z : (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModule U}
    (hz : z ∈ (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModuleGrading U n) :
    situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U z ∈
      Stacks.RelativeProj.Situation.sectionModuleGrading
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U n :=
  hz

/-- The inverse comparison preserves degrees. -/
theorem situationSectionModuleEquiv_symm_mem (U : S.Opens) (n : ℤ)
    {z : Stacks.RelativeProj.Situation.sectionModule
      (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U}
    (hz : z ∈ Stacks.RelativeProj.Situation.sectionModuleGrading
      (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U n) :
    (situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U).symm z ∈
      (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModuleGrading U n :=
  hz

/-- **The two internal gradings of the one module of sections are the same subgroup in every
degree.** -/
theorem sectionModuleGrading_situationOfGradedModule (U : S.Opens) (n : ℤ) :
    (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModuleGrading U n =
      Stacks.RelativeProj.Situation.sectionModuleGrading
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U n := rfl

/-- **The two internal gradings of the section ring are the same subgroup in every degree.** -/
theorem grading_situationOfGradedAlgebra (U : S.Opens) (n : ℕ) :
    (toSheafGradedAlgebra A hcomm hneg hqc).grading U n =
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U n := rfl

/-- **The two direct-sum decompositions of the module of sections are the same
decomposition.** -/
theorem sectionModuleDecomposition_situationOfGradedModule (U : S.Opens) :
    (toSheafGradedModule hcomm hneg hqc ℳ hqcM).sectionModuleDecomposition U =
      Stacks.RelativeProj.Situation.sectionModuleDecomposition
        (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ U :=
  Subsingleton.elim _ _

/-! ### Naturality in the open -/

/-- **The comparison is natural in the open**: it commutes with the restriction maps of the two
graded modules of sections. -/
theorem situationSectionModuleEquiv_res {U V : S.Opens} (h : U ≤ V) :
    (situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U).toAddMonoidHom.comp
        ((toSheafGradedModule hcomm hneg hqc ℳ hqcM).res h) =
      (Stacks.RelativeProj.Situation.sectionModuleRestrict
          (s := situationOfGradedAlgebra A hcomm hneg hqc) ℳ h).comp
        (situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM V).toAddMonoidHom := by
  refine DirectSum.addHom_ext fun n x => ?_
  change situationSectionModuleEquiv hcomm hneg hqc ℳ hqcM U
      ((toSheafGradedModule hcomm hneg hqc ℳ hqcM).res h (DirectSum.of _ n x)) = _
  rw [SheafGradedModule.res_of, situationSectionModuleEquiv_of]
  exact (sectionModuleRestrict_of_situation hcomm hneg hqc ℳ hqcM h n x).symm

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
