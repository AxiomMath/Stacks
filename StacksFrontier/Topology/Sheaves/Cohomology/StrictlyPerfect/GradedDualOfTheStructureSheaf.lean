module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectGradedDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import Mathlib.Algebra.Homology.Single

/-!
# The graded dual of the structure sheaf in degree zero

[Stacks, Tag 0FP9] asserts that a locally bounded complex `ℱ^•` of `𝒪_X`-modules whose terms are
locally direct summands of finite free modules has `𝒢^• = SheafHom^•(ℱ^•, 𝒪_X)` as a left dual.
This file shows that the complex `𝒪_X[0]`, the structure sheaf placed in degree zero, satisfies
the hypotheses of the graded assemblies
`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyFiniteFreeSummand` and
`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyStrictlyPerfect`, on an
arbitrary ringed space `X`, and that it vanishes in degree zero exactly when `𝒪_X` is the zero
module.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.structureSheafComplex`: the complex `𝒪_X[0]`.
* `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectStructureSheaf` and
  `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectStructureSheafOfCovering`: the
  graded dual pairing of [Stacks, Tag 0FP9] at the complex `𝒪_X[0]`.

## Main results

* `Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_unit`: the structure sheaf, as a
  module over itself, is locally a direct summand of a finite free module.
* `Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isZero` and
  `isLocallyFiniteFreeSummand_of_iso`: the predicate holds for a zero module and transfers along
  an isomorphism.
* `Stacks.SheafOfModules.OnSpace.isLocallyStrictlyPerfect_structureSheafComplex`: the complex
  `𝒪_X[0]` is locally strictly perfect.
* `Stacks.SheafOfModules.OnSpace.isZero_structureSheafComplex_X_zero_iff`: the complex `𝒪_X[0]`
  vanishes in degree zero exactly when `𝒪_X` is the zero module.

## Implementation notes

On a ringed space `AlgebraicGeometry.RingedSpace.{u, u}` the monoidal structure on complexes is
reached by `letI := Strict.monoidalCategoryCochainComplex X.sheaf`;
`attribute [local instance] SheafOfModules.monoidalCategorySheafTensor` does not work there.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.GradedObject

noncomputable section

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- A zero module is locally a direct summand of a finite free module. -/
theorem isLocallyFiniteFreeSummand_of_isZero
    (G : _root_.SheafOfModules.{u} (structureSheafRing X)) (hG : IsZero G) :
    IsLocallyFiniteFreeSummand X G := by
  have hover : ∀ U : TopologicalSpace.Opens X.carrier, IsZero (G.over U) := by
    intro U
    rw [IsZero.iff_id_eq_zero]
    rw [show (𝟙 (G.over U))
        = (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map (𝟙 G) by simp]
    rw [hG.eq_of_src (𝟙 G) 0, Functor.map_zero]
  intro x
  exact ⟨⊤, trivial, 0, ⟨⟨0, 0, (hover ⊤).eq_of_src _ _⟩⟩⟩

/-- Being locally a direct summand of a finite free module transfers along an isomorphism. -/
theorem isLocallyFiniteFreeSummand_of_iso
    {G H : _root_.SheafOfModules.{u} (structureSheafRing X)} (e : G ≅ H)
    (h : IsLocallyFiniteFreeSummand X H) : IsLocallyFiniteFreeSummand X G := by
  intro x
  obtain ⟨U, hxU, n, ⟨ρ⟩⟩ := h x
  exact ⟨U, hxU, n, ⟨(Retract.ofIso
    ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapIso e)).trans ρ⟩⟩

/-- The structure sheaf, as a module over itself, is locally a direct summand of a finite free
module. -/
theorem isLocallyFiniteFreeSummand_unit :
    IsLocallyFiniteFreeSummand X (_root_.SheafOfModules.unit (structureSheafRing X)) := by
  intro x
  exact ⟨⊤, trivial, 1, ⟨Retract.ofIso
    (Stacks.SheafOfModules.Invertible.freeUniqueIso
      (R := (structureSheafRing X).over ⊤) (ULift.{u} (Fin 1))).symm⟩⟩

/-- The complex `𝒪_X[0]`: the structure sheaf, as a module over itself, placed in degree zero. -/
def structureSheafComplex :
    CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  (HomologicalComplex.single (_root_.SheafOfModules.{u} (structureSheafRing X))
    (ComplexShape.up ℤ) 0).obj (_root_.SheafOfModules.unit (structureSheafRing X))

/-- In degree zero the complex `𝒪_X[0]` is the structure sheaf. -/
def structureSheafComplexXZeroIso :
    (structureSheafComplex X).X 0 ≅ _root_.SheafOfModules.unit (structureSheafRing X) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _

/-- The graded dual pairing of
`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyFiniteFreeSummand` at the
complex `𝒪_X[0]`, with bound `{0}`. -/
@[instance_reducible]
def exactPairingDualGradedObjectStructureSheaf :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      ((structureSheafComplex X).X : GradedObject ℤ (Strict.Mod X.sheaf))
      (Strict.dualGradedObject X.sheaf (structureSheafComplex X)) :=
  exactPairingDualGradedObjectOfLocallyFiniteFreeSummand X (structureSheafComplex X) {0}
    (fun m hm => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ m
      (by simpa using hm))
    (fun n => by
      by_cases h : n = 0
      · subst h
        exact isLocallyFiniteFreeSummand_of_iso X (structureSheafComplexXZeroIso X)
          (isLocallyFiniteFreeSummand_unit X)
      · exact isLocallyFiniteFreeSummand_of_isZero X _
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n h))

/-- The complex `𝒪_X[0]` is locally strictly perfect. -/
theorem isLocallyStrictlyPerfect_structureSheafComplex :
    IsLocallyStrictlyPerfect X (structureSheafComplex X) :=
  (isLocallyStrictlyPerfect_iff_of_bound X (s := {0})
    (fun m hm => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ m
      (by simpa using hm))).mpr
    (fun n => by
      by_cases h : n = 0
      · subst h
        exact isLocallyFiniteFreeSummand_of_iso X (structureSheafComplexXZeroIso X)
          (isLocallyFiniteFreeSummand_unit X)
      · exact isLocallyFiniteFreeSummand_of_isZero X _
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n h))

/-- The graded dual pairing of
`Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObjectOfLocallyStrictlyPerfect` at the
complex `𝒪_X[0]`, with bound `{0}`. -/
@[instance_reducible]
def exactPairingDualGradedObjectStructureSheafOfCovering :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      ((structureSheafComplex X).X : GradedObject ℤ (Strict.Mod X.sheaf))
      (Strict.dualGradedObject X.sheaf (structureSheafComplex X)) :=
  exactPairingDualGradedObjectOfLocallyStrictlyPerfect X (structureSheafComplex X) {0}
    (fun m hm => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ m
      (by simpa using hm))
    (isLocallyStrictlyPerfect_structureSheafComplex X)

/-- The complex `𝒪_X[0]` vanishes in degree zero if and only if `𝒪_X`, as a module over itself,
is a zero object. -/
theorem isZero_structureSheafComplex_X_zero_iff :
    IsZero ((structureSheafComplex X).X 0) ↔
      IsZero (_root_.SheafOfModules.unit (structureSheafRing X)) :=
  ⟨fun h => h.of_iso (structureSheafComplexXZeroIso X).symm,
    fun h => h.of_iso (structureSheafComplexXZeroIso X)⟩

end Stacks.SheafOfModules.OnSpace

end

end
