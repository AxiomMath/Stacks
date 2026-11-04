module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ConeSequence
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftAxiomB
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated

/-!
# Axiom (C) for the differential graded category of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R`. This file completes
axiom (C) of Tag 09QJ for the differential graded category `Mod^dg(C)` of right differential
graded `C`-modules: every closed degree-zero morphism `f : M ⟶ N` has the cone `c(f)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Cone`, the sequence
`N ⟶ c(f) ⟶ M⟦1⟧` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ConeSequence` is admissible, and its
connecting arrow `M⟦1⟧ ⟶ N⟦1⟧` is `f⟦1⟧`.

Together with axioms (A) and (B) this is a `DGCategory.ConeSituation`, the hypothesis under
which `DGCategory.homotopyCategory_isTriangulated` makes `K(Mod^dg(C))` triangulated.

## Main definitions

* `DGCategory.rightModuleConeSituation`: axioms (A), (B) and (C) for `Mod^dg(C)`.

## Main results

* `DGCategory.RightModule.coneConnecting`: the connecting arrow of the cone sequence is the
  shift of the morphism.
* `DGCategory.rightModuleHomotopyCategory_isTriangulated`: `K(Mod^dg(C))` is triangulated.

## Implementation notes

The connecting morphism of a graded-split short exact sequence is `π d(s)`, here the composite
of the inclusion `M⟦1⟧ ⟶ c(f)` — which is not closed, its differential being exactly the twist
of the cone — with the projection `c(f) ⟶ N`. Both the twist and the shift of `f` by one are
`f` itself with no sign: the shift of a *degree-zero* morphism carries the Koszul sign
`(-1)^{n·0} = 1`. The identification of the two is therefore pointwise, once the transports of
degree on either side have been absorbed.
-/

@[expose] public section

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R} {M N : RightModule.{w} C}

namespace RightModule

/-- The connecting arrow of the cone sequence of a closed degree-zero morphism `f : M ⟶ N` is
the shift `f⟦1⟧ : M⟦1⟧ ⟶ N⟦1⟧`. -/
theorem coneConnecting (f : (rightModuleCategory.{w} C).Cocycle M N) :
    GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{w} C)
        (coneSequenceOf f.1 f.2) =
      ((rightModuleShiftAxiomB.{w} C).shiftFunctor 1).mapCocycle f := by
  refine Subtype.ext ?_
  refine hom_ext fun x i j e a => ?_
  have hr : app ((((rightModuleShiftAxiomB.{w} C).shiftFunctor 1).mapCocycle f).1) e a =
      app f.1 (show i + 1 + 0 = j + 1 by omega) a := by
    show app (shiftMap f.1 1) e a = _
    rw [app_shiftMap]
    norm_num
  refine Eq.trans ?_ hr.symm
  show app (coneFst f.1 f.2) (show i + (0 + 1) + 0 = j + 1 by omega)
      (app (homD (coneInr f.1 f.2)) (rfl : i + (0 + 1) = i + (0 + 1)) a) = _
  simp only [app_homD, app_coneInr, coneOf_d, coneD_mk, Int.natAbs_zero, pow_zero, one_smul,
    d_zero, zero_add, app_sub, app_coneFst, map_zero, sub_zero]
  rw [shift_objCast, app_objCast f.1 (show i + 1 = i + 0 + 1 by omega)
      (show i + 0 + 1 + 0 = i + (0 + 1) by omega) (show i + 1 + 0 = i + (0 + 1) by omega),
    objCast_app' f.1 (show i + 1 + 0 = i + (0 + 1) by omega)
      (show i + (0 + 1) = j + 1 by omega) (show i + 1 + 0 = j + 1 by omega)]

end RightModule

/-- **Axioms (A), (B) and (C) for `Mod^dg(C)`.** Every closed degree-zero morphism
`f : M ⟶ N` of right differential graded `C`-modules has the cone `c(f) = N ⊕ M⟦1⟧` with
differential twisted by `f`; the sequence `N ⟶ c(f) ⟶ M⟦1⟧` is admissible and its connecting
arrow is `f⟦1⟧`. -/
def rightModuleConeSituation (C : DGCategory.{v, u} R) :
    ConeSituation (rightModuleCategory.{w} C) where
  directSum := rightModuleDirectSumAxiom.{w} C
  shift := rightModuleShiftAxiomB.{w} C
  cone := by intro M N f; exact RightModule.coneOf f.1 f.2
  coneSequence := by intro M N f; exact RightModule.coneSequenceOf f.1 f.2
  cone_connecting := by intro M N f; exact RightModule.coneConnecting f

open CategoryTheory CategoryTheory.Limits in
/-- The homotopy category `K(Mod^dg(C))` of the right differential graded modules over a
differential graded category `C` is triangulated, with the translation functors of axiom (B)
and the triangles of admissible short exact sequences as distinguished triangles. -/
theorem rightModuleHomotopyCategory_isTriangulated (C : DGCategory.{v, u} R) :
    letI : Preadditive (rightModuleCategory.{w} C).K :=
      homotopyPreadditive (rightModuleCategory.{w} C)
    letI : HasZeroObject (rightModuleCategory.{w} C).K :=
      homotopyHasZeroObject _ (rightModuleConeSituation.{w} C)
    letI : HasShift (rightModuleCategory.{w} C).K ℤ :=
      (rightModuleConeSituation.{w} C).shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor (rightModuleCategory.{w} C).K n).Additive :=
      fun n => homotopyShiftAdditive _ (rightModuleConeSituation.{w} C) n
    letI : Pretriangulated (rightModuleCategory.{w} C).K :=
      homotopyPretriangulated _ (rightModuleConeSituation.{w} C)
    IsTriangulated (rightModuleCategory.{w} C).K :=
  homotopyCategory_isTriangulated (rightModuleCategory.{w} C) (rightModuleConeSituation.{w} C)

end DGCategory
