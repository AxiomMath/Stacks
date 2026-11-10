module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.PieceZero

/-!
# The structure map of a graded algebra of sections is a bijection onto degree zero

For a sheaf-level graded `𝒪_S`-algebra `A` and an open `U` of `S`, the structure map
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` sends a function `r` on
`U` to the degree-zero homogeneous section `r • 1`. **This file shows that it is a bijection onto
the degree-zero part of the graded ring of sections** as soon as multiplying the algebra unit by
a function is a bijection onto the degree-zero local sections, and reads off the consequence a
consumer of `Stacks.GradedRationalPoint` needs: when every nonzero function on `U` is invertible,
every nonzero element of the degree-zero part of the section ring is a unit.

The hypothesis is supplied for the symmetric algebra of a module on an arbitrary scheme by
`Stacks.SymGraded.bijective_smul_one` below, which is
`SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit` fed the degree-zero
identification `Stacks.SymGraded.pieceZeroIso` of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/PieceZero.lean`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom_injective` and
  `exists_strHom_eq_of_mem_grading_zero`: **the structure map is injective, and its image is the
  degree-zero part of the section ring.**
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.isUnit_coe_of_ne_zero`: **every
  nonzero element of the degree-zero part of the section ring is a unit**, when every nonzero
  function on `U` is.
* `Stacks.SymGraded.bijective_smul_one`: **multiplying the unit of `Sym(E)` by a function on the
  base is a bijection onto the degree-zero local sections**, for a module on an arbitrary scheme.

## Implementation notes

The two spellings of a degree-zero local section are the reason the bijectivity statement is
restated here rather than used directly from the module
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic`.
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` writes `Γ(M, U)` for
`(Scheme.Modules.presheaf M).obj (op U)`, an object of `Ab`, and keys the instance
`Module Γ(S, U) Γ(M, U)` on that spelling together with `M : S.Modules`, while the graded-algebra
API speaks of `M.val.obj (op U)`, an object of `ModuleCat Γ(S, U)`. The module structures are the
same term — the instance is literally `(M.val.obj (op U)).isModule` — so
`Stacks.SymGraded.bijective_smul_one` is the degree-zero bijectivity of the sheaf-level algebra
with no transport, stated in the spelling `Stacks.AlgebraicGeometry.RelativeProjBridge
.SheafGradedAlgebra.strHom` uses.

No `@[stacks]` attribute is attached: the degree-zero identification is not an assertion of a
Stacks tag, and the graded rings of local sections of Tag 01NN are already claimed by
`StacksFrontier/AlgebraicGeometry/RelativeProjBridge/SectionRing.lean`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)
    (hbij : Function.Bijective (fun r : Γ(S, U) => r • A.one U))

include hbij

/-- **The structure map is injective**, as soon as multiplying the algebra unit by a function on
the base is a bijection onto the degree-zero local sections. -/
theorem strHom_injective : Function.Injective (A.strHom U) := fun _ _ hr =>
  hbij.injective (DirectSum.of_injective (β := A.sectionPieces U) 0 hr)

/-- **The image of the structure map is the degree-zero part of the section ring.** -/
theorem exists_strHom_eq_of_mem_grading_zero {x : A.sectionRing U} (hx : x ∈ A.grading U 0) :
    ∃ r : Γ(S, U), A.strHom U r = x := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨r, hr⟩ := hbij.surjective y
  exact ⟨r, congrArg (DirectSum.of (A.sectionPieces U) 0) hr⟩

/-- **Every nonzero element of the degree-zero part of the section ring is a unit**, when every
nonzero function on `U` is a unit. This is the hypothesis `hfield` of
`Stacks.GradedRationalPoint.exists_mem_degreeOne_forall_notMem`. -/
theorem isUnit_coe_of_ne_zero (hU : ∀ r : Γ(S, U), r ≠ 0 → IsUnit r)
    (c : ↥(A.grading U 0)) (hc : c ≠ 0) : IsUnit ((c : A.sectionRing U)) := by
  obtain ⟨r, hr⟩ := exists_strHom_eq_of_mem_grading_zero A U hbij c.2
  have hr0 : r ≠ 0 := by
    intro h
    refine hc (Subtype.ext ?_)
    rw [← hr, h, map_zero]
    rfl
  rw [← hr]
  exact (hU r hr0).map (A.strHom U)

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **Multiplying the unit of `Sym(E)` by a function on the base is a bijection onto the
degree-zero local sections**, for a module on an arbitrary scheme: the degree-zero piece of
`Sym(E)` is the structure sheaf, by `Stacks.SymGraded.pieceZeroIso`, compatibly with the units,
by `Stacks.SymGraded.pieceZeroIso_hom_one`.

This is the hypothesis of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom_injective` and of
`Stacks.RelativeProj.Situation.isIso_sectionRingZeroMap` for the projective bundle of `E`. -/
theorem bijective_smul_one (U : X.Opens) :
    Function.Bijective
      (fun r : Γ(X, U) => r • (schemeSheafGradedAlgebra E hqc).one U) :=
  SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit
    (Scheme.Modules.symmetricAlgebra X E) (pieceZeroIso E) (pieceZeroIso_hom_one E) (op U)

end Stacks.SymGraded

end
