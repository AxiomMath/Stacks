module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex of a functional on a presheaf of modules

`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential` builds the Koszul differential
`PresheafOfModules.exteriorKoszulD` on the sectionwise exterior algebra of a presheaf of
modules. This file assembles its nonnegative degrees into a chain complex of presheaves of
modules: in degree `n` the presheaf `U ↦ ⋀^n_{O(U)}(F(U))`, with the contraction differential.

This is the underlying complex of the object of Stacks tag 062K, in the same relation to it as
`Koszul.complex` is to `Koszul.differentialGradedAlgebra` at the ring level: the graded algebra
is `PresheafOfModules.exteriorAlgebraGradedAlgebra` and the derivation is
`PresheafOfModules.exteriorKoszulD`, and this complex records only the homogeneous pieces and
the differential between them.

## Main definitions

* `PresheafOfModules.exteriorKoszulComplex`: the chain complex of presheaves of modules.

## Main results

* `PresheafOfModules.exteriorKoszulComplex_d`: its differential is `exteriorKoszulD`, whose
  action on sections is contraction by the functional
  (`PresheafOfModules.exteriorAlgebraPieceVal_exteriorKoszulD`).

## Implementation notes

The complex is indexed by `ℕ`, and its degree-`n` object is the piece of the `ℤ`-graded
sectionwise exterior algebra in degree `(n : ℤ)`. The negative degrees are omitted because
they carry no nonzero sections (`exteriorAlgebraPiece_eq_zero_of_neg`), so nothing is lost;
`exteriorKoszulD_eq_zero_of_neg` is the statement that the differentials there vanish.

The two degree coercions `((n + 1 : ℕ) : ℤ)` and `(n : ℤ) + 1` are definitionally equal, which
is what lets `exteriorKoszulD F φ (n : ℤ)` be used as the differential from degree `n + 1` to
degree `n` with no transport.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
-/

@[expose] public section

open CategoryTheory Opposite

open scoped ExteriorAlgebra

universe v u w a

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))
  (φ : ExteriorFunctional.{v, u, w, a} F)

/-- **The Koszul complex of a functional on a presheaf of modules.** In degree `n` it is the
presheaf `U ↦ ⋀^n_{O(U)}(F(U))` of sectionwise exterior powers, and its differential is
contraction by the functional. -/
@[sga "3 III 4.6.1" "more general", sga "6 VII 1.1" "more general"]
noncomputable def exteriorKoszulComplex :
    ChainComplex (PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) ℕ :=
  ChainComplex.of (fun n => exteriorAlgebraPiece (n : ℤ) F)
    (fun n => exteriorKoszulD F φ (n : ℤ))
    (fun n => exteriorKoszulD_comp_exteriorKoszulD F φ (n : ℤ))

/-- The degree-`n` object of `exteriorKoszulComplex F φ` is the presheaf of `n`-th sectionwise
exterior powers `exteriorAlgebraPiece (n : ℤ) F`. -/
@[simp]
theorem exteriorKoszulComplex_X (n : ℕ) :
    (exteriorKoszulComplex F φ).X n = exteriorAlgebraPiece (n : ℤ) F :=
  rfl

/-- The differential of `exteriorKoszulComplex F φ` from degree `n + 1` to degree `n` is the
Koszul differential `exteriorKoszulD F φ (n : ℤ)`. -/
@[simp]
theorem exteriorKoszulComplex_d (n : ℕ) :
    (exteriorKoszulComplex F φ).d (n + 1) n = exteriorKoszulD F φ (n : ℤ) :=
  ChainComplex.of_d (fun n : ℕ => exteriorAlgebraPiece (n : ℤ) F)
    (fun n : ℕ => exteriorKoszulD F φ (n : ℤ)) n

end PresheafOfModules

end
