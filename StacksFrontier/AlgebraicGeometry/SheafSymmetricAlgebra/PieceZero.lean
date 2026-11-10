module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras

/-!
# The degree-zero piece of `Sym(E)` is the structure sheaf

`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the degreewise sheafification of the
sectionwise symmetric algebra of an `𝒪_X`-module `E`. Its degree-zero piece is the sheafification
of `U ↦ Sym⁰_{𝒪(U)}(E(U))`, and that presheaf is the free presheaf of rank one; sheafification
carries the free presheaf of rank one to the free *sheaf* of rank one. **So the degree-zero piece
of `Sym(E)` is the structure sheaf, and the identification carries the unit of `Sym(E)` to `1`.**

This is the degree-zero comparison that the `Not done here` section of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ProjComparison.lean` records as owed, in the
form a consumer of the graded ring of sections needs it: the structure map
`Γ(X, U) →+* Γ(Sym(E), U)₀` of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` is `r ↦ r • 1`, so
knowing the degree-zero piece and the unit pins that map down.

## Main definitions

* `Stacks.SymGraded.pieceZeroIso`: **the degree-zero piece of `Sym(E)` is the structure
  sheaf.**

## Main results

* `Stacks.SymGraded.symPowZeroIso_hom_one` and
  `Stacks.SymGraded.symPowZeroIso_inv_one`: the degree-zero identification of the *sectionwise*
  symmetric powers matches `1` with the unit of the symmetric algebra. These are the symmetric
  analogues of `PresheafOfModules.tensorPowZeroIso_inv_one`.
* `Stacks.SymGraded.siteOne_eval_eq_symPowOneSection`: the unit of the sectionwise symmetric
  algebra of `StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Site.lean` is the unit of
  `PresheafOfModules.symPow 0`; the two constructions of the zeroth power are the same presheaf,
  so this is `Subtype.ext rfl`.
* `Stacks.SymGraded.pieceZeroIso_hom_one`: **the identification carries the unit of `Sym(E)` to
  `1`.**

## Implementation notes

`PresheafOfModules.symPow 0 E.val` and `Stacks.SymGraded.siteGradedPiece E.val 0` are the same
presheaf of modules by `rfl` — both are `U ↦ Sym⁰_{𝒪(U)}(E(U))` with the semilinear base changes
of the restriction maps of `E` — so the sectionwise lemmas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/QuasicoherentAlgebras.lean` apply to the pieces of
`Scheme.Modules.symmetricAlgebra` with no comparison in between.

The naturality step of `pieceZeroIso_hom_one` names its sheafification map explicitly. Left as
an implicit argument it is a metavariable when the rewrite's instances are synthesized, and
`Presheaf.IsLocallyInjective` for the identity is then not found, although it is found as soon as
the map is given.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace Stacks.SymGraded

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- The zeroth sectionwise symmetric power is the free presheaf of rank one, and the
identification carries `1` to the unit of the symmetric algebra. -/
theorem symPowZeroIso_hom_one (X : Cᵒᵖ) :
    (PresheafOfModules.symPowZeroIso F).hom.app X
        (PresheafOfModules.unitOneSection (O ⋙ forget₂ _ RingCat) X) =
      PresheafOfModules.symPowOneSection F X :=
  Subtype.ext (map_one (algebraMap ((O ⋙ forget₂ CommRingCat RingCat).obj X)
    (SymmetricAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj X) (F.obj X))))

/-- The degree-zero identification of the sectionwise symmetric powers carries the algebra unit
back to `1`. The symmetric analogue of `PresheafOfModules.tensorPowZeroIso_inv_one`. -/
theorem symPowZeroIso_inv_one (X : Cᵒᵖ) :
    (PresheafOfModules.symPowZeroIso F).inv.app X (PresheafOfModules.symPowOneSection F X) =
      PresheafOfModules.unitOneSection (O ⋙ forget₂ _ RingCat) X := by
  rw [← symPowZeroIso_hom_one F X]
  change ((PresheafOfModules.symPowZeroIso F).hom ≫
    (PresheafOfModules.symPowZeroIso F).inv).app X
      (PresheafOfModules.unitOneSection (O ⋙ forget₂ _ RingCat) X) = _
  rw [(PresheafOfModules.symPowZeroIso F).hom_inv_id]
  rfl

/-- The unit of the sectionwise symmetric algebra is the unit of the zeroth symmetric power. -/
theorem siteOne_eval_eq_symPowOneSection (X : Cᵒᵖ) :
    (siteOne F).eval X = PresheafOfModules.symPowOneSection F X :=
  Subtype.ext rfl

end Sectionwise

/-! ### The degree-zero piece on a scheme -/

variable {X : Scheme.{u}} (E : X.Modules)

/-- **The degree-zero piece of `Sym(E)` is the structure sheaf.** The zeroth sectionwise
symmetric power is the free presheaf of rank one, and sheafification carries that to the free
sheaf of rank one. -/
def pieceZeroIso :
    (Scheme.Modules.symmetricAlgebra X E).piece 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.symPowZeroIso E.val).symm ≪≫
    PresheafOfModules.sheafificationObjUnitIso (𝟙 X.ringCatSheaf.obj)

/-- **The degree-zero identification carries the unit of `Sym(E)` to `1`.** -/
theorem pieceZeroIso_hom_one (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    (pieceZeroIso E).hom.val.app U ((Scheme.Modules.symmetricAlgebra X E).one.eval U) =
      (1 : X.ringCatSheaf.obj.obj U) := by
  change (PresheafOfModules.sheafificationObjUnitIso (𝟙 X.ringCatSheaf.obj)).hom.val.app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModules.symPowZeroIso E.val).inv).val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (PresheafOfModules.symPow 0 E.val)).app U
          (PresheafOfModules.symPowOneSection E.val U))) = _
  have key : (PresheafOfModules.symPowZeroIso E.val).inv.app U
      (PresheafOfModules.symPowOneSection E.val U) =
      PresheafOfModules.unitOneSection X.ringCatSheaf.obj U :=
    symPowZeroIso_inv_one E.val U
  rw [PresheafOfModules.unit_naturality_apply (α := 𝟙 X.ringCatSheaf.obj)
      (PresheafOfModules.symPowZeroIso E.val).inv U
      (PresheafOfModules.symPowOneSection E.val U)]
  refine Eq.trans (congrArg (fun z =>
    (PresheafOfModules.sheafificationObjUnitIso (𝟙 X.ringCatSheaf.obj)).hom.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (PresheafOfModules.unit X.ringCatSheaf.obj)).app U z)) key) ?_
  exact Eq.trans
    (PresheafOfModules.sheafificationObjUnitIso_hom_unit (𝟙 X.ringCatSheaf.obj) U _) rfl

end Stacks.SymGraded

end
