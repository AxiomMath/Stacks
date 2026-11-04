module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Unit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Degree zero of the symmetric algebra is the structure sheaf

`PresheafOfModules.symmetricAlgebraSheafify α F` is the symmetric algebra of the sheafification
of a presheaf of modules `F`, as a sheaf of graded algebras, and
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X F` is its instantiation at a module sheaf on
a scheme. This file identifies the degree-zero piece of either with the free rank-one sheaf of
modules on the base, compatibly with the units, and reads off the consequence that multiplying
the algebra unit by a function on the base is a bijection onto the degree-zero local sections.

The identification is the composite of two steps: `PresheafOfModules.symPowIntZeroIso`
identifies `Sym⁰ F` with the free rank-one presheaf of modules at the sectionwise level, and
`PresheafOfModules.sheafificationObjUnitIso` carries the free rank-one presheaf of modules across
the sheafification.

## Main definitions

* `PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso`: **degree zero of `Sym(F)` is the free
  rank-one sheaf of modules**, `(symmetricAlgebraSheafify α F).piece 0 ≅ SheafOfModules.unit R`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso`: the same for the symmetric
  algebra of a module sheaf on a scheme.

## Main results

* `SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit`: multiplying the algebra
  unit by a function on the base is a bijection onto the degree-zero local sections, whenever
  degree zero is identified with the free rank-one sheaf of modules compatibly with the units.
* `PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso_hom_one`: the identification carries the
  unit of `Sym(F)` to `1`.
* `AlgebraicGeometry.Scheme.Modules.bijective_smul_one_symmetricAlgebra`: multiplying the unit of
  the symmetric algebra of a module sheaf on a scheme by a function on the base is a bijection
  onto the degree-zero local sections.

## Implementation notes

The module universe is the ring universe: `PresheafOfModules.unit` forces it, so the site-level
results are stated for a presheaf of modules in the ring universe `w`. A scheme fixes every
universe to `u`, so the scheme-level results are unaffected.

The scheme-level results pass their instance arguments positionally, with the universes pinned:
supplying `α := 𝟙 X.ringCatSheaf.obj` asks the elaborator to solve `?R.obj ≟ X.ringCatSheaf.obj`,
a projection it cannot invert, and the four instance arguments are then synthesized against goals
still carrying `?R`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public section

open CategoryTheory Opposite PresheafOfModules TopologicalSpace

universe v u w

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Multiplying the algebra unit by a function on the base is a bijection onto the degree-zero
local sections**, whenever degree zero of the algebra is identified with the free rank-one sheaf
of modules by an isomorphism carrying the unit to `1`. -/
theorem bijective_smul_one_of_pieceZeroIsoUnit (A : GradedAlgebra.{w, w} R)
    (e : A.piece 0 ≅ SheafOfModules.unit R)
    (he : ∀ U : Cᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U)) (U : Cᵒᵖ) :
    Function.Bijective (fun r : R.obj.obj U => r • A.one.eval U) := by
  refine ⟨fun r r' hr => ?_, fun x => exists_smul_one_of_isoUnit A e he U x⟩
  have key (c : R.obj.obj U) : e.hom.val.app U (c • A.one.eval U) = c := by
    rw [map_smul, he]
    exact _root_.mul_one c
  rw [← key r, ← key r']
  exact congrArg (e.hom.val.app U) hr

end SheafOfModules.GradedAlgebra

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **Degree zero of `Sym(F)` is the free rank-one sheaf of modules.** The degree-zero piece of
the sheafified symmetric algebra is the sheafification of `Sym⁰ F`, which is the free rank-one
presheaf of modules by `PresheafOfModules.symPowIntZeroIso`, and
`PresheafOfModules.sheafificationObjUnitIso` carries that across the sheafification. -/
noncomputable def symmetricAlgebraSheafifyPieceZeroIso :
    (symmetricAlgebraSheafify α F).piece 0 ≅ SheafOfModules.unit R :=
  ((sheafification α).mapIso (symPowIntZeroIso F)).symm ≪≫ sheafificationObjUnitIso α

/-- The inverse of the degree-zero identification of `Sym(F)`, unfolded. -/
theorem symmetricAlgebraSheafifyPieceZeroIso_inv :
    (symmetricAlgebraSheafifyPieceZeroIso α F).inv =
      sheafificationObjUnitInv α ≫ (sheafification α).map (symPowIntZeroIso F).hom := rfl

/-- The degree-zero identification of `Sym(F)` carries `1` to the unit of `Sym(F)`. -/
theorem symmetricAlgebraSheafifyPieceZeroIso_inv_one (W : Cᵒᵖ) :
    (symmetricAlgebraSheafifyPieceZeroIso α F).inv.val.app W (1 : R.obj.obj W) =
      (symmetricAlgebraSheafify α F).one.eval W := by
  have e₁ : (symmetricAlgebraSheafifyPieceZeroIso α F).inv.val.app W (1 : R.obj.obj W) =
      ((sheafification α).map (symPowIntZeroIso F).hom).val.app W
        ((sheafificationObjUnitInv α).val.app W (1 : R.obj.obj W)) := rfl
  have e₂ : (symmetricAlgebraSheafify α F).one.eval W =
      Hom.app (sheafifyUnit α (symPowInt 0 F)) W ((symPowIntOne F).eval W) := rfl
  rw [e₁, sheafificationObjUnitInv_app_one α W,
    ← sheafifyUnit_naturality_apply α (symPowIntZeroIso F).hom W
      (1 : (O ⋙ forget₂ CommRingCat RingCat).obj W),
    symPowIntZeroIso_hom_one F W, e₂]

/-- **The degree-zero identification of `Sym(F)` carries the unit of `Sym(F)` to `1`.** -/
theorem symmetricAlgebraSheafifyPieceZeroIso_hom_one (W : Cᵒᵖ) :
    (symmetricAlgebraSheafifyPieceZeroIso α F).hom.val.app W
        ((symmetricAlgebraSheafify α F).one.eval W) = (1 : R.obj.obj W) := by
  rw [← symmetricAlgebraSheafifyPieceZeroIso_inv_one α F W]
  exact congrArg (fun h : SheafOfModules.unit R ⟶ SheafOfModules.unit R =>
    h.val.app W (1 : R.obj.obj W)) (symmetricAlgebraSheafifyPieceZeroIso α F).inv_hom_id

/-- **Multiplying the unit of `Sym(F)` by a function on the base is a bijection onto the
degree-zero local sections.** -/
theorem bijective_smul_one_symmetricAlgebraSheafify (W : Cᵒᵖ) :
    Function.Bijective (fun r : R.obj.obj W => r • (symmetricAlgebraSheafify α F).one.eval W) :=
  SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit
    (symmetricAlgebraSheafify α F) (symmetricAlgebraSheafifyPieceZeroIso α F)
    (symmetricAlgebraSheafifyPieceZeroIso_hom_one α F) W

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)

/-- **Degree zero of the symmetric algebra of a module sheaf on a scheme is the structure
sheaf.** -/
noncomputable def symmetricAlgebraPieceZeroIso :
    (symmetricAlgebra X F).piece 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  @PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso.{u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val

/-- **Multiplying the unit of `Sym(F)` by a function on the base is a bijection onto the
degree-zero local sections.** -/
theorem bijective_smul_one_symmetricAlgebra (U : X.Opens) :
    Function.Bijective
      (fun r : X.ringCatSheaf.obj.obj (op U) => r • (symmetricAlgebra X F).one.eval (op U)) :=
  @PresheafOfModules.bijective_smul_one_symmetricAlgebraSheafify.{u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val (op U)

end AlgebraicGeometry.Scheme.Modules

end
