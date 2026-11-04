module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitIterModel
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic

/-!
# Reducing the colimiting property of Stacks Tag 0EXB to abelian sheaves

The cocone whose colimiting property is the remaining input to Stacks Tag 0EXB lives in sheaves
of `𝒪_X`-modules, and its legs and transition morphisms are built from iterates of restriction
of scalars. Restriction of scalars does not change the underlying sheaf of abelian groups, and
the forgetful functor to abelian sheaves reflects colimits. So the whole cocone may be read on
abelian sheaves, where every restriction of scalars — and with it every transport which exists
only to make the iterates typecheck — simply disappears.

## Main results

* `Stacks.SheafOfModules.reflectsColimitsOfShape_toSheaf`: the forgetful functor from sheaves
  of modules to abelian sheaves reflects colimits.
* `AlgebraicGeometry.endoIter_frobeniusRestrictScalars_comp_toSheaf`: the `j`-fold iterate of
  restriction of scalars along Frobenius does not change the underlying abelian sheaf.
* `AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone_of_toSheaf`: **it suffices to prove
  the colimiting property on abelian sheaves.**

## Implementation notes

All three identities of functors below hold on the nose: restriction of scalars of a sheaf of
modules replaces only the scalar action on the underlying presheaf of abelian groups, and the
forgetful functor to abelian sheaves reads off exactly that presheaf. That is what makes the
reduction free of transports, and is why it is worth isolating before any computation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe w' w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The forgetful functor to abelian sheaves reflects colimits.** It preserves them and
reflects isomorphisms. -/
lemma reflectsColimitsOfShape_toSheaf (R : Sheaf J RingCat.{u}) (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] [HasColimitsOfShape K (_root_.SheafOfModules.{v} R)] :
    ReflectsColimitsOfShape K (_root_.SheafOfModules.toSheaf.{v} R) :=
  have := Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf.{w', w}
    R K
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- Restriction of scalars along Frobenius does not change the underlying abelian sheaf. -/
lemma frobeniusRestrictScalars_comp_toSheaf :
    frobeniusRestrictScalars X p hX ⋙ _root_.SheafOfModules.toSheaf X.ringSheafOnOpens =
      _root_.SheafOfModules.toSheaf X.ringSheafOnOpens :=
  rfl

/-- Restriction of scalars along the stage-`n` coprojection does not change the underlying
abelian sheaf. -/
lemma frobeniusStageRestrictScalars_comp_toSheaf (n : ℕ) :
    frobeniusStageRestrictScalars X p hX n ⋙
        _root_.SheafOfModules.toSheaf X.ringSheafOnOpens =
      _root_.SheafOfModules.toSheaf (frobeniusColimitRingSheaf X p hX) :=
  rfl

/-- **The `j`-fold iterate of restriction of scalars along Frobenius does not change the
underlying abelian sheaf.** -/
lemma endoIter_frobeniusRestrictScalars_comp_toSheaf (j : ℕ) :
    (frobeniusRestrictScalars X p hX).endoIter j ⋙
        _root_.SheafOfModules.toSheaf X.ringSheafOnOpens =
      _root_.SheafOfModules.toSheaf X.ringSheafOnOpens := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Functor.endoIter_succ, Functor.assoc, frobeniusRestrictScalars_comp_toSheaf, ih]

/-- **It suffices to prove the colimiting property of the cocone of Stacks Tag 0EXB on abelian
sheaves.** -/
noncomputable def isColimit_frobeniusStageRestrictCocone_of_toSheaf (n : ℕ)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (h : IsColimit ((_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).mapCocone
      (frobeniusStageRestrictCocone X p hX n G))) :
    IsColimit (frobeniusStageRestrictCocone X p hX n G) :=
  have := Stacks.SheafOfModules.reflectsColimitsOfShape_toSheaf.{0, 0}
    X.ringSheafOnOpens ℕ
  isColimitOfReflects (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens) h

end AlgebraicGeometry

end
