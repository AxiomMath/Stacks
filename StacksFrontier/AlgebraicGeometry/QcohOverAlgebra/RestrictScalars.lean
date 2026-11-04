module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic

/-!
# Restriction of scalars reflects colimits, epimorphisms and generating sections

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`.  Restriction of scalars
`SheafOfModules.restrictScalars α` does not change the underlying sheaf of abelian groups of a
sheaf of modules, so it reflects isomorphisms, colimits and epimorphisms.  Consequently a family
of sections of an `R'`-module which generates it after restriction of scalars already generates
it as an `R'`-module.  No local surjectivity hypothesis on `α` is involved.

## Main definitions

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.freeComparison`: the canonical morphism from the free
  `R`-module on a type to the restriction of scalars of the free `R'`-module on it.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.generatingSectionsOfRestrictScalars`: a family of
  generating sections of `(restrictScalars α).obj N` is a family of generating sections of `N`.

## Main results

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsIsomorphisms_restrictScalars`,
  `Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsColimitsOfShape_restrictScalars` and
  `Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsEpimorphisms_restrictScalars`: restriction
  of scalars reflects isomorphisms, colimits and epimorphisms.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.preservesFiniteLimits_restrictScalars`: restriction
  of scalars preserves finite limits, in particular kernels.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.freeComparison_comp`: the morphism from the free
  `R`-module on a family of sections of an `R'`-module factors through the restriction of scalars
  of the morphism from the free `R'`-module on it.
-/

@[expose] public section

universe w' w v u u'

open CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.QcohOverAlgebra

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-! ### Reflection properties of restriction of scalars -/

/-- Restriction of scalars along a morphism of sheaves of rings reflects isomorphisms: a
morphism of sheaves of `R'`-modules which becomes invertible as a morphism of sheaves of
`R`-modules is invertible. -/
instance reflectsIsomorphisms_restrictScalars :
    (SheafOfModules.restrictScalars.{u} α).ReflectsIsomorphisms where
  reflects {_M _N} f _ :=
    have : IsIso ((SheafOfModules.toSheaf.{u} R').map f) :=
      inferInstanceAs (IsIso ((SheafOfModules.toSheaf.{u} R).map
        ((SheafOfModules.restrictScalars.{u} α).map f)))
    isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} R')

/-- Restriction of scalars along a morphism of sheaves of rings reflects colimits of shape `K`. -/
instance reflectsColimitsOfShape_restrictScalars (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{u}] :
    ReflectsColimitsOfShape K (SheafOfModules.restrictScalars.{u} α) :=
  have := RestrictScalarsColimits.preservesColimitsOfShape_restrictScalars.{w', w} α K
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- Restriction of scalars along a morphism of sheaves of rings reflects epimorphisms. -/
instance reflectsEpimorphisms_restrictScalars :
    (SheafOfModules.restrictScalars.{u} α).ReflectsEpimorphisms :=
  have := reflectsColimitsOfShape_restrictScalars.{0, 0} α WalkingSpan
  inferInstance

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits; in
particular it preserves kernels. -/
noncomputable instance preservesFiniteLimits_restrictScalars :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) :=
  have : PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R'))
  preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R)

/-! ### Generating sections over the bigger sheaf of rings -/

/-- The canonical morphism from the free sheaf of `R`-modules on a type `I` to the restriction
of scalars of the free sheaf of `R'`-modules on `I`.  It is the morphism attached to the
tautological family of sections of the free `R'`-module. -/
noncomputable def freeComparison (I : Type u) :
    SheafOfModules.free.{u} (R := R) I ⟶
      (SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.free.{u} (R := R') I) :=
  ((SheafOfModules.restrictScalars.{u} α).obj
    (SheafOfModules.free.{u} (R := R') I)).freeHomEquiv.symm
      (fun i ↦ SheafOfModules.freeSection (R := R') i)

/-- The morphism from the free sheaf of `R`-modules on a family of sections of an `R'`-module
`N` factors through the restriction of scalars of the morphism from the free sheaf of
`R'`-modules on the same family. -/
theorem freeComparison_comp (N : SheafOfModules.{u} R') {I : Type u} (s : I → N.sections) :
    freeComparison α I ≫
        (SheafOfModules.restrictScalars.{u} α).map (N.freeHomEquiv.symm s) =
      ((SheafOfModules.restrictScalars.{u} α).obj N).freeHomEquiv.symm s :=
  (SheafOfModules.freeHomEquiv_symm_comp _ _).trans
    (congrArg _ (funext (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s)))

/-- A family of sections of a sheaf of `R'`-modules `N` which generates `N` after restriction of
scalars along `α : R ⟶ R'` already generates `N` as a sheaf of `R'`-modules, with the same index
type and the same sections. -/
noncomputable def generatingSectionsOfRestrictScalars {N : SheafOfModules.{u} R'}
    (σ : ((SheafOfModules.restrictScalars.{u} α).obj N).GeneratingSections) :
    N.GeneratingSections where
  I := σ.I
  s := σ.s
  epi :=
    have _h : Epi (freeComparison α σ.I ≫
        (SheafOfModules.restrictScalars.{u} α).map (N.freeHomEquiv.symm σ.s)) :=
      (freeComparison_comp α N σ.s) ▸ σ.epi
    Functor.epi_of_epi_map (SheafOfModules.restrictScalars.{u} α)
      (epi_of_epi (freeComparison α σ.I) _)

end Stacks.AlgebraicGeometry.QcohOverAlgebra

end
