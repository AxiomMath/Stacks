module

public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Restriction of scalars of sheaves of modules on a site

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`. Restriction of scalars
`SheafOfModules R' ⥤ SheafOfModules R` changes nothing but the scalars: the underlying sheaf of
abelian groups is untouched. This file records the two consequences of that which the library
needed and did not have on a general site.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso`: **restriction of scalars
  commutes with the sheafification of presheaves of modules**, even though the two
  sheafifications are formed over different sheaves of rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits`: restriction of scalars
  preserves all colimits indexed by diagram objects in the module universe.
* `AlgebraicGeometry.SheafOfModules.sheafify_smul_restrictScalars`: the scalar multiplication on
  a sheafified presheaf of modules does not depend on which of the two sheaves of rings it is
  formed over.

## Implementation notes

Colimit preservation was available only over a scheme, as the private
`restrictScalars_preservesColimits` of
`StacksFrontier/AlgebraicGeometry/FunctorsAndMorphisms/IntegralTransformQcoh/Equivalence.lean`;
nothing in that proof uses the topology of a scheme, and the version here is the same argument
over an arbitrary site.

`Mathlib.PresheafOfModules.sheafify` endows the sheafification of the *underlying presheaf of
abelian groups* with a module structure, so the two sheaves of modules compared by
`restrictScalarsSheafificationIso` have literally the same sections and the comparison map is
the identity on them. Only the two scalar multiplications have to be compared, and each is
determined by separatedness from its values on local sections of the original presheaf, where
they agree by naturality of the map of sheaves of rings. The identification is *not* available
from the uniqueness of adjoints, the way
`Stacks.ModuleUp.pullbackIdSheafificationIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteUpSheafificationPullback.lean` identifies
sheafification over `α` with extension of scalars followed by sheafification: restriction of
scalars is a right adjoint, so neither composite here is a left adjoint.

Both statements are written with `α` an arbitrary morphism of sheaves of rings; the
`RingCat`-valued spelling is the one `SheafOfModules` is indexed by.

Nothing here carries a `stacks` attribute. The nearest tags are [Stacks, Tag 03DB], which is
the existence of limits and colimits in `Mod(𝒪)` together with their preservation by the
forgetful functor to abelian sheaves — not by a change of rings — and [Stacks, Tag 03CZ], which
is the adjunction between restriction and change of rings; neither states either result below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {R R' : Sheaf J RingCat.{u}}

/-- **Restriction of scalars along a morphism of sheaves of rings preserves all colimits**
indexed by diagram objects in the module universe: after forgetting the module structure it is
the identity, and forgetting both preserves and reflects colimits. -/
theorem restrictScalars_preservesColimits (α : R ⟶ R') :
    PreservesColimitsOfSize.{max u' v, v} (_root_.SheafOfModules.restrictScalars.{v} α) := by
  have : PreservesColimitsOfSize.{max u' v, v}
      (_root_.SheafOfModules.restrictScalars.{v} α ⋙ _root_.SheafOfModules.toSheaf.{v} R) := by
    show PreservesColimitsOfSize.{max u' v, v} (_root_.SheafOfModules.toSheaf.{v} R')
    exact toSheaf_preservesColimits R'
  constructor
  intro K _
  have : ReflectsColimitsOfShape K (_root_.SheafOfModules.toSheaf.{v} R) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (_root_.SheafOfModules.restrictScalars.{v} α) (_root_.SheafOfModules.toSheaf.{v} R)

section Sheafification

variable (α : R ⟶ R') (P : PresheafOfModules.{v} R'.obj)

/-- Scalar multiplication on the sheafification of a presheaf of modules does not depend on
which of two sheaves of rings it is formed over: the scalar `r` of `R` acts on the sheafified
sections as its image in `R'` does.  Both actions are determined, by separatedness, by the
action on local sections of the original presheaf, where they agree by naturality of `α`. -/
theorem sheafify_smul_restrictScalars (X : Cᵒᵖ)
    (r : R.obj.obj X) (a : (CategoryTheory.sheafify J P.presheaf).obj X) :
    PresheafOfModules.Sheafify.smul (𝟙 R.obj)
        (CategoryTheory.toSheafify J
          ((PresheafOfModules.restrictScalars α.hom).obj P).presheaf) r a =
      PresheafOfModules.Sheafify.smul (𝟙 R'.obj)
        (CategoryTheory.toSheafify J P.presheaf) ((α.hom.app X).hom r) a := by
  apply ((presheafToSheaf J AddCommGrpCat.{v}).obj P.presheaf).isSeparated _ _
    (Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J P.presheaf) a)
  rintro Y f ⟨a₀, ha₀⟩
  refine Eq.trans (PresheafOfModules.Sheafify.map_smul_eq (𝟙 R.obj)
    (CategoryTheory.toSheafify J ((PresheafOfModules.restrictScalars α.hom).obj P).presheaf)
    r a f.op (R.obj.map f.op r) (by simp) a₀ ha₀) (Eq.trans ?_
      (PresheafOfModules.Sheafify.map_smul_eq (𝟙 R'.obj)
        (CategoryTheory.toSheafify J P.presheaf) ((α.hom.app X).hom r) a f.op
        (R'.obj.map f.op ((α.hom.app X).hom r)) (by simp) a₀ ha₀).symm)
  have hnat : (α.hom.app (Opposite.op Y)).hom ((R.obj.map f.op).hom r)
      = (R'.obj.map f.op).hom ((α.hom.app X).hom r) := by
    rw [← RingCat.comp_apply, α.hom.naturality f.op, RingCat.comp_apply]
  show (CategoryTheory.toSheafify J P.presheaf).app (Opposite.op Y)
      ((α.hom.app (Opposite.op Y)).hom ((R.obj.map f.op).hom r) • a₀) = _
  rw [hnat]
  rfl

/-- **Restriction of scalars commutes with the sheafification of presheaves of modules**, even
though the two sheafifications are formed over *different* sheaves of rings: sheafifying a
presheaf of `R'`-modules and then restricting the scalars to `R` gives the same sheaf of
`R`-modules as restricting the scalars first and then sheafifying.

Both sides have the sheafification of the underlying presheaf of abelian groups for their
sections, so the comparison map is the identity there; what has to be checked is that it is
`R`-linear, which is `sheafify_smul_restrictScalars`. -/
noncomputable def restrictScalarsSheafificationIso :
    (_root_.SheafOfModules.restrictScalars.{v} α).obj
        ((PresheafOfModules.sheafification (𝟙 R'.obj)).obj P) ≅
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars α.hom).obj P) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _)
    (fun X r m => (sheafify_smul_restrictScalars α P X r m).symm)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _)
    (fun X r m => sheafify_smul_restrictScalars α P X r m)⟩

end Sheafification

end AlgebraicGeometry.SheafOfModules

end
