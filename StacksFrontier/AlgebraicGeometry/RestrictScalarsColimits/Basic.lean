module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Restriction of scalars along a morphism of sheaves of rings preserves colimits

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`. The restriction of scalars
functor `SheafOfModules.restrictScalars α : SheafOfModules R' ⥤ SheafOfModules R` preserves
colimits and finite limits.

## Main results

* `Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_of_isIso_counit`: if
  `L ⊣ U` is an adjunction whose counit is an isomorphism, the source of `L` has colimits of shape
  `K`, and `L ⋙ G` preserves colimits of shape `K`, then `G` preserves colimits of shape `K`.
* `Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf`: the
  functor `SheafOfModules.toSheaf R`, which forgets the module structure of a sheaf of modules,
  preserves colimits.
* `Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_restrictScalars`
  and its `PreservesColimitsOfSize` and `PreservesFiniteColimits` variants: restriction of
  scalars along a morphism of sheaves of rings preserves colimits.
* `Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteLimits_restrictScalars`:
  restriction of scalars preserves finite limits.
-/

@[expose] public section

universe w' w v v' u u'

open CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.RestrictScalarsColimits

/-! ### Extracting colimit preservation from a reflection -/

section General

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃]

/-- Let `adj : L ⊣ U` be an adjunction whose counit is an isomorphism. If the source of `L` has
colimits of shape `K` and `L ⋙ G` preserves them, then `G` preserves them. -/
lemma preservesColimitsOfShape_of_isIso_counit {L : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} (adj : L ⊣ U)
    [IsIso adj.counit] (G : C₂ ⥤ C₃) (K : Type w) [Category.{w'} K] [HasColimitsOfShape K C₁]
    [PreservesColimitsOfShape K (L ⋙ G)] :
    PreservesColimitsOfShape K G where
  preservesColimit {F} := by
    have := adj.isLeftAdjoint
    have e : (F ⋙ U) ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit)
    have : PreservesColimit ((F ⋙ U) ⋙ L) G :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (F ⋙ U)))
        (isColimitOfPreserves (L ⋙ G) (colimit.isColimit (F ⋙ U)))
    exact preservesColimit_of_iso_diagram G e

end General

section Sheaf

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-! ### Forgetting the module structure preserves colimits -/

/-- The functor `SheafOfModules.toSheaf R`, which sends a sheaf of modules to its underlying
sheaf of abelian groups, preserves colimits of shape `K`. -/
lemma preservesColimitsOfShape_toSheaf (R : Sheaf J RingCat.{u}) (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v} R) := by
  have : PreservesColimitsOfShape K
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{v} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm
  exact preservesColimitsOfShape_of_isIso_counit
    (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)) _ K

/-! ### Restriction of scalars preserves colimits -/

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

omit [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- Restriction of scalars does not change the underlying sheaf of abelian groups. -/
lemma restrictScalars_comp_toSheaf :
    SheafOfModules.restrictScalars.{v} α ⋙ SheafOfModules.toSheaf.{v} R =
      SheafOfModules.toSheaf.{v} R' :=
  rfl

/-- If `α : R ⟶ R'` is a morphism of sheaves of rings, the functor
`SheafOfModules.restrictScalars α : SheafOfModules R' ⥤ SheafOfModules R` preserves colimits of
shape `K`. -/
instance preservesColimitsOfShape_restrictScalars (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (SheafOfModules.restrictScalars.{v} α) := by
  have hR : ReflectsColimitsOfShape K (SheafOfModules.toSheaf.{v} R) :=
    have := preservesColimitsOfShape_toSheaf.{w', w} R K
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hcomp : PreservesColimitsOfShape K
      (SheafOfModules.restrictScalars.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
    restrictScalars_comp_toSheaf.{v} α ▸ preservesColimitsOfShape_toSheaf.{w', w} R' K
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{v} R)

/-- Restriction of scalars along a morphism of sheaves of rings preserves colimits of size
`(w', w)`. -/
instance preservesColimitsOfSize_restrictScalars
    [HasColimitsOfSize.{w', w} AddCommGrpCat.{v}] :
    PreservesColimitsOfSize.{w', w} (SheafOfModules.restrictScalars.{v} α) where

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite colimits. -/
instance preservesFiniteColimits_restrictScalars :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{v} α) where

/-! ### Restriction of scalars preserves finite limits -/

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits. -/
instance preservesFiniteLimits_restrictScalars :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{v} α) := by
  have hR : ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  have hcomp : PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
    restrictScalars_comp_toSheaf.{v} α ▸
      (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R'))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{v} R)

end Sheaf

end Stacks.AlgebraicGeometry.RestrictScalarsColimits

end
