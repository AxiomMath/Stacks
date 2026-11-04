module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-!
# Forgetting the module structure of a colimit of sheaves of modules

Let `R` be a sheaf of rings on a site `(𝒞, K)`. Forgetting the module structure of a sheaf of
`R`-modules, `SheafOfModules.toSheaf R : Mod(R) ⥤ Ab(𝒞, K)`, preserves colimits of every shape
for which abelian groups have them.

## Main results

* `SheafOfModules.preservesColimitsOfShape_toSheaf`: the underlying abelian sheaf of a colimit
  of sheaves of modules is the colimit of the underlying abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v₂ u₂

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {K : GrothendieckTopology C} (R : Sheaf K RingCat.{w})
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- For a shape `J` for which presheaves
of `R`-modules have colimits, the underlying abelian sheaf of a `J`-indexed colimit of sheaves of
`R`-modules is the colimit of the underlying abelian sheaves. -/
theorem preservesColimitsOfShape_toSheaf {J : Type u₂} [Category.{v₂} J]
    [HasColimitsOfShape J AddCommGrpCat.{w}] :
    PreservesColimitsOfShape J (SheafOfModules.toSheaf.{w} R) := by
  have hcomp : PreservesColimitsOfShape J
      (PresheafOfModules.sheafification (R := R) (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{w} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  have hfull : (SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).Full :=
    (PresheafOfModules.sheafificationAdjunction
      (R := R) (𝟙 R.obj)).fullyFaithfulROfIsIsoCounit.full
  have hfaithful : (SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).Faithful :=
    (PresheafOfModules.sheafificationAdjunction
      (R := R) (𝟙 R.obj)).fullyFaithfulROfIsIsoCounit.faithful
  exact ((PresheafOfModules.sheafificationAdjunction (R := R)
    (𝟙 R.obj)).preservesColimitsOfShape_iff _ J).2 hcomp

end SheafOfModules

end
