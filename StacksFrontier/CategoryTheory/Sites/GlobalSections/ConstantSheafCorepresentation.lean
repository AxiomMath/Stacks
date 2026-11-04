module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Global sections of abelian sheaves on a site of any size are corepresented

`ModuleSheafCohomology.globalSectionsRepresentation` corepresents the global sections of abelian
sheaves on a small site by the constant sheaf on `ℤ`. Only the adjunction between constant
sheaves and global sections enters, so the same holds for a site whose objects form a type of any
universe, with coefficients in that universe.

## Main definitions

* `ModuleSheafCohomology.globalSectionsIsoCoyonedaConstantSheaf`: global sections of abelian
  sheaves on an arbitrary site are corepresented by the constant sheaf on `ℤ`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe v u'

namespace ModuleSheafCohomology

variable {D : Type u'} [Category.{v} D] (K : GrothendieckTopology D) [HasSheafify K Ab.{u'}]
  [HasGlobalSectionsFunctor K Ab.{u'}]

/-- **Global sections of abelian sheaves are corepresented by the constant sheaf on `ℤ`**, on a
site whose objects form a type of any universe, with coefficients in that universe. -/
def globalSectionsIsoCoyonedaConstantSheaf :
    Sheaf.Γ K Ab.{u'} ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf K Ab.{u'}).obj (AddCommGrpCat.of (ULift.{u'} ℤ)))) := by
  refine (NatIso.ofComponents (fun F =>
    (((constantSheafΓAdj K Ab.{u'}).homAddEquiv (AddCommGrpCat.of (ULift.{u'} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) ?_).symm
  intro F G f
  ext x
  change ((constantSheaf K Ab.{u'}).obj (AddCommGrpCat.of (ULift.{u'} ℤ)) ⟶ F) at x
  change ((constantSheafΓAdj K Ab.{u'}).homEquiv _ G (x ≫ f)) (ULift.up (1 : ℤ)) =
    ((Sheaf.Γ K Ab.{u'}).map f)
      (((constantSheafΓAdj K Ab.{u'}).homEquiv _ F x) (ULift.up (1 : ℤ)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

end ModuleSheafCohomology

end
