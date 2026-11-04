module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting

/-!
# The constant sheaf `Λ_Y` is the structure sheaf of the constant ringed site

Let `Y` be a scheme and `Λ` a commutative ring. The equivalence
`Stacks.EtaleCohomology.etaleModulesEquivalence Λ Y` identifies sheaves of `Λ`-modules on the
small étale site of `Y` with sheaves of modules over the constant ringed site
`Stacks.EtaleCohomology.etaleRingedSite Λ Y`. This file shows that it carries the constant sheaf
`Λ_Y` to the structure sheaf `SheafOfModules.unit` of that ringed site.

Both objects corepresent the same functor, the sections over the terminal object `Y` of the
small étale site read through the equivalence: maps out of `Λ_Y` are the global sections
(the constant sheaf is left adjoint to evaluation at a terminal object), and maps out of the
structure sheaf are the global sections too (`SheafOfModules.unitHomEquiv`), which on a site with
a terminal object are the sections over it. Yoneda then gives the isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedTopSections`: the sections over `Y`, as a functor on
  sheaves of modules over the constant ringed site.
* `Stacks.EtaleCohomology.etaleConstantCorepresentableBy`,
  `Stacks.EtaleCohomology.etaleRingedUnitCorepresentableBy`: the two corepresentations.
* `Stacks.EtaleCohomology.etaleModulesEquivalenceConstantIso`: `e(Λ_Y) ≅ 𝒪`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (Y : Scheme.{u})

/-- The sections over the terminal object `Y` of the small étale site, read on sheaves of modules
over the constant ringed site through `etaleModulesEquivalence`. -/
abbrev etaleRingedTopSections : EtaleRingedModules.{u, r} Λ Y ⥤ Type (max (u + 1) r) :=
  (etaleModulesEquivalence.{u, r} Λ Y).inverse ⋙
    (sheafSections Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
      (op (etaleSiteTerminal Y)) ⋙ forget _

/-- **Maps out of the image of `Λ_Y` are the sections over `Y`.** -/
def etaleConstantCorepresentableBy :
    (etaleRingedTopSections.{u, r} Λ Y).CorepresentableBy
      ((etaleModulesEquivalence.{u, r} Λ Y).functor.obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ Y.smallEtaleTopology)) where
  homEquiv := ((etaleModulesEquivalence.{u, r} Λ Y).toAdjunction.homEquiv _ _).trans
    (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (etaleSiteTerminalIsTerminal Y)).homEquiv _ _).trans
        (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{r, u + 1} Λ _).toEquiv)
  homEquiv_comp g f := by
    simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
    rfl

/-- The terminal object of the small model of the small étale site. -/
def etaleSmallModelTerminalIsTerminal :
    IsTerminal ((AsSmall.equiv : Y.Etale ≌ AsSmall.{max (u + 1) r} Y.Etale).functor.obj
      (etaleSiteTerminal Y)) :=
  (etaleSiteTerminalIsTerminal Y).isTerminalObj _

/-- **Maps out of the structure sheaf of the constant ringed site are the sections over `Y`.** -/
def etaleRingedUnitCorepresentableBy :
    (etaleRingedTopSections.{u, r} Λ Y).CorepresentableBy
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (etaleRingedSite.{u, r} Λ Y).O)) where
  homEquiv {N} := (SheafOfModules.unitHomEquiv N).trans
    (PresheafOfModules.sectionsEquivObjOfIsTerminal N.val
      (etaleSmallModelTerminalIsTerminal.{u, r} Y))
  homEquiv_comp _ _ := rfl

/-- **`etaleModulesEquivalence` carries the constant sheaf `Λ_Y` to the structure sheaf** of the
constant ringed site `etaleRingedSite Λ Y`. -/
def etaleModulesEquivalenceConstantIso :
    (etaleModulesEquivalence.{u, r} Λ Y).functor.obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ Y.smallEtaleTopology) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (etaleRingedSite.{u, r} Λ Y).O) :=
  (etaleConstantCorepresentableBy.{u, r} Λ Y).uniqueUpToIso
    (etaleRingedUnitCorepresentableBy.{u, r} Λ Y)

end Stacks.EtaleCohomology

end
