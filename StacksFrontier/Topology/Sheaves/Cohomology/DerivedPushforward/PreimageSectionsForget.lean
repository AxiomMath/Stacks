module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# Derived sections over the preimage of the whole space, with the scalars forgotten

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Derived sections over `f⁻¹(Y) = X`,
`RΓ(f⁻¹ Y, -) : D(𝒪_X) ⥤ D(Γ(Y, 𝒪_Y))`
(`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤`), is the functor through
which [Stacks, Tag 0D5W] compares cohomology on `X` with cohomology on `Y`.  This file identifies
it, once the `Γ(Y, 𝒪_Y)`-action is forgotten, with the abelian-group-valued derived global
sections of the ringed site of `X`
(`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections`), the functor in which the
identifications of [Stacks, Tag 08DK] and [Stacks, Tag 08DQ] are stated, and records the same
identification in degree zero.

## Main definitions

* `Stacks.Cohomology.PreimageSectionsForget.preimageSectionsForgetIso`: the underived
  comparison, sections over `f⁻¹ ⊤` with the scalars forgotten are the global sections of the
  ringed site.
* `Stacks.Cohomology.PreimageSectionsForget.derivedPreimageSectionsForgetIso`: the derived
  comparison.
* `Stacks.Cohomology.PreimageSectionsForget.homologyZeroForgetNatIso`: the comparison in degree
  zero, naturally in the object of `D(𝒪_X)`.

## Implementation notes

Both sides are total right derived functors of functors on `K(𝒪_X)` which agree on the nose
after forgetting the scalars, so the comparison is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedLinearSectionsForgetIso`, exactly as for
the `A`-linear global sections of a scheme over `Spec A` in
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.Cohomology.PreimageSectionsForget

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `Γ(Y, 𝒪_Y)` is a commutative ring. -/
instance commRingGlobalSections :
    CommRing ↑((structureSheafRing Y).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing ↑(Y.presheaf.obj (op ⊤)))

/-- **The underived comparison**: sections over `f⁻¹ ⊤` of a sheaf of `𝒪_X`-modules, as a
`Γ(Y, 𝒪_Y)`-module with its scalars forgotten, are the global sections of the ringed site of
`X`. -/
def preimageSectionsForgetIso :
    Stacks.Cohomology.DerivedSectionsLeray.preimageSections f ⊤ ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) AddCommGrpCat.{u} ≅
      moduleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  Stacks.Cohomology.ModuleComparison.evaluationCompForgetIso
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O) ⊤ ≪≫
    Functor.isoWhiskerLeft
      (_root_.SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.abelianGlobalSectionsTopIso X.sheaf).symm

/-- **Derived sections over `f⁻¹ ⊤`, with the scalars forgotten, are the derived global sections
of the ringed site of `X`.** -/
def derivedPreimageSectionsForgetIso :
    Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤ ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory ≅
      derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  @Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedLinearSectionsForgetIso
    (Stacks.SheafOfModules.ringedSite X.sheaf) _ _
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSections f ⊤)
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive f ⊤)
    (preimageSectionsForgetIso f)

/-- **The comparison in degree zero, naturally in the object of `D(𝒪_X)`**: the degree-zero
cohomology `Γ(Y, 𝒪_Y)`-module of `RΓ(f⁻¹ ⊤, -)`, with its scalars forgotten, is the degree-zero
hypercohomology group of the ringed site of `X`. -/
def homologyZeroForgetNatIso :
    Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) 0 ⋙
        forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) AddCommGrpCat.{u} ≅
      derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 :=
  Functor.isoWhiskerLeft (Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f ⊤)
      (Stacks.Homology.derivedHomologyIso
        (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op ⊤))) AddCommGrpCat.{u})
        0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedPreimageSectionsForgetIso f)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)

end Stacks.Cohomology.PreimageSectionsForget

end
