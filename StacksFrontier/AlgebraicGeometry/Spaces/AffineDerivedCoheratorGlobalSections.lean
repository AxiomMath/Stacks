module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The derived coherator of an affine algebraic space is the associated complex of `RΓ`

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B` and set
`A = Γ(X, 𝒪_X)`. The derived coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` sends an object `E` to
the complex of quasi-coherent `𝒪_X`-modules associated to the object `RΓ(X, E)` of `D(A)`.

## Main definitions

* `AlgebraicGeometry.Space.modulesAbelianSmallEtale`,
  `AlgebraicGeometry.Space.quasicoherentSheavesAbelianSmallEtale`,
  `AlgebraicGeometry.Space.modulesHasDerivedCategorySmallEtale` and
  `AlgebraicGeometry.Space.quasicoherentSheavesHasDerivedCategorySmallEtale`: the abelian
  structures on `Mod(𝒪_X)` and `QCoh(𝒪_X)` at the universe of the schemes, and the models of
  their unbounded derived categories.
* `AlgebraicGeometry.Space.derivedModuleGlobalSectionsSmallEtale` is
  `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, the total right derived functor of `Γ(X, -)` on the whole
  unbounded derived category.
* `AlgebraicGeometry.Space.derivedCoheratorSmallEtale` is `RQ_X`, the total right derived
  functor of a coherator `Q_X`.
* `AlgebraicGeometry.Space.derivedCoheratorIsoAssociatedDerivedGlobalSections`: the isomorphism
  of `RQ_X` with `RΓ(X, -)` followed by a carried associated-module functor; vacuous for a
  representable affine `X` with nontrivial global functions, and not the registration of
  Stacks 08H0 (2), which is
  `AlgebraicGeometry.Space.derivedCoheratorIsoDerivedGlobalSectionsAssociated_of_isAffineSpace`.

## Main results

* `AlgebraicGeometry.Space.additive_assoc_functor`: the associated-module functor is additive.
* `AlgebraicGeometry.Space.additive_coherator`: a coherator is additive.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The abelian structures and the derived-category models at the universe of the schemes -/

/-- The `𝒪_X`-modules on the small étale ringed site of an algebraic space are abelian at the
universe of the schemes. -/
abbrev modulesAbelianSmallEtale : Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- The quasi-coherent `𝒪_X`-modules on an algebraic space are abelian at the universe of the
schemes. -/
abbrev quasicoherentSheavesAbelianSmallEtale :
    Abelian (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  quasicoherentSheaves_abelian_of_closure.{u, u} B S hS F hF

/-- `D(𝒪_X)` with its morphisms at the universe `u` of the schemes, the derived category of a
Grothendieck abelian category. -/
abbrev modulesHasDerivedCategorySmallEtale :
    letI := modulesAbelianSmallEtale B S hS F hF
    HasDerivedCategory.{u} (Modules.{u, u} B S hS F hF) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := isGrothendieckAbelian_modules B S hS F hF
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

/-- `D(QCoh(𝒪_X))` at the standard model. -/
abbrev quasicoherentSheavesHasDerivedCategorySmallEtale :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    HasDerivedCategory.{u + 1} (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  HasDerivedCategory.standard _

/-! ### `RΓ(X, -)` -/

/-- `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, the total right derived functor of global sections of
`𝒪_X`-modules on the whole unbounded derived category. -/
abbrev derivedModuleGlobalSectionsSmallEtale :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := modulesHasDerivedCategorySmallEtale B S hS F hF
    letI := isGrothendieckAbelian_modules B S hS F hF
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS F hF)) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := modulesHasDerivedCategorySmallEtale B S hS F hF
  letI := isGrothendieckAbelian_modules B S hS F hF
  ((moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))

section Affine

variable (assoc : ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS F hF) ≌
      QuasicoherentSheaves.{u, u} B S hS F hF)
    (adjAssoc : assoc.functor ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
        moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF)

include adjAssoc in
/-- The associated-module functor `Mod(A) ⥤ QCoh(𝒪_X)` is additive. -/
theorem additive_assoc_functor :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    assoc.functor.Additive :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  letI : (assoc.functor ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι).Additive :=
      adjAssoc.left_adjoint_additive
  Functor.additive_of_comp_faithful assoc.functor
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι

/-- Deriving `Γ(X, -)` and then taking associated complexes of quasi-coherent modules derives
the composite `Γ(X, -) ⋙ (-)^~`. -/
def derivedGlobalSectionsCompAssociatedIso :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    letI := modulesHasDerivedCategorySmallEtale B S hS F hF
    letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
    letI := additive_assoc_functor B S hS F hF assoc adjAssoc
    letI := isGrothendieckAbelian_modules B S hS F hF
    derivedModuleGlobalSectionsSmallEtale B S hS F hF ⋙
        assoc.functor.mapDerivedCategory ≅
      ((moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF ⋙ assoc.functor).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  letI := modulesHasDerivedCategorySmallEtale B S hS F hF
  letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
  letI := additive_assoc_functor B S hS F hF assoc adjAssoc
  letI := isGrothendieckAbelian_modules B S hS F hF
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF) assoc.functor

section Coherator

variable (Q : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF)
    (adjQ : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ Q)

include adjQ in
/-- A coherator of an algebraic space is additive, being a right adjoint of the additive
inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`. -/
theorem additive_coherator :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    Q.Additive :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  adjQ.right_adjoint_additive

/-- `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))`, the total right derived functor of a coherator `Q_X` on the
whole unbounded derived category. -/
abbrev derivedCoheratorSmallEtale :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    letI := modulesHasDerivedCategorySmallEtale B S hS F hF
    letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
    letI := additive_coherator B S hS F hF Q adjQ
    letI := isGrothendieckAbelian_modules B S hS F hF
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  letI := modulesHasDerivedCategorySmallEtale B S hS F hF
  letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
  letI := additive_coherator B S hS F hF Q adjQ
  letI := isGrothendieckAbelian_modules B S hS F hF
  (Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF)
      (ComplexShape.up ℤ))

/-- Let `X` be an algebraic space, `A = Γ(X, 𝒪_X)`, `Q` a right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, and `assoc : ModuleCat.{u + 1} A ≌ QCoh(𝒪_X)` an equivalence with an
adjunction `assoc.functor ⋙ ι ⊣ Γ(X, -)`.  Then the total right derived functor of `Q` is
naturally isomorphic to `RΓ(X, -)` followed by `assoc.functor` applied termwise.

This is **vacuous** for every representable affine algebraic space with nontrivial ring of
global functions: there no such `assoc` exists
(`AlgebraicGeometry.Space.not_nonempty_equivalence_moduleCat_quasicoherentSheaves_yoneda`),
because `A` lies in `Type (u + 1)` and `ModuleCat.{u + 1} A` is equivalent to no category with
Hom-sets in `Type u`.  It is therefore not a registration of Stacks 08H0 (2); the unconditional
statement is
`AlgebraicGeometry.Space.derivedCoheratorIsoDerivedGlobalSectionsAssociated_of_isAffineSpace`. -/
def derivedCoheratorIsoAssociatedDerivedGlobalSections (hAffine : IsAffineSpace B S hS F) :
    letI := modulesAbelianSmallEtale B S hS F hF
    letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
    letI := modulesHasDerivedCategorySmallEtale B S hS F hF
    letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
    letI := additive_assoc_functor B S hS F hF assoc adjAssoc
    letI := additive_coherator B S hS F hF Q adjQ
    letI := isGrothendieckAbelian_modules B S hS F hF
    derivedCoheratorSmallEtale B S hS F hF Q adjQ ≅
      derivedModuleGlobalSectionsSmallEtale B S hS F hF ⋙ assoc.functor.mapDerivedCategory :=
  letI := modulesAbelianSmallEtale B S hS F hF
  letI := quasicoherentSheavesAbelianSmallEtale B S hS F hF
  letI := modulesHasDerivedCategorySmallEtale B S hS F hF
  letI := quasicoherentSheavesHasDerivedCategorySmallEtale B S hS F hF
  letI := additive_assoc_functor B S hS F hF assoc adjAssoc
  letI := additive_coherator B S hS F hF Q adjQ
  letI := isGrothendieckAbelian_modules B S hS F hF
  have e₀ : Q ≅ moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF ⋙ assoc.functor :=
    coheratorIsoAssociatedGlobalSections B S hS F hF assoc adjAssoc Q adjQ hAffine
  have eHC : Q.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF ⋙
        assoc.functor).mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e₀.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  Functor.rightDerivedNatIso
      ((Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF)
          (ComplexShape.up ℤ)))
      (((moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF ⋙
          assoc.functor).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
      ((Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
      (((moduleGlobalSectionsSmallEtale.{u, u} B S hS F hF ⋙
          assoc.functor).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight eHC DerivedCategory.Qh) ≪≫
    (derivedGlobalSectionsCompAssociatedIso B S hS F hF assoc adjAssoc).symm

end Coherator

end Affine

end AlgebraicGeometry.Space

end
