module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughAffineObjects
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.AlgebraicGeometry.Modules.ExactOnAffineOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps

/-!
# The derived direct image `Rε_*` of the small étale site

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7.  Its direct image `ε_*` on modules is restriction along the inclusion of the small
Zariski site, `AlgebraicGeometry.SmallEtale.restrictModule`, right adjoint to the
associated-module functor `ε^*`.  This file constructs the unbounded derived direct image

`Rε_* : D(S_étale, 𝒪) ⥤ D(𝒪_S)`

from K-injective resolutions, shows that it is right adjoint to the functor `ε^*` induces on
unbounded derived categories, and computes its cohomology sheaves on complexes with
quasi-coherent cohomology: for such an `E`,

`H^q(Rε_* E) = ε_* H^q(E)`.

That is the step of the proof of Stacks 071Q which passes through Stacks 03DW, 01XB and 0BKZ.
Its two inputs are the acyclicity of a quasi-coherent module on an affine object of the small
étale site, `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isAffine`, and
Stacks 0BKZ itself,
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ε^*` and `ε_*` on sheaves of modules -/

/-- `ε^*` is additive, being the pullback of sheaves of modules along a morphism of ringed sites,
hence a left adjoint of an additive functor. -/
instance additive_associatedModuleOfSheaf : (associatedModuleOfSheaf B S hS).Additive :=
  SheafOfModules.pullback_additive (structureMap B S hS)

/-- `ε^*` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_associatedModuleOfSheaf :
    PreservesFiniteColimits (associatedModuleOfSheaf B S hS) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_associatedModuleOfSheaf B S hS _⟩

/-- `ε_*`, the restriction of a sheaf of modules on the small étale site of `S` to the small
Zariski site, retyped with target `SheafOfModules.{u} S.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules`, the source of
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`. -/
abbrev restrictModuleOfSheaf :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤ SheafOfModules.{u} S.ringCatSheaf :=
  restrictModule B S hS

/-- `ε^* ⊣ ε_*`, at the retypings `associatedModuleOfSheaf` and `restrictModuleOfSheaf`. -/
def associatedModuleOfSheafAdjunction :
    associatedModuleOfSheaf B S hS ⊣ restrictModuleOfSheaf B S hS :=
  associatedModuleAdjunction B S hS

/-- `ε_*` is additive. -/
instance additive_restrictModuleOfSheaf : (restrictModuleOfSheaf B S hS).Additive :=
  (associatedModuleOfSheafAdjunction B S hS).right_adjoint_additive

/-- `ε_*` is left exact, being a right adjoint. -/
instance preservesFiniteLimits_restrictModuleOfSheaf :
    PreservesFiniteLimits (restrictModuleOfSheaf B S hS) :=
  have := (associatedModuleOfSheafAdjunction B S hS).rightAdjoint_preservesLimits
  inferInstance

/-- Every complex of `𝒪`-modules on the small étale site of `S` admits a quasi-isomorphism into a
K-injective complex: these modules form a Grothendieck abelian category. -/
theorem exists_quasiIso_isKInjective
    (K : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance, inferInstance⟩

/-! ### `ε_*` on the cohomology of a K-injective complex -/

open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison in
/-- **`ε_*` commutes with the cohomology of a K-injective complex with quasi-coherent cohomology
sheaves**: for such a complex `I` of `𝒪`-modules on the small étale site of `S`, the comparison
`H^q(ε_* I) ⟶ ε_* H^q(I)` is an isomorphism.

Over an affine open `U` of `S`, the object `U` of the small étale site is affine, so the
cohomology sheaves of `I` have no higher cohomology over it (Stacks 03DW and 01XB,
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isAffine`), and Stacks 0BKZ makes
`I^{q-1}(U) ⟶ Z^q(I)(U) ⟶ H^q(I)(U) ⟶ 0` exact.  These are the sections over `U` of
`ε_*` applied to the cokernel presentation of `H^q(I)`, and the affine opens form a basis of
`S`, so that presentation stays a cokernel presentation after `ε_*`. -/
theorem isIso_homologyComparison_restrictModuleOfSheaf
    (I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ m, (I.homology m).IsQuasicoherentOnSite) (q : ℤ) :
    IsIso (homologyComparison (restrictModuleOfSheaf B S hS) I q) := by
  obtain ⟨hex, hepi⟩ := Scheme.exact_and_epi_of_isAffineOpen.{u} (X := S)
    (cyclesHomologyShortComplex (restrictModuleOfSheaf B S hS) I q) (fun U hU => by
      have hU' : AlgebraicGeometry.IsAffine
          ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj U)) := hU
      exact Stacks.Cohomology.HypercohomologyEdge.exact_and_epi_sections_of_acyclic_cover
        (structureSheaf B S hS) I hI
        (fun V => AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V))
        (hasEnoughObjects_isAffine B S hS)
        (fun V hV p hp m => isZero_rightDerived_evaluation_of_isAffine B S hS _ (hqc m) V hV p hp)
        hU' q)
  exact isIso_homologyComparison_of_exact_of_epi _ I q hex hepi

/-! ### `Rε_*` -/

section Derived

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- Degreewise `ε_*`, followed by localization to the derived category. -/
abbrev restrictModuleToDerived :
    HomotopyCategory (SheafOfModules.{u} (structureSheaf B S hS)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) :=
  (restrictModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image pointwise. -/
instance restrictModuleToDerived_hasPointwiseRightDerivedFunctor :
    (restrictModuleToDerived B S hS).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B S hS))
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0} (restrictModuleToDerived B S hS) (exists_quasiIso_isKInjective B S hS)).1

/-- **`Rε_*`**, the unbounded derived direct image along `ε : S_étale ⟶ S_Zar`: the total right
derived functor of degreewise `ε_*`. -/
abbrev derivedRestrictModule :
    DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)) ⥤
      DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) :=
  (restrictModuleToDerived B S hS).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B S hS)) (ComplexShape.up ℤ))

/-- The canonical comparison `ε_* K ⟶ Rε_* K`. -/
abbrev derivedRestrictModuleUnit :
    restrictModuleToDerived B S hS ⟶ DerivedCategory.Qh ⋙ derivedRestrictModule B S hS :=
  (restrictModuleToDerived B S hS).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B S hS)) (ComplexShape.up ℤ))

/-- A K-injective complex computes `Rε_*`. -/
theorem isIso_derivedRestrictModuleUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedRestrictModuleUnit B S hS).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (restrictModuleToDerived B S hS) (exists_quasiIso_isKInjective B S hS)).2
    DerivedCategory.Qh (derivedRestrictModule B S hS) (derivedRestrictModuleUnit B S hS) I hI

/-- **`ε^* ⊣ Rε_*` on unbounded derived categories**, the adjunction induced by `ε^* ⊣ ε_*`,
`ε^*` being exact (Stacks 08H8). -/
def derivedAssociatedModuleAdjunction :
    (associatedModuleOfSheaf B S hS).mapDerivedCategory ⊣ derivedRestrictModule B S hS :=
  Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
    (associatedModuleOfSheafAdjunction B S hS) (derivedRestrictModule B S hS)
    (derivedRestrictModuleUnit B S hS) (exists_quasiIso_isKInjective B S hS)

end Derived

end AlgebraicGeometry.SmallEtale

end
