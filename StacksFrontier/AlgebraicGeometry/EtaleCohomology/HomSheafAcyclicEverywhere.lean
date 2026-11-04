module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianAcyclicModuleAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveSheafSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicComposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct

/-!
# `Hom_R(N, I)` of an injective sheaf is acyclic everywhere

Let `I` be an injective sheaf of `R`-modules on the small étale site of a scheme `X` and `N` an
`(R, S)`-bimodule. The sheaf `Hom_R(N, I)` of `S`-modules, computed sectionwise, is acyclic for
the sections over every étale `X`-scheme `W`: the sections over `W` are the global sections of the
restriction to `W`, restriction is exact and preserves injectives, and the restriction of
`Hom_R(N, I)` is `Hom_R(N, -)` of the restriction of `I`, which is acyclic for global sections by
`Stacks.EtaleCohomology.rightAcyclic_bimoduleHom_of_injective`. Hence `Hom_R(N, I)` is acyclic for
every direct image.

In Step 7 of the proof of [Stacks, Tag 03UG], `Hom_{A[G]}(M^*, I^•)` for an injective resolution
`I^•` therefore computes `RΓ(X_k̄, Hom_{A[G]}(M^*, -))` together with its Frobenius action.

## Main definitions

* `Stacks.EtaleCohomology.sheafSectionsIsoRestrictionGlobalSections`: sections over `W` are global
  sections of the restriction to `W`.

## Main results

* `Stacks.EtaleCohomology.isAcyclicEverywhere_bimoduleHom_of_injective`: `Hom_R(N, I)` is acyclic
  for the sections over every étale `X`-scheme.
* `Stacks.EtaleCohomology.rightAcyclic_directImage_bimoduleHom_of_injective`: `Hom_R(N, I)` is
  acyclic for every direct image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u r

namespace Stacks.EtaleCohomology

/-- **Sections over an étale `X`-scheme `W` are the global sections of the restriction to `W`.** -/
def sheafSectionsIsoRestrictionGlobalSections (Λ : Type r) [Ring Λ] {X : Scheme.{u}}
    (W : X.Etale) :
    (sheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj (op W) ≅
      etaleModuleRestriction.{u, r} Λ W.hom ⋙ etaleModuleGlobalSections.{u, r} Λ W.left :=
  (NatIso.ofComponents (fun F => F.val.mapIso (smallEtaleComposeIdIso W).symm.op)
      (fun φ => (φ.hom.naturality (smallEtaleComposeIdIso W).inv.op).symm) :
    (sheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj (op W) ≅
      etaleModuleRestriction.{u, r} Λ W.hom ⋙
        (sheafSections W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 W.left)))) ≪≫
    Functor.isoWhiskerLeft (etaleModuleRestriction.{u, r} Λ W.hom)
      (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
        (etaleMkIdIsTerminal W.left)).symm

/-- Restriction of étale sheaves of modules along an étale morphism preserves injective objects. -/
instance etaleModuleRestriction_preservesInjectiveObjects (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleRestriction.{u, r} Λ j).PreservesInjectiveObjects :=
  ⟨fun {I} _ => injective_etaleModuleRestriction Λ j I⟩

variable {R S : Type} [Ring R] [Ring S] (N : Type (u + 1)) [AddCommGroup N] [Module R N]
  [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N] {X : Scheme.{u}}

/-- **`Hom_R(N, I)` of an injective sheaf of `R`-modules is acyclic for the sections over every
étale `X`-scheme.** -/
theorem isAcyclicEverywhere_bimoduleHom_of_injective (I : EtaleModules.{u, 0} R X) [Injective I] :
    IsAcyclicEverywhere
      ((sheafCompose X.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I) := by
  intro W
  have hI := injective_etaleModuleRestriction R W.hom I
  have h : (etaleModuleGlobalSections.{u, 0} S W.left).rightAcyclic
      ((etaleModuleRestriction.{u, 0} S W.hom).obj
        ((sheafCompose X.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I)) :=
    rightAcyclic_bimoduleHom_of_injective N ((etaleModuleRestriction.{u, 0} R W.hom).obj I)
  have h' := Functor.rightAcyclic_comp_of_exact_of_preservesInjectiveObjects
    (etaleModuleRestriction.{u, 0} S W.hom) (etaleModuleGlobalSections.{u, 0} S W.left) _ h
  exact Functor.rightAcyclic_of_iso (sheafSectionsIsoRestrictionGlobalSections S W).symm _ h'

/-- **`Hom_R(N, I)` of an injective sheaf of `R`-modules is acyclic for every direct image.** -/
theorem rightAcyclic_directImage_bimoduleHom_of_injective {Y : Scheme.{u}} (f : X ⟶ Y)
    (I : EtaleModules.{u, 0} R X) [Injective I] :
    (etaleModuleDirectImage.{u, 0} S f).rightAcyclic
      ((sheafCompose X.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I) :=
  rightAcyclic_directImage_of_isAcyclicEverywhere f _
    (isAcyclicEverywhere_bimoduleHom_of_injective N I)

/-- **`Hom_R(N, I)` of an injective sheaf of `R`-modules is acyclic for global sections.** -/
theorem rightAcyclic_globalSections_bimoduleHom_of_injective (I : EtaleModules.{u, 0} R X)
    [Injective I] :
    (etaleModuleGlobalSections.{u, 0} S X).rightAcyclic
      ((sheafCompose X.smallEtaleTopology (ModuleCat.BimoduleHom.functor R S N)).obj I) :=
  rightAcyclic_bimoduleHom_of_injective N I

end Stacks.EtaleCohomology

end
