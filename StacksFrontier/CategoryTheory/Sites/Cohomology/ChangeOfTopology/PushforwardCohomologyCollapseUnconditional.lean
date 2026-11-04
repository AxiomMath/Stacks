module
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmallUnconditional

/-!
# PushforwardCohomologyCollapseUnconditional

Stronger forms of declarations of
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built
on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.BiggerSite

universe v u u'

noncomputable section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).Additive]
  [PreservesFiniteLimits (u.sheafPushforwardContinuous AddCommGrpCat.{v} J K)]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).PreservesInjectiveObjects]

section Collapse

variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{v})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{v})]

end Collapse

section Cohomology

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{v})]

/-- **`sheafCohomologyPushforwardIso` is natural in the sheaf**, for a morphism between two
sheaves whose higher direct images vanish in the degrees `1, …, i`. Each of its factors is a
component of a natural transformation of functors on abelian sheaves: the identifications of
sheaf cohomology with right-derived sections
(`FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_hom_naturality`), the edge morphism,
and the derived identity `sheafPushforwardContinuousCompSheafSectionsIso`. -/
theorem sheafCohomologyPushforwardIso_hom_naturality {F G : Sheaf K AddCommGrpCat.{v}}
    (ψ : F ⟶ G) (T : C) (i : ℕ)
    (hF : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).rightDerived q).obj F))
    (hG : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).rightDerived q).obj G)) :
    ((Sheaf.cohomologyPresheafFunctor J i).map
        ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map ψ)).app (op T) ≫
        (sheafCohomologyPushforwardIso J K u G T i hG).hom =
      (sheafCohomologyPushforwardIso J K u F T i hF).hom ≫
        ((Sheaf.cohomologyPresheafFunctor K i).map ψ).app (op (u.obj T)) := by
  have hedge := (RightDerivedEdge.edge (u.sheafPushforwardContinuous AddCommGrpCat.{v} J K)
    ((sheafSections J AddCommGrpCat.{v}).obj (op T)) i).naturality ψ
  have hiso := (Functor.rightDerivedIsoOfNatIso
    (sheafPushforwardContinuousCompSheafSectionsIso J K u AddCommGrpCat.{v} T) i).hom.naturality ψ
  dsimp only [Functor.comp_map] at hedge
  simp only [sheafCohomologyPushforwardIso, rightDerivedSectionsCollapseIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, RightDerivedEdgeIso.edgeAppIso_hom, Iso.app_hom]
  rw [reassoc_of% (FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_hom_naturality J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map ψ) i T),
    reassoc_of% hedge, reassoc_of% hiso,
    FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections_inv_naturality K ψ i (u.obj T)]

end Cohomology

section EssentiallySmall

variable [EssentiallySmall.{v} C] [EssentiallySmall.{v} D]

attribute [local instance] FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  FreeYonedaUnivLE.hasExt_essentiallySmallSite

end EssentiallySmall

end

end Stacks.Cohomology.BiggerSite

end
