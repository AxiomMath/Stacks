module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# Global cohomology along a continuous and cocontinuous equivalence of sites

Let `G : C ⥤ D` be continuous and cocontinuous for topologies `J` and `K` such that restriction
of sheaves along `G` is an equivalence. Then the pullback along `G` takes the constant sheaf to
the constant sheaf, and `H^p(C, g⁻¹ F) ≅ H^p(D, F)` naturally in the abelian sheaf `F` on `D`.

## Main definitions

* `pullbackConstantSheafIso'`: The isomorphism `g_! M_C ≅ M_D` of constant sheaves.
* `sheafCohomologyIsoOfIsEquivalence'`: The natural isomorphism `H^p(C, g⁻¹ F) ≅ H^p(D, F)`,
  constructed on injective resolutions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace Stacks.Cohomology.DenseSubsiteGlobal
universe w v v' u u'
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
variable [(G.sheafPushforwardContinuous A J K).IsEquivalence]

/-- **The lower shriek takes the constant sheaf to the constant sheaf**, `g_! M_C ≅ M_D`, when
restriction is an equivalence, for sites whose morphisms live in independent universes. This
generalizes `pullbackConstantSheafIso`, which asks the two sites to have their morphisms in the
same universe. -/
def pullbackConstantSheafIso' (M : A) :
    (G.sheafPullback A J K).obj ((constantSheaf J A).obj M) ≅ (constantSheaf K A).obj M :=
  (G.sheafPullback A J K).mapIso ((constantSheafRestrictionIso J K G A).app M).symm ≪≫
    asIso ((G.sheafAdjunctionContinuous A J K).counit.app ((constantSheaf K A).obj M))

section
variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]
/-- **The same comparison, read on injective resolutions.**  For every degree `p`,

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on `(D, K)`, under exactly the hypotheses of
`sheafCohomologyIsoOfIsEquivalence`: an equivalence preserves injective objects
(`CategoryTheory.Functor.preservesInjectiveObjects_of_isEquivalence`), which is what
`sheafCohomologyIsoOfIsEquivalence` spends on producing its acyclicity datum instead.

The isomorphism is constructed through
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIso`, hence through
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp` on the globally chosen injective
resolution, so `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`
identifies it with the edge morphism of the Grothendieck spectral sequence. -/
def sheafCohomologyIsoOfIsEquivalence' (p : ℕ) :
    G.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v', u} K p :=
  Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIso J K G
    (pullbackConstantSheafIso' J K G AddCommGrpCat.{w} (AddCommGrpCat.of (ULift.{w} ℤ))) p

end
end Stacks.Cohomology.DenseSubsiteGlobal
end
