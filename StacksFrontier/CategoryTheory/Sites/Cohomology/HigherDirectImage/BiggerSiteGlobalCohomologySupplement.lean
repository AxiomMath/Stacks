module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology

/-!
# Global cohomology on a bigger site, for independent universes of morphisms

For a continuous functor `u : C ⥤ D` between sites whose morphisms live in independent universes,
we construct the adjunction `g_! ⊣ g⁻¹` on abelian sheaves, show both functors are additive, and
prove that restriction from `(D, K)` to `(C, J)` does not change global cohomology once `g_!`
carries the constant sheaf on `ℤ` to the constant sheaf on `ℤ`.

## Main definitions

* `lowerShriekAdjunction'`: The adjunction `g_! ⊣ g⁻¹` on abelian sheaves.

## Main results

* `sheafCohomologyIsoOfConstantSheafIso`: An isomorphism `H^p(C, g⁻¹ F) ≅ H^p(D, F)`, natural in
  the abelian sheaf `F` on `(D, K)`, given an isomorphism of `g_!` of the constant sheaf on `ℤ`
  with the constant sheaf on `ℤ`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace Stacks.Cohomology.BiggerSiteGlobal
universe w v v' u
section
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
section
variable [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The adjunction `g_! ⊣ g⁻¹` on abelian sheaves, for sites whose morphisms live in independent
universes. This generalizes `lowerShriekAdjunction`, which asks the two sites to have their
morphisms in the same universe. -/
abbrev lowerShriekAdjunction' :
    lowerShriekAbelian J K u ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K

/-- Restriction of abelian sheaves is additive, for sites whose morphisms live in independent
universes. This generalizes the corresponding instance for sites with morphisms in the same
universe. -/
instance sheafPushforwardContinuous_additive' :
    (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :=
    (lowerShriekAdjunction' J K u).rightAdjoint_preservesLimits
  haveI : HasBinaryProducts (Sheaf K AddCommGrpCat.{w}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf K _)
  Functor.additive_of_preserves_binary_products _

/-- Lower shriek of abelian sheaves is additive, for sites whose morphisms live in independent
universes. This generalizes the corresponding instance for sites with morphisms in the same
universe. -/
instance lowerShriekAbelian_additive' : (lowerShriekAbelian J K u).Additive :=
  (lowerShriekAdjunction' J K u).left_adjoint_additive

variable [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{w})]
  [PreservesFiniteColimits (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K)]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesInjectiveObjects]
/-- **Restriction from a bigger site does not change global cohomology, from the comparison of
constant sheaves.** Suppose `g_!` carries the constant sheaf on `ℤ` of `(C, J)` to the constant
sheaf on `ℤ` of `(D, K)`. Then for every degree `p`

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`.

This is `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso` with the two terminal objects
replaced by the one isomorphism they are a route to: terminality enters that statement only
through `lowerShriekConstantSheafIso`, which produces exactly the datum `e` below.

It is the counterpart of `sheafCohomologyIsoOfConstantSheafIsoOfAcyclic` which keeps preservation
of injective objects by `g⁻¹` rather than weakening it to acyclicity, and the two differ in more
than their hypotheses: this one is built from
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`, hence from Stacks 015Z read on an
injective resolution, so it can be compared with the edge morphism of the Grothendieck spectral
sequence — see
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app` — whereas the acyclic
form is built from δ-functor universality and admits no such comparison. -/
def sheafCohomologyIsoOfConstantSheafIso
    (e : (lowerShriekAbelian J K u).obj ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift.{w} ℤ))) ≅
        (constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ)))
    (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v', u} K p :=
  (Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (lowerShriekAdjunction' J K u) e p).symm

end
end
end Stacks.Cohomology.BiggerSiteGlobal
end
