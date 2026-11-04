module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcDirectImageAcyclic
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcSmallCohomology

/-!
# The higher direct images of `a_X^{-1}F` along the comparison `a_X : Sh(LC_qc/X) → Sh(X)`

Let `X` be an object of the quasi-compact site `LC_qc` of Stacks 09X2 and let
`a_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism of topoi of Section 09WY, the bottom
horizontal arrow of the diagram of Stacks 0DAF. The proof of Stacks 0D91 shows that for an abelian
sheaf `F` on `X`

`a_{X,*} a_X^{-1} F = F` and `R^q a_{X,*} a_X^{-1} F = 0` for `q > 0`.

This file proves these statements on the small model of `LC_qc`, for abelian sheaves with values
in the universe of the spaces, where the direct image of `a_X` is restriction along `W ↦ W/X`.

## Main results

* `Stacks.Topology.Simplicial.isZero_rightDerived_qcSmallOpensPushforward`: for every abelian
  sheaf `F` on `X` and `q > 0`, `R^q a_{X,*} a_X^{-1} F = 0` on the small model.
* `Stacks.Topology.Simplicial.isIso_qcSmallBottomAbelianAdjunction_unit`: the unit
  `F ⟶ a_{X,*} a_X^{-1} F` is an isomorphism (Stacks 09X3).

## References

* [Stacks Project, Tag 0D91](https://stacks.math.columbia.edu/tag/0D91)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 09X4](https://stacks.math.columbia.edu/tag/09X4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.UniverseLift Stacks.Topos.AbelianPushforward

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- Stacks 09X3 on the small model, for abelian sheaves: the unit `F ⟶ a_{X,*} a_X^{-1} F` of the
abelian adjunction of the bottom horizontal arrow, with its direct image read as restriction along
`W ↦ W/X`, is an isomorphism. -/
instance isIso_qcSmallBottomAbelianAdjunction_unit :
    haveI := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u} S X
    IsIso (abelianInverseImageAdjRestriction (qcSmallOpensFunctor S X)
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
      (qcSmallBottomMorphism S X) (qcSmallBottomPushforwardIso S X)).unit := by
  have := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u} S X
  have : IsIso (qcSmallBottomMorphism S X).adj.unit :=
    isIso_qcSmallBottomMorphismOfSize_adj_unit.{u, w, u} S X
  have : ∀ F, IsIso ((abelianInverseImageAdjRestriction (qcSmallOpensFunctor S X)
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
      (qcSmallBottomMorphism S X) (qcSmallBottomPushforwardIso S X)).unit.app F) := fun F =>
    isIso_abelianInverseImageAdjRestriction_unit_app (qcSmallOpensFunctor S X)
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
      (qcSmallBottomMorphism S X) (qcSmallBottomPushforwardIso S X) inferInstance F
  exact NatIso.isIso_of_isIso_app _

section BigUniverse


/-- The vanishing of Stacks 0D91 on the small model, in the universe above that of the spaces:
for an abelian sheaf `F` on `X` with values in `AddCommGrpCat.{u + 1}` and `q > 0`,
`R^q a_{X,*} a_X^{-1} F = 0`. -/
theorem isZero_rightDerived_qcSmallOpensPushforward_succ
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u + 1}) (q : ℕ)
    (hq : 0 < q) :
    IsZero ((((qcSmallOpensFunctor S X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).rightDerived q).obj
        ((Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X)).obj F)) := by
  let E := S.qcSite.smallOverSheafEquiv X AddCommGrpCat.{u + 1}
  have : HasSheafify (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u + 1} :=
    hasSheafify_opens_succ S X
  have : HasSheafify (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{u + 1} :=
    hasSheafify_qcTopology_over_succ S X
  have := qcTopologicalAbelianDirectImage_additive.{u, w, 0} S X
  have := qcTopologicalAbelianDirectImage_preservesFiniteLimits.{u, w, 0} S X
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hbase := isZero_rightDerived_qcTopologicalAbelianDirectImage.{u, w, 0} S X F q hq
  have e₁ := (Functor.rightDerivedIsoOfSquare E.inverse
    ((qcSmallOpensFunctor S X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X))
    (qcTopologicalAbelianDirectImage.{u, w, 0} S X) (𝟭 _)
    (Functor.rightUnitor _ ≪≫ (smallOverInverseCompDirectImageIso S X).symm) q).app
      ((Sites.abelianInverseImage (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X)).obj F)
  have e₂ : E.inverse.obj ((Sites.abelianInverseImage
      (qcSmallBottomMorphismOfSize.{u, w, u + 1} S X)).obj F) ≅
        (qcTopologicalAbelianInverseImage.{u, w, 0} S X).obj F :=
    E.inverse.mapIso ((smallAbelianInverseImageIsoLarge S X).app F) ≪≫ E.unitIso.symm.app _
  exact hbase.of_iso
    (e₁ ≪≫ ((qcTopologicalAbelianDirectImage.{u, w, 0} S X).rightDerived q).mapIso e₂)

end BigUniverse

/-- The vanishing of Stacks 0D91 on the small model of `LC_qc`: for an abelian sheaf `F` on
the space underlying `X`, with values in the universe of the spaces, and `q > 0`,
`R^q a_{X,*} a_X^{-1} F = 0`, where `a_X : Sh((LC_qc)_{small}/X) → Sh(X)` is the bottom
horizontal arrow of the diagram of Stacks 0DAF, whose direct image is restriction along
`W ↦ W/X`. -/
theorem isZero_rightDerived_qcSmallOpensPushforward
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero ((((qcSmallOpensFunctor S X).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).rightDerived q).obj
        ((Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F)) := by
  let L := uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X.obj.obj)
  have e₁ := (rightDerivedSheafPushforwardContinuousULiftIso.{u + 1, u}
    (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
    (qcSmallOpensFunctor S X) q).app
      ((Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F)
  have e₂ := ((smallAbelianInverseImageULiftIso S X).app F).symm
  have hbig := isZero_rightDerived_qcSmallOpensPushforward_succ S X (L.obj F) q hq
  have hL : IsZero (L.obj ((((qcSmallOpensFunctor S X).sheafPushforwardContinuous
      AddCommGrpCat.{u} (Opens.grothendieckTopology X.obj.obj)
      (S.qcSite.smallOverTopology X)).rightDerived q).obj
        ((Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F))) :=
    hbig.of_iso (e₁ ≪≫ (((qcSmallOpensFunctor S X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.obj.obj)
      (S.qcSite.smallOverTopology X)).rightDerived q).mapIso e₂)
  rw [IsZero.iff_id_eq_zero] at hL ⊢
  exact L.map_injective (by rwa [L.map_id, L.map_zero])

end Stacks.Topology.Simplicial

end
