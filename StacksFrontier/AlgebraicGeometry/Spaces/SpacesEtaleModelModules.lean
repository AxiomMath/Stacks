module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSmallModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# Sheaves of modules on the model of the spaces-étale site

Let `X` be an algebraic space.  The `Type u`-presented model
`AlgebraicGeometry.Space.spacesEtaleModelRingedTopos X` of the ringed spaces-étale site
`(X_{spaces,étale}, 𝒪_X)` contains, through the comparison functor of Stacks 03G1, the model of the
small étale site of `X` as a dense subsite.  On a scheme chart `U ⟶ X` the two structure sheaves
agree: the global functions of the algebraic space represented by `U` are the regular functions on
`U` (`AlgebraicGeometry.Space.globalFunctionsYonedaEquiv`).  So the Comparison Lemma for sheaves of
modules identifies the sheaves of modules on the model with the `𝒪_X`-modules on the small étale
site.

## Main definitions

* `AlgebraicGeometry.Space.comparisonStructureIso`: the global functions of the algebraic space
  represented by an étale chart of `X` are the regular functions on the chart, naturally in the
  chart.
* `AlgebraicGeometry.Space.spacesEtaleModelStructureRestrictionIso` and
  `AlgebraicGeometry.Space.spacesEtaleModelRingRestrictionIso`: the restriction of the structure
  sheaf of the spaces-étale model to the small étale model is the structure sheaf of the small
  étale model.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`: **the equivalence** between the sheaves
  of modules on the spaces-étale model and the `𝒪_X`-modules.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The ring isomorphism at one chart: the shrunk global functions of the algebraic space
represented by an étale chart `V` of `X` are the regular functions on `V`. -/
def comparisonStructureRingEquiv (V : SmallEtale B S hS X.1) :
    (shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X)).obj
        (op ((comparisonFunctor B S hS X).obj V)) ≃+*
      (structurePresheaf B S hS X.1).obj (op V) :=
  (Shrink.ringEquiv _).trans
    (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS X.1).obj V))

/-- **The structure sheaves agree on scheme charts.** Restricted along the comparison functor of
Stacks 03G1, the `u`-small structure presheaf of the spaces-étale site of `X` is the structure
presheaf of the small étale site of `X`: the global functions of the algebraic space represented by
an étale chart are the regular functions on the chart, compatibly with pullback. -/
def comparisonStructureIso :
    (comparisonFunctor B S hS X).op ⋙
        shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X) ≅
      structurePresheaf B S hS X.1 :=
  NatIso.ofComponents (fun V => (comparisonStructureRingEquiv B S hS X V.unop).toCommRingCatIso)
    (fun {V W} g => by
      ext (σ : Shrink.{u} ((SpacesEtale.structurePresheaf B S hS X).obj
        (op ((comparisonFunctor B S hS X).obj V.unop))))
      have h := shrinkCommRingPresheaf_map_apply.{u, u + 1}
        (SpacesEtale.structurePresheaf B S hS X) ((comparisonFunctor B S hS X).op.map g) σ
      change globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS X.1).obj W.unop)
          (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
              (op ((comparisonFunctor B S hS X).obj W.unop))) (((comparisonFunctor B S hS X).op ⋙
            shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X)).map g σ)) =
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g.unop)).appTop.hom
          (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS X.1).obj V.unop)
            (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
              (op ((comparisonFunctor B S hS X).obj V.unop))) σ))
      refine (congrArg (globalFunctionsYonedaEquiv B S hS _) h).trans ?_
      exact globalFunctionsMap_val_of_yoneda_map_comp B S hS
        ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map g.unop)) _
        (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj W.unop))
        (idChart B S hS ((SmallEtale.toOver B S hS X.1).obj V.unop))
        ((SmallEtale.toOver B S hS X.1).map g.unop) (by
          change yoneda.map ((SmallEtale.toOver B S hS X.1).map g.unop) ≫ 𝟙 _ =
            𝟙 _ ≫ yoneda.map ((SmallEtale.toOver B S hS X.1).map g.unop)
          rw [Category.comp_id, Category.id_comp]))

/-- **The structure sheaves of the two models agree.** Restricted along the comparison of the
model of the small étale site of `X` with the model of its spaces-étale site, the structure sheaf
of the latter is the structure sheaf of the former, as sheaves of commutative rings. -/
def spacesEtaleModelStructureRestrictionIso :
    ((spacesEtaleModelComparison B S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)).obj
          (spacesEtaleModelStructureSheaf B S hS X) ≅
      smallEtaleModelStructureSheaf B S hS X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft (smallEtaleModelEquiv B S hS X).inverse.op
      (Functor.isoWhiskerLeft (comparisonFunctor B S hS X).op
          (Functor.isoWhiskerRight (NatIso.op (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso)
            (shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X))) ≪≫
        comparisonStructureIso B S hS X))

/-- `AlgebraicGeometry.Space.spacesEtaleModelStructureRestrictionIso` for the underlying sheaves of
rings, in the form in which the two module categories are indexed. -/
def spacesEtaleModelRingRestrictionIso :
    ringRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
        (spacesEtaleModelComparison B S hS X)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ≅
      ringRestriction (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
        (smallEtaleModelEquiv B S hS X).inverse (structureRingSheaf B S hS X) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (spacesEtaleModelStructureRestrictionIso B S hS X)

/-- **The sheaves of modules on the model of the spaces-étale site of `X` are the `𝒪_X`-modules.**
Restriction to the model of the small étale site (the Comparison Lemma along Stacks 03G1), followed
by the identification of the structure sheaves and the Comparison Lemma for the small étale model.
-/
def spacesEtaleModelModulesEquiv :
    (spacesEtaleModelRingedTopos B S hS X).Modules ≌ Modules.{u, u} B S hS X.1 X.2 :=
  (moduleRestrictionEquivalence.{u} (smallEtaleModelTopology B S hS X.1)
      (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X))).trans
    ((Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (spacesEtaleModelRingRestrictionIso B S hS X)).trans
        (smallEtaleModelModulesEquiv B S hS X).symm)

end AlgebraicGeometry.Space

end
