module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelModules

/-!
# Étale pullback on the spaces-étale model and on the small étale site

Let `j : X ⟶ Y` be an étale morphism of algebraic spaces.  Restriction of modules along
postcomposition with `j` on the models of the spaces-étale sites corresponds, under the
equivalences `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of Stacks 03G1, to the étale
pullback `AlgebraicGeometry.Space.etaleModulePullback j` of `𝒪`-modules on the small étale sites.

## Main results

* `SheafOfModules.pushforwardCompRestrictScalarsIso`: restriction of scalars commutes with the
  pushforward of sheaves of modules along compatible maps of sheaves of rings.
* `AlgebraicGeometry.Space.spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso`: the
  structure maps of postcomposition on the two models agree under the identification of the
  structure sheaves.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivPostcompIso`: **the comparison**
  `e_X ∘ (restriction along postcomposition with j) ≅ j^* ∘ e_Y`.

## Implementation notes

The comparison is assembled from four squares: restriction to the small étale models commutes with
postcomposition on the spaces-étale models (Step A) and on the small étale sites (Step B), both
being restrictions along functors related by unit isomorphisms; restriction of scalars along the
identifications of the structure sheaves commutes with restriction along postcomposition (Step C),
whose content is the agreement of the two structure maps, checked on sections; and the inverse of
the Comparison Lemma intertwines the two restrictions along postcomposition (Step D).

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

/-- Postcomposition with an étale morphism, on the models of the small étale sites. -/
abbrev smallEtaleModelPostcomp :
    SmallModel.{u} (SmallEtale B S hS X.1) ⥤ SmallModel.{u} (SmallEtale B S hS Y.1) :=
  (smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj ⋙
    (smallEtaleModelEquiv B S hS Y).functor

/-- The comparison of Stacks 03G1 on the models carries postcomposition on the small étale model to
postcomposition on the spaces-étale model. -/
def spacesEtaleModelComparisonPostcompIso :
    spacesEtaleModelComparison B S hS X ⋙ smallModelPostcomp B S hS j hj ≅
      smallEtaleModelPostcomp B S hS j hj ⋙ spacesEtaleModelComparison B S hS Y :=
  Functor.isoWhiskerLeft ((smallEtaleModelEquiv B S hS X).inverse ⋙ comparisonFunctor B S hS X)
      (Functor.isoWhiskerRight (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.symm
        (spacesEtalePostcomp B S hS j hj ⋙ (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor)) ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj)
      (Functor.isoWhiskerRight (smallEtaleModelEquiv B S hS Y).unitIso
        (comparisonFunctor B S hS Y ⋙ (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor))

/-- The comparison of the small étale site with its model carries postcomposition on the model to
postcomposition on the site. -/
def smallEtaleModelInversePostcompIso :
    (smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj ≅
      smallEtaleModelPostcomp B S hS j hj ⋙ (smallEtaleModelEquiv B S hS Y).inverse :=
  Functor.isoWhiskerLeft ((smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj)
    (smallEtaleModelEquiv B S hS Y).unitIso

/-- Postcomposition with an étale morphism on the small étale models is continuous. -/
instance isContinuous_smallEtaleModelPostcomp :
    (smallEtaleModelPostcomp B S hS j hj).IsContinuous (smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelTopology B S hS Y.1) :=
  have : (smallEtalePostcomp B S hS j hj ⋙ (smallEtaleModelEquiv B S hS Y).functor).IsContinuous
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS Y.1) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS Y.1) _
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS X.1) _

/-! ### Restriction of modules along the comparisons and postcomposition -/

section RestrictScalars

variable {C : Type*} [Category C] {D : Type*} [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {R R' : Sheaf J RingCat.{u}} {T T' : Sheaf K RingCat.{u}}

/-- Restriction of scalars commutes with pushforward of sheaves of modules along compatible maps of
sheaves of rings: if `α ≫ φ = ψ ≫ F_*β`, then `β^* ∘ ψ_* ≅ φ_* ∘ α^*`, both functors being the
identity on sections. -/
def _root_.SheafOfModules.pushforwardCompRestrictScalarsIso (α : R' ⟶ R) (β : T' ⟶ T)
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj T)
    (ψ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj T')
    (h : α ≫ φ = ψ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map β) :
    SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.restrictScalars.{u} α ≅
      SheafOfModules.restrictScalars.{u} β ⋙ SheafOfModules.pushforward.{u} ψ :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U =>
      { hom := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.restrictScalars.{u} α).obj
            ((SheafOfModules.pushforward.{u} φ).obj M)).val.obj U))
          (Y := ↑(((SheafOfModules.pushforward.{u} ψ).obj
            ((SheafOfModules.restrictScalars.{u} β).obj M)).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj (op (F.obj U.unop)) from ((α ≫ φ).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x) =
                (show T.obj.obj (op (F.obj U.unop)) from
                  ((ψ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map β).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x)
              rw [h] }
        inv := ModuleCat.ofHom
          (X := ↑(((SheafOfModules.pushforward.{u} ψ).obj
            ((SheafOfModules.restrictScalars.{u} β).obj M)).val.obj U))
          (Y := ↑(((SheafOfModules.restrictScalars.{u} α).obj
            ((SheafOfModules.pushforward.{u} φ).obj M)).val.obj U))
          { toFun := fun x => x
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              change (show T.obj.obj (op (F.obj U.unop)) from
                  ((ψ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map β).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x) =
                (show T.obj.obj (op (F.obj U.unop)) from ((α ≫ φ).hom.app U).hom r) •
                  (show M.val.obj (op (F.obj U.unop)) from x)
              rw [h] }
        hom_inv_id := rfl
        inv_hom_id := rfl }) (fun _ _ _ => rfl))) (fun _ => rfl)

end RestrictScalars

/-- The comparison of Stacks 03G1 from the small étale model to the spaces-étale model is
continuous. -/
instance isContinuous_spacesEtaleModelComparison :
    (spacesEtaleModelComparison B S hS X).IsContinuous (smallEtaleModelTopology B S hS X.1)
      (smallModelTopology B S hS X) :=
  inferInstance

/-- The comparison of Stacks 03G1 is continuous for the topology of the ringed topos of the
spaces-étale model. -/
instance isContinuous_spacesEtaleModelComparison_ringedTopos :
    (spacesEtaleModelComparison B S hS X).IsContinuous (smallEtaleModelTopology B S hS X.1)
      (spacesEtaleModelRingedTopos B S hS X).J :=
  isContinuous_spacesEtaleModelComparison B S hS

/-- The comparison of Stacks 03G1 is continuous for the category and topology of the ringed topos
of the spaces-étale model. -/
instance isContinuous_spacesEtaleModelComparison_ringedTopos_category :
    @Functor.IsContinuous _ _ _ (spacesEtaleModelRingedTopos B S hS X).category
      (spacesEtaleModelComparison B S hS X) (smallEtaleModelTopology B S hS X.1)
      (spacesEtaleModelRingedTopos B S hS X).J :=
  isContinuous_spacesEtaleModelComparison B S hS

/-- The comparison of Stacks 03G1 followed by postcomposition on the spaces-étale models is
continuous, with the category structure of the ringed topos. -/
instance isContinuous_spacesEtaleModelComparison_comp_smallModelPostcomp_ringedTopos :
    (@Functor.comp _ _ _ (spacesEtaleModelRingedTopos B S hS X).category _ _
      (spacesEtaleModelComparison B S hS X) (smallModelPostcomp B S hS j hj)).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS Y) :=
  Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS X) _

/-- The comparison of Stacks 03G1 followed by postcomposition on the spaces-étale models is
continuous. -/
instance isContinuous_spacesEtaleModelComparison_comp_smallModelPostcomp :
    (spacesEtaleModelComparison B S hS X ⋙ smallModelPostcomp B S hS j hj).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS Y) :=
  Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS X) _

/-- Postcomposition on the small étale models followed by the comparison of Stacks 03G1 is
continuous. -/
instance isContinuous_smallEtaleModelPostcomp_comp_spacesEtaleModelComparison :
    (smallEtaleModelPostcomp B S hS j hj ⋙ spacesEtaleModelComparison B S hS Y).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS Y) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleModelTopology B S hS Y.1) _

/-- The structure map of postcomposition on the spaces-étale models, restricted to the small étale
models: a map from the restricted structure sheaf of `X` to the direct image along postcomposition
of the restricted structure sheaf of `Y`. -/
def spacesEtaleModelRestrictedPostcompSharp :
    ringRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
        (spacesEtaleModelComparison B S hS X)
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ⟶
      ((smallEtaleModelPostcomp B S hS j hj).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).obj
        (ringRestriction (smallEtaleModelTopology B S hS Y.1) (smallModelTopology B S hS Y)
          (spacesEtaleModelComparison B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y))) :=
  ((spacesEtaleModelComparison B S hS X).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)).map
      (smallModelPostcompSharp B S hS j hj) ≫
    (Functor.sheafPushforwardContinuousNatTrans
      (spacesEtaleModelComparisonPostcompIso B S hS j hj).inv RingCat.{u}
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS Y)).app
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y))

/-- **Step A.** Restricting to the small étale model after restricting along postcomposition on the
spaces-étale models is restricting along postcomposition on the small étale models after
restricting to the small étale model of `Y`. -/
def moduleRestrictionPostcompIso :
    SheafOfModules.pushforward.{u} (smallModelPostcompSharp B S hS j hj) ⋙
        moduleRestriction (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
          (spacesEtaleModelComparison B S hS X)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)) ≅
      moduleRestriction (smallEtaleModelTopology B S hS Y.1) (smallModelTopology B S hS Y)
          (spacesEtaleModelComparison B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y)) ⋙
        SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS j hj) :=
  haveI := isContinuous_spacesEtaleModelComparison_ringedTopos B S hS (X := X)
  haveI := isContinuous_spacesEtaleModelComparison_comp_smallModelPostcomp B S hS j hj
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (spacesEtaleModelComparisonPostcompIso B S hS j hj).symm
      (by
        have := isContinuous_spacesEtaleModelComparison_ringedTopos B S hS (X := X)
        have := isContinuous_spacesEtaleModelComparison_comp_smallModelPostcomp B S hS j hj
        rfl) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- The inverse of the equivalence of the small étale site with its model, followed by
postcomposition on the small étale sites, is continuous. -/
instance isContinuous_smallEtaleModelEquiv_inverse_comp_smallEtalePostcomp :
    ((smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS X.1) _

/-- Postcomposition on the small étale models followed by the inverse of the equivalence of the
small étale site with its model is continuous. -/
instance isContinuous_smallEtaleModelPostcomp_comp_smallEtaleModelEquiv_inverse :
    (smallEtaleModelPostcomp B S hS j hj ⋙ (smallEtaleModelEquiv B S hS Y).inverse).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleModelTopology B S hS Y.1) _

/-- The inverse of the equivalence of the small étale site with its model is continuous for the
category and topology of the small étale ringed site. -/
instance isContinuous_smallEtaleModelEquiv_inverse_smallEtaleRingedSite :
    @Functor.IsContinuous _ _ _ (smallEtaleRingedSite B S hS X.1 X.2).category
      (smallEtaleModelEquiv B S hS X).inverse (smallEtaleModelTopology B S hS X.1)
      (smallEtaleRingedSite B S hS X.1 X.2).J :=
  inferInstanceAs ((smallEtaleModelEquiv B S hS X).inverse.IsContinuous
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1))

/-- Postcomposition on the small étale models followed by the inverse of the equivalence with the
model is continuous for the category and topology of the small étale ringed site of `Y`. -/
instance isContinuous_smallEtaleModelPostcomp_comp_inverse_smallEtaleRingedSite :
    @Functor.IsContinuous _ _ _ (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallEtaleModelPostcomp B S hS j hj ⋙ (smallEtaleModelEquiv B S hS Y).inverse)
      (smallEtaleModelTopology B S hS X.1) (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  isContinuous_smallEtaleModelPostcomp_comp_smallEtaleModelEquiv_inverse B S hS j hj

/-- The inverse of the equivalence of the small étale site with its model is continuous for the
topology of the small étale ringed site. -/
instance isContinuous_smallEtaleModelEquiv_inverse_smallEtaleRingedSite_topology :
    (smallEtaleModelEquiv B S hS X).inverse.IsContinuous (smallEtaleModelTopology B S hS X.1)
      (smallEtaleRingedSite B S hS X.1 X.2).J :=
  inferInstanceAs ((smallEtaleModelEquiv B S hS X).inverse.IsContinuous
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1))

/-- Postcomposition on the small étale models followed by the inverse of the equivalence with the
model is continuous for the topology of the small étale ringed site of `Y`. -/
instance isContinuous_smallEtaleModelPostcomp_comp_inverse_smallEtaleRingedSite_topology :
    (smallEtaleModelPostcomp B S hS j hj ⋙ (smallEtaleModelEquiv B S hS Y).inverse).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  isContinuous_smallEtaleModelPostcomp_comp_smallEtaleModelEquiv_inverse B S hS j hj

/-- The inverse of the equivalence of the small étale site with its model, followed by
postcomposition on the small étale sites, is continuous for the topology of the small étale ringed
site of `Y`. -/
instance isContinuous_smallEtaleModelEquiv_inverse_comp_smallEtalePostcomp_ringedSite :
    ((smallEtaleModelEquiv B S hS X).inverse ⋙ smallEtalePostcomp B S hS j hj).IsContinuous
      (smallEtaleModelTopology B S hS X.1) (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  isContinuous_smallEtaleModelEquiv_inverse_comp_smallEtalePostcomp B S hS j hj

/-- The identification of the restricted structure sheaf of `X` with the direct image along
postcomposition of the restricted structure sheaf of `Y`, on the small étale models: a chart and
its postcomposite with `j` have the same underlying scheme. -/
def smallEtaleModelPostcompSharp :
    ringRestriction (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
        (smallEtaleModelEquiv B S hS X).inverse (structureRingSheaf B S hS X) ⟶
      ((smallEtaleModelPostcomp B S hS j hj).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).obj
        (ringRestriction (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1)
          (smallEtaleModelEquiv B S hS Y).inverse (structureRingSheaf B S hS Y)) :=
  (Functor.sheafPushforwardContinuousNatTrans
    (smallEtaleModelInversePostcompIso B S hS j hj).inv RingCat.{u}
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS Y.1)).app
    (structureRingSheaf B S hS Y)

/-- **Step B.** Restricting to the small étale model after the étale pullback is restricting along
postcomposition on the small étale models after restricting to the small étale model of `Y`. -/
def smallEtaleModelModuleRestrictionPostcompIso :
    etaleModulePullback.{u, u} B S hS j hj ⋙ smallEtaleModelModuleRestriction B S hS X ≅
      smallEtaleModelModuleRestriction B S hS Y ⋙
        SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS j hj) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (smallEtaleModelInversePostcompIso B S hS j hj).symm
      (Sheaf.hom_ext (NatTrans.ext (funext fun _ => RingCat.hom_ext (RingHom.ext fun _ => rfl)))) ≪≫
    (SheafOfModules.pushforwardComp (smallEtaleModelPostcompSharp B S hS j hj)
      (𝟙 (ringRestriction (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1)
        (smallEtaleModelEquiv B S hS Y).inverse (structureRingSheaf B S hS Y)))).symm

/-- The comparison `AlgebraicGeometry.Space.spacesEtaleModelComparisonPostcompIso`, read back on
the spaces-étale site of `Y` between the unit isomorphisms of the small model: the image of the
unit isomorphism of the small étale model of `Y` followed by the unit of the small spaces-étale
model of `X`. -/
theorem spacesEtaleModelComparisonPostcompIso_inv_inverse
    (W : SmallModel.{u} (SmallEtale B S hS X.1)) :
    (equivSmallModel.{u} (SpacesEtale B S hS Y)).unit.app
        ((comparisonFunctor B S hS Y).obj ((smallEtaleModelEquiv B S hS Y).inverse.obj
          ((smallEtaleModelPostcomp B S hS j hj).obj W))) ≫
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map
        ((spacesEtaleModelComparisonPostcompIso B S hS j hj).inv.app W) ≫
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
        ((spacesEtalePostcomp B S hS j hj).obj
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
            ((spacesEtaleModelComparison B S hS X).obj W))) =
      (comparisonFunctor B S hS Y).map ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS j hj).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W))) ≫
        (spacesEtalePostcomp B S hS j hj).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
            ((comparisonFunctor B S hS X).obj
                ((smallEtaleModelEquiv B S hS X).inverse.obj W))) := by
  have he : (spacesEtaleModelComparisonPostcompIso B S hS j hj).inv.app W =
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map ((comparisonFunctor B S hS Y).map
        ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS j hj).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W)))) ≫
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map
          ((spacesEtalePostcomp B S hS j hj).map
          ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
          ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W)))) :=
    rfl
  rw [he]
  simp only [Functor.map_comp, Equivalence.inv_fun_map, Category.assoc, Equivalence.unit,
    Equivalence.unitInv, Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc]
  have h : ∀ {A A' : SpacesEtale B S hS Y} (f : A ⟶ A'),
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app A ≫
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).functor.map f) ≫
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app A' = f := fun f => by
    simp
  exact congrArg (_ ≫ ·) (h _)

/-- Pulling back a global function along the comparison of an étale morphism of charts is pulling
back the regular function on the chart along the underlying morphism of schemes. -/
theorem globalFunctionsYonedaEquiv_globalFunctionsMap_comparisonFunctor_map
    {V W : SmallEtale B S hS Y.1} (g : W ⟶ V)
    (σ : globalFunctions' B S hS ((SpacesEtale.toSpaces B S hS Y).obj
      ((comparisonFunctor B S hS Y).obj V)).1) :
    globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj W)
        (globalFunctionsMap B S hS
          ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map g)) σ) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map g)).appTop.hom
        (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj V) σ) :=
  globalFunctionsMap_val_of_yoneda_map_comp B S hS
    ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map g)) σ
    (idChart B S hS ((SmallEtale.toOver B S hS Y.1).obj W))
    (idChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))
    ((SmallEtale.toOver B S hS Y.1).map g) (by
      change yoneda.map ((SmallEtale.toOver B S hS Y.1).map g) ≫ 𝟙 _ =
        𝟙 _ ≫ yoneda.map ((SmallEtale.toOver B S hS Y.1).map g)
      rw [Category.comp_id, Category.id_comp])

/-- **The structure maps of postcomposition agree** under the identification of the structure
sheaves of the two models (`AlgebraicGeometry.Space.spacesEtaleModelRingRestrictionIso`): both read
a regular function on a chart of `X` as one on the same scheme, a chart of `Y`. -/
theorem spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso :
    spacesEtaleModelRestrictedPostcompSharp B S hS j hj ≫
        ((smallEtaleModelPostcomp B S hS j hj).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelTopology B S hS Y.1)).map
          (spacesEtaleModelRingRestrictionIso B S hS Y).hom =
      (spacesEtaleModelRingRestrictionIso B S hS X).hom ≫
        smallEtaleModelPostcompSharp B S hS j hj := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun s => ?_)))
  have h1 := smallModelPostcompSharpComm_apply B S hS j hj (op
      ((spacesEtaleModelComparison B S hS X).obj W.unop)) s
  have h2 := spacesEtaleModelStructureSheaf_map_apply B S hS Y
    ((spacesEtaleModelComparisonPostcompIso B S hS j hj).inv.app W.unop).op
    (((smallModelPostcompSharpComm B S hS j hj).app (op
        ((spacesEtaleModelComparison B S hS X).obj W.unop))).hom s)
  have h3 := shrinkCommRingPresheaf_map_apply.{u, u + 1} (SpacesEtale.structurePresheaf B S hS Y)
    ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
        ((comparisonFunctor B S hS Y).obj ((smallEtaleModelEquiv B S hS Y).inverse.obj
            ((smallEtaleModelPostcomp B S hS j hj).obj W.unop)))).op
    (((spacesEtaleModelStructureSheaf B S hS Y).obj.map
      ((spacesEtaleModelComparisonPostcompIso B S hS j hj).inv.app W.unop).op).hom
      (((smallModelPostcompSharpComm B S hS j hj).app (op
          ((spacesEtaleModelComparison B S hS X).obj W.unop))).hom s))
  have h4 := shrinkCommRingPresheaf_map_apply.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X)
    ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
        ((comparisonFunctor B S hS X).obj
            ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))).op s
  have hkey := spacesEtaleModelComparisonPostcompIso_inv_inverse B S hS j hj W.unop
  have hL : ∀ σ, ((SpacesEtale.structurePresheaf B S hS Y).map ((equivSmallModel.{u}
      (SpacesEtale B S hS Y)).unitIso.hom.app ((comparisonFunctor B S hS
          Y).obj ((smallEtaleModelEquiv B S hS Y).inverse.obj ((smallEtaleModelPostcomp B S hS j
              hj).obj W.unop)))).op).hom
      (((SpacesEtale.structurePresheaf B S hS Y).map ((equivSmallModel.{u}
          (SpacesEtale B S hS Y)).inverse.map ((spacesEtaleModelComparisonPostcompIso B S hS j
              hj).inv.app
        W.unop)).op).hom (((globalFunctionsPresheaf B S hS).map ((SpacesEtale.toSpaces B S hS
            Y).map ((equivSmallModel.{u} (SpacesEtale B S hS
                Y)).unitIso.inv.app ((spacesEtalePostcomp B S hS j hj).obj ((equivSmallModel.{u}
                    (SpacesEtale B S hS X)).inverse.obj
          ((spacesEtaleModelComparison B S hS X).obj W.unop))))).op).hom σ)) =
      globalFunctionsMap B S hS ((SpacesEtale.toSpaces B S hS Y).map
          ((comparisonFunctor B S hS Y).map ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
          ((smallEtalePostcomp B S hS j hj).obj
              ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop)))))
        (((SpacesEtale.structurePresheaf B S hS X).map ((equivSmallModel.{u}
            (SpacesEtale B S hS X)).unitIso.hom.app ((comparisonFunctor B S hS
                X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))).op).hom σ) := by
    intro σ
    let f₁ := (comparisonFunctor B S hS Y).map ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app
      ((smallEtalePostcomp B S hS j hj).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop)))
    let f₂ := (spacesEtalePostcomp B S hS j hj).map
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
        ((comparisonFunctor B S hS X).obj ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop)))
    have := congrArg (fun f => globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS Y).map f) σ) hkey
    simp only [Functor.map_comp, globalFunctionsMap_comp] at this
    refine this.trans ?_
    exact RingHom.congr_fun ((congrArg (globalFunctionsMap B S hS)
      ((SpacesEtale.toSpaces B S hS Y).map_comp f₁ f₂)).trans
      (globalFunctionsMap_comp B S hS ((SpacesEtale.toSpaces B S hS Y).map f₁)
        ((SpacesEtale.toSpaces B S hS Y).map f₂))) σ
  change globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS Y.1).obj
      ((smallEtaleModelEquiv B S hS Y).inverse.obj
          ((smallEtaleModelPostcomp B S hS j hj).obj W.unop)))
      (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj (op
          ((comparisonFunctor B S hS Y).obj ((smallEtaleModelEquiv B S hS Y).inverse.obj
              ((smallEtaleModelPostcomp B S hS j hj).obj W.unop)))))
        ((shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS Y)).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.hom.app
              ((comparisonFunctor B S hS Y).obj ((smallEtaleModelEquiv B S hS Y).inverse.obj
                  ((smallEtaleModelPostcomp B S hS j hj).obj W.unop)))).op
          (((spacesEtaleModelStructureSheaf B S hS Y).obj.map
            ((spacesEtaleModelComparisonPostcompIso B S hS j hj).inv.app W.unop).op).hom
            (((smallModelPostcompSharpComm B S hS j hj).app (op
                ((spacesEtaleModelComparison B S hS X).obj W.unop))).hom s)))) =
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map
      ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app ((smallEtalePostcomp B S hS j hj).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))))).appTop.hom
      (globalFunctionsYonedaEquiv B S hS ((SmallEtale.toOver B S hS X.1).obj
          ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))
        (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj (op
            ((comparisonFunctor B S hS X).obj
                ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))))
          ((shrinkCommRingPresheaf.{u, u + 1} (SpacesEtale.structurePresheaf B S hS X)).map
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.hom.app
                ((comparisonFunctor B S hS X).obj
                    ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))).op s)))
  refine ((congrArg (globalFunctionsYonedaEquiv B S hS _) (h3.trans
    (congrArg ((SpacesEtale.structurePresheaf B S hS Y).map _).hom
      (h2.trans (congrArg ((SpacesEtale.structurePresheaf B S hS Y).map _).hom h1))))).trans
    (congrArg (globalFunctionsYonedaEquiv B S hS _) (hL _))).trans
    ((globalFunctionsYonedaEquiv_globalFunctionsMap_comparisonFunctor_map B S hS _ _).trans ?_)
  exact congrArg (fun t => ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map
      ((smallEtaleModelEquiv B S hS Y).unitIso.inv.app ((smallEtalePostcomp B S hS j hj).obj
        ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))))).appTop.hom
    (globalFunctionsYonedaEquiv B S hS _ t)) h4.symm

/-- **Step C.** Restriction of scalars along the identifications of the structure sheaves of the
two models commutes with restriction along postcomposition on the small étale models. -/
def restrictScalarsRingRestrictionPostcompIso :
    SheafOfModules.pushforward.{u} (spacesEtaleModelRestrictedPostcompSharp B S hS j hj) ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv ≅
      SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS Y).inv ⋙
        SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS j hj) :=
  SheafOfModules.pushforwardCompRestrictScalarsIso _ _ _ _ (by
    rw [← cancel_epi (spacesEtaleModelRingRestrictionIso B S hS X).hom, Iso.hom_inv_id_assoc,
      ← reassoc_of% (spacesEtaleModelRestrictedPostcompSharp_comp_ringRestrictionIso B S hS j hj),
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id])

/-- **Step D.** The étale pullback, transported to the small étale models: restriction along
postcomposition on the small étale models followed by the inverse of the Comparison Lemma is the
inverse of the Comparison Lemma followed by the étale pullback. -/
def smallEtaleModelModulesEquivInversePostcompIso :
    SheafOfModules.pushforward.{u} (smallEtaleModelPostcompSharp B S hS j hj) ⋙
        (smallEtaleModelModulesEquiv B S hS X).inverse ≅
      (smallEtaleModelModulesEquiv B S hS Y).inverse ⋙ etaleModulePullback.{u, u} B S hS j hj :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleModelModulesEquiv B S hS Y).counitIso.symm _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleModelModulesEquiv B S hS Y).inverse
      (Functor.isoWhiskerRight (smallEtaleModelModuleRestrictionPostcompIso B S hS j hj).symm
        (smallEtaleModelModulesEquiv B S hS X).inverse) ≪≫
    Functor.isoWhiskerLeft ((smallEtaleModelModulesEquiv B S hS Y).inverse ⋙
      etaleModulePullback.{u, u} B S hS j hj) (smallEtaleModelModulesEquiv B S hS X).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` is restriction to the small étale model,
followed by restriction of scalars along the identification of the structure sheaves and the
inverse of the Comparison Lemma. -/
theorem spacesEtaleModelModulesEquiv_functor_eq (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelModulesEquiv B S hS Z).functor =
      moduleRestriction (smallEtaleModelTopology B S hS Z.1) (smallModelTopology B S hS Z)
          (spacesEtaleModelComparison B S hS Z)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Z)) ⋙
        SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS Z).inv ⋙
          (smallEtaleModelModulesEquiv B S hS Z).inverse :=
  rfl

/-- The comparison of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivPostcompIso`, with the
equivalences written out as composites. -/
def spacesEtaleModelModulesEquivPostcompIsoAux :
    (SheafOfModules.pushforward.{u} (smallModelPostcompSharp B S hS j hj) ⋙ (moduleRestriction
        (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
          (spacesEtaleModelComparison B S hS X)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)))) ⋙
        ((SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv) ⋙
            (smallEtaleModelModulesEquiv B S hS X).inverse) ≅
      (moduleRestriction (smallEtaleModelTopology B S hS Y.1) (smallModelTopology B S hS Y)
          (spacesEtaleModelComparison B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS
                  Y))) ⋙
        ((SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS Y).inv) ⋙
          ((smallEtaleModelModulesEquiv B S hS Y).inverse ⋙
          etaleModulePullback.{u, u} B S hS j hj)) :=
  Functor.isoWhiskerRight (moduleRestrictionPostcompIso B S hS j hj)
      ((SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv) ⋙
          (smallEtaleModelModulesEquiv B S hS X).inverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleRestriction (smallEtaleModelTopology B S hS Y.1)
        (smallModelTopology B S hS Y)
          (spacesEtaleModelComparison B S hS Y)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS Y)))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictScalarsRingRestrictionPostcompIso B S hS j hj)
          (smallEtaleModelModulesEquiv B S hS X).inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.restrictScalars.{u}
            (spacesEtaleModelRingRestrictionIso B S hS
                Y).inv) (smallEtaleModelModulesEquivInversePostcompIso B S hS j hj))

/-- **The étale pullback on the spaces-étale model is the étale pullback on the small étale site.**
For an étale morphism `j : X ⟶ Y` of algebraic spaces, restriction of modules along postcomposition
with `j` on the models of the spaces-étale sites (which is the inverse image along
`AlgebraicGeometry.Space.spacesEtaleModelHom j`, by
`AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward`) corresponds, under the
equivalences `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of Stacks 03G1, to the étale
pullback `j^*` of `𝒪`-modules on the small étale sites. -/
def spacesEtaleModelModulesEquivPostcompIso :
    SheafOfModules.pushforward.{u} (smallModelPostcompSharp B S hS j hj) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor ≅
      (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ etaleModulePullback.{u, u} B S hS j hj :=
  Functor.isoWhiskerLeft _ (eqToIso (spacesEtaleModelModulesEquiv_functor_eq B S hS X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ spacesEtaleModelModulesEquivPostcompIsoAux B S hS j hj ≪≫
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso ((Functor.assoc _ _ _).trans
      (spacesEtaleModelModulesEquiv_functor_eq B S hS Y).symm)) _

end AlgebraicGeometry.Space

end
