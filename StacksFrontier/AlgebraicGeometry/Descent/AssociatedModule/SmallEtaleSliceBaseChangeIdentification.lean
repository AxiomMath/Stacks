module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImagePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalizedPushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQcqsPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleZariskiLocalCartesian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localized direct image is the direct image along the base-changed morphism

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `V` be an object of the small
étale site of `Y`, with underlying scheme `V₀`. Write `P_V` for the direct image along the
morphism of ringed sites obtained by localizing `ε_a` at `V` ([Stacks, Tag 04J0] (1)), and
`a_V : X ×_Y V₀ ⟶ V₀` for the base change of `a`. Across the equivalences
`AlgebraicGeometry.SmallEtale.objRestrictEquivalence` between modules on a slice of a small étale
site and modules on the small étale site of the underlying scheme, `P_V` is identified with the
direct image `(ε_{a_V})_*`, and so are their right derived functors.

The site half of this identification is the transitivity of base change: for an object `T` of
the small étale site of `V₀`, the two fibre products `T ×_{V₀} (V₀ ×_Y X)` and `T ×_Y X` are
identified by `CategoryTheory.Limits.pullbackRightPullbackFstIso`. The ring half states that the
two composite comparisons of structure sheaves agree.

As a consequence, for `a` quasi-compact and separated and `𝓕` quasi-coherent on the site, the
higher direct images `R ⁿ (ε_a)_*(𝓕)` are quasi-coherent on the site, with no hypothesis on `Y`:
this is the étale comparison of [Stacks, Tag 071N] above degree zero, under the stronger
hypothesis that `a` is separated rather than quasi-separated. Separatedness is inherited from the
affine-base case, where it makes a one-step Čech resolution acyclic.

## Main definitions

* `CategoryTheory.Over.pullbackFstCompMapSndIso`: transitivity of base change, as a comparison of
  slice functors in a category with pullbacks.
* `AlgebraicGeometry.SmallEtale.objBaseChangeHom`: the base-changed morphism
  `a_V : X ×_Y V₀ ⟶ V₀`.
* `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso` and
  `AlgebraicGeometry.SmallEtale.sliceBaseChangeLocalizationIso`: the comparison of the two routes
  round the base-change square, at the small étale sites and in the slice at `a⁻¹V`.
* `AlgebraicGeometry.SmallEtale.localizedPushforwardBaseChangeIso`: the identification
  `P_V ⋙ (−)|_{V₀,étale} ≅ (−)|_{(X ×_Y V₀),étale} ⋙ (ε_{a_V})_*`.
* `AlgebraicGeometry.SmallEtale.rightDerivedLocalizedPushforwardObjIso`: its derived form,
  `(R ⁿ P_V (𝓜))|_{V₀,étale} ≅ R ⁿ (ε_{a_V})_* (𝓜|_{(X ×_Y V₀),étale})`.

## Main results

* `AlgebraicGeometry.SmallEtale.comparisonComp_sliceBaseChangeLocalizationIso`: the two composite
  comparisons of structure sheaves round the base-change square agree.
* `isCartesianOnAffines_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom` and
  `isQuasicoherentOnSite_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom`: for `a`
  quasi-compact and separated and `𝓕` quasi-coherent on the site, `R ⁿ (ε_a)_*(𝓕)` is cartesian
  between affine objects, equivalently quasi-coherent on the site, in every degree.

## Implementation notes

The instances `AlgebraicGeometry.SmallEtale.additive_objRestrictFunctor` and
`AlgebraicGeometry.SmallEtale.isEquivalence_objRestrictFunctor` are stated explicitly, since
instance search does not find them: matching the identity structure map requires unfolding
`Stacks.SheafOfModules.reindexRing`, which is not reducible.

`SheafOfModules.instAbelian` is made a high-priority local instance for the derived statements,
as in `SmallEtaleLocalizedPushforwardSquare`: otherwise instance search commits to the instances
in a larger module universe and gets stuck on `u + 1 =?= max (u + 1) ?w`.

Wherever a `Limits.pullback` appears on both sides of an equation, the proofs are term-mode
`Eq.trans`/`congrArg` chains: the two spellings of such an object differ in their `HasPullback`
instance, so they are equal only by proof irrelevance, which `rw` does not see.

## References

* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C] {X Y Z : C} (v : Z ⟶ Y) (a : X ⟶ Y)

/-- **Base change is transitive, as a comparison of slice functors.** Let `v : Z ⟶ Y` and
`a : X ⟶ Y`, and let `a_v = pullback.fst v a : X ×_Y Z ⟶ Z` and
`x_v = pullback.snd v a : X ×_Y Z ⟶ X` be the two projections of the chosen fibre product. Then
pulling an object `T / Z` back along `a_v` and reading the result over `X` agrees with reading `T`
over `Y` and pulling back along `a`: both are `T ×_Y X`.

The component at `T` is `CategoryTheory.Limits.pullbackRightPullbackFstIso`, the pasting
comparison `T ×_Z (Z ×_Y X) ≅ T ×_Y X`. -/
@[ega "I 3.3.9" "partial"]
def pullbackFstCompMapSndIso :
    Over.pullback (pullback.fst v a) ⋙ Over.map (pullback.snd v a) ≅
      Over.map v ⋙ Over.pullback a :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (pullbackRightPullbackFstIso v a T.hom) (by simp))
    (fun {T T'} k ↦ by
      apply Over.OverMorphism.ext
      dsimp
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp)

/-- The component of `CategoryTheory.Over.pullbackFstCompMapSndIso` at `T`, on underlying objects,
is the pasting comparison `CategoryTheory.Limits.pullbackRightPullbackFstIso`. -/
@[simp]
theorem pullbackFstCompMapSndIso_hom_app_left (T : Over Z) :
    ((pullbackFstCompMapSndIso v a).hom.app T).left =
      (pullbackRightPullbackFstIso v a T.hom).hom :=
  rfl

end CategoryTheory.Over

namespace AlgebraicGeometry.SmallEtale

section Reindexing

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- The reindexing of modules along the localization equivalence is additive. -/
instance additive_objRestrictFunctor : (objRestrictFunctor B S hS U).Additive where
  map_add := by intros; rfl

/-- The reindexing of modules along the localization equivalence is an equivalence, being the
functor of `AlgebraicGeometry.SmallEtale.objRestrictEquivalence`. -/
instance isEquivalence_objRestrictFunctor : (objRestrictFunctor B S hS U).IsEquivalence :=
  inferInstanceAs ((objRestrictEquivalence B S hS U).functor.IsEquivalence)

end Reindexing

section Localized

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property)

/-- **The base change of `a` along the structure morphism of `V`.** For an object `V` of the
small étale site of `Y` with scheme `V₀`, this is the projection `a_V : X ×_Y V₀ ⟶ V₀`, a morphism
of the big étale site from the scheme of `(smallEtaleBaseChange B a).obj V` to the scheme of `V`.
-/
abbrev objBaseChangeHom : ((smallEtaleBaseChange B a).obj V).obj.left ⟶ V.obj.left :=
  pullback.fst V.obj.hom a

/-- **Base change along `a` commutes with post-composition into the slices, on the small étale
sites.** Base-changing an object of the small étale site of the scheme of `V` along `a_V` and
then post-composing into the small étale site of `X` agrees with post-composing into the small
étale site of `Y` and then base-changing along `a`. Along the inclusion of the small étale
category into the big étale slice, this is `CategoryTheory.Over.pullbackFstCompMapSndIso`. -/
def postcomposeBaseChangeIso :
    smallEtaleBaseChange B (objBaseChangeHom B a V) ⋙
        postcompose B X.obj X.property ((smallEtaleBaseChange B a).obj V) ≅
      postcompose B Y.obj Y.property V ⋙ smallEtaleBaseChange B a :=
  Functor.fullyFaithfulCancelRight (SmallEtale.inclusion B X.obj X.property)
    (NatIso.ofComponents
      (fun T ↦ (Over.pullbackFstCompMapSndIso V.obj.hom a).app T.obj)
      (fun {_T _T'} k ↦ (Over.pullbackFstCompMapSndIso V.obj.hom a).hom.naturality k.hom))

/-- The comparison of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso`, read on the
underlying objects of the big étale slice:  it is the pasting comparison
`T ×_{V₀} (V₀ ×_Y X) ≅ T ×_Y X`. -/
theorem inclusion_map_postcomposeBaseChangeIso_hom_app
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((postcomposeBaseChangeIso B a V).hom.app T) =
      (Over.pullbackFstCompMapSndIso V.obj.hom a).hom.app T.obj := by
  simp only [postcomposeBaseChangeIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  rfl

/-- `AlgebraicGeometry.SmallEtale.inclusion_map_postcomposeBaseChangeIso_hom_app` with the
inclusion of the small étale category spelled out as the `hom` field. -/
theorem postcomposeBaseChangeIso_hom_app_hom
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((postcomposeBaseChangeIso B a V).hom.app T).hom =
      (Over.pullbackFstCompMapSndIso V.obj.hom a).hom.app T.obj :=
  inclusion_map_postcomposeBaseChangeIso_hom_app B a V T

/-- The comparison of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso` on underlying
schemes of the big étale site:  it is `CategoryTheory.Limits.pullbackRightPullbackFstIso`. -/
theorem postcomposeBaseChangeIso_hom_app_hom_left
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((postcomposeBaseChangeIso B a V).hom.app T).hom.left =
      (pullbackRightPullbackFstIso V.obj.hom a T.obj.hom).hom :=
  congrArg Over.Hom.left (postcomposeBaseChangeIso_hom_app_hom B a V T)

/-- `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso_hom_app_hom_left` with the component
of the natural isomorphism spelled as `CategoryTheory.NatIso.app`. -/
theorem postcomposeBaseChangeIso_app_hom_hom_left
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    (((postcomposeBaseChangeIso B a V).app T).hom.hom).left =
      (pullbackRightPullbackFstIso V.obj.hom a T.obj.hom).hom :=
  postcomposeBaseChangeIso_hom_app_hom_left B a V T

/-- **The localized base-change square of small étale sites.** Base-changing an object of the
small étale site of the scheme of `V` along `a_V` and reading the result in the slice of `X_étale`
at `a⁻¹V` agrees with reading the object in the slice of `Y_étale` at `V` and applying the slice of
base change along `a`:

`a_V^{-1} ⋙ (−)_{X_étale/a⁻¹V} ≅ (−)_{Y_étale/V} ⋙ Over.post a^{-1}`.

Its components are those of `AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso`. -/
def sliceBaseChangeLocalizationIso :
    smallEtaleBaseChange B (objBaseChangeHom B a V) ⋙
        (localizationEquivalence B X.obj X.property
          ((smallEtaleBaseChange B a).obj V)).functor ≅
      (localizationEquivalence B Y.obj Y.property V).functor ⋙
        Over.post (X := V) (smallEtaleBaseChange B a) :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk ((postcomposeBaseChangeIso B a V).app T) (by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
        postcomposeBaseChangeIso_app_hom_hom_left]
      change (pullbackRightPullbackFstIso V.obj.hom a T.obj.hom).hom ≫
          ((Over.pullback a).map
            (Over.homMk T.obj.hom rfl : (Over.map V.obj.hom).obj T.obj ⟶ V.obj)).left =
        pullback.snd T.obj.hom (pullback.fst V.obj.hom a)
      simp only [Over.pullback_map_left, Over.homMk_left, Over.map_obj_hom]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
        exact pullback.condition
      · rw [Category.assoc, pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd]))
    (fun {T T'} k ↦ (Over.forget ((smallEtaleBaseChange B a).obj V)).map_injective
      ((postcomposeBaseChangeIso B a V).hom.naturality k))

/-- The component of `AlgebraicGeometry.SmallEtale.sliceBaseChangeLocalizationIso`, read in the
small étale site of `X` after forgetting the arrow to `a⁻¹V`:  it is
`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeIso`. -/
theorem sliceBaseChangeLocalizationIso_hom_app_left
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((sliceBaseChangeLocalizationIso B a V).hom.app T).left =
      (postcomposeBaseChangeIso B a V).hom.app T :=
  rfl

/-- **The structure map of the localized morphism of [Stacks, Tag 04J0] (1), on sections.** Over
an object `T` of the slice of `Y_étale` at `V` it is the structure map of `ε_a` over the
underlying object of `Y_étale`. -/
theorem localizedStructureMapBaseChange_hom_app (T : Over V) :
    (localizedStructureMapBaseChange B a V).hom.app (op T) =
      (smallEtaleStructureMapRing B a).hom.app (op T.left) := by
  simp only [localizedStructureMapBaseChange,
    RingedSite.MorphismLocalization.localizedStructureMap,
    RingedSite.MorphismLocalization.localizationComparisonIso_inv_app]
  rfl

/-- The component of `AlgebraicGeometry.SmallEtale.sliceBaseChangeLocalizationIso` on underlying
schemes of the big étale site:  it is the pasting comparison
`CategoryTheory.Limits.pullbackRightPullbackFstIso`. -/
theorem sliceBaseChangeLocalizationIso_hom_app_left_hom_left
    (T : SmallEtale B V.obj.left.obj V.obj.left.property) :
    ((sliceBaseChangeLocalizationIso B a V).hom.app T).left.hom.left =
      (pullbackRightPullbackFstIso V.obj.hom a T.obj.hom).hom :=
  (congrArg (fun g ↦ g.hom.left) (sliceBaseChangeLocalizationIso_hom_app_left B a V T)).trans
    (postcomposeBaseChangeIso_hom_app_hom_left B a V T)

/-- Base change along `a_V` followed by the equivalence with the slice of `X_étale` at `a⁻¹V` is
continuous. -/
instance isContinuous_sliceBaseChange_comp_localization :
    (smallEtaleBaseChange B (objBaseChangeHom B a V) ⋙
        (localizationEquivalence B X.obj X.property
          ((smallEtaleBaseChange B a).obj V)).functor).IsContinuous
      (topology B V.obj.left.obj V.obj.left.property)
      ((topology B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)) :=
  Functor.isContinuous_comp _ _ _
    (topology B ((smallEtaleBaseChange B a).obj V).obj.left.obj
      ((smallEtaleBaseChange B a).obj V).obj.left.property) _

/-- The equivalence with the slice of `Y_étale` at `V` followed by the slice of base change along
`a` is continuous. -/
instance isContinuous_localization_comp_overPostBaseChange :
    ((localizationEquivalence B Y.obj Y.property V).functor ⋙
        Over.post (X := V) (smallEtaleBaseChange B a)).IsContinuous
      (topology B V.obj.left.obj V.obj.left.property)
      ((topology B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)) :=
  Functor.isContinuous_comp _ _ _ ((topology B Y.obj Y.property).over V) _

/-- **The structure-map half of the localized base-change square.** The two composite
comparisons of structure sheaves round the square of
`AlgebraicGeometry.SmallEtale.sliceBaseChangeLocalizationIso` agree: on sections over an object
`T` of the small étale site of the scheme of `V`, both pull a global function on `T` back along
the projection to `T` from `T ×_Y X`, the left-hand side through the two-step fibre product
`T ×_{V₀} (V₀ ×_Y X)`. -/
theorem comparisonComp_sliceBaseChangeLocalizationIso :
    SheafOfModules.comparisonComp
        (𝟙 (Stacks.SheafOfModules.reindexRing
          (topology B V.obj.left.obj V.obj.left.property)
          (localizationEquivalence B Y.obj Y.property V)
          ((structureSheaf B Y.obj Y.property).over V)))
        (localizedStructureMapBaseChange B a V) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (sliceBaseChangeLocalizationIso B a V).hom RingCat.{u}
        (topology B V.obj.left.obj V.obj.left.property)
        ((topology B X.obj X.property).over ((smallEtaleBaseChange B a).obj V))).app
          ((structureSheaf B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)) =
      SheafOfModules.comparisonComp
        (smallEtaleStructureMapRing B (objBaseChangeHom B a V))
        (𝟙 (Stacks.SheafOfModules.reindexRing
          (topology B ((smallEtaleBaseChange B a).obj V).obj.left.obj
            ((smallEtaleBaseChange B a).obj V).obj.left.property)
          (localizationEquivalence B X.obj X.property ((smallEtaleBaseChange B a).obj V))
          ((structureSheaf B X.obj X.property).over ((smallEtaleBaseChange B a).obj V)))) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun T => ?_)
  induction T with | op T => ?_
  let G : ∀ {P Q : B.Scheme}, (P ⟶ Q) → _ := fun m ↦
    (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map (op (B.inclusion.map m)))
  have hG : ∀ {P Q R : B.Scheme} (f : P ⟶ Q) (g : Q ⟶ R), G g ≫ G f = G (f ≫ g) := by
    intro P Q R f g
    simp [G, ← Functor.map_comp]
  change _ ≫ _ = _
  refine Eq.trans (congrArg (· ≫ _) ((Category.id_comp _).trans
    ((localizedStructureMapBaseChange_hom_app B a V _).trans
      (smallEtaleStructureMapRing_hom_app B a _)) : _ = G _)) ?_
  refine Eq.trans (congrArg (G _ ≫ ·) (congrArg G
    (sliceBaseChangeLocalizationIso_hom_app_left_hom_left B a V T))) ?_
  refine Eq.trans (hG _ _) ?_
  refine Eq.trans (congrArg G (pullbackRightPullbackFstIso_hom_fst V.obj.hom a T.obj.hom)) ?_
  exact ((Category.comp_id _).trans
    (smallEtaleStructureMapRing_hom_app B (objBaseChangeHom B a V) T)).symm

/-- **`P_V` is the direct image along the base-changed morphism `a_V`.** Across the equivalences
`AlgebraicGeometry.SmallEtale.objRestrictEquivalence` between modules on a slice of a small étale
site and modules on the small étale site of the underlying scheme, the direct image
`AlgebraicGeometry.SmallEtale.localizedPushforwardBaseChange` along the morphism of ringed sites
localized at `V` is the direct image `(ε_{a_V})_*` along `a_V : X ×_Y V₀ ⟶ V₀`:

`P_V ⋙ (−)|_{V₀,étale} ≅ (−)|_{(X ×_Y V₀),étale} ⋙ (ε_{a_V})_*`. -/
def localizedPushforwardBaseChangeIso :
    localizedPushforwardBaseChange B a V ⋙ objRestrictFunctor B Y.obj Y.property V ≅
      objRestrictFunctor B X.obj X.property ((smallEtaleBaseChange B a).obj V) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (objBaseChangeHom B a V)) :=
  SheafOfModules.pushforwardComp.{u}
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B V.obj.left.obj V.obj.left.property)
        (localizationEquivalence B Y.obj Y.property V)
        ((structureSheaf B Y.obj Y.property).over V)))
      (localizedStructureMapBaseChange B a V) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (sliceBaseChangeLocalizationIso B a V)
      (comparisonComp_sliceBaseChangeLocalizationIso B a V) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (smallEtaleStructureMapRing B (objBaseChangeHom B a V))
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B ((smallEtaleBaseChange B a).obj V).obj.left.obj
          ((smallEtaleBaseChange B a).obj V).obj.left.property)
        (localizationEquivalence B X.obj X.property ((smallEtaleBaseChange B a).obj V))
        ((structureSheaf B X.obj X.property).over ((smallEtaleBaseChange B a).obj V))))).symm

/-- **The derived form of the identification of `P_V` with `(ε_{a_V})_*`:** the `n`-th higher
direct image along the localized morphism, read on the small étale site of the scheme of `V`, is
the `n`-th higher direct image along `a_V` of the module read on the small étale site of
`X ×_Y V₀`:

`(R ⁿ P_V (𝓜))|_{V₀,étale} ≅ R ⁿ (ε_{a_V})_* (𝓜|_{(X ×_Y V₀),étale})`. -/
def rightDerivedLocalizedPushforwardObjIso
    (M : SheafOfModules.{u} ((structureSheaf B X.obj X.property).over
      ((smallEtaleBaseChange B a).obj V))) (n : ℕ) :
    (objRestrictFunctor B Y.obj Y.property V).obj
        (((localizedPushforwardBaseChange B a V).rightDerived n).obj M) ≅
      ((SheafOfModules.pushforward.{u}
          (smallEtaleStructureMapRing B (objBaseChangeHom B a V))).rightDerived n).obj
        ((objRestrictFunctor B X.obj X.property ((smallEtaleBaseChange B a).obj V)).obj M) :=
  haveI hacyc : Stacks.RightDerivedComp.acyclic
      (objRestrictFunctor B X.obj X.property ((smallEtaleBaseChange B a).obj V)) M := fun q hq ↦
    Functor.isZero_rightDerived_of_exactFunctor _
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩) M q hq
  ((Functor.rightDerivedCompIso (localizedPushforwardBaseChange B a V)
      (objRestrictFunctor B Y.obj Y.property V) n).app M).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (localizedPushforwardBaseChangeIso B a V) n).app M ≪≫
    Stacks.RightDerivedComp.objIso
      (objRestrictFunctor B X.obj X.property ((smallEtaleBaseChange B a).obj V))
      (injectiveResolution M) hacyc
      (SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B (objBaseChangeHom B a V))) n

end Localized

section GeneralBase

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The restriction of a higher direct image to the slice at an object with affine scheme is
quasi-coherent**, for `a` quasi-compact and separated and `𝓕` quasi-coherent on the site, in
every degree. -/
theorem
  isQuasicoherentOnSite_over_rightDerived_pushforward_of_isAffine_of_quasiCompact_of_isSeparatedHom
    [QuasiCompact (schemeHom B a)] [IsSeparated (schemeHom B a)]
    (V : SmallEtale B Y.obj Y.property)
    (hV : AlgebraicGeometry.IsAffine (objScheme B Y.obj Y.property V))
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
      V).IsQuasicoherentOnSite := by
  have := hV
  have : QuasiCompact (schemeHom B (objBaseChangeHom B a V)) :=
    quasiCompact_smallEtaleBaseChange_proj B a V
  have : IsSeparated (schemeHom B (objBaseChangeHom B a V)) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback V.obj.hom a).map B.inclusion).flip inferInstance
  have hqcW : ((objRestrictFunctor B X.obj X.property
      ((smallEtaleBaseChange B a).obj V)).obj
        (𝓕.over ((smallEtaleBaseChange B a).obj V))).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_objRestrict_iff B X.obj X.property
      ((smallEtaleBaseChange B a).obj V) 𝓕).2
      (Stacks.SheafOfModules.isQuasicoherent_over 𝓕 h𝓕 _)
  have hqc := (isQuasicoherentOnSite_iff_isCartesianOnAffines B
      (objScheme B Y.obj Y.property V) (contains_objScheme B Y.obj Y.property V) _).2
    (isCartesianOnAffines_rightDerived_pushforward_of_isAffine_of_quasiCompact_of_isSeparatedHom
      B (objBaseChangeHom B a V) _ hqcW n)
  have hiff : ((objRestrictFunctor B Y.obj Y.property V).obj
        ((((SheafOfModules.pushforward.{u}
          (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
            V)).IsQuasicoherentOnSite ↔
      ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
          V).IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
      (localizationEquivalence B Y.obj Y.property V)
      ((structureSheaf B Y.obj Y.property).over V) _
  refine hiff.1 ?_
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((((objRestrictFunctor B Y.obj Y.property V).mapIso
        (rightDerivedPushforwardOverFunctorObjIso B a V 𝓕 n)) ≪≫
      rightDerivedLocalizedPushforwardObjIso B a V
        (𝓕.over ((smallEtaleBaseChange B a).obj V)) n).symm) hqc

/-- **The étale clause of [Stacks, Tag 071N] above degree zero, for a quasi-compact separated
`a`:** for `𝓕` quasi-coherent on the site, `R ⁿ (ε_a)_*(𝓕)` is cartesian between the affine
objects of `Y_étale` in every degree. -/
theorem isCartesianOnAffines_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom
    [QuasiCompact (schemeHom B a)] [IsSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) :=
  isCartesianOnAffines_rightDerived_pushforward_of_forall_affineOpens B a 𝓕 n fun U ↦
  isQuasicoherentOnSite_over_rightDerived_pushforward_of_isAffine_of_quasiCompact_of_isSeparatedHom
      B a ((opensToSmallEtale B Y.obj Y.property).obj (U : Y.obj.Opens)) U.2 𝓕 h𝓕 n

/-- **The higher direct images along `ε_a` of a module quasi-coherent on the site are
quasi-coherent on the site**, for `a` quasi-compact and separated, in every degree. -/
theorem isQuasicoherentOnSite_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom
    [QuasiCompact (schemeHom B a)] [IsSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffines B Y.obj Y.property _).2
    (isCartesianOnAffines_rightDerived_pushforward_of_quasiCompact_of_isSeparatedHom B a 𝓕 h𝓕 n)

end GeneralBase

end AlgebraicGeometry.SmallEtale

end
