module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceSchemePullback

/-!
# The transition of a module on a slice of the total Zariski site

Let `X` be a simplicial scheme, `(a, W)` an object of its total Zariski site and `φ : b ⟶ a` a
map of simplicial degrees. The slice of the total Zariski site at `(a, W)` carries, for each
such `φ`, a degree-`φ` component functor
`AlgebraicGeometry.SimplicialScheme.sliceComponentModuleAt`, landing on the slice of the
open-set site of `X_b` at `(X φ)⁻¹W`; and it carries the degree-`a` component functor
`AlgebraicGeometry.SimplicialScheme.sliceComponentModule`, landing on the slice of the open-set
site of `X_a` at `W`. The arrows of the slice lying over `φ`
(`AlgebraicGeometry.SimplicialScheme.sliceTransitionLevelNatTrans`) relate the two: restricting
along them gives a morphism `M_a ⟶ (X φ|)_* M_φ`, and its mate under the localized pullback of
`AlgebraicGeometry.SimplicialScheme.sliceSchemePullback` is the transition
`(X φ|)^* M_a ⟶ M_φ`.

This is the transition of Stacks 09WF read on a slice of the total Zariski site, which is what
both directions of Stacks 0D7M run the colimit mechanism on. For `M` the restriction of a module
on the whole total site it is the localization of the transition of
`AlgebraicGeometry.SimplicialScheme.componentModuleTransition`; that identification is the
sibling module `ZariskiSliceTransitionLocalization`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.sliceSchemePushforward`: the direct image of sheaves of
  modules along `X φ`, localized at `W`; the right adjoint of `sliceSchemePullback`.
* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleDirectTransition`: the direct form
  `M_a ⟶ (X φ|)_* M_φ` of the transition on the slice, as a natural transformation.
* `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition` and
  `.sliceComponentModuleTransitionNatTrans`: its mate `(X φ|)^* M_a ⟶ M_φ`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.sliceTransitionStructureHom_eq`: the structure map that the
  comparison of the degree-`a` and degree-`φ` restrictions on the slice produces is the structure
  map of the composite `(X φ|)_* ∘ (-)_φ`.
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceComponentModuleTransition_unit`: **the transition
  on the slice is invertible on the structure sheaf.**
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceComponentModuleTransition_of_presentation`: it is
  therefore invertible on every module on the slice admitting a global presentation.

## Implementation notes

The construction copies `AlgebraicGeometry.SimplicialScheme.componentModuleDirectTransition`, one
localization down: `SheafOfModules.pushforwardNatTrans` turns the arrows over `φ` into a
comparison of restrictions, `SheafOfModules.pushforwardCongr` rewrites the structure map it
produces into the structure map of the composite, and `SheafOfModules.pushforwardComp` splits
that composite. The only thing with content is `sliceTransitionStructureHom_eq`, and it is the
same statement as `transitionStructureHom_eq` with every site replaced by its slice: on sections
over an object `V ≤ W` of the slice of the degree-`a` site both sides are the map `X φ` induces
on sections over `V`, one spelled as the restriction `appLE` of `𝒪_X` along the arrow over `φ`
and the other as `(X φ)^♯`, and `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` identifies them.

Continuity of the localized inverse image `Over.post (Opens.map (X φ))` is found by instance
search, but continuity of its composite with the degree-`φ` component inclusion is not — the
intermediate topology has to be named — so that composite is given as an instance here.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) {a b : SimplexCategoryᵒᵖ} (W : Opens ↥(X.obj a))
  (φ : b ⟶ a)

/-- The localized inverse image `V ↦ (X φ)⁻¹V` from the slice of the degree-`a` site at `W` to
the slice of the degree-`b` site at `(X φ)⁻¹W`, as a continuous functor of sites. -/
public instance slicePreimageFunctor_isContinuous :
    (Over.post (X := W) (Opens.map (X.map φ).base)).IsContinuous
      ((Opens.grothendieckTopology ↥(X.obj a)).over W)
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ)) :=
  inferInstance

/-- Taking the localized inverse image along `X φ` and then including the degree-`b` component of
the slice at `(a, W)` is a continuous functor: the intermediate topology is the one of the slice
of the degree-`b` site at `(X φ)⁻¹W`. -/
public instance slicePreimageCompComponentFunctorAt_isContinuous :
    (Over.post (X := W) (Opens.map (X.map φ).base) ⋙ sliceComponentFunctorAt X W φ).IsContinuous
      ((Opens.grothendieckTopology ↥(X.obj a)).over W)
      ((zariskiTopology X).over (sliceObj X a W)) :=
  Functor.isContinuous_comp _ _ _
    ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ)) _

/-- **The direct image of sheaves of modules along `X φ`, localized at an open `W` of `X_a`.**
The right adjoint of `AlgebraicGeometry.SimplicialScheme.sliceSchemePullback`. -/
public noncomputable abbrev sliceSchemePushforward :=
  SheafOfModules.pushforward.{u}
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- The localized pullback along `X φ` is left adjoint to the localized direct image. -/
public noncomputable abbrev sliceSchemePullbackAdj :
    sliceSchemePullback X W φ ⊣ sliceSchemePushforward X W φ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u}
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- The structure map of the composite `(X φ|)_* ∘ (-)_φ` on the slice at `(a, W)`: the localized
structure map of `X φ` followed by the structure map of the degree-`φ` component inclusion. -/
public noncomputable def sliceTransitionStructureHom :
    sliceDegreeRingSheaf X a W ⟶
      ((Over.post (X := W) (Opens.map (X.map φ).base) ⋙
          sliceComponentFunctorAt X W φ).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥(X.obj a)).over W)
        ((zariskiTopology X).over (sliceObj X a W))).obj (sliceStructureRingSheaf X a W) :=
  SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W ≫
    ((Over.post (X := W) (Opens.map (X.map φ).base)).sheafPushforwardContinuous RingCat.{u}
      ((Opens.grothendieckTopology ↥(X.obj a)).over W)
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))).map
      (sliceComponentStructureHomAt X W φ)

/-- **The structure map produced by the comparison of the degree-`a` and degree-`φ` restrictions
on the slice at `(a, W)` is the structure map of the composite `(X φ|)_* ∘ (-)_φ`.** On sections
over an object `V ≤ W` of the slice of the degree-`a` site both sides are the map `X φ` induces
on sections over `V`: on the left it is the restriction of `𝒪_X` along the arrow of the slice
lying over `φ`, on the right the localized `(X φ)^♯`, and `Scheme.Hom.appLE_eq_app` identifies
them. -/
public theorem sliceTransitionStructureHom_eq :
    SheafOfModules.overComparison (componentStructureHom X a) W ≫
        (Functor.sheafPushforwardContinuousNatTrans (sliceTransitionLevelNatTrans X W φ)
          RingCat.{u} ((Opens.grothendieckTopology ↥(X.obj a)).over W)
          ((zariskiTopology X).over (sliceObj X a W))).app
          (sliceStructureRingSheaf X a W) =
      sliceTransitionStructureHom X W φ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have hl : (SheafOfModules.overComparison (componentStructureHom X a) W ≫
      (Functor.sheafPushforwardContinuousNatTrans (sliceTransitionLevelNatTrans X W φ)
        RingCat.{u} ((Opens.grothendieckTopology ↥(X.obj a)).over W)
        ((zariskiTopology X).over (sliceObj X a W))).app
        (sliceStructureRingSheaf X a W)).hom.app V =
      (forget₂ CommRingCat RingCat.{u}).map ((structurePresheaf X).map
        (SimplicialSheafSystem.transitionHom (X := zariskiSpace X) φ V.unop.left).op) := rfl
  have hr : (sliceTransitionStructureHom X W φ).hom.app V =
      (forget₂ CommRingCat RingCat.{u}).map ((X.map φ).c.app (op V.unop.left)) := rfl
  refine hl.trans (Eq.trans ?_ hr.symm)
  exact congrArg ((forget₂ CommRingCat RingCat.{u}).map)
    (Scheme.Hom.appLE_eq_app (X.map φ) (U := V.unop.left))

/-- **The direct form of the transition of Stacks 09WF on a slice of the total Zariski site.**
For a map of simplicial degrees `φ : b ⟶ a` the restriction maps of a sheaf of modules on the
slice at `(a, W)` along the arrows of the slice lying over `φ` give a morphism
`M_a ⟶ (X φ|)_* M_φ`, natural in `M`. -/
public noncomputable def sliceComponentModuleDirectTransition :
    sliceComponentModule X a W ⟶
      sliceComponentModuleAt X W φ ⋙ sliceSchemePushforward X W φ :=
  SheafOfModules.pushforwardNatTrans.{u}
      (J := (Opens.grothendieckTopology ↥(X.obj a)).over W)
      (K := (zariskiTopology X).over (sliceObj X a W))
      (SheafOfModules.overComparison (componentStructureHom X a) W)
      (sliceTransitionLevelNatTrans X W φ) ≫
    (SheafOfModules.pushforwardCongr.{u}
        (J := (Opens.grothendieckTopology ↥(X.obj a)).over W)
        (K := (zariskiTopology X).over (sliceObj X a W))
        (sliceTransitionStructureHom_eq X W φ)).hom ≫
      (SheafOfModules.pushforwardComp.{u}
        (K' := (zariskiTopology X).over (sliceObj X a W))
        (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)
        (sliceComponentStructureHomAt X W φ)).inv

/-- On sections over an object `V ≤ W` of the slice of the degree-`a` site, the direct transition
on the slice is the restriction map of `M` along the arrow of the slice lying over `φ`. -/
public theorem sliceComponentModuleDirectTransition_app_val_app
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W))
    (V : (Over W)ᵒᵖ) (x : ((sliceComponentModule X a W).obj M).val.obj V) :
    ((sliceComponentModuleDirectTransition X W φ).app M).val.app V x =
      M.val.map ((sliceTransitionLevelNatTrans X W φ).app V.unop).op x :=
  rfl

/-- **The transition of Stacks 09WF on a slice of the total Zariski site.** The mate
`(X φ|)^* M_a ⟶ M_φ` of the direct transition under the adjunction of the localized pullback
along `X φ`. -/
public noncomputable def sliceComponentModuleTransition
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W)) :
    (sliceSchemePullback X W φ).obj ((sliceComponentModule X a W).obj M) ⟶
      (sliceComponentModuleAt X W φ).obj M :=
  ((sliceSchemePullbackAdj X W φ).homEquiv _ _).symm
    ((sliceComponentModuleDirectTransition X W φ).app M)

/-- **The transition of Stacks 09WF on the slice, as a natural transformation.** The mate of
`sliceComponentModuleDirectTransition` is natural in the module, because the direct transition
is. -/
public noncomputable def sliceComponentModuleTransitionNatTrans :
    sliceComponentModule X a W ⋙ sliceSchemePullback X W φ ⟶ sliceComponentModuleAt X W φ where
  app M := sliceComponentModuleTransition X W φ M
  naturality M N f :=
    ((Adjunction.homEquiv_naturality_left_symm (sliceSchemePullbackAdj X W φ)
        ((sliceComponentModule X a W).map f)
        ((sliceComponentModuleDirectTransition X W φ).app N)).symm.trans
      (congrArg (fun t => ((sliceSchemePullbackAdj X W φ).homEquiv
            ((sliceComponentModule X a W).obj M)
            ((sliceComponentModuleAt X W φ).obj N)).symm t)
        ((sliceComponentModuleDirectTransition X W φ).naturality f))).trans
      (Adjunction.homEquiv_naturality_right_symm (sliceSchemePullbackAdj X W φ)
        ((sliceComponentModuleDirectTransition X W φ).app M)
        ((sliceComponentModuleAt X W φ).map f))

/-- The component of `sliceComponentModuleTransitionNatTrans X W φ` at `M` is
`sliceComponentModuleTransition X W φ M`. -/
@[simp] public theorem sliceComponentModuleTransitionNatTrans_app
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W)) :
    (sliceComponentModuleTransitionNatTrans X W φ).app M =
      sliceComponentModuleTransition X W φ M := rfl

/-! ### The transition on the structure sheaf -/

/-- The structure map of the degree-`φ` component inclusion of the slice at `(a, W)`, as an
isomorphism: its two factors are the structure map of the degree-`b` component inclusion of the
slice at `(b, (X φ)⁻¹W)` and the comparison of the two readings of `𝒪_X` restricted along the
arrow over `φ`, and both are invertible. -/
public noncomputable def sliceComponentStructureHomAtIso :
    sliceDegreeRingSheaf X b (slicePreimage X W φ) ≅
      ((sliceComponentFunctorAt X W φ).sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
          (((zariskiRingedTopos X).J).over (sliceObj X a W))).obj
        (sliceStructureRingSheaf X a W) :=
  asIso (SheafOfModules.overComparison (componentStructureHom X b) (slicePreimage X W φ)) ≪≫
    Functor.mapIso ((sliceComponentFunctor X b (slicePreimage X W φ)).sheafPushforwardContinuous
        RingCat.{u} ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ))
        (((zariskiRingedTopos X).J).over (sliceObj X b (slicePreimage X W φ))))
      (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)
        (sliceTransitionHom X W φ)).symm

/-- The structure map `sliceComponentStructureHomAt X W φ` is an isomorphism, being the forward
map of `sliceComponentStructureHomAtIso X W φ`. -/
public instance isIso_sliceComponentStructureHomAt :
    IsIso (sliceComponentStructureHomAt X W φ) := by
  have h : sliceComponentStructureHomAt X W φ = (sliceComponentStructureHomAtIso X W φ).hom := rfl
  rw [h]
  infer_instance

/-- **The degree-`a` component of `𝒪_X` on the slice at `(a, W)` is the structure sheaf of the
slice of the degree-`a` site.** -/
public noncomputable def sliceComponentUnitHom :
    (SheafOfModules.unit (sliceDegreeRingSheaf X a W)) ⟶
      (sliceComponentModule X a W).obj (SheafOfModules.unit (sliceStructureRingSheaf X a W)) :=
  SheafOfModules.unitToPushforwardObjUnit
    (SheafOfModules.overComparison (componentStructureHom X a) W)

/-- The comparison `sliceComponentUnitHom X W` is an isomorphism. -/
public instance isIso_sliceComponentUnitHom : IsIso (sliceComponentUnitHom X W) :=
  isIso_unitToPushforwardObjUnit' _

/-- **The degree-`φ` component of `𝒪_X` on the slice at `(a, W)` is the structure sheaf of the
slice of the degree-`b` site at `(X φ)⁻¹W`.** -/
public noncomputable def sliceComponentUnitHomAt :
    (SheafOfModules.unit (sliceDegreeRingSheaf X b (slicePreimage X W φ))) ⟶
      (sliceComponentModuleAt X W φ).obj
        (SheafOfModules.unit (sliceStructureRingSheaf X a W)) :=
  SheafOfModules.unitToPushforwardObjUnit (sliceComponentStructureHomAt X W φ)

/-- The comparison `sliceComponentUnitHomAt X W φ` is an isomorphism. -/
public instance isIso_sliceComponentUnitHomAt : IsIso (sliceComponentUnitHomAt X W φ) :=
  isIso_unitToPushforwardObjUnit' _

/-- **The localized structure morphism of `X φ`**, read as a morphism of sheaves of modules out
of the unit object of the slice of the degree-`a` site at `W`. -/
public noncomputable def sliceTransitionUnitHom :
    (SheafOfModules.unit (sliceDegreeRingSheaf X a W)) ⟶
      (sliceSchemePushforward X W φ).obj
        (SheafOfModules.unit (sliceDegreeRingSheaf X b (slicePreimage X W φ))) :=
  SheafOfModules.unitToPushforwardObjUnit
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- **The localized pullback of the structure sheaf is the structure sheaf.** The comparison
`(X φ|)^* 𝒪_W ⟶ 𝒪_{(X φ)⁻¹W}` is an isomorphism, because the localized inverse image
`Over.post (Opens.map (X φ))` is a final functor: it is `Over.post` of a functor, and the slice
it starts from has a terminal object which it carries to a terminal object. -/
public noncomputable def sliceTransitionPullbackUnitHom :
    (sliceSchemePullback X W φ).obj (SheafOfModules.unit (sliceDegreeRingSheaf X a W)) ⟶
      (SheafOfModules.unit (sliceDegreeRingSheaf X b (slicePreimage X W φ))) :=
  SheafOfModules.pullbackObjUnitToUnit
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- The comparison `sliceTransitionPullbackUnitHom X W φ` is an isomorphism, because the localized
inverse image `Over.post (Opens.map (X φ))` is final. -/
public instance isIso_sliceTransitionPullbackUnitHom :
    IsIso (sliceTransitionPullbackUnitHom X W φ) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- **The direct transition on the slice, on the structure sheaf, is the localized structure
morphism of `X φ`**, under the identifications of the degree-`a` and degree-`φ` components of
`𝒪_X` on the slice with the structure sheaves of the two localized degree sites. -/
public theorem sliceComponentModuleDirectTransition_app_unit :
    sliceComponentUnitHom X W ≫ (sliceComponentModuleDirectTransition X W φ).app
        (SheafOfModules.unit (sliceStructureRingSheaf X a W)) =
      sliceTransitionUnitHom X W φ ≫
        (sliceSchemePushforward X W φ).map (sliceComponentUnitHomAt X W φ) := by
  ext V
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (Sheaf.hom_ext_iff.mp (sliceTransitionStructureHom_eq X W φ)) V) 1

/-- **The transition on the slice is invertible on the structure sheaf.** This is the one input
that the colimit mechanism of Stacks 0D7M asks of a slice of the total Zariski site: it is what
makes the transition invertible on free modules, hence on every module with a global
presentation. -/
public theorem isIso_sliceComponentModuleTransition_unit :
    IsIso (sliceComponentModuleTransition X W φ
      (SheafOfModules.unit (sliceStructureRingSheaf X a W))) := by
  let ea := @asIso _ _ _ _ (sliceComponentUnitHom X W) (isIso_sliceComponentUnitHom X W)
  let eb := @asIso _ _ _ _ (sliceComponentUnitHomAt X W φ) (isIso_sliceComponentUnitHomAt X W φ)
  let ep := @asIso _ _ _ _ (sliceTransitionPullbackUnitHom X W φ)
    (isIso_sliceTransitionPullbackUnitHom X W φ)
  have hdir : (sliceComponentModuleDirectTransition X W φ).app
      (SheafOfModules.unit (sliceStructureRingSheaf X a W)) =
      ea.inv ≫ (sliceTransitionUnitHom X W φ ≫
          (sliceSchemePushforward X W φ).map (sliceComponentUnitHomAt X W φ)) :=
    (ea.inv_hom_id_assoc _).symm.trans
      (congrArg (fun t => ea.inv ≫ t) (sliceComponentModuleDirectTransition_app_unit X W φ))
  have key : sliceComponentModuleTransition X W φ
        (SheafOfModules.unit (sliceStructureRingSheaf X a W)) =
      ((sliceSchemePullback X W φ).mapIso ea).inv ≫ (ep ≪≫ eb).hom :=
    (congrArg (fun t => ((sliceSchemePullbackAdj X W φ).homEquiv
          ((sliceComponentModule X a W).obj
            (SheafOfModules.unit (sliceStructureRingSheaf X a W)))
          ((sliceComponentModuleAt X W φ).obj
            (SheafOfModules.unit (sliceStructureRingSheaf X a W)))).symm t)
        hdir).trans
      ((Adjunction.homEquiv_naturality_left_symm _ ea.inv _).trans
        (congrArg (fun t => (sliceSchemePullback X W φ).map ea.inv ≫ t)
          (Adjunction.homEquiv_naturality_right_symm _ (sliceTransitionUnitHom X W φ)
            (sliceComponentUnitHomAt X W φ))))
  rw [key]
  infer_instance

/-- **The transition on the slice is invertible on a presented module.** It is a natural
transformation between two functors that preserve colimits — the degree-`a` component functor
followed by the localized pullback along `X φ`, and the degree-`φ` component functor — and it is
invertible on the structure sheaf, so it is invertible on every module exhibited as a cokernel of
a map of coproducts of copies of the structure sheaf. -/
public theorem isIso_sliceComponentModuleTransition_of_presentation
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _ (sliceStructureRingSheaf X a W))
    (P : M.Presentation) :
    IsIso (sliceComponentModuleTransition X W φ M) := by
  have h1 : PreservesColimitsOfSize.{u, u}
      (sliceComponentModule X a W ⋙ sliceSchemePullback X W φ) :=
    Limits.comp_preservesColimits _ _
  have h2 : PreservesFiniteColimits
      (sliceComponentModule X a W ⋙ sliceSchemePullback X W φ) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have h3 : PreservesFiniteColimits (sliceComponentModuleAt X W φ) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have h4 : ∀ I : Type u, Limits.PreservesColimitsOfShape (Discrete I)
      (sliceComponentModule X a W ⋙ sliceSchemePullback X W φ) := fun _ => inferInstance
  have h5 : ∀ I : Type u, Limits.PreservesColimitsOfShape (Discrete I)
      (sliceComponentModuleAt X W φ) := fun _ => inferInstance
  exact Stacks.SheafOfModules.isIso_app_of_presentation_of_unit
    (sliceComponentModuleTransitionNatTrans X W φ)
    (isIso_sliceComponentModuleTransition_unit X W φ) P

end AlgebraicGeometry.SimplicialScheme

end
