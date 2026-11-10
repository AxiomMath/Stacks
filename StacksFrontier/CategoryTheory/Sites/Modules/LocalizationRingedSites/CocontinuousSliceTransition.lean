module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationIsIso
public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.CocontinuousLocalizedMate
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransition

/-!
# Transitions of restrictions along a cocontinuous functor, localized at a slice

Let `v : X.C ⥤ Y.C` be a cocontinuous functor between the sites of two ringed sites, let `T` be a
site with a sheaf of rings `R`, and let `G : X.C ⥤ T`, `G' : Y.C ⥤ T` be continuous functors with
a transformation `τ : G ⟶ v ⋙ G'`. Restriction of sheaves along `G` and `G'` is related by a
transition `ρ_{G'} ⟶ ρ_G ⋙ v_*` into the direct image along `v` (the right Kan extension): it is
the transpose of restriction along `τ`.

For `V : X.C` the same data localize: `q = Over.post G' : Y.C/v(V) ⥤ T/G'(v(V))` and
`p = Over.post G ⋙ Over.map τ_V : X.C/V ⥤ T/G'(v(V))`, with the transformation
`p ⟶ Over.post v ⋙ q` given by `τ`. The localized transition at the restriction of `P` to
`T/G'(v(V))` is the restriction of the transition at `P` followed by the base change map of
Stacks 03EG.

## Main definitions

All declarations below are in the namespace `AlgebraicGeometry.RingedSite`.

* `cocontinuousTransitionSetCocontinuousSliceTransition`: the transition of sheaves of sets.
* `cocontinuousSiteTransitionCocontinuousSliceTransition`: the transition of modules
  `ρ_{G'} ⟶ ρ_G ⋙ f_*`, and `cocontinuousSiteTransitionPullbackCocontinuousSliceTransition` its
  transpose `f^*ρ_{G'} ⟶ ρ_G`.
* `cocontinuousSliceTransitionPullbackCocontinuousSliceTransition`: the localized transposed
  transition on the slice `T/G'(v(V))`.

## Main results

* `cocontinuousTransitionSet_slice_cocontinuousSliceTransition`: the localized transition is the
  restricted transition followed by the base change map.
* `cocontinuousLocalizedPullbackMate_comp_siteTransition_cocontinuousSliceTransition`: the
  transposed transition commutes with localization through the invertible localization mate.
* `isIso_cocontinuousSliceTransitionPullback_app_iff_cocontinuousSliceTransition`,
  `isIso_cocontinuousSiteTransitionPullback_app_of_locally_cocontinuousSliceTransition` and
  `isIso_cocontinuousSliceRight_map_of_isIso_cocontinuousSliceTransition`: the local-to-global
  steps of Stacks 0D7M, together with the case of a module with a global presentation.

## References

* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.RingedToposModules
  Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.Sheaves.RingedToposModules

section PushforwardOperations

universe w v u' v'

variable {C : Type u'} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{w}) {S : Sheaf J RingCat.{w}}
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} J K).obj O) (M : SheafOfModules.{w} O)
  (P : Sheaf J (Type w) ⥤ Type w) [PreservesFiniteProducts P]

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})] in
/-- The addition of a module transported along `G^s ⋙ P` is the addition of its pushforward
along `G` and a ring map `φ`, transported along `P`. -/
theorem moduleAddObj_sheafOfModulesPushforward_cocontinuousSliceTransition
    (a b : P.obj (Sheaf.moduleSheaf S ((SheafOfModules.pushforward.{w} φ).obj M))) :
    Sheaf.moduleAddObj O M (G.sheafPushforwardContinuous (Type w) J K ⋙ P) a b =
      Sheaf.moduleAddObj S ((SheafOfModules.pushforward.{w} φ).obj M) P a b := by
  change _ = Sheaf.moduleAddObj S
    ((SheafOfModules.restrictScalars φ).obj ((restrictionModules J K G O).obj M)) P a b
  exact moduleAddObj_restrictionModules J K G O M P _ _

/-- The scalar action of a module transported along `G^s ⋙ P`, at a scalar coming from `S`
along `φ`, is the action of its pushforward along `G` and `φ`, transported along `P`. -/
theorem moduleSMulObj_sheafOfModulesPushforward_cocontinuousSliceTransition
    (r : P.obj (Sheaf.ringSheaf S))
    (a : P.obj (Sheaf.moduleSheaf S ((SheafOfModules.pushforward.{w} φ).obj M))) :
    Sheaf.moduleSMulObj O M (G.sheafPushforwardContinuous (Type w) J K ⋙ P)
        (P.map ((sheafCompose J (forget RingCat.{w})).map φ) r) a =
      Sheaf.moduleSMulObj S ((SheafOfModules.pushforward.{w} φ).obj M) P r a := by
  change _ = Sheaf.moduleSMulObj S
    ((SheafOfModules.restrictScalars φ).obj ((restrictionModules J K G O).obj M)) P r a
  exact (moduleSMulObj_restrictionModules J K G O M P _ _).trans
    (moduleSMulObj_restrictScalars φ ((restrictionModules J K G O).obj M) P r a).symm

end PushforwardOperations

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

section SetTransition

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T}
  {X Y : RingedSite.{u, u, u}} (v : X.C ⥤ Y.C) [hv : v.IsCocontinuous X.J Y.J]
  {G : X.C ⥤ T} {G' : Y.C ⥤ T} [hG : G.IsContinuous X.J JT] [hG' : G'.IsContinuous Y.J JT]
  (τ : G ⟶ v ⋙ G')

/-- **The transition of restrictions along a cocontinuous functor**, for sheaves of sets:
`G'^s P ⟶ v_*(G^s P)`, the transpose under `v^p ⊣ v_*` of restriction of `P` along `τ`. -/
noncomputable def cocontinuousTransitionSetCocontinuousSliceTransition :
    G'.sheafPushforwardContinuous (Type u) Y.J JT ⟶
      G.sheafPushforwardContinuous (Type u) X.J JT ⋙
        (cocontinuousToposHomCocontinuousMorphism v hv).pushforward where
  app P := ⟨(v.op.ranAdjunction (Type u)).homEquiv _ _
    (Functor.whiskerRight (NatTrans.op τ) P.obj)⟩
  naturality P Q f := by
    apply (sheafToPresheaf _ _).map_injective
    change Functor.whiskerLeft G'.op f.hom ≫ _ =
      _ ≫ v.op.ran.map (Functor.whiskerLeft G.op f.hom)
    apply Adjunction.homEquiv_naturality_left_square
    exact NatTrans.ext (funext fun _ => (f.hom.naturality _).symm)

/-- On underlying presheaves the transition is the transpose of restriction along `τ`. -/
theorem cocontinuousTransitionSet_app_hom_cocontinuousSliceTransition (P : Sheaf JT (Type u)) :
    ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).app P).hom =
      (v.op.ranAdjunction (Type u)).homEquiv _ _ (Functor.whiskerRight (NatTrans.op τ) P.obj) :=
  rfl

variable (V : X.C)

/-- The transformation `p ⟶ Over.post v ⋙ q` of functors `X.C/V ⥤ T/G'(v(V))` induced by
`τ : G ⟶ v ⋙ G'`, where `p = Over.post G ⋙ Over.map τ_V` and `q = Over.post G'`. -/
@[simps]
def cocontinuousSliceNatTransCocontinuousSliceTransition :
    Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V) ⟶
      Over.post (X := V) v ⋙ Over.post (X := v.obj V) G' where
  app Z := Over.homMk (τ.app Z.left) (τ.naturality Z.hom).symm
  naturality _ _ g := Over.OverMorphism.ext (τ.naturality g.left)

omit hv hG' in
/-- `p = Over.post G ⋙ Over.map τ_V` is continuous for the localized topologies. -/
theorem isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition :
    (Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V)).IsContinuous (X.over V).J
      (JT.over (G'.obj (v.obj V))) :=
  have := Functor.isContinuous_overPost_of_isContinuous X.J JT G V
  Functor.isContinuous_comp _ _ (X.J.over V) (JT.over (G.obj V)) (JT.over (G'.obj (v.obj V)))

/-- **The localized transition is the restricted transition followed by base change.** At the
restriction of a sheaf `P` to `T/G'(v(V))`, the transition of the localized data is the
restriction to `Y.C/v(V)` of the transition at `P` followed by the base change map
`j_{v(V)}^{-1}(v_* G^s P) ⟶ v'_*(j_V^{-1} G^s P)` of Stacks 03EG. -/
theorem cocontinuousTransitionSet_slice_cocontinuousSliceTransition (P : Sheaf JT (Type u)) :
    (cocontinuousTransitionSetCocontinuousSliceTransition (X := X.over V) (Y := Y.over (v.obj V))
        (Over.post (X := V) v)
        (hv := isCocontinuous_overPost_over_cocontinuousMorphism v V)
        (hG := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition v τ V)
        (hG' := Hom.isContinuous_sliceLeft (v.obj V))
        (cocontinuousSliceNatTransCocontinuousSliceTransition v τ V)).app
        (((Over.forget (G'.obj (v.obj V))).sheafPushforwardContinuous (Type u)
          (JT.over (G'.obj (v.obj V))) JT).obj P) =
      ((Over.forget (v.obj V)).sheafPushforwardContinuous (Type u) (Y.J.over (v.obj V)) Y.J).map
          ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).app P) ≫
        (Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J) (K := Y.J)).app
          ((G.sheafPushforwardContinuous (Type u) X.J JT).obj P) := by
  refine Sheaf.hom_ext ((Equiv.injective (((Over.post (X := V) v).op.ranAdjunction
    (Type u)).homEquiv _ _).symm) ?_)
  refine ((Equiv.symm_apply_apply _ _).trans ?_).trans
    (Functor.overPostRanBaseChange_homEquiv_symm_cocontinuousBaseChange v V
      ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).app P).hom).symm
  rw [cocontinuousTransitionSet_app_hom_cocontinuousSliceTransition]
  exact (congrArg ((Functor.whiskeringLeft (Over V)ᵒᵖ X.Cᵒᵖ (Type u)).obj (Over.forget V).op).map
    (((v.op.ranAdjunction (Type u)).homEquiv
      ((G'.sheafPushforwardContinuous (Type u) Y.J JT).obj P).obj
      ((sheafToPresheaf X.J (Type u)).obj ((G.sheafPushforwardContinuous (Type u) X.J JT).obj
        P))).symm_apply_apply (Functor.whiskerRight (NatTrans.op τ) P.obj))).symm

end SetTransition

section ModuleTransition

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
  {X Y : RingedSite.{u, u, u}} (v : X.C ⥤ Y.C) [hv : v.IsCocontinuous X.J Y.J]
  (fsharp : Y.O ⟶
    (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O)
  {G : X.C ⥤ T} {G' : Y.C ⥤ T} [hG : G.IsContinuous X.J JT] [hG' : G'.IsContinuous Y.J JT]
  (τ : G ⟶ v ⋙ G')
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⟶
    (G.sheafPushforwardContinuous RingCat.{u} X.J JT).obj R)
  (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶
    (G'.sheafPushforwardContinuous RingCat.{u} Y.J JT).obj R)

/-- The compatibility of the ring maps `O_X ⟶ G^s R`, `O_Y ⟶ G'^s R` with the structure map
`O_Y ⟶ v_* O_X` and with `τ`, on underlying sheaves of sets: both ways of mapping `O_Y` to
`v_*(G^s R)` agree. -/
abbrev CocontinuousRingCompatibleCocontinuousSliceTransition : Prop :=
  (sheafCompose Y.J (forget RingCat.{u})).map ψ' ≫
      (cocontinuousTransitionSetCocontinuousSliceTransition v τ).app (Sheaf.ringSheaf.{u, u, u} R) =
    (sheafCompose Y.J (forget RingCat.{u})).map
        (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp).fSharpRing ≫
      (pushforwardRingSheafIso (cocontinuousToposHomCocontinuousMorphism v hv)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ≫
        (cocontinuousToposHomCocontinuousMorphism v hv).pushforward.map
          ((sheafCompose X.J (forget RingCat.{u})).map ψ)

/-- **The transition of restrictions of modules along a cocontinuous functor**, at one module:
`ρ_{G'}M ⟶ f_*(ρ_G M)`, `f` the morphism of ringed topoi given by `v` and `fsharp`. On
underlying sheaves of sets it is the transition of sheaves of sets. -/
noncomputable def cocontinuousSiteTransitionAppCocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (SheafOfModules.pushforward.{u} (F := G') ψ').obj M ⟶
      (RingedToposHom.pushforwardModules
          (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)).obj
        ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) :=
  ofSheafHom.{u, u, u} ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).app
      (Sheaf.moduleSheaf.{u, u, u} R M))
    (fun Z x y => by
      have h1 : Sheaf.moduleAddObj R M
          (G'.sheafPushforwardContinuous (Type u) Y.J JT ⋙ Sheaf.sectionsFunctor Y.J Z) x y =
            x + y :=
        Sheaf.sectionsFunctor_map_moduleAddHom R M _ x y
      have key := Sheaf.moduleAddObj_naturality R M
        (Functor.whiskerRight (cocontinuousTransitionSetCocontinuousSliceTransition v τ)
          (Sheaf.sectionsFunctor Y.J Z)) x y
      rw [h1] at key
      refine key.trans (Eq.trans
        (moduleAddObj_sheafOfModulesPushforward_cocontinuousSliceTransition X.J JT G R ψ M
          ((cocontinuousToposHomCocontinuousMorphism v hv).pushforward ⋙
            Sheaf.sectionsFunctor Y.J Z) _ _) ?_)
      exact ((cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp).pushforwardModules_add
        ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) Z _ _).symm)
    (fun Z r x => by
      have h1 : Sheaf.moduleSMulObj R M
          (G'.sheafPushforwardContinuous (Type u) Y.J JT ⋙ Sheaf.sectionsFunctor Y.J Z)
          ((Sheaf.sectionsFunctor Y.J Z).map ((sheafCompose Y.J (forget RingCat.{u})).map ψ') r)
            x = r • x :=
        (moduleSMulObj_sheafOfModulesPushforward_cocontinuousSliceTransition Y.J JT G' R ψ' M
          (Sheaf.sectionsFunctor Y.J Z) r x).trans
          (Sheaf.sectionsFunctor_map_moduleSMulHom _ _ Z r x)
      have key := Sheaf.moduleSMulObj_naturality R M
        (Functor.whiskerRight (cocontinuousTransitionSetCocontinuousSliceTransition v τ)
          (Sheaf.sectionsFunctor Y.J Z))
        ((Sheaf.sectionsFunctor Y.J Z).map ((sheafCompose Y.J (forget RingCat.{u})).map ψ') r) x
      rw [h1] at key
      have hr := congrArg (fun m => (Sheaf.sectionsFunctor Y.J Z).map m r) hτ
      refine key.trans ?_
      refine (congrArg (fun s => Sheaf.moduleSMulObj R M
        ((G.sheafPushforwardContinuous (Type u) X.J JT ⋙
          (cocontinuousToposHomCocontinuousMorphism v hv).pushforward) ⋙
          Sheaf.sectionsFunctor Y.J Z) s
        ((Sheaf.sectionsFunctor Y.J Z).map
          ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).app
          (Sheaf.moduleSheaf.{u, u, u} R M)) x)) hr).trans ?_
      refine (moduleSMulObj_sheafOfModulesPushforward_cocontinuousSliceTransition X.J JT G R ψ M
        ((cocontinuousToposHomCocontinuousMorphism v hv).pushforward ⋙
          Sheaf.sectionsFunctor Y.J Z) _ _).trans ?_
      exact ((cocontinuousRingedToposHomCocontinuousMorphism v hv
          fsharp).pushforwardModules_smul_pushforward
        ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) Z r _).symm)

/-- **The transition of restrictions of modules along a cocontinuous functor**:
`ρ_{G'} ⟶ ρ_G ⋙ f_*`, `f` the morphism of ringed topoi given by `v` and `fsharp`. -/
noncomputable def cocontinuousSiteTransitionCocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ') :
    SheafOfModules.pushforward.{u} (F := G') ψ' ⟶
      SheafOfModules.pushforward.{u} (F := G) ψ ⋙
        RingedToposHom.pushforwardModules.{u, u, u, u, u, u}
          (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp) where
  app M := cocontinuousSiteTransitionAppCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ M
  naturality M N g := by
    refine hom_ext_moduleSheafFunctor
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ?_
    refine Sheaf.hom_ext_sections (J := Y.J) fun Z x => ?_
    exact congrArg (fun t => (Sheaf.sectionsFunctor Y.J Z).map t x)
      ((cocontinuousTransitionSetCocontinuousSliceTransition v τ).naturality
        ((Sheaf.moduleSheafFunctor.{u, u, u} R).map g))

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The transpose of the transition along `f^* ⊣ f_*`: the transformation
`f^*(ρ_{G'}M) ⟶ ρ_G M`. -/
noncomputable def cocontinuousSiteTransitionPullbackCocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ') :
    SheafOfModules.pushforward.{u} (F := G') ψ' ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
          (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp).toModulesHom ⟶
      SheafOfModules.pushforward.{u} (F := G) ψ :=
  Functor.whiskerRight
      (cocontinuousSiteTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)).counit ≫
    (Functor.rightUnitor _).hom

/-- The component of the transposed transition is the transpose of the component. -/
theorem cocontinuousSiteTransitionPullback_app_cocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app M =
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)).homEquiv _ _).symm
          ((cocontinuousSiteTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app M) := by
  rw [Adjunction.homEquiv_counit]
  simp [cocontinuousSiteTransitionPullbackCocontinuousSliceTransition]

end Pullback

section Slice

variable (V : X.C)

/-- The ring map `O_{X/V} ⟶ p^s(R|_{G'(v(V))})` obtained by restricting `ψ`. -/
noncomputable abbrev cocontinuousSliceRingMapRightCocontinuousSliceTransition :
    haveI := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition (JT := JT) v τ V
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.over V).J) (X.over V).O) ⟶
      ((Over.post (X := V) G ⋙
          Over.map (Y := G'.obj (v.obj V)) (τ.app V)).sheafPushforwardContinuous
        RingCat.{u} (X.over V).J (JT.over (G'.obj (v.obj V)))).obj
          (Hom.sliceRing (G' := G') R (v.obj V)) :=
  (X.J.overPullback RingCat.{u} V).map ψ

/-- The ring compatibility localizes: the restricted ring maps are compatible with the localized
morphism of ringed topoi and the localized transformation induced by `τ`. -/
theorem cocontinuousRingCompatible_localized_cocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ') :
    CocontinuousRingCompatibleCocontinuousSliceTransition (X := X.over V) (Y := Y.over (v.obj V))
      (hv := isCocontinuous_overPost_over_cocontinuousMorphism v V)
      (hG := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition v τ V)
      (hG' := Hom.isContinuous_sliceLeft (v.obj V)) (Hom.sliceRing (G' := G') R (v.obj V))
      (Over.post (X := V) v) (localizedCocontinuousFSharpCocontinuousMorphism v V fsharp)
      (cocontinuousSliceNatTransCocontinuousSliceTransition v τ V)
      (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)
      (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ') := by
  refine Sheaf.hom_ext_sections fun Z r => ?_
  have h1 := congrArg (fun m => (Sheaf.sectionsFunctor _ Z).map m
      ((Sheaf.sectionsFunctor _ Z).map ((sheafCompose _ (forget RingCat.{u})).map
        (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')) r))
    (cocontinuousTransitionSet_slice_cocontinuousSliceTransition v τ V
      (Sheaf.ringSheaf.{u, u, u} R))
  have h2 := congrArg (fun m => (Sheaf.sectionsFunctor Y.J (Opposite.op Z.unop.left)).map m r) hτ
  have h3 := congrArg (fun m => (Sheaf.sectionsFunctor _ Z).map m r)
    (forgetFSharp_localizedCocontinuousRingedToposHom_cocontinuousMorphism v V fsharp)
  have h4 := congrArg (fun m => (Sheaf.sectionsFunctor _ Z).map m
      ((Sheaf.sectionsFunctor Y.J (Opposite.op Z.unop.left)).map
        ((sheafCompose Y.J (forget CommRingCat.{u})).map fsharp) r))
    ((Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J)
      (K := Y.J)).naturality
      ((sheafCompose X.J (forget RingCat.{u})).map ψ))
  refine h1.trans ?_
  refine (congrArg (fun y => (Sheaf.sectionsFunctor _ Z).map
    ((Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J) (K := Y.J)).app
      ((G.sheafPushforwardContinuous (Type u) X.J JT).obj (Sheaf.ringSheaf.{u, u, u} R))) y)
    h2).trans ?_
  refine h4.trans ?_
  exact congrArg (fun y => (Sheaf.sectionsFunctor _ Z).map
    ((Over.post (X := V) v).sheafPushforwardCocontinuous (Type u) (X.J.over V)
      (Y.J.over (v.obj V)) |>.map ((X.J.overPullback (Type u) V).map
        ((sheafCompose X.J (forget RingCat.{u})).map ψ))) y) h3.symm

/-- **The localized transition** `q^*N ⟶ f'_*(p^*N)` of modules on the slice `T/G'(v(V))`,
`f'` the localized morphism of ringed topoi. -/
noncomputable abbrev cocontinuousSliceTransitionCocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ') :=
  cocontinuousSiteTransitionCocontinuousSliceTransition (X := X.over V) (Y := Y.over (v.obj V))
    (hv := isCocontinuous_overPost_over_cocontinuousMorphism v V)
    (hG := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition v τ V)
    (hG' := Hom.isContinuous_sliceLeft (v.obj V)) (Hom.sliceRing (G' := G') R (v.obj V))
    (Over.post (X := V) v) (localizedCocontinuousFSharpCocontinuousMorphism v V fsharp)
    (cocontinuousSliceNatTransCocontinuousSliceTransition v τ V)
    (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)
    (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')
    (cocontinuousRingCompatible_localized_cocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ)

omit hv hG' in
/-- Restricting `ρ_G M` to `X.C/V` is restricting `M|_{G'(v(V))}` along `p`, on the nose. -/
theorem cocontinuousSliceRight_obj_restriction_cocontinuousSliceTransition
    (M : SheafOfModules.{u} R) :
    haveI := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition (JT := JT) v τ V
    (SheafOfModules.pushforward.{u}
        (F := Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V))
        (J := (X.over V).J) (K := JT.over (G'.obj (v.obj V)))
        (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)).obj
      ((restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V))) R).obj
        M) =
    (X.overRestrictionModules V).obj ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) :=
  rfl

/-- The base change square of sheaves of modules for the localization at `V` of the morphism
of ringed topoi given by `v`. -/
noncomputable abbrev cocontinuousBaseChangeModulesCocontinuousSliceTransition :=
  baseChangeModulesCocontinuousLocalizedMate V (v.obj V)
    (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)
    (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp)
    (Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J) (K := Y.J))
    (forgetFSharp_localizedCocontinuousRingedToposHom_cocontinuousMorphism v V fsharp)

/-- On sections, the localized transition at `M|_{G'(v(V))}` is the restriction of the
transition at `M` followed by the base change map. -/
theorem cocontinuousSliceTransition_app_restriction_cocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (cocontinuousSliceTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ).app
          ((restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V)))
            R).obj M) ≫
        (RingedToposHom.pushforwardModules.{u, u, u, u, u, u}
          (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp)).map
          (eqToHom
            (cocontinuousSliceRight_obj_restriction_cocontinuousSliceTransition R v τ ψ V M)) =
      eqToHom (Hom.sliceLeft_obj_restriction (G' := G') R (v.obj V) ψ' M) ≫
        (Y.overRestrictionModules (v.obj V)).map
          ((cocontinuousSiteTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app M) ≫
        (cocontinuousBaseChangeModulesCocontinuousSliceTransition v fsharp V).app
          ((SheafOfModules.pushforward.{u} (F := G) ψ).obj M) := by
  rw [eqToHom_map]
  apply hom_ext_moduleSheafFunctor
  refine Sheaf.hom_ext_sections fun W x => ?_
  exact congrArg (fun m => (Sheaf.sectionsFunctor _ W).map m x)
    (cocontinuousTransitionSet_slice_cocontinuousSliceTransition v τ V
      (Sheaf.moduleSheaf.{u, u, u} R M))

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The localization mate `f'^*(N|_{v(V)}) ⟶ (f^*N)|_V` of the morphism of ringed topoi given by
`v`. -/
noncomputable abbrev cocontinuousLocalizedPullbackMateCocontinuousSliceTransition :=
  baseChangePullbackMateCocontinuousLocalizedMate V (v.obj V)
    (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)
    (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp)
    (Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J) (K := Y.J))
    (forgetFSharp_localizedCocontinuousRingedToposHom_cocontinuousMorphism v V fsharp)

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The localization mate of the morphism given by a cocontinuous functor is invertible.** -/
theorem isIso_cocontinuousLocalizedPullbackMate_cocontinuousSliceTransition :
    IsIso (cocontinuousLocalizedPullbackMateCocontinuousSliceTransition v fsharp V) :=
  isIso_baseChangePullbackMate_cocontinuousLocalizedMate _ _ _ _ _ _
    (Functor.isIso_mateEquiv_overPostSheafBaseChange_cocontinuousBaseChange v V)

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The transition commutes with localization** (the compatibility in the proof of
Stacks 0D7M, case of a cocontinuous functor). The localization mate followed by the restriction
of the transposed transition is the transposed localized transition. -/
theorem cocontinuousLocalizedPullbackMate_comp_siteTransition_cocontinuousSliceTransition
    (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ')
    (M : SheafOfModules.{u} R) :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
          (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp).toModulesHom).map
        (eqToHom (Hom.sliceLeft_obj_restriction (G' := G') R (v.obj V) ψ' M)) ≫
      (cocontinuousLocalizedPullbackMateCocontinuousSliceTransition v fsharp V).app
          ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M) ≫
        (X.overRestrictionModules V).map
          (((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
            (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp)).homEquiv _ _).symm
              ((cocontinuousSiteTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
                M)) =
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp)).homEquiv _ _).symm
          ((cocontinuousSliceTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ).app
            ((restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V)))
              R).obj M)) ≫
        eqToHom
          (cocontinuousSliceRight_obj_restriction_cocontinuousSliceTransition R v τ ψ V M) := by
  have h := Stacks.CategoryTheory.mate_compat
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (cocontinuousRingedToposHomCocontinuousMorphism v hv fsharp))
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp))
    (cocontinuousBaseChangeModulesCocontinuousSliceTransition v fsharp V)
    (cocontinuousSiteTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ)
    (cocontinuousSliceTransitionCocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ)
    (restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V))) R) M
    (eqToIso (Hom.sliceLeft_obj_restriction (G' := G') R (v.obj V) ψ' M))
    (eqToIso (cocontinuousSliceRight_obj_restriction_cocontinuousSliceTransition R v τ ψ V M))
    (cocontinuousSliceTransition_app_restriction_cocontinuousSliceTransition R v fsharp τ ψ ψ' V
      hτ M)
  refine Eq.trans ?a (Eq.trans h ?b)
  case a => rfl
  case b => rfl

end Pullback

end Slice

end ModuleTransition

section SliceIso

open Opposite

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
  {X Y : RingedSite.{u, u, u}} (v : X.C ⥤ Y.C) [hv : v.IsCocontinuous X.J Y.J]
  (fsharp : Y.O ⟶
    (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O)
  {G : X.C ⥤ T} {G' : Y.C ⥤ T} [hG : G.IsContinuous X.J JT] [hG' : G'.IsContinuous Y.J JT]
  (τ : G ⟶ v ⋙ G')
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⟶
    (G.sheafPushforwardContinuous RingCat.{u} X.J JT).obj R)
  (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶
    (G'.sheafPushforwardContinuous RingCat.{u} Y.J JT).obj R)
  (hτ : CocontinuousRingCompatibleCocontinuousSliceTransition R v fsharp τ ψ ψ')
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Slice

variable (V : X.C)

/-- **The localized transposed transition** `f'^*(q^*N) ⟶ p^*N` of modules on the slice
`T/G'(v(V))`. -/
noncomputable abbrev cocontinuousSliceTransitionPullbackCocontinuousSliceTransition :=
  cocontinuousSiteTransitionPullbackCocontinuousSliceTransition (X := X.over V)
    (Y := Y.over (v.obj V))
    (hv := isCocontinuous_overPost_over_cocontinuousMorphism v V)
    (hG := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition v τ V)
    (hG' := Hom.isContinuous_sliceLeft (v.obj V)) (Hom.sliceRing (G' := G') R (v.obj V))
    (Over.post (X := V) v) (localizedCocontinuousFSharpCocontinuousMorphism v V fsharp)
    (cocontinuousSliceNatTransCocontinuousSliceTransition v τ V)
    (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)
    (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')
    (cocontinuousRingCompatible_localized_cocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ)

/-- **Invertibility of the transition is local on slices.** The restriction to `X.C/V` of the
transposed transition at `M` is invertible exactly when the localized transition is invertible
at `M|_{G'(v(V))}`: the two differ by the invertible localization mate. -/
theorem isIso_cocontinuousSliceTransitionPullback_app_iff_cocontinuousSliceTransition
    (M : SheafOfModules.{u} R) :
    IsIso
      ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
        ((restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V))) R).obj
          M)) ↔
      IsIso ((X.overRestrictionModules V).map
        ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
          M)) := by
  have h := cocontinuousLocalizedPullbackMate_comp_siteTransition_cocontinuousSliceTransition R v
    fsharp τ ψ ψ' V hτ M
  have e₁ := cocontinuousSiteTransitionPullback_app_cocontinuousSliceTransition (X := X.over V)
    (Y := Y.over (v.obj V))
    (hv := isCocontinuous_overPost_over_cocontinuousMorphism v V)
    (hG := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition v τ V)
    (hG' := Hom.isContinuous_sliceLeft (v.obj V)) (Hom.sliceRing (G' := G') R (v.obj V))
    (Over.post (X := V) v) (localizedCocontinuousFSharpCocontinuousMorphism v V fsharp)
    (cocontinuousSliceNatTransCocontinuousSliceTransition v τ V)
    (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)
    (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')
    (cocontinuousRingCompatible_localized_cocontinuousSliceTransition R v fsharp τ ψ ψ' V hτ)
    ((restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V))) R).obj M)
  have e₂ :=
    cocontinuousSiteTransitionPullback_app_cocontinuousSliceTransition R v fsharp τ ψ ψ' hτ M
  rw [← e₂] at h
  have := isIso_cocontinuousLocalizedPullbackMate_cocontinuousSliceTransition v fsharp V
  have : IsIso ((cocontinuousLocalizedPullbackMateCocontinuousSliceTransition v fsharp V).app
      ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M)) :=
    inferInstanceAs (IsIso
      ((cocontinuousLocalizedPullbackMateCocontinuousSliceTransition v fsharp V).app _))
  rw [e₁, ← isIso_comp_right_iff _
      (eqToHom (cocontinuousSliceRight_obj_restriction_cocontinuousSliceTransition R v τ ψ V M)),
    ← h, isIso_comp_left_iff, isIso_comp_left_iff]

/-- The localized transition is invertible at the structure sheaf of the slice as soon as the
transition is invertible at the structure sheaf. -/
theorem isIso_cocontinuousSliceTransitionPullback_app_unit_cocontinuousSliceTransition
    (hunit : IsIso
      ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
        (SheafOfModules.unit R))) :
    IsIso
      ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
        (SheafOfModules.unit (Hom.sliceRing (G' := G') R (v.obj V)))) := by
  have hA : (restrictionModules (JT.over (G'.obj (v.obj V))) JT (Over.forget (G'.obj (v.obj V)))
      R).obj (SheafOfModules.unit R) = SheafOfModules.unit (Hom.sliceRing (G' := G') R (v.obj V)) :=
    rfl
  have h := (isIso_cocontinuousSliceTransitionPullback_app_iff_cocontinuousSliceTransition R v
    fsharp τ ψ ψ' hτ V (SheafOfModules.unit R)).mpr inferInstance
  exact Eq.mp (congrArg (fun A ↦ IsIso
    ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
      A)) hA) h

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The localized transition carries invertibility from `q^*` to `p^*`.** For a morphism
`c : P ⟶ N` of modules on `T/G'(v(V))` at whose ends the localized transition is invertible, if
the restriction `q^*c` is invertible then so is `p^*c`. -/
theorem isIso_cocontinuousSliceRight_map_of_isIso_cocontinuousSliceTransition
    {P N : SheafOfModules.{u} (Hom.sliceRing (G' := G') R (v.obj V))} (c : P ⟶ N)
    (hc : haveI := Hom.isContinuous_sliceLeft (G' := G') (hG' := hG') (v.obj V)
      IsIso ((SheafOfModules.pushforward.{u} (F := Over.post (X := v.obj V) G')
        (J := (Y.over (v.obj V)).J) (K := JT.over (G'.obj (v.obj V)))
        (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')).map c))
    (hP : IsIso
      ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
        P))
    (hN : IsIso
      ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
        N)) :
    haveI := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition (JT := JT) v τ V
    IsIso ((SheafOfModules.pushforward.{u}
        (F := Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V))
        (J := (X.over V).J) (K := JT.over (G'.obj (v.obj V)))
        (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)).map c) := by
  have := Hom.isContinuous_sliceLeft (G' := G') (hG' := hG') (v.obj V)
  have := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition (JT := JT) v τ V
  have e := (cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ
    V).naturality c
  have : IsIso ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ
      V).app P ≫
      (SheafOfModules.pushforward.{u}
        (F := Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V))
        (J := (X.over V).J) (K := JT.over (G'.obj (v.obj V)))
        (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)).map c) := by
    rw [← e]
    exact inferInstanceAs (IsIso
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp).toModulesHom).map _ ≫
          _))
  exact IsIso.of_isIso_comp_left
    ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
      P) _

variable [hGc : G.IsCocontinuous X.J JT] [hG'c : G'.IsCocontinuous Y.J JT]

/-- **The localized transition is invertible on globally presented modules**, once the
transition is invertible at the structure sheaf and `G`, `G'` are cocontinuous. -/
theorem isIso_cocontinuousSliceTransitionPullback_app_of_hasGlobalPresentation
    (hunit : IsIso
      ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
        (SheafOfModules.unit R)))
    {N : SheafOfModules.{u} (Hom.sliceRing (G' := G') R (v.obj V))}
    (hN : N.HasGlobalPresentation) :
    IsIso
      ((cocontinuousSliceTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ V).app
        N) := by
  have := Hom.isContinuous_sliceLeft (G' := G') (hG' := hG') (v.obj V)
  have := isContinuous_cocontinuousSliceRight_cocontinuousSliceTransition (JT := JT) v τ V
  have : (Over.post (X := v.obj V) G').IsCocontinuous (Y.over (v.obj V)).J
      (JT.over (G'.obj (v.obj V))) :=
    inferInstanceAs ((Over.post (X := v.obj V) G').IsCocontinuous (Y.J.over (v.obj V))
      (JT.over (G'.obj (v.obj V))))
  have : (Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V)).IsCocontinuous
      (X.over V).J (JT.over (G'.obj (v.obj V))) :=
    isCocontinuous_comp (Over.post (X := V) G) (Over.map (Y := G'.obj (v.obj V)) (τ.app V))
      (X.J.over V) (JT.over (G.obj V)) (L := JT.over (G'.obj (v.obj V)))
  have h₁ : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (F := Over.post (X := v.obj V) G')
        (J := (Y.over (v.obj V)).J) (K := JT.over (G'.obj (v.obj V)))
        (Hom.sliceRingMapLeft (G' := G') R (v.obj V) ψ')) :=
    Stacks.SheafOfModules.pushforward_preservesColimits _ _
  have h₂ : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u}
        (F := Over.post (X := V) G ⋙ Over.map (Y := G'.obj (v.obj V)) (τ.app V))
        (J := (X.over V).J) (K := JT.over (G'.obj (v.obj V)))
        (cocontinuousSliceRingMapRightCocontinuousSliceTransition R v τ ψ V)) :=
    Stacks.SheafOfModules.pushforward_preservesColimits _ _
  have h₃ : PreservesColimitsOfSize.{u, u}
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp).toModulesHom) :=
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (localizedCocontinuousRingedToposHomCocontinuousMorphism v V
        fsharp)).leftAdjoint_preservesColimits
  exact Stacks.SheafOfModules.isIso_app_of_hasGlobalPresentation _
    (isIso_cocontinuousSliceTransitionPullback_app_unit_cocontinuousSliceTransition R v fsharp τ ψ
      ψ' hτ V hunit) hN

end Slice

variable [hGc : G.IsCocontinuous X.J JT] [hG'c : G'.IsCocontinuous Y.J JT]

/-- **The transition is invertible once it is on a covering by globally presented slices.** If
the transposed transition is invertible at the structure sheaf and the objects `V i` of `X.C`, for
which `M|_{G'(v(V i))}` has a global presentation, cover the final object of `X.C`, then the
transposed transition is invertible at `M`. -/
theorem isIso_cocontinuousSiteTransitionPullback_app_of_coversTop_cocontinuousSliceTransition
    (hunit : IsIso
      ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
        (SheafOfModules.unit R)))
    (M : SheafOfModules.{u} R) {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hM : ∀ i, ((restrictionModules (JT.over (G'.obj (v.obj (V i)))) JT
      (Over.forget (G'.obj (v.obj (V i)))) R).obj M).HasGlobalPresentation) :
    IsIso ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
      M) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop hV _ fun i W g ↦ ?_
  have h := (isIso_cocontinuousSliceTransitionPullback_app_iff_cocontinuousSliceTransition R v
    fsharp τ ψ ψ' hτ (V i) M).mp
    (isIso_cocontinuousSliceTransitionPullback_app_of_hasGlobalPresentation
      R v fsharp τ ψ ψ' hτ (V i) hunit (hM i))
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward _ _ h
    (op (Over.mk g))

/-- **The transition is invertible once the module is locally globally presented.** If the
transposed transition is invertible at the structure sheaf and every object `U` of `X.C` has a
covering family by objects `W` with `M|_{G'(v(W))}` globally presented, then the transposed
transition is invertible at `M`. -/
theorem isIso_cocontinuousSiteTransitionPullback_app_of_locally_cocontinuousSliceTransition
    (hunit : IsIso
      ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
        (SheafOfModules.unit R)))
    (M : SheafOfModules.{u} R)
    (hM : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ U), S g →
      ((restrictionModules (JT.over (G'.obj (v.obj W))) JT (Over.forget (G'.obj (v.obj W)))
        R).obj M).HasGlobalPresentation) :
    IsIso ((cocontinuousSiteTransitionPullbackCocontinuousSliceTransition R v fsharp τ ψ ψ' hτ).app
      M) := by
  refine isIso_cocontinuousSiteTransitionPullback_app_of_coversTop_cocontinuousSliceTransition R v
    fsharp τ ψ ψ' hτ hunit M
    (V := fun W : {W : X.C // ((restrictionModules (JT.over (G'.obj (v.obj W))) JT
      (Over.forget (G'.obj (v.obj W))) R).obj M).HasGlobalPresentation} ↦ W.1)
    (fun U ↦ ?_) (fun W ↦ W.2)
  obtain ⟨S, hS, hpres⟩ := hM U
  refine X.J.superset_covering ?_ hS
  rintro Z g ⟨W, h, s, hs, rfl⟩
  exact ⟨⟨W, hpres s hs⟩, ⟨h⟩⟩

end SliceIso

end AlgebraicGeometry.RingedSite
