module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalComparisonPseudonaturalProofRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverPullbackComp

/-!
# Compatibility of the comparison of right adjoints of restriction with composition

For a site `C` with a sheaf of rings `R` and arrows `f : V ⟶ U`, `g : W ⟶ V`, this file computes
the mate of the composition isomorphism `Stacks.SheafOfModules.overMapCompIso` of restriction
with respect to the adjunctions `Stacks.SheafOfModules.overMapStarAdjunction`, and expresses the
composition isomorphism `Stacks.SheafOfModules.overPullbackComp` of
`SheafOfModules.overPullback` through `SheafOfModules.pushforwardCongr₂` and
`SheafOfModules.pushforwardComp`. The results are then specialised to the big fppf site.

## Main results

* `Stacks.Mates.conjugateIsoEquiv_eq_of_counit`: an isomorphism of right adjoints compatible with
  the counits along an isomorphism of left adjoints is the mate of that isomorphism.
* `Stacks.SheafOfModules.conjugateIsoEquiv_pushforwardCongr₂_of_counit`,
  `Stacks.SheafOfModules.conjugateIsoEquiv_pushforwardCongr₂`: the mate of
  `SheafOfModules.pushforwardCongr₂` along an isomorphism `α` of left adjoint functors of sites is
  `SheafOfModules.pushforwardCongr₂` along the mate of `α`.
* `Stacks.SheafOfModules.pullbackComp_inv_app_left_comp_fst`: `CategoryTheory.Over.pullbackComp`
  is compatible with the projections.
* `Stacks.SheafOfModules.toPushforwardOverPullback_comp`: the structure sheaves of a composite
  base change match along `CategoryTheory.Over.pullbackComp`.
* `Stacks.SheafOfModules.overPullbackComp_eq`: `Stacks.SheafOfModules.overPullbackComp` is the
  transport along `CategoryTheory.Over.pullbackComp` followed by the inverse of
  `SheafOfModules.pushforwardComp`.
* `Stacks.SheafOfModules.conjugateIsoEquiv_overMapCompIso_overMapStarAdjunction`,
  `Stacks.SheafOfModules.conjugateIsoEquiv_overMapCompIso_overMapStarAdjunction_eq`: the mate of
  `overMapCompIso R f g ≪≫ overMapCongrIso R e` with respect to
  `Stacks.SheafOfModules.overMapStarAdjunction`.
* `AlgebraicGeometry.BigFppfOver.heq_objRestrictAdjunction`: the adjunction of restriction to an
  object of the big fppf site is heterogeneously equal to
  `Stacks.SheafOfModules.overMapStarAdjunction` of its structure morphism.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq`,
  `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq₂`: the
  mate of `AlgebraicGeometry.BigFppfOver.objRestrictComp` with
  `Stacks.SheafOfModules.overPullbackComp`, and then also the comparison of right adjoints at the
  source, replaced by their values.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w v u

namespace Stacks.Mates

/-- For adjunctions `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂` and `α : L₂ ≅ L₁`, an isomorphism
`φ : R₁ ≅ R₂` with `L₂.map (φ.hom.app X) ≫ adj₂.counit.app X = α.hom.app _ ≫ adj₁.counit.app X`
for every `X` is `CategoryTheory.conjugateIsoEquiv adj₁ adj₂ α`. -/
public theorem conjugateIsoEquiv_eq_of_counit {C₀ : Type u₁} {C₁ : Type u₂}
    [Category.{v₁} C₀] [Category.{v₂} C₁] {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) (φ : R₁ ≅ R₂)
    (h : ∀ X, L₂.map (φ.hom.app X) ≫ adj₂.counit.app X =
      α.hom.app (R₁.obj X) ≫ adj₁.counit.app X) :
    conjugateIsoEquiv adj₁ adj₂ α = φ := by
  refine Iso.ext ?_
  ext X
  refine (adj₂.homEquiv (R₁.obj X) X).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h X]
  exact conjugateEquiv_counit adj₁ adj₂ α.hom X

/-- Precomposing `P.map` with the unit of `adj₁` and the mate of `α` agrees with `P.map` of the
unit of `adj₂` and `R₂.map (α.app X)`. -/
private theorem map_conjugateEquiv_comp_map_unit {C₀ : Type u₁} {C₁ : Type u₂} {A : Type w}
    [Category.{v₁} C₀] [Category.{v₂} C₁] [Category.{v} A] {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (P : C₀ᵒᵖ ⥤ A) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (X : C₀) :
    P.map ((conjugateEquiv adj₁ adj₂ α).app (L₁.obj X)).op ≫ P.map (adj₁.unit.app X).op =
      P.map (R₂.map (α.app X)).op ≫ P.map (adj₂.unit.app X).op := by
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, ← op_comp, unit_conjugateEquiv]

end Stacks.Mates

namespace Stacks.SheafOfModules

/-! ### The mate of a transport of pushforwards along an isomorphism of sites -/

section Congr₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G : C ⥤ D} {F' G' : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G J K]
  [Functor.IsContinuous F' K J] [Functor.IsContinuous G' K J]

/-- Let `adjF : F ⊣ F'` and `adjG : G ⊣ G'` be adjunctions of continuous functors of sites and
`α : F ≅ G`, and let `AF`, `AG` be adjunctions between the pushforwards of sheaves of modules
along `φF`, `ψF` and along `φG`, `ψG` whose counits are given on sections by restriction along
the units of `adjF` and `adjG` (hypotheses `hF`, `hG`). Then the mate of
`SheafOfModules.pushforwardCongr₂` along `α` is `SheafOfModules.pushforwardCongr₂` along
`CategoryTheory.conjugateIsoEquiv adjG adjF α`. -/
public theorem conjugateIsoEquiv_pushforwardCongr₂_of_counit (adjF : F ⊣ F') (adjG : G ⊣ G')
    (α : F ≅ G) {φF : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    {φG : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    {ψF : R ⟶ (F'.sheafPushforwardContinuous RingCat.{u} K J).obj S}
    {ψG : R ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K J).obj S}
    (AF : SheafOfModules.pushforward.{v} φF ⊣ SheafOfModules.pushforward.{v} ψF)
    (AG : SheafOfModules.pushforward.{v} φG ⊣ SheafOfModules.pushforward.{v} ψG)
    (hF : ∀ (M : SheafOfModules.{v} S) (Z : Cᵒᵖ) (x), (AF.counit.app M).val.app Z x =
      M.val.map (adjF.unit.app Z.unop).op x)
    (hG : ∀ (M : SheafOfModules.{v} S) (Z : Cᵒᵖ) (x), (AG.counit.app M).val.app Z x =
      M.val.map (adjG.unit.app Z.unop).op x)
    (he : φG ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom RingCat.{u} J K).app R = φF)
    (he' : ψF ≫ (Functor.sheafPushforwardContinuousNatTrans
        (conjugateIsoEquiv adjG adjF α).hom RingCat.{u} K J).app S = ψG) :
    conjugateIsoEquiv AF AG (SheafOfModules.pushforwardCongr₂.{v} φG α he) =
      SheafOfModules.pushforwardCongr₂.{v} ψF (conjugateIsoEquiv adjG adjF α) he' := by
  refine Stacks.Mates.conjugateIsoEquiv_eq_of_counit _ _ _ _ fun M => ?_
  ext Z x
  refine Eq.trans (hG M Z _) (Eq.trans ?_ (hF M Z _).symm)
  exact ConcreteCategory.congr_hom
    (Stacks.Mates.map_conjugateEquiv_comp_map_unit M.val.presheaf adjG adjF α.hom Z.unop) x

/-- The mate of `SheafOfModules.pushforwardCongr₂` along an isomorphism `α : F ≅ G` of left
adjoint functors of sites, with respect to the adjunctions
`SheafOfModules.pushforwardPushforwardAdj` induced by `adjF` and `adjG`, is
`SheafOfModules.pushforwardCongr₂` along `CategoryTheory.conjugateIsoEquiv adjG adjF α`. -/
public theorem conjugateIsoEquiv_pushforwardCongr₂ (adjF : F ⊣ F') (adjG : G ⊣ G') (α : F ≅ G)
    (φF : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (φG : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψF : R ⟶ (F'.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (ψG : R ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (HF₁ : Functor.whiskerRight (NatTrans.op adjF.counit) R.obj =
      ψF.hom ≫ F'.op.whiskerLeft φF.hom)
    (HF₂ : φF.hom ≫ F.op.whiskerLeft ψF.hom ≫
      Functor.whiskerRight (NatTrans.op adjF.unit) S.obj = 𝟙 S.obj)
    (HG₁ : Functor.whiskerRight (NatTrans.op adjG.counit) R.obj =
      ψG.hom ≫ G'.op.whiskerLeft φG.hom)
    (HG₂ : φG.hom ≫ G.op.whiskerLeft ψG.hom ≫
      Functor.whiskerRight (NatTrans.op adjG.unit) S.obj = 𝟙 S.obj)
    (he : φG ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom RingCat.{u} J K).app R = φF)
    (he' : ψF ≫ (Functor.sheafPushforwardContinuousNatTrans
        (conjugateIsoEquiv adjG adjF α).hom RingCat.{u} K J).app S = ψG) :
    conjugateIsoEquiv (SheafOfModules.pushforwardPushforwardAdj.{v} adjF φF ψF HF₁ HF₂)
        (SheafOfModules.pushforwardPushforwardAdj.{v} adjG φG ψG HG₁ HG₂)
        (SheafOfModules.pushforwardCongr₂.{v} φG α he) =
      SheafOfModules.pushforwardCongr₂.{v} ψF (conjugateIsoEquiv adjG adjF α) he' :=
  conjugateIsoEquiv_pushforwardCongr₂_of_counit adjF adjG α _ _
    (SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app adjF φF ψF HF₁ HF₂)
    (SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app adjG φG ψG HG₁ HG₂) he he'

end Congr₂

/-! ### Base change along a composite -/

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {U V W : C} (R : Sheaf J RingCat.{w})

/-- `CategoryTheory.Over.pullbackComp` is compatible with the projections: base changing
`Z : Over U` along `f : V ⟶ U` and then along `g : W ⟶ V`, and base changing it along `g ≫ f`,
have the same projection to `Z`. -/
public theorem pullbackComp_inv_app_left_comp_fst (f : V ⟶ U) (g : W ⟶ V) (Z : Over U) :
    ((Over.pullbackComp g f).inv.app Z).left ≫ pullback.fst Z.hom (g ≫ f) =
      pullback.fst (pullback.snd Z.hom f) g ≫ pullback.fst Z.hom f := by
  have key : ∀ u : (Over.pullback f ⋙ Over.pullback g).obj Z ⟶ (Over.pullback (g ≫ f)).obj Z,
      u.left ≫ pullback.fst Z.hom (g ≫ f) =
        ((Over.map (g ≫ f)).map u ≫ (Over.mapPullbackAdj (g ≫ f)).counit.app Z).left := by
    intro u; simp
  refine Eq.trans (key _) ?_
  refine Eq.trans (congrArg CommaMorphism.left (conjugateEquiv_counit
    ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f))
    (Over.mapPullbackAdj (g ≫ f)) (Over.mapComp g f).hom Z)) ?_
  simp

/-- Base change along `f` followed by base change along `g` is continuous for the induced
topologies. -/
public instance isContinuous_overPullback_comp (f : V ⟶ U) (g : W ⟶ V) :
    (Over.pullback f ⋙ Over.pullback g).IsContinuous (J.over U) (J.over W) :=
  Functor.isContinuous_comp _ _ _ (J.over V) _

/-- The structure sheaves of a composite base change match:
`Sheaf.toPushforwardOverPullback R (g ≫ f)` followed by the transport along
`CategoryTheory.Over.pullbackComp g f` is `Sheaf.toPushforwardOverPullback R f` followed by the
pushforward of `Sheaf.toPushforwardOverPullback R g`. -/
public theorem toPushforwardOverPullback_comp (f : V ⟶ U) (g : W ⟶ V) :
    Sheaf.toPushforwardOverPullback R (g ≫ f) ≫
        (Functor.sheafPushforwardContinuousNatTrans (Over.pullbackComp g f).inv
          RingCat.{w} (J.over U) (J.over W)).app (R.over W) =
      Sheaf.toPushforwardOverPullback R f ≫
        ((Over.pullback f).sheafPushforwardContinuous RingCat.{w}
          (J.over U) (J.over V)).map (Sheaf.toPushforwardOverPullback R g) := by
  ext : 2
  funext Z
  show R.obj.map (pullback.fst Z.unop.hom (g ≫ f)).op ≫
      R.obj.map ((Over.pullbackComp g f).inv.app Z.unop).left.op =
    R.obj.map (pullback.fst Z.unop.hom f).op ≫
      R.obj.map (pullback.fst (pullback.snd Z.unop.hom f) g).op
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, ← op_comp,
    pullbackComp_inv_app_left_comp_fst f g Z.unop]

/-- The composition isomorphism `Stacks.SheafOfModules.overPullbackComp R f g` of
`SheafOfModules.overPullback` is `SheafOfModules.pushforwardCongr₂` along
`CategoryTheory.Over.pullbackComp g f` followed by the inverse of
`SheafOfModules.pushforwardComp`. -/
public theorem overPullbackComp_eq (f : V ⟶ U) (g : W ⟶ V) :
    overPullbackComp R f g =
      SheafOfModules.pushforwardCongr₂ (Sheaf.toPushforwardOverPullback R (g ≫ f))
          (Over.pullbackComp g f).symm (toPushforwardOverPullback_comp R f g) ≪≫
        (SheafOfModules.pushforwardComp (Sheaf.toPushforwardOverPullback R f)
          (Sheaf.toPushforwardOverPullback R g)).symm := by
  have hF : ∀ (M : SheafOfModules.{w} (R.over W)) (Z : (Over W)ᵒᵖ) (x),
      (((SheafOfModules.overMapPushforwardAdj R (g ≫ f)).counit.app M).val.app Z) x =
        (M.val.map ((Over.mapPullbackAdj (g ≫ f)).unit.app Z.unop).op) x :=
    fun _ _ _ => rfl
  have hG : ∀ (M : SheafOfModules.{w} (R.over W)) (Z : (Over W)ᵒᵖ) (x),
      ((((SheafOfModules.overMapPushforwardAdj R f).comp
          (SheafOfModules.overMapPushforwardAdj R g)).counit.app M).val.app Z) x =
        (M.val.map (((Over.mapPullbackAdj g).comp
          (Over.mapPullbackAdj f)).unit.app Z.unop).op) x := by
    intro M Z x
    show (M.val.presheaf.map ((Over.pullback g).map
          ((Over.mapPullbackAdj f).unit.app ((Over.map g).obj Z.unop))).op ≫
        M.val.presheaf.map ((Over.mapPullbackAdj g).unit.app Z.unop).op) x =
      M.val.presheaf.map (((Over.mapPullbackAdj g).comp
        (Over.mapPullbackAdj f)).unit.app Z.unop).op x
    rw [Adjunction.comp_unit_app, op_comp, Functor.map_comp]
  refine Eq.trans (conjugateIsoEquiv_overMapCompIso R f g).symm
    (Stacks.Mates.conjugateIsoEquiv_eq_of_counit _ _ _ _ fun M => ?_)
  ext Z x
  refine Eq.trans (hG M Z _) (Eq.trans ?_ (hF M Z _).symm)
  exact ConcreteCategory.congr_hom (Stacks.Mates.map_conjugateEquiv_comp_map_unit M.val.presheaf
    ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)) (Over.mapPullbackAdj (g ≫ f))
    (Over.mapComp g f).hom Z.unop) x

/-! ### The cocycle -/

/-- For `f : V ⟶ U`, `g : W ⟶ V` and `e : g ≫ f = a`, the mate of
`overMapCompIso R f g ≪≫ overMapCongrIso R e` with respect to
`Stacks.SheafOfModules.overMapStarAdjunction` at `a`, `f` and `g` is
`Stacks.SheafOfModules.overPullbackCongr` followed by `Stacks.SheafOfModules.overPullbackComp`,
conjugated by the comparisons `Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback` at
the three arrows. -/
public theorem conjugateIsoEquiv_overMapCompIso_overMapStarAdjunction (f : V ⟶ U) (g : W ⟶ V)
    {a : W ⟶ U} (e : g ≫ f = a) :
    conjugateIsoEquiv (overMapStarAdjunction a R)
        ((overMapStarAdjunction f R).comp (overMapStarAdjunction g R))
        (overMapCompIso R f g ≪≫ overMapCongrIso R e) =
      overMapStarPushforwardIsoOverPullback a R ≪≫
        (overPullbackCongr R e.symm ≪≫ overPullbackComp R f g) ≪≫
          (Functor.isoWhiskerRight (overMapStarPushforwardIsoOverPullback g R).symm
              (SheafOfModules.overPullback.{w} R f) ≪≫
            Functor.isoWhiskerLeft _ (overMapStarPushforwardIsoOverPullback f R).symm) := by
  have h1 := Stacks.Mates.conjugateIsoEquiv_congr_target
    (SheafOfModules.overMapPushforwardAdj R a) (overMapStarAdjunction a R)
    ((overMapStarAdjunction f R).comp (overMapStarAdjunction g R))
    (overMapCompIso R f g ≪≫ overMapCongrIso R e)
  have h2 := Stacks.Mates.conjugateIsoEquiv_congr_source
    (SheafOfModules.overMapPushforwardAdj R a)
    ((SheafOfModules.overMapPushforwardAdj R f).comp
      (SheafOfModules.overMapPushforwardAdj R g))
    ((overMapStarAdjunction f R).comp (overMapStarAdjunction g R))
    (overMapCompIso R f g ≪≫ overMapCongrIso R e)
  refine h1.trans (Eq.trans (congrArg (fun x => conjugateIsoEquiv (overMapStarAdjunction a R)
      (SheafOfModules.overMapPushforwardAdj R a)
      (Iso.refl (SheafOfModules.overMap R a)) ≪≫ x) h2) ?_)
  refine congrArg₂ (fun x y => x ≪≫ y) ?_ (congrArg₂ (fun x y => x ≪≫ y)
    (conjugateIsoEquiv_overMapCompIso_trans_overMapCongrIso R f g e) ?_)
  · exact Eq.trans (Stacks.Mates.conjugateIsoEquiv_refl _ _)
      (rightAdjointUniq_overMapStarAdjunction a R)
  · refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_refl _ _) ?_
    refine Eq.trans (Stacks.Mates.rightAdjointUniq_comp _ _ _ _) ?_
    refine congrArg₂ (fun x y => x ≪≫ y) ?_ ?_
    · exact congrArg (fun x => Functor.isoWhiskerRight x (SheafOfModules.overPullback.{w} R f))
        (Eq.trans (Stacks.Mates.rightAdjointUniq_symm _ _).symm
          (congrArg Iso.symm (rightAdjointUniq_overMapStarAdjunction g R)))
    · exact congrArg (fun x => Functor.isoWhiskerLeft _ x)
        (Eq.trans (Stacks.Mates.rightAdjointUniq_symm _ _).symm
          (congrArg Iso.symm (rightAdjointUniq_overMapStarAdjunction f R)))

/-- The mate of `overMapCompIso R f g ≪≫ overMapCongrIso R e` with respect to
`Stacks.SheafOfModules.overMapStarAdjunction`, with `Stacks.SheafOfModules.overPullbackComp`
expanded: it is `Stacks.SheafOfModules.overPullbackCongr` followed by
`SheafOfModules.pushforwardCongr₂` along `CategoryTheory.Over.pullbackComp g f` and the inverse of
`SheafOfModules.pushforwardComp`, conjugated by the comparisons
`Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback` at the three arrows. -/
public theorem conjugateIsoEquiv_overMapCompIso_overMapStarAdjunction_eq (f : V ⟶ U) (g : W ⟶ V)
    {a : W ⟶ U} (e : g ≫ f = a) :
    conjugateIsoEquiv (overMapStarAdjunction a R)
        ((overMapStarAdjunction f R).comp (overMapStarAdjunction g R))
        (overMapCompIso R f g ≪≫ overMapCongrIso R e) =
      overMapStarPushforwardIsoOverPullback a R ≪≫
        (overPullbackCongr R e.symm ≪≫
            (SheafOfModules.pushforwardCongr₂ (Sheaf.toPushforwardOverPullback R (g ≫ f))
                (Over.pullbackComp g f).symm (toPushforwardOverPullback_comp R f g) ≪≫
              (SheafOfModules.pushforwardComp (Sheaf.toPushforwardOverPullback R f)
                (Sheaf.toPushforwardOverPullback R g)).symm)) ≪≫
          (Functor.isoWhiskerRight (overMapStarPushforwardIsoOverPullback g R).symm
              (SheafOfModules.overPullback.{w} R f) ≪≫
            Functor.isoWhiskerLeft _ (overMapStarPushforwardIsoOverPullback f R).symm) := by
  rw [conjugateIsoEquiv_overMapCompIso_overMapStarAdjunction R f g e, overPullbackComp_eq]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

open Stacks.SheafOfModules

/-- The adjunction `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction B S hS T` of restriction
to an object `T` of the big fppf site is heterogeneously equal to
`Stacks.SheafOfModules.overMapStarAdjunction` of the structure morphism `T.hom`. -/
public theorem heq_objRestrictAdjunction (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigFppfOver B S hS) :
    HEq (objRestrictAdjunction B S hS T)
      (overMapStarAdjunction T.hom B.structureSheaf) :=
  heq_overMapStarAdjunction T.hom B.structureSheaf

/-- The mate of `AlgebraicGeometry.BigFppfOver.objRestrictComp B S hS g` with respect to the
adjunctions `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`, with
`Stacks.SheafOfModules.overPullbackComp` expanded: it is
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso` at `T'`, followed by
`Stacks.SheafOfModules.overPullbackCongr`, `SheafOfModules.pushforwardCongr₂` along
`CategoryTheory.Over.pullbackComp` and the inverse of `SheafOfModules.pushforwardComp`, followed
by the inverses of the comparisons of right adjoints at `g` and at `T`. -/
public theorem conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    conjugateIsoEquiv (objRestrictAdjunction B S hS T')
        ((objRestrictAdjunction B S hS T).comp
          (objRestrictAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)))
        (objRestrictComp B S hS g) =
      objRestrictRightAdjointIso B S hS T' ≪≫
        (overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
            (SheafOfModules.pushforwardCongr₂
                (Sheaf.toPushforwardOverPullback B.structureSheaf (g.left ≫ T.hom))
                (Over.pullbackComp g.left T.hom).symm
                (toPushforwardOverPullback_comp B.structureSheaf T.hom g.left) ≪≫
              (SheafOfModules.pushforwardComp
                (Sheaf.toPushforwardOverPullback B.structureSheaf T.hom)
                (Sheaf.toPushforwardOverPullback B.structureSheaf g.left)).symm)) ≪≫
          (Functor.isoWhiskerRight (objRestrictRightAdjointIso B (objScheme B S hS T)
                (contains_objScheme B S hS T) (Over.mk g.left)).symm
              (SheafOfModules.overPullback.{u} B.structureSheaf T.hom) ≪≫
            Functor.isoWhiskerLeft _ (objRestrictRightAdjointIso B S hS T).symm) := by
  rw [conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction B S hS g,
    overPullbackComp_eq]
  rfl

/-- The mate of `AlgebraicGeometry.BigFppfOver.objRestrictComp B S hS g` with respect to the
adjunctions `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction`, as in
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq`, with
the comparison of right adjoints at `T'` replaced by
`Stacks.SheafOfModules.overMapStarPushforwardIsoOverPullback T'.hom B.structureSheaf`. -/
public theorem conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq₂
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    conjugateIsoEquiv (objRestrictAdjunction B S hS T')
        ((objRestrictAdjunction B S hS T).comp
          (objRestrictAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
            (Over.mk g.left)))
        (objRestrictComp B S hS g) =
      overMapStarPushforwardIsoOverPullback T'.hom B.structureSheaf ≪≫
        (overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
            (SheafOfModules.pushforwardCongr₂
                (Sheaf.toPushforwardOverPullback B.structureSheaf (g.left ≫ T.hom))
                (Over.pullbackComp g.left T.hom).symm
                (toPushforwardOverPullback_comp B.structureSheaf T.hom g.left) ≪≫
              (SheafOfModules.pushforwardComp
                (Sheaf.toPushforwardOverPullback B.structureSheaf T.hom)
                (Sheaf.toPushforwardOverPullback B.structureSheaf g.left)).symm)) ≪≫
          (Functor.isoWhiskerRight (objRestrictRightAdjointIso B (objScheme B S hS T)
                (contains_objScheme B S hS T) (Over.mk g.left)).symm
              (SheafOfModules.overPullback.{u} B.structureSheaf T.hom) ≪≫
            Functor.isoWhiskerLeft _ (objRestrictRightAdjointIso B S hS T).symm) := by
  rw [conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction_eq B S hS g,
    objRestrictRightAdjointIso_eq B S hS T']
  rfl

end AlgebraicGeometry.BigFppfOver

end
