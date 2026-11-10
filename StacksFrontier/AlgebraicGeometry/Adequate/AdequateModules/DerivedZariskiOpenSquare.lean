module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiOpenRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTrans

/-!
# The square of `070U` morphisms over an open subscheme of the base

Let `g : T ⟶ S` be an open immersion of schemes below the cutoff of a big `τ`-site `𝒮`, and let
`f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` and `f_T : ((Sch/T)_τ, 𝒪) ⟶ (T_Zar, 𝒪_T)` be the morphisms of
[Stacks, Tag 070U]. Restriction `j^*` to the big site over `T` and restriction `g^*` to `T_Zar`
make a square

```
  Mod(𝒪_S)   --f^*-->   Mod((Sch/S)_τ)
    | g^*                  | j^*
  Mod(𝒪_T)   --f_T^*-->  Mod((Sch/T)_τ)
```

which commutes: the direct images satisfy `f_* j_* ≅ g_* f_{T,*}`, both being the direct image
along `W ↦ W ×_S T = g⁻¹W`, so the conjugate transformation `g^* f_T^* ⟶ j^* f^*` is an
isomorphism. Its mate `g^* f_* ⟶ f_{T,*} j^*` is an isomorphism as well: it is the inverse mate of
the isomorphism of direct images, whose components are invertible because an open of `T` is its
own base change to `T` and `g_*` is fully faithful. The mate relation then says that restricting
the unit of `f^* ⊣ f_*` to `T` gives the unit of `f_T^* ⊣ f_{T,*}`, up to these isomorphisms.

## Main definitions

* `Stacks.Adequate.openSquarePushforwardIso`: `j_* ⋙ f_* ≅ f_{T,*} ⋙ g_*`.
* `Stacks.Adequate.openSquarePullbackHom`: the base change `g^* ⋙ f_T^* ⟶ f^* ⋙ j^*`.
* `Stacks.Adequate.openSquareBaseChange`: its mate `f_* ⋙ g^* ⟶ j^* ⋙ f_{T,*}`.
* `Stacks.Adequate.zariskiOpenHom`: the morphism of ringed topoi `(T_Zar, 𝒪_T) ⟶ (S_Zar, 𝒪_S)`.

## Main results

* `Stacks.Adequate.isIso_openSquarePullbackHom` and
  `Stacks.Adequate.isIso_openSquareBaseChange_app`: both base change transformations are
  isomorphisms.
* `Stacks.Adequate.openSquare_unit`: the restriction of the unit is the unit of the restriction.

## References

* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} (𝒮 : AlgebraicGeometry.BigSite.{u} τ) {S T : Scheme.{u}}
  (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮) (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮)
  (g : T ⟶ S)

/-- The square `g⁻¹W ⟶ W`, `g⁻¹W ⟶ T` over `W ⟶ S ⟵ T` is a pullback of schemes of the
ambient category. -/
theorem isPullback_openPreimage (W : S.Opens) : IsPullback
    (ObjectProperty.homMk (X := (⟨((g ⁻¹ᵁ W : T.Opens) : Scheme.{u}),
        opensBelow_mem hT (g ⁻¹ᵁ W)⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
      (Y := ⟨(W : Scheme.{u}), opensBelow_mem hS W⟩) (g ∣_ W))
    (ObjectProperty.homMk (Y := (⟨T, hT⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
      (g ⁻¹ᵁ W).ι)
    (ObjectProperty.homMk (Y := (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮))) W.ι)
    (ambientHom 𝒮 hS hT g) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (isPullback_morphismRestrict g W)

/-- The open `g⁻¹W` of `T` is the fibre product `W ×_S T`. -/
def openPreimageLeftIso (W : S.Opens) :
    (⟨((g ⁻¹ᵁ W : T.Opens) : Scheme.{u}), opensBelow_mem hT (g ⁻¹ᵁ W)⟩ :
      SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)) ≅
    pullback (ObjectProperty.homMk (X := (⟨(W : Scheme.{u}), opensBelow_mem hS W⟩ :
        SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
        (Y := (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮))) W.ι)
      (ambientHom 𝒮 hS hT g) :=
  (isPullback_openPreimage 𝒮 hS hT g W).isoPullback

/-- The identification `g⁻¹W ≅ W ×_S T` followed by the first projection is `g` restricted to
`g⁻¹W`. -/
theorem openPreimageLeftIso_hom_fst (W : S.Opens) :
    ((openPreimageLeftIso 𝒮 hS hT g W).hom ≫ pullback.fst _ _).hom = g ∣_ W := by
  rw [openPreimageLeftIso, IsPullback.isoPullback_hom_fst]
  rfl

/-- The open `g⁻¹W` of `T` is, as an object of the big site over `T`, the base change of the
open `W` of `S`. -/
def openPreimageIsoPullback (W : S.Opens) :
    (BigSite.ofAmbient 𝒮 T hT).opensToBig.obj ((Opens.map g.base).obj W) ≅
      (Over.pullback (ambientHom 𝒮 hS hT g)).obj ((BigSite.ofAmbient 𝒮 S hS).opensToBig.obj W) :=
  Over.isoMk (openPreimageLeftIso 𝒮 hS hT g W)
    (IsPullback.isoPullback_hom_snd (isPullback_openPreimage 𝒮 hS hT g W))

/-- The structure maps of the two composite morphisms of ringed sites agree over an open `W`:
`Γ(S, W) ⟶ Γ(W) ⟶ Γ(W ×_S T) ≅ Γ(g⁻¹W)` is `g^♯ : Γ(S, W) ⟶ Γ(T, g⁻¹W) ≅ Γ(g⁻¹W)`. -/
theorem openSquare_structureMap (W : S.Opens) :
    (Scheme.Opens.topIso W).inv ≫ Scheme.Γ.map (pullback.fst
      (ObjectProperty.homMk (X := (⟨(W : Scheme.{u}), opensBelow_mem hS W⟩ :
        SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
        (Y := (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮))) W.ι)
        (ambientHom 𝒮 hS hT g)).hom.op ≫
      Scheme.Γ.map (openPreimageLeftIso 𝒮 hS hT g W).hom.hom.op =
    g.app W ≫ (Scheme.Opens.topIso (g ⁻¹ᵁ W)).inv := by
  have h := openPreimageLeftIso_hom_fst 𝒮 hS hT g W
  rw [ObjectProperty.FullSubcategory.comp_hom] at h
  have h2 : Scheme.Γ.map (pullback.fst
      (ObjectProperty.homMk (X := (⟨(W : Scheme.{u}), opensBelow_mem hS W⟩ :
        SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
        (Y := (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮))) W.ι)
        (ambientHom 𝒮 hS hT g)).hom.op ≫
      Scheme.Γ.map (openPreimageLeftIso 𝒮 hS hT g W).hom.hom.op = (g ∣_ W).appTop := by
    rw [← Functor.map_comp, ← op_comp, h]
    rfl
  refine (congrArg (fun k => (Scheme.Opens.topIso W).inv ≫ k) h2).trans ?_
  dsimp only
  simp only [Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  have key : ∀ (A : S.Opens) (hA : A = W) (B : T.Opens) (hB : B = g ⁻¹ᵁ W) e e',
      S.presheaf.map (eqToHom hA).op ≫ g.appLE A B e =
        g.appLE W (g ⁻¹ᵁ W) e' ≫ T.presheaf.map (eqToHom hB).op := by
    rintro A rfl B rfl e e'
    simp
  exact key _ _ _ _ _ _

/-- The two functors from the opens of `S` to the big site over `T`, `W ↦ g⁻¹W` and
`W ↦ W ×_S T`, are isomorphic. -/
def openPreimageNatIso :
    Opens.map g.base ⋙ (BigSite.ofAmbient 𝒮 T hT).opensToBig ≅
      (BigSite.ofAmbient 𝒮 S hS).opensToBig ⋙ Over.pullback (ambientHom 𝒮 hS hT g) :=
  NatIso.ofComponents (openPreimageIsoPullback 𝒮 hS hT g) fun {_ _} _ ↦
    ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).homEquiv _ _).symm.injective
      (overHom_ext_opensBelowObj _ _)

/-- The morphism of ringed topoi `(T_Zar, 𝒪_T) ⟶ (S_Zar, 𝒪_S)` of `g`. -/
abbrev zariskiOpenHom : RingedToposHom T.zariskiRingedSite.toRingedTopos
    S.zariskiRingedSite.toRingedTopos :=
  g.zariskiRingedSiteHom.toRingedToposHom

/-- **The square of direct images.** Base change to the big site over `T` followed by `f_*` on
the big site over `S` is `f_*` on the big site over `T` followed by `g_*`. -/
def openSquarePushforwardIso :
    openPushforward 𝒮 hS hT g ⋙
        (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules ≅
      (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.pushforwardModules ⋙
        (zariskiOpenHom g).pushforwardModules :=
  letI := ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.toRingedToposSiteHom.comp
      (openRingedToposSiteHom 𝒮 hS hT g)).isContinuous
  letI : (Opens.map g.base ⋙ (BigSite.ofAmbient 𝒮 T hT).opensToBig).IsContinuous
      S.zariskiRingedSite.toRingedTopos.J (BigSite.ofAmbient 𝒮 T hT).ringedSite.toRingedTopos.J :=
    (g.zariskiRingedSiteHom.toRingedToposSiteHom.comp
      (BigSite.ofAmbient 𝒮 T hT).zariskiRingedSiteHom.toRingedToposSiteHom).isContinuous
  Functor.isoWhiskerLeft (openPushforward 𝒮 hS hT g)
      (BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.pushforwardToposIsoGeneral ≪≫
    (RingedToposSiteHom.pushforwardToposCompIso (openRingedToposSiteHom 𝒮 hS hT g)
      (BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.toRingedToposSiteHom).symm ≪≫
    SheafOfModules.pushforwardCongr₂ _ (openPreimageNatIso 𝒮 hS hT g) (by
      apply ObjectProperty.hom_ext
      ext V x
      change ((Scheme.Opens.topIso V.unop).inv ≫ Scheme.Γ.map (pullback.fst
          (ObjectProperty.homMk (X := (⟨(V.unop : Scheme.{u}), opensBelow_mem hS V.unop⟩ :
            SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
            (Y := (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮))) V.unop.ι)
            (ambientHom 𝒮 hS hT g)).hom.op ≫
          Scheme.Γ.map (openPreimageLeftIso 𝒮 hS hT g V.unop).hom.hom.op) x =
        (g.app V.unop ≫ (Scheme.Opens.topIso (g ⁻¹ᵁ V.unop)).inv) x
      exact congrArg (fun φ => (ConcreteCategory.hom φ) x)
        (openSquare_structureMap 𝒮 hS hT g V.unop)) ≪≫
    RingedToposSiteHom.pushforwardToposCompIso
      (BigSite.ofAmbient 𝒮 T hT).zariskiRingedSiteHom.toRingedToposSiteHom
      g.zariskiRingedSiteHom.toRingedToposSiteHom ≪≫
    Functor.isoWhiskerRight
      (BigSite.ofAmbient 𝒮 T hT).zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm _ ≪≫
    Functor.isoWhiskerLeft _ g.zariskiRingedSiteHom.pushforwardToposIsoGeneral.symm

/-! ### The base change transformations -/

/-- The comparison `g^* ⋙ f_T^* ⟶ f^* ⋙ j^*` of the two pullbacks around the square, conjugate to
the isomorphism `openSquarePushforwardIso` of the direct images. -/
@[irreducible] def openSquarePullbackHom :
    (zariskiOpenHom g).toModulesHom.pullbackModules ⋙
        (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.toModulesHom.pullbackModules ⟶
      (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules ⋙
        openRestrict 𝒮 hS hT g :=
  (conjugateEquiv
    ((RingedToposHom.pullbackAdjPushforwardModules
      (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom).comp (openRestrictAdjunction 𝒮 hS hT g))
    ((RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g)).comp
      (RingedToposHom.pullbackAdjPushforwardModules
        (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom))).symm
    (openSquarePushforwardIso 𝒮 hS hT g).hom

/-- The comparison `openSquarePullbackHom` of the two pullbacks around the square is an
isomorphism. -/
instance isIso_openSquarePullbackHom : IsIso (openSquarePullbackHom 𝒮 hS hT g) := by
  rw [openSquarePullbackHom]
  exact conjugateEquiv_symm_iso _ _ (openSquarePushforwardIso 𝒮 hS hT g).hom

/-- The base change transformation `g^* ⋙ f_* ⟶ j^* ⋙ f_{T,*}` of the square, the mate of
`openSquarePullbackHom` for the adjunctions `f^* ⊣ f_*` over `S` and over `T`. -/
abbrev openSquareBaseChange :=
  (mateEquiv (G := (zariskiOpenHom g).toModulesHom.pullbackModules)
    (H := openRestrict 𝒮 hS hT g)
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom)
    (openSquarePullbackHom 𝒮 hS hT g))

/-- **The restriction of the unit is the unit of the restriction**, up to the two base change
transformations. -/
theorem openSquare_unit (c : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)) :
    (zariskiOpenHom g).toModulesHom.pullbackModules.map
        ((RingedToposHom.pullbackAdjPushforwardModules
          (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom).unit.app c) ≫
      (openSquareBaseChange 𝒮 hS hT g).app
        ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.toModulesHom.pullbackModules.obj c) =
    (RingedToposHom.pullbackAdjPushforwardModules
        (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom).unit.app
        ((zariskiOpenHom g).toModulesHom.pullbackModules.obj c) ≫
      (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom.pushforwardModules.map
        ((openSquarePullbackHom 𝒮 hS hT g).app c) := by
  simpa only [Functor.id_obj] using
    unit_mateEquiv (G := (zariskiOpenHom g).toModulesHom.pullbackModules)
    (H := openRestrict 𝒮 hS hT g)
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom)
    (openSquarePullbackHom 𝒮 hS hT g) c

/-- The base change transformation is the inverse mate of the isomorphism of direct images. -/
theorem openSquareBaseChange_eq :
    TwoSquare.mk _ _ _ _ (openSquareBaseChange 𝒮 hS hT g) =
      (mateEquiv (openRestrictAdjunction 𝒮 hS hT g)
        (RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g))).symm
        (TwoSquare.mk _ _ _ _ (openSquarePushforwardIso 𝒮 hS hT g).hom) := by
  apply (mateEquiv (openRestrictAdjunction 𝒮 hS hT g)
    (RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g))).injective
  rw [Equiv.apply_symm_apply]
  have e : conjugateEquiv
      ((RingedToposHom.pullbackAdjPushforwardModules
        (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom).comp (openRestrictAdjunction 𝒮 hS hT g))
      ((RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g)).comp
        (RingedToposHom.pullbackAdjPushforwardModules
          (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom))
      (openSquarePullbackHom 𝒮 hS hT g) = (openSquarePushforwardIso 𝒮 hS hT g).hom := by
    rw [openSquarePullbackHom, Equiv.apply_symm_apply]
  exact (iterated_mateEquiv_conjugateEquiv
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules (BigSite.ofAmbient 𝒮 T hT).zariskiRingedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g))
    (openRestrictAdjunction 𝒮 hS hT g) (openSquarePullbackHom 𝒮 hS hT g)).trans e

/-- The components of an inverse mate. -/
theorem mateEquiv_symm_app {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F}
    {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm α).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (α.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  dsimp [mateEquiv]
  simp

/-- A pullback along a monomorphism of an arrow factoring through it has invertible first
projection. -/
theorem isIso_pullback_fst_of_eq_comp {C : Type*} [Category* C] {X Y Z : C} {f : X ⟶ Z}
    {i : Y ⟶ Z} [Mono i] [HasPullback f i] (h : X ⟶ Y) (hf : f = h ≫ i) :
    IsIso (pullback.fst f i) := by
  refine ⟨⟨pullback.lift (𝟙 X) h (by rw [Category.id_comp, hf]), ?_, pullback.lift_fst _ _ _⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono i, Category.assoc, Category.assoc, pullback.lift_snd_assoc,
      Category.id_comp, ← hf]
    exact pullback.condition

variable [IsOpenImmersion g]

/-- An open immersion `g : T ⟶ S` is a monomorphism in the ambient category of schemes. -/
instance mono_ambientHom : Mono (ambientHom 𝒮 hS hT g) :=
  (ObjectProperty.ι _).mono_of_mono_map (show Mono g from inferInstance)

/-- The base change to `T` of an open of `S` contained in the image of `T` is that open. -/
theorem isIso_mapPullbackAdj_counit_app (W : S.Opens) (hW : W ≤ g.opensRange) :
    IsIso ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit.app
      ((BigSite.ofAmbient 𝒮 S hS).opensToBig.obj W)) := by
  have hr : Set.range W.ι ⊆ Set.range g := by
    rwa [Scheme.Opens.range_ι]
  let X : Over (⟨S, hS⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)) :=
    (BigSite.ofAmbient 𝒮 S hS).opensToBig.obj W
  have hfac : X.hom =
      ObjectProperty.homMk (Y := (⟨T, hT⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)))
        (IsOpenImmersion.lift g W.ι hr) ≫ ambientHom 𝒮 hS hT g :=
    ObjectProperty.hom_ext _ (IsOpenImmersion.lift_fac g W.ι hr).symm
  have : IsIso
      ((Over.forget _).map ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit.app X)) := by
    simpa only [Over.forget_map, Over.mapPullbackAdj_counit_app, Over.homMk_left] using
      isIso_pullback_fst_of_eq_comp _ hfac
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The direct image of modules along the morphism of ringed topoi of `g` is the direct image of
`𝒪_T`-modules along `g`. -/
def zariskiOpenPushforwardIso :
    (zariskiOpenHom g).pushforwardModules ≅ Scheme.Modules.pushforward g :=
  g.zariskiRingedSiteHom.pushforwardToposIsoGeneral

/-- The direct image of modules along an open immersion `g` is full. -/
instance full_zariskiOpenPushforward : (zariskiOpenHom g).pushforwardModules.Full :=
  @Functor.Full.of_iso _ _ _ _ _ _
    (Scheme.Modules.restrictAdjunction g).fullyFaithfulROfIsIsoCounit.full
    (zariskiOpenPushforwardIso g).symm

/-- The direct image of modules along an open immersion `g` is faithful. -/
instance faithful_zariskiOpenPushforward : (zariskiOpenHom g).pushforwardModules.Faithful :=
  @Functor.Faithful.of_iso _ _ _ _ _ _
    (Scheme.Modules.restrictAdjunction g).fullyFaithfulROfIsIsoCounit.faithful
    (zariskiOpenPushforwardIso g).symm

/-- Restriction of `𝒪_S`-modules to the open subscheme `T`, read on the categories of modules of
the two small Zariski ringed topoi. -/
abbrev zariskiOpenRestrictFunctor :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.toRingedTopos.O) :=
  Scheme.Modules.restrictFunctor g

/-- The pullback of modules along `g` is restriction to the open subscheme `T`. -/
def zariskiOpenPullbackIso :
    (zariskiOpenHom g).toModulesHom.pullbackModules ≅ zariskiOpenRestrictFunctor g :=
  ((RingedToposHom.pullbackAdjPushforwardModules (zariskiOpenHom g)).ofNatIsoRight
    (zariskiOpenPushforwardIso g)).leftAdjointUniq (Scheme.Modules.restrictAdjunction g)

/-- **Restricting to `T` the image under `f_*` of the unit of `j^* ⊣ j_*` gives an isomorphism**:
over an open `V` of `T` it is the restriction map of the module along the projection
`g(V) ×_S T ⟶ g(V)`, which is an isomorphism because `g(V)` lies in the image of `T`. -/
theorem isIso_zariskiOpenPullback_map_unit (M : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) :
    IsIso ((zariskiOpenHom g).toModulesHom.pullbackModules.map
      ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.map
        ((openRestrictAdjunction 𝒮 hS hT g).unit.app M))) := by
  rw [NatIso.isIso_map_iff (zariskiOpenPullbackIso g)]
  have key : IsIso ((zariskiOpenRestrictFunctor g).map
      ((BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos.map
        ((openRestrictAdjunction 𝒮 hS hT g).unit.app M))) := by
    refine Stacks.AlgebraicGeometry.ModuleNatTransGlue.isIso_of_isIso_app _ fun V ↦ ?_
    have hc := isIso_mapPullbackAdj_counit_app 𝒮 hS hT g (g ''ᵁ V) (g.image_le_opensRange V)
    change IsIso (M.val.presheaf.map ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit.app
      ((BigSite.ofAmbient 𝒮 S hS).opensToBig.obj (g ''ᵁ V))).op)
    exact @Functor.map_isIso _ _ _ _ _ _ M.val.presheaf _ (@isIso_op _ _ _ _ _ hc)
  let e := (BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.pushforwardToposIsoGeneral
  have hη : (BigSite.ofAmbient 𝒮 S hS).zariskiRingedToposHom.pushforwardModules.map
      ((openRestrictAdjunction 𝒮 hS hT g).unit.app M) =
      e.hom.app _ ≫
        (BigSite.ofAmbient 𝒮 S hS).zariskiRingedSiteHom.toRingedToposSiteHom.pushforwardTopos.map
          ((openRestrictAdjunction 𝒮 hS hT g).unit.app M) ≫ e.inv.app _ := by
    rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hη, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The base change transformation of the square is an isomorphism.** It is the inverse mate of
the isomorphism of direct images, whose components are `g^*` of the unit of `j^* ⊣ j_*` after
`f_*`, which is invertible over `T`, `g^*` of that isomorphism, and the counit of `g^* ⊣ g_*`,
which is invertible because `g_*` is fully faithful for an open immersion. -/
instance isIso_openSquareBaseChange_app (M : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) :
    IsIso ((openSquareBaseChange 𝒮 hS hT g).app M) := by
  have h := congrArg (fun α ↦ α.app M) (openSquareBaseChange_eq 𝒮 hS hT g)
  simp only [mateEquiv_symm_app] at h
  rw [show (openSquareBaseChange 𝒮 hS hT g).app M = _ from h]
  have := isIso_zariskiOpenPullback_map_unit 𝒮 hS hT g M
  infer_instance

end Stacks.Adequate

end
