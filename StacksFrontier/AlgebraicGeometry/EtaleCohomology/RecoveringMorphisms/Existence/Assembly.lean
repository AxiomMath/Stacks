module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.ComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.GoodCharts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.StandardPresentationExists

/-!
# Stacks 04I7: the existence of the morphism of schemes

Let `g : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of locally ringed topoi and
`f : X ⟶ Y` the morphism of schemes glued from it (`AlgebraicGeometry.glueHom`).  On every good
chart `V'` of `Y_étale` (an affine chart lying over an affine open of `Y`) there is a comparison
isomorphism `g⁻¹h_{V'} ≅ h_{X ×_Y V'}` carrying `pr₂^* b` to `g⁻¹(b) ≫ g^♯`.  Through the
adjunction `g⁻¹ ⊣ g_*` and Yoneda this identifies the sections of `g_*F` and `f_*F` over every good
chart, naturally; good charts being cover-dense, this extends to an isomorphism `g_* ≅ f_*`, and
the defining property of the comparisons is exactly the compatibility of this isomorphism with
the two structure maps.  So `g` is 2-isomorphic to `(f_small, f_small^♯)`.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-- The pullback of global functions along the base-change projection is natural. -/
theorem smallEtaleRestrict_baseChangeRingHom {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)
    {V₁ V₂ : SmallEtale B Y.obj Y.property} (ι : V₁ ⟶ V₂)
    (b : ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj V₂, ⊤)) :
    smallEtaleRestrict B X.obj X.property ((smallEtaleBaseChange B f).map ι)
        (baseChangeRingHom f V₂ b) =
      baseChangeRingHom f V₁ (smallEtaleRestrict B Y.obj Y.property ι b) :=
  (ConcreteCategory.congr_hom ((structureSharp B f).hom.naturality ι.op) b).symm

/-- Morphisms of sheaves on `Y_étale` agree as soon as their restrictions to good charts do. -/
theorem sheaf_hom_ext_goodChart {B : BigEtaleSite.{u}} {Y : B.Scheme}
    {F F' : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u)}
    {φ χ : F ⟶ F'} (h : Functor.whiskerLeft (SmallEtale.goodChartInclusion B Y.obj Y.property).op
      φ.hom = Functor.whiskerLeft (SmallEtale.goodChartInclusion B Y.obj Y.property).op χ.hom) :
    φ = χ := by
  have := SmallEtale.goodChartInclusion_isCoverDense B Y.obj Y.property
  exact Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (ℱ := F.obj) (ℱ' := F')
    (G := SmallEtale.goodChartInclusion B Y.obj Y.property)).symm.injective h)

/-- The section-ring identification `smallEtaleSectionRingEquiv` and the Yoneda identification of
sections of the structure sheaf send a function `b` on `U` to the same morphism `h_U ⟶ 𝒪`. -/
theorem smallEtaleSectionRingEquiv_symm_eq_yonedaEquiv_symm {B : BigEtaleSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S}
    (U : SmallEtale B S hS) (b : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) :
    (smallEtaleSectionRingEquiv B S hS U).symm b =
      ((SmallEtale.topology B S hS).yonedaEquiv
        (F := Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) (X := U)).symm b := by
  apply (smallEtaleSectionRingEquiv B S hS U).injective
  rw [RingEquiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply
    ((SmallEtale.topology B S hS).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) (X := U)) b).symm

section Assembly

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (hg : g.IsLocallyRinged)

include hg

/-- **On a good chart, a comparison exists, is an isomorphism, and maps into `h_{X ×_Y V'}` are
detected by the pullbacks `pr₂^* b`.** -/
theorem exists_goodComparison (V' : SmallEtale B Y.obj Y.property)
    (hV' : SmallEtale.IsGoodChart B Y.obj Y.property V') :
    ∃ c : g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
        (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V'),
      IsIso c ∧ IsComparison g V' c ∧
        ∀ {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
          (φ χ : F ⟶ (smallEtaleYoneda B X.obj X.property).obj
            ((smallEtaleBaseChange B (glueHom g)).obj V')),
          (∀ b, φ ≫ (smallEtaleSectionRingEquiv B X.obj X.property _).symm
              (baseChangeRingHom (glueHom g) V' b) =
            χ ≫ (smallEtaleSectionRingEquiv B X.obj X.property _).symm
              (baseChangeRingHom (glueHom g) V' b)) → φ = χ := by
  obtain ⟨haff, V, ⟨k⟩⟩ := hV'
  have := haff
  have : Etale ((SmallEtale.toScheme B Y.obj Y.property).map k ≫ (V : Y.obj.Opens).ι) := by
    rw [← smallEtaleMap_eq_comp k]
    exact V'.property
  have : Etale ((SmallEtale.toScheme B Y.obj Y.property).map k) :=
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (V : Y.obj.Opens).ι
      (inferInstanceAs (Etale (V : Y.obj.Opens).ι)) ‹_›
  obtain ⟨n, P, ⟨pres⟩, hEt⟩ :=
    Stacks.EtaleCohomology.exists_standardPresentationOver
      ((SmallEtale.toScheme B Y.obj Y.property).map k)
  have := hEt
  refine ⟨comparison g hg V k P pres, isIso_comparison g hg V k P pres,
    isComparison_comparison g hg V k P pres, fun φ χ h => ?_⟩
  refine (sourceRelPresentation g V k P pres hg).hom_ext φ χ fun i => ?_
  rw [sourceRelPresentation_coord]
  exact h _

/-- The comparison on a good chart. -/
def goodComparison (V' : SmallEtale.GoodChart B Y.obj Y.property) :
    g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V'.obj) ⟶
      (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V'.obj) :=
  (exists_goodComparison g hg V'.obj V'.property).choose

/-- The comparison on a good chart is an isomorphism. -/
instance isIso_goodComparison (V' : SmallEtale.GoodChart B Y.obj Y.property) :
    IsIso (goodComparison g hg V') :=
  (exists_goodComparison g hg V'.obj V'.property).choose_spec.1

/-- The comparison on a good chart carries `pr₂^* b` to `g⁻¹(b) ≫ g^♯`. -/
theorem isComparison_goodComparison (V' : SmallEtale.GoodChart B Y.obj Y.property) :
    IsComparison g V'.obj (goodComparison g hg V') :=
  (exists_goodComparison g hg V'.obj V'.property).choose_spec.2.1

/-- Two morphisms into `h_{X ×_Y V'}`, for a good chart `V'`, are equal as soon as their
composites with every pullback `pr₂^* b` agree. -/
theorem goodChart_hom_ext (V' : SmallEtale.GoodChart B Y.obj Y.property)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
    (φ χ : F ⟶ (smallEtaleYoneda B X.obj X.property).obj
      ((smallEtaleBaseChange B (glueHom g)).obj V'.obj))
    (h : ∀ b, φ ≫ (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V'.obj b) =
      χ ≫ (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V'.obj b)) : φ = χ :=
  (exists_goodComparison g hg V'.obj V'.property).choose_spec.2.2 φ χ h

/-- **The comparisons are natural in the good chart.** -/
theorem goodComparison_naturality {V₁ V₂ : SmallEtale.GoodChart B Y.obj Y.property}
    (ι : V₁ ⟶ V₂) :
    goodComparison g hg V₁ ≫ (smallEtaleYoneda B X.obj X.property).map
        ((smallEtaleBaseChange B (glueHom g)).map ι.hom) =
      g.toToposHom.inverseImage.map ((smallEtaleYoneda B Y.obj Y.property).map ι.hom) ≫
        goodComparison g hg V₂ := by
  refine goodChart_hom_ext g hg V₂ _ _ fun b => ?_
  have hY := yoneda_map_comp_smallEtaleSectionRingEquiv_symm B Y.obj Y.property ι.hom b
  have hX := yoneda_map_comp_smallEtaleSectionRingEquiv_symm B X.obj X.property
    ((smallEtaleBaseChange B (glueHom g)).map ι.hom) (baseChangeRingHom (glueHom g) V₂.obj b)
  rw [smallEtaleRestrict_baseChangeRingHom] at hX
  have h₁ := isComparison_goodComparison g hg V₁ (smallEtaleRestrict B Y.obj Y.property ι.hom b)
  have h₂ := isComparison_goodComparison g hg V₂ b
  have e3 : g.toToposHom.inverseImage.map ((smallEtaleSectionRingEquiv B Y.obj Y.property
      V₁.obj).symm (smallEtaleRestrict B Y.obj Y.property ι.hom b)) ≫ g.fSharpSet =
      g.toToposHom.inverseImage.map ((smallEtaleYoneda B Y.obj Y.property).map ι.hom) ≫
        (g.toToposHom.inverseImage.map
          ((smallEtaleSectionRingEquiv B Y.obj Y.property V₂.obj).symm b) ≫ g.fSharpSet) := by
    rw [← hY, Functor.map_comp]
    exact Category.assoc _ _ _
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hX)).trans (h₁.trans (e3.trans
    ((congrArg (_ ≫ ·) h₂.symm).trans (Category.assoc _ _ _).symm)))

/-- The comparison on a good chart, as an isomorphism. -/
def goodComparisonIso (V' : SmallEtale.GoodChart B Y.obj Y.property) :
    g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V'.obj) ≅
      (SmallEtale.topology B X.obj X.property).yoneda.obj
        ((smallEtaleBaseChange B (glueHom g)).obj V'.obj) :=
  @asIso _ _ _ _ (goodComparison g hg V') (isIso_goodComparison g hg V')

/-- **The sections of `g_*F` and `f_*F` over a good chart agree**: through Yoneda, the adjunction
`g⁻¹ ⊣ g_*` and the comparison isomorphism, a section of `g_*F` over `V'` is a morphism
`h_{X ×_Y V'} ⟶ F`, i.e. a section of `F` over `X ×_Y V'`. -/
def goodSectionEquiv (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u))
    (V' : SmallEtale.GoodChart B Y.obj Y.property) :
    (g.toToposHom.pushforward.obj F).obj.obj (op V'.obj) ≃
      F.obj.obj (op ((smallEtaleBaseChange B (glueHom g)).obj V'.obj)) :=
  ((SmallEtale.topology B Y.obj Y.property).yonedaEquiv).symm.trans
    (((g.toToposHom.adj.homEquiv _ _).symm).trans
      ((Iso.homCongr (goodComparisonIso g hg V') (Iso.refl F)).trans
        (SmallEtale.topology B X.obj X.property).yonedaEquiv))

/-- `goodSectionEquiv` sends a section `s` of `g_*F` over `V'` to the section of `F` corresponding
under Yoneda to the inverse comparison followed by the adjoint of the morphism `h_{V'} ⟶ g_*F`
determined by `s`. -/
theorem goodSectionEquiv_apply (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u))
    (V' : SmallEtale.GoodChart B Y.obj Y.property)
    (s : (g.toToposHom.pushforward.obj F).obj.obj (op V'.obj)) :
    goodSectionEquiv g hg F V' s = (SmallEtale.topology B X.obj X.property).yonedaEquiv
      ((goodComparisonIso g hg V').inv ≫ (g.toToposHom.adj.homEquiv _ _).symm
        ((SmallEtale.topology B Y.obj Y.property).yonedaEquiv.symm s)) :=
  congrArg (SmallEtale.topology B X.obj X.property).yonedaEquiv
    (congrArg ((goodComparisonIso g hg V').inv ≫ ·) (Category.comp_id
      ((g.toToposHom.adj.homEquiv _ F).symm
        ((SmallEtale.topology B Y.obj Y.property).yonedaEquiv.symm s))))

/-- `goodSectionEquiv` commutes with restriction along a morphism of good charts. -/
theorem goodSectionEquiv_naturality (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u))
    {V₁ V₂ : SmallEtale.GoodChart B Y.obj Y.property} (ι : V₁ ⟶ V₂)
    (s : (g.toToposHom.pushforward.obj F).obj.obj (op V₂.obj)) :
    goodSectionEquiv g hg F V₁ ((g.toToposHom.pushforward.obj F).obj.map ι.hom.op s) =
      F.obj.map ((smallEtaleBaseChange B (glueHom g)).map ι.hom).op
        (goodSectionEquiv g hg F V₂ s) := by
  let Jy := SmallEtale.topology B Y.obj Y.property
  let Jx := SmallEtale.topology B X.obj X.property
  let cI₁ := goodComparisonIso g hg V₁
  let cI₂ := goodComparisonIso g hg V₂
  let m := g.toToposHom.inverseImage.map (Jy.yoneda.map ι.hom)
  let mX := Jx.yoneda.map ((smallEtaleBaseChange B (glueHom g)).map ι.hom)
  have h : m ≫ cI₂.hom = cI₁.hom ≫ mX := (goodComparison_naturality g hg ι).symm
  have key : cI₁.inv ≫ m = mX ≫ cI₂.inv :=
    (Iso.inv_comp_eq cI₁).2 (((Iso.eq_comp_inv cI₂).2 h).trans (Category.assoc _ _ _))
  let t := Jy.yonedaEquiv.symm s
  calc goodSectionEquiv g hg F V₁ ((g.toToposHom.pushforward.obj F).obj.map ι.hom.op s)
      = Jx.yonedaEquiv (cI₁.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm
          (Jy.yoneda.map ι.hom ≫ t)) :=
        (goodSectionEquiv_apply g hg F V₁ _).trans (congrArg (fun z => Jx.yonedaEquiv
          (cI₁.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm z))
          (Jy.yonedaEquiv_symm_naturality_left ι.hom _ s).symm)
    _ = Jx.yonedaEquiv ((cI₁.inv ≫ m) ≫ (g.toToposHom.adj.homEquiv _ _).symm t) :=
        congrArg Jx.yonedaEquiv ((congrArg (cI₁.inv ≫ ·)
          (Adjunction.homEquiv_naturality_left_symm _ _ _)).trans (Category.assoc _ _ _).symm)
    _ = Jx.yonedaEquiv (mX ≫ cI₂.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm t) :=
        congrArg Jx.yonedaEquiv ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))
    _ = F.obj.map ((smallEtaleBaseChange B (glueHom g)).map ι.hom).op
          (Jx.yonedaEquiv (cI₂.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm t)) :=
        (Jx.yonedaEquiv_naturality _ _).symm
    _ = _ := congrArg _ (goodSectionEquiv_apply g hg F V₂ s).symm

/-- The identification of the restrictions of `g_*F` and `f_*F` to the good charts. -/
def goodRestrictionIso (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)) :
    (SmallEtale.goodChartInclusion B Y.obj Y.property).op ⋙ (g.toToposHom.pushforward.obj F).obj ≅
      (SmallEtale.goodChartInclusion B Y.obj Y.property).op ⋙
        ((smallEtaleRingedToposHom B (glueHom g)).toToposHom.pushforward.obj F).obj :=
  NatIso.ofComponents (fun V' => (goodSectionEquiv g hg F V'.unop).toIso) (fun ι =>
    TypeCat.homEquiv.injective (funext fun s => goodSectionEquiv_naturality g hg F ι.unop s))

/-- `goodSectionEquiv` is natural in the sheaf `F`. -/
theorem goodSectionEquiv_natural {F F' : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
    (φ : F ⟶ F') (V' : SmallEtale.GoodChart B Y.obj Y.property)
    (s : (g.toToposHom.pushforward.obj F).obj.obj (op V'.obj)) :
    goodSectionEquiv g hg F' V' ((g.toToposHom.pushforward.map φ).hom.app (op V'.obj) s) =
      φ.hom.app _ (goodSectionEquiv g hg F V' s) := by
  let Jy := SmallEtale.topology B Y.obj Y.property
  let Jx := SmallEtale.topology B X.obj X.property
  refine (goodSectionEquiv_apply g hg F' V' _).trans ?_
  refine Eq.trans ?_ (congrArg (φ.hom.app _) (goodSectionEquiv_apply g hg F V' s).symm)
  refine Eq.trans ?_ (Jx.yonedaEquiv_comp _ φ)
  refine congrArg Jx.yonedaEquiv ?_
  refine (congrArg (fun z => (goodComparisonIso g hg V').inv ≫
    (g.toToposHom.adj.homEquiv _ _).symm z)
    (Jy.yonedaEquiv_symm_naturality_right V'.obj (g.toToposHom.pushforward.map φ) s).symm).trans ?_
  exact (congrArg ((goodComparisonIso g hg V').inv ≫ ·)
    (Adjunction.homEquiv_naturality_right_symm _ _ _)).trans (Category.assoc _ _ _).symm

/-- The isomorphism `g_*F ≅ f_*F`, extended from the good charts. -/
def pushforwardIsoApp (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)) :
    g.toToposHom.pushforward.obj F ≅
      (smallEtaleRingedToposHom B (glueHom g)).toToposHom.pushforward.obj F :=
  have := SmallEtale.goodChartInclusion_isCoverDense B Y.obj Y.property
  Functor.IsCoverDense.sheafIso (goodRestrictionIso g hg F)

/-- The restriction of `pushforwardIsoApp` to the good charts is `goodRestrictionIso`. -/
theorem whiskerLeft_pushforwardIsoApp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)) :
    Functor.whiskerLeft (SmallEtale.goodChartInclusion B Y.obj Y.property).op
      (pushforwardIsoApp g hg F).hom.hom = (goodRestrictionIso g hg F).hom :=
  have := SmallEtale.goodChartInclusion_isCoverDense B Y.obj Y.property
  Functor.IsCoverDense.sheafHom_restrict_eq _

/-- **`g_* ≅ f_*`.** -/
def pushforwardIso :
    g.toToposHom.pushforward ≅ (smallEtaleRingedToposHom B (glueHom g)).toToposHom.pushforward :=
  NatIso.ofComponents (fun F => pushforwardIsoApp g hg F) (fun {F F'} φ => by
    refine sheaf_hom_ext_goodChart ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      Functor.whiskerLeft_comp, Functor.whiskerLeft_comp,
      whiskerLeft_pushforwardIsoApp, whiskerLeft_pushforwardIsoApp]
    refine NatTrans.ext (funext fun V' => TypeCat.homEquiv.injective (funext fun s => ?_))
    exact goodSectionEquiv_natural g hg φ V'.unop s)

/-- **The isomorphism `g_* ≅ f_*` carries `g^♯` to `f^♯`.** -/
theorem pushforwardIso_commutes :
    RingedToposHom.forgetFSharp g ≫ (pushforwardIso g hg).hom.app
        ((RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
          (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B (glueHom g)) := by
  refine sheaf_hom_ext_goodChart ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerLeft_comp]
  change _ ≫ Functor.whiskerLeft _ (pushforwardIsoApp g hg _).hom.hom = _
  rw [whiskerLeft_pushforwardIsoApp]
  refine NatTrans.ext (funext fun V' => TypeCat.homEquiv.injective (funext fun s => ?_))
  let Jy := SmallEtale.topology B Y.obj Y.property
  let Jx := SmallEtale.topology B X.obj X.property
  let cI := goodComparisonIso g hg V'.unop
  change goodSectionEquiv g hg _ V'.unop
      ((RingedToposHom.forgetFSharp g).hom.app (op V'.unop.obj) s) =
    (show ↥Γ((SmallEtale.toScheme B X.obj X.property).obj
      ((smallEtaleBaseChange B (glueHom g)).obj V'.unop.obj), ⊤) from
      baseChangeRingHom (glueHom g) V'.unop.obj s)
  have hc := isComparison_goodComparison g hg V'.unop s
  have h1 : Jy.yonedaEquiv.symm ((RingedToposHom.forgetFSharp g).hom.app (op V'.unop.obj) s) =
      (smallEtaleSectionRingEquiv B Y.obj Y.property V'.unop.obj).symm s ≫
        RingedToposHom.forgetFSharp g :=
    (Jy.yonedaEquiv_symm_naturality_right V'.unop.obj (RingedToposHom.forgetFSharp g) s).symm.trans
      (congrArg (· ≫ RingedToposHom.forgetFSharp g)
        (smallEtaleSectionRingEquiv_symm_eq_yonedaEquiv_symm V'.unop.obj s).symm)
  have h2 : (g.toToposHom.adj.homEquiv _ _).symm
      ((smallEtaleSectionRingEquiv B Y.obj Y.property V'.unop.obj).symm s ≫
        RingedToposHom.forgetFSharp g) =
      g.toToposHom.inverseImage.map
        ((smallEtaleSectionRingEquiv B Y.obj Y.property V'.unop.obj).symm s) ≫ g.fSharpSet :=
    Adjunction.homEquiv_naturality_left_symm _ _ _
  have h3 : cI.inv ≫ (g.toToposHom.inverseImage.map
        ((smallEtaleSectionRingEquiv B Y.obj Y.property V'.unop.obj).symm s) ≫ g.fSharpSet) =
      (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V'.unop.obj s) :=
    (Iso.inv_comp_eq cI).2 hc.symm
  refine (goodSectionEquiv_apply g hg _ V'.unop _).trans ?_
  refine (congrArg (fun z => Jx.yonedaEquiv (cI.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm z))
    h1).trans ?_
  refine (congrArg (fun z => Jx.yonedaEquiv (cI.inv ≫ z)) h2).trans ?_
  refine (congrArg Jx.yonedaEquiv h3).trans ?_
  exact (congrArg Jx.yonedaEquiv (smallEtaleSectionRingEquiv_symm_eq_yonedaEquiv_symm _ _)).trans
    (Equiv.apply_symm_apply _ _)

/-- **The 2-isomorphism `(g, g^♯) ≅ (f_small, f_small^♯)`.** -/
def twoIsoGlueHom :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B (glueHom g)) where
  e := pushforwardIso g hg
  commutes := pushforwardIso_commutes g hg

end Assembly

/-- **The existence clause of Stacks 04I7 holds.** -/
theorem clause04I7 (B : BigEtaleSite.{u}) : Clause04I7 B :=
  fun _ _ g hg => ⟨glueHom g, ⟨twoIsoGlueHom g hg⟩⟩

/-- Let `X` and `Y` be schemes (of a big étale site) and let
`(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of locally ringed topoi.  Then
there is a unique morphism of schemes `f : X ⟶ Y` such that `(g, g^♯)` is 2-isomorphic to
`(f_small, f_small^♯)`.

Existence: `f` is glued from the morphisms `f_V : W_V ⟶ V` over the affine opens `V` of `Y`
determined by `g` on global sections (`AlgebraicGeometry.glueHom`), and the 2-isomorphism is
`AlgebraicGeometry.twoIsoGlueHom`.  Uniqueness is Stacks 04LW
(`AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`). -/
@[stacks 04I7]
theorem existsUnique_schemeHom_twoIso_smallEtaleRingedToposHom (B : BigEtaleSite.{u})
    {X Y : B.Scheme}
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B f)) :=
  existsUnique_schemeHom_twoIso_of_clause04I7 B (clause04I7 B) g hg

end AlgebraicGeometry

end
