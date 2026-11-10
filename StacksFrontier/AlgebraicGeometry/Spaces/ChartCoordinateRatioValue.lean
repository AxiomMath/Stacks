module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinateValue

/-!
# The coordinates of a chart of an inverse image as values of a ratio, in general

Let `ι : U ⟶ P`, `π : P ⟶ X` be morphisms of algebraic spaces, `τ : π^*𝓕 ⟶ 𝓛`, and
`q : (π ∘ ι)^*ℰ ⟶ 𝒪_U` the ratio of `ι^*(π^*σ_E ≫ τ)` and `ι^*(π^*σ_O ≫ τ)` for `σ_E : ℰ ⟶ 𝓕` and
`σ_O : 𝒪_X ⟶ 𝓕`. For a chart diagram `U_c ⟶ V` over `π ∘ ι`, if the inverse images to `U_c` of the
`π^*σ ≫ τ` read on the scheme of `U_c` as `g^*σ_V` followed by the pulled-back tautological
quotient along a morphism `f : U_c ⟶ 𝐏(𝓕|_V)` over `g : U_c ⟶ V`, with a common identification of
the targets, then the value of `q` on the inverse image of a section `x` of `ℰ` over `V` is the
value on `g^*x` of the coordinate morphism `c_f` of `f` for a split datum of `𝓕|_V`
(`Stacks.RelativeProj.UnitSplitting.splitCoordMap`). This is the core of Stacks 0ERW (proof),
stated over arbitrary data so that the projective completion instantiates it syntactically.

The unit compatibility of `AlgebraicGeometry.Space.chartSectionsReadingEquiv` at `V` and at `U_c`
is taken as hypotheses `hbV`, `hbU`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- Two morphisms to `𝒪_T` agree if `ζ.hom ≫ γ' = 𝟙` for an isomorphism `ζ : 𝒪_T ≅ P` and `γ`
sends the image `p` of `1` to `1`. -/
theorem _root_.Stacks.RelativeProj.eq_of_app_top_eq_one_of_iso {T : Scheme.{u}} {P : T.Modules}
    (ζ : Scheme.unitModule T ≅ P) (γ γ' : P ⟶ Scheme.unitModule T) (p : Γ(P, ⊤))
    (hp : ζ.hom.app ⊤ (1 : Γ(T, ⊤)) = p) (hγ' : ζ.hom ≫ γ' = 𝟙 _)
    (h : γ.app ⊤ p = (1 : Γ(T, ⊤))) : γ = γ' := by
  subst hp
  refine Stacks.RelativeProj.eq_of_iso_hom_comp_app_top_one ζ γ γ' ?_
  refine h.trans ?_
  rw [hγ']
  rfl

/-- `Stacks.RelativeProj.eq_of_app_top_eq_one_of_iso` with the value of `γ` given as `o` and
`o = 1` separately. -/
theorem _root_.Stacks.RelativeProj.eq_of_app_top_eq_of_eq_one_of_iso {T : Scheme.{u}}
    {P : T.Modules} (ζ : Scheme.unitModule T ≅ P) (γ γ' : P ⟶ Scheme.unitModule T)
    (p : Γ(P, ⊤)) (o : Γ(Scheme.unitModule T, ⊤))
    (hp : ζ.hom.app ⊤ (1 : Γ(T, ⊤)) = p) (hγ' : ζ.hom ≫ γ' = 𝟙 _) (h : γ.app ⊤ p = o)
    (ho : o = (1 : Γ(T, ⊤))) : γ = γ' :=
  Stacks.RelativeProj.eq_of_app_top_eq_one_of_iso ζ γ γ' p hp hγ' (h.trans ho)

/-- For `UV : R ≅ 𝒪_Y`, the isomorphism `𝒪_T ≅ g^*𝒪_Y ≅ g^*R` followed by `g^*UV.hom` and
`g^*𝒪_Y ≅ 𝒪_T` is the identity of `𝒪_T`. -/
theorem _root_.Stacks.RelativeProj.pullbackUnitIso_symm_trans_mapIso_hom_comp {T Y : Scheme.{u}}
    (g : T ⟶ Y) {R : Y.Modules} (UV : R ≅ Scheme.unitModule Y) :
    ((Scheme.Modules.pullbackUnitIso g).symm ≪≫ (Scheme.Modules.pullback g).mapIso UV.symm).hom ≫
      (Scheme.Modules.pullback g).map UV.hom ≫ (Scheme.Modules.pullbackUnitIso g).hom = 𝟙 _ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

/-- For `UV : R ≅ 𝒪_Y` with `UV.inv` sending `1` to `r`, the isomorphism `𝒪_T ≅ g^*𝒪_Y ≅ g^*R`
sends `1` to the pullback `g^*r` of `r`. -/
theorem _root_.Stacks.RelativeProj.pullbackUnitIso_symm_trans_mapIso_hom_app_one {T Y : Scheme.{u}}
    (g : T ⟶ Y) {R : Y.Modules} (UV : R ≅ Scheme.unitModule Y) (r : Γ(R, ⊤))
    (hr : UV.inv.app ⊤ (1 : Γ(Y, ⊤)) = r) :
    ((Scheme.Modules.pullbackUnitIso g).symm ≪≫ (Scheme.Modules.pullback g).mapIso UV.symm).hom.app
        ⊤ (1 : Γ(T, ⊤)) = pullbackSectionHom g R ⊤ ⊤ le_top r :=
  (Stacks.RelativeProj.pullbackUnitIso_inv_comp_map_app_top_one g UV.inv).trans
    (congrArg (fun z => pullbackSectionHom g R ⊤ ⊤ le_top z) hr)

/-- A section of `𝒪_Y` over an étale chart equal to `1`, as a function on the scheme of the
chart. -/
theorem eq_chartScheme_one_of_eq_one {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : AlgebraicSpaces B S hS} {W : SmallEtale B S hS Y.1}
    {a : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op W)}
    (h : a = (1 : (structureRingSheaf B S hS Y).obj.obj (op W))) :
    @Eq Γ(Scheme.unitModule (chartScheme W), ⊤) a (1 : Γ(chartScheme W, ⊤)) :=
  h

/-- An equation of functions on the scheme of an étale chart, read as an equation of sections of
`𝒪_Y` over the chart. -/
theorem eq_etale_of_eq_chartScheme {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : AlgebraicSpaces B S hS} {W : SmallEtale B S hS Y.1}
    {a b : Γ(Scheme.unitModule ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj W)), ⊤)} (h : a = b) :
    @Eq ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj (op W)) a b :=
  h

section RepresentedSpelling

/-! ### `θ` on chart sections of inverse images, in the spelling of the represented chart

The composite `U_c ⟶ U ⟶ X` has two spellings, with source `chartSpace U U_c` or with source
`representedAlgebraicSpace (chartFppfObject U U_c)`; the readings along a composite use the
second. These are the statements of
`AlgebraicGeometry.Space.chartSectionsReadingEquiv_modulePullbackChartSection` and
`AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_reading` in the second spelling. -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z) (N : Modules.{u, u} B S hS Z.1 Z.2)
  (hN : N.IsQuasicoherentOnSite) (d : ChartDiagram B S hS Y.1 Z.1 f.hom)
  (w : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Z d.V =
    @CategoryStruct.comp _ _
      (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj d.U)) Y Z
      (chartToSpace B S hS Y d.U) f)

omit d in
/-- **θ is natural in the module**, with the reading of the morphism spelled with source the
represented chart (`AlgebraicGeometry.Space.chartSectionsReadingEquiv_naturality`). -/
theorem chartSectionsReadingEquiv_naturality_rep {N₁ N₂ : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : N₁ ⟶ N₂) (W : SmallEtale B S hS Y.1) (x : N₁.val.obj (op W)) :
    chartSectionsReadingEquiv N₂ W (φ.val.app (op W) x) =
      (schemeReadingMap (T := (SmallEtale.toOver B S hS Y.1).obj W)
        (chartToSpace B S hS Y W) φ).app ⊤ (chartSectionsReadingEquiv N₁ W x) := by
  have h1 := modulePullbackChartSection_map B S hS
    (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj W))
    (chartToSpace B S hS Y W)
    (M := N₁) (M' := N₂) φ (readingChartDiagram W (𝟙 _) (chartToSpace_hom_eq W)) x
  have h2 := readingTopSectionsAddEquiv_map (chartFppfObject B S hS Y W)
    ((modulePullback B S hS
      (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj W))
      (chartToSpace B S hS Y W)).map φ)
    (modulePullbackChartSection B S hS
      (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj W))
      (chartToSpace B S hS Y W) N₁ (readingChartDiagram W (𝟙 _) (chartToSpace_hom_eq W)) x)
  rw [chartSectionsReadingEquiv_apply, chartSectionsReadingEquiv_apply]
  exact h1.symm.trans h2.symm

/-- The reading of the inverse image along `f` of a section `x` of `N` over `V`, transported by
`schemeReadingModulePullbackIso`, is the inverse image of `x` along the composite `U_c ⟶ Y ⟶ Z`
with source the represented chart. -/
theorem schemeReadingModulePullbackIso_hom_chartSectionsReadingEquiv_rep
    (x : N.val.obj (op d.V)) :
    (schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)).hom.app ⊤
        (chartSectionsReadingEquiv ((modulePullback B S hS f).obj N) d.U
          (modulePullbackChartSection B S hS f N d x)) =
      modulePullbackChartSection B S hS
        (@CategoryStruct.comp _ _
          (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj d.U))
          Y Z (chartToSpace B S hS Y d.U) f) N
        (ChartDiagram.comp B S hS (chartToSpace B S hS Y d.U) f
          (readingTopChartMap ((SmallEtale.toOver B S hS Y.1).obj d.U) ≫ 𝟙 _) d.g
          (readingChartDiagram_comm d.U (𝟙 _) (chartToSpace_hom_eq d.U)) d.comm) x := by
  rw [chartSectionsReadingEquiv_apply]
  exact (schemeReadingModulePullbackIso_hom_app_top f N (chartToSpace B S hS Y d.U) _).trans
    (pullbackComparison_inv_chartReadingSection f N d (𝟙 _) (chartToSpace_hom_eq d.U) x)

include w in
/-- `AlgebraicGeometry.Space.chartSectionsReadingEquiv_modulePullbackChartSection`, with the
composite `U_c ⟶ U ⟶ X` spelled with source the represented chart. -/
theorem chartSectionsReadingEquiv_modulePullbackChartSection_rep (x : N.val.obj (op d.V)) :
    chartSectionsReadingEquiv ((modulePullback B S hS f).obj N) d.U
        (modulePullbackChartSection B S hS f N d x) =
      (schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)).inv.app ⊤
        ((schemeReadingPullbackIso N hN d.g w).hom.app ⊤
          (pullbackSectionHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
            (schemeReading N (chartToSpace B S hS Z d.V)) ⊤ ⊤ le_top
            (chartSectionsReadingEquiv N d.V x))) := by
  have hψ' : (@CategoryStruct.comp _ _ (representedAlgebraicSpace B S hS
      ((SmallEtale.toOver B S hS Y.1).obj d.U)) Y Z (chartToSpace B S hS Y d.U) f).hom =
        yoneda.map (d.g ≫ 𝟙 _) ≫ d.V.1.hom := by
    rw [Category.comp_id]
    exact d.comm
  rw [chartSectionsReadingEquiv_apply N d.V x,
    ← chartReadingSection_comp N hN d.V d.g (𝟙 _) (chartToSpace_hom_eq d.V) w hψ' x]
  refine (scheme_modules_iso_inv_hom_app
    (schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)) ⊤ _).symm.trans ?_
  refine congrArg (fun z => (schemeReadingModulePullbackIso f N
    (chartToSpace B S hS Y d.U)).inv.app ⊤ z) ?_
  refine (schemeReadingModulePullbackIso_hom_chartSectionsReadingEquiv_rep f N d x).trans ?_
  exact modulePullbackChartSection_mk_congr_vertical
    (@CategoryStruct.comp _ _
      (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj d.U))
      Y Z (chartToSpace B S hS Y d.U) f) N _ _
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.id_comp _).trans (Category.comp_id _).symm))) x

include w in
/-- **The value of a morphism `φ : f^*N ⟶ 𝒪_Y` on a chart section of the inverse image**, read
on the scheme of the chart, given the unit compatibility `hb` of `chartSectionsReadingEquiv` at
`d.U`, with the composite spelled with source the represented chart. -/
theorem modulePullbackChartSection_value_eq_reading_rep
    (UA : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (chartToSpace B S hS Y d.U) ≅ Scheme.unitModule (chartScheme d.U))
    (hb : ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op d.U),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) d.U r) = r)
    (φ : (modulePullback B S hS f).obj N ⟶ SheafOfModules.unit (structureRingSheaf B S hS Y))
    (x : N.val.obj (op d.V)) :
    @Eq Γ(Scheme.unitModule (chartScheme d.U), ⊤)
      (φ.val.app (op d.U) (modulePullbackChartSection B S hS f N d x))
      (UA.hom.app ⊤
        ((schemeReadingMap (T := (SmallEtale.toOver B S hS Y.1).obj d.U)
          (chartToSpace B S hS Y d.U) φ).app ⊤
        ((schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)).inv.app ⊤
          ((schemeReadingPullbackIso N hN d.g w).hom.app ⊤
            (pullbackSectionHom
              (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
              (schemeReading N (chartToSpace B S hS Z d.V)) ⊤ ⊤ le_top
              (chartSectionsReadingEquiv N d.V x)))))) := by
  have h1 := chartSectionsReadingEquiv_naturality_rep φ d.U
    (modulePullbackChartSection B S hS f N d x)
  have h2 := chartSectionsReadingEquiv_modulePullbackChartSection_rep f N hN d w x
  rw [h2] at h1
  have h3 := hb (φ.val.app (op d.U) (modulePullbackChartSection B S hS f N d x))
  rw [h1] at h3
  exact h3.symm

omit w in
/-- A composite of four morphisms of `𝒪_T`-modules acts on global sections as the composite of
their actions. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.comp₄_app_top {T : Scheme.{u}}
    {P Q R W O : T.Modules} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ W) (e : W ⟶ O) (p : Γ(P, ⊤)) :
    (a ≫ b ≫ c ≫ e).app ⊤ p = e.app ⊤ (c.app ⊤ (b.app ⊤ (a.app ⊤ p))) :=
  rfl

include w in
/-- `AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_reading_rep` with the readings
composed, read from the scheme side. -/
theorem reading_comp_app_eq_modulePullbackChartSection_value
    (UA : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (chartToSpace B S hS Y d.U) ≅ Scheme.unitModule (chartScheme d.U))
    (hb : ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op d.U),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) d.U r) = r)
    (φ : (modulePullback B S hS f).obj N ⟶ SheafOfModules.unit (structureRingSheaf B S hS Y))
    (x : N.val.obj (op d.V)) :
    ((schemeReadingPullbackIso N hN d.g w).hom ≫
        (schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)).inv ≫
        schemeReadingMap (T := (SmallEtale.toOver B S hS Y.1).obj d.U)
          (chartToSpace B S hS Y d.U) φ ≫
        UA.hom).app ⊤
      (pullbackSectionHom
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
        (schemeReading N (chartToSpace B S hS Z d.V)) ⊤ ⊤ le_top
        (chartSectionsReadingEquiv N d.V x)) =
      φ.val.app (op d.U) (modulePullbackChartSection B S hS f N d x) := by
  have h1 := modulePullbackChartSection_value_eq_reading_rep f N hN d w UA hb φ x
  have h2 := Scheme.Modules.comp₄_app_top (schemeReadingPullbackIso N hN d.g w).hom
          (schemeReadingModulePullbackIso f N (chartToSpace B S hS Y d.U)).inv
          (schemeReadingMap (T := (SmallEtale.toOver B S hS Y.1).obj d.U)
            (chartToSpace B S hS Y d.U) φ)
          UA.hom
        (pullbackSectionHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
          (schemeReading N (chartToSpace B S hS Z d.V)) ⊤ ⊤ le_top
          (chartSectionsReadingEquiv N d.V x))
  with_reducible exact h2.trans h1.symm

include w in
/-- **The unit part**, generic: for `φ : f^*𝒪 ⟶ 𝒪` with `φ(f^*1) = 1` at the chart, the reading
of `φ` through the comparisons is the pullback of the identification `𝒪_V`-reading `≅ 𝒪`. -/
theorem reading_unit_eq_rep
    (hOq : (SheafOfModules.unit (structureRingSheaf B S hS Z) :
      Modules.{u, u} B S hS Z.1 Z.2).IsQuasicoherentOnSite)
    (UV : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS Z) :
        Modules.{u, u} B S hS Z.1 Z.2) (chartToSpace B S hS Z d.V) ≅
      Scheme.unitModule (chartScheme d.V))
    (UA : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (chartToSpace B S hS Y d.U) ≅ Scheme.unitModule (chartScheme d.U))
    (hbV : UV.inv.app ⊤ (1 : Γ(chartScheme d.V, ⊤)) =
      chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Z)) d.V
        (1 : (structureRingSheaf B S hS Z).obj.obj (op d.V)))
    (hbU : ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op d.U),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) d.U r) = r)
    (φ : (modulePullback B S hS f).obj (SheafOfModules.unit (structureRingSheaf B S hS Z)) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS Y))
    (hφ : φ.val.app (op d.U) (modulePullbackChartSection B S hS f
      (SheafOfModules.unit (structureRingSheaf B S hS Z)) d
        (1 : (structureRingSheaf B S hS Z).obj.obj (op d.V))) =
      (1 : (structureRingSheaf B S hS Y).obj.obj (op d.U))) :
    (schemeReadingPullbackIso _ hOq d.g w).hom ≫
        (schemeReadingModulePullbackIso f _ (chartToSpace B S hS Y d.U)).inv ≫
        schemeReadingMap (T := (SmallEtale.toOver B S hS Y.1).obj d.U)
          (chartToSpace B S hS Y d.U) φ ≫
        UA.hom =
      (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) d.g.left)).map UV.hom ≫
      (Scheme.Modules.pullbackUnitIso _).hom := by
  have e3 := reading_comp_app_eq_modulePullbackChartSection_value f
    (SheafOfModules.unit (structureRingSheaf B S hS Z) : Modules.{u, u} B S hS Z.1 Z.2) hOq
    d w UA hbU φ (1 : (structureRingSheaf B S hS Z).obj.obj (op d.V))
  have e7 := Stacks.RelativeProj.pullbackUnitIso_symm_trans_mapIso_hom_app_one
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left) UV _ hbV
  have hR := Stacks.RelativeProj.pullbackUnitIso_symm_trans_mapIso_hom_comp
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left) UV
  exact Stacks.RelativeProj.eq_of_app_top_eq_of_eq_one_of_iso _ _ _ _ _ e7 hR e3
    (eq_chartScheme_one_of_eq_one hφ)

end RepresentedSpelling

/-! ### `Φ` with the readings spelled by `schemeReadingMap` -/

section RatioReading

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)
  {F : Modules.{u, u} B S hS X.1 X.2} {L : Modules.{u, u} B S hS P.1 P.2}
  (τ : (modulePullback B S hS π).obj F ⟶ L)
  {E : Modules.{u, u} B S hS X.1 X.2} (hEq : E.IsQuasicoherentOnSite)
  (hOq : (SheafOfModules.unit (structureRingSheaf B S hS X) :
    Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
  (σE : E ⟶ F)
  (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
  {A Y : BigFppfOver B S hS} {ρ : A ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
  (c : representedAlgebraicSpace B S hS A ⟶ U)
  (wρ : representedSpaceMap B S hS ρ ≫ ψY = c ≫ (ι ≫ π))
  {TU : ((BigFppfOver.toScheme B S hS).obj A).Modules}
  (ε : representedZariskiModule B S hS A
    ((modulePullback B S hS c).obj ((modulePullback B S hS ι).obj L)) ≅ TU)
  (univE : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
  (univO : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading (SheafOfModules.unit (structureRingSheaf B S hS X) :
          Modules.{u, u} B S hS X.1 X.2) ψY) ⟶ TU)

/-- **`Φ`** (`AlgebraicGeometry.Space.reading_modulePullback_comp_inv_eq`) with the readings of
`q` and of the unit identification spelled with `AlgebraicGeometry.Space.schemeReadingMap`. -/
theorem reading_modulePullback_comp_inv_eq_schemeReadingMap
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))] [hU : IsIso univO]
    (hE : QuotientReadingHyp E hEq wρ univE ε
      ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σE))
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl E).symm)
    (hO : QuotientReadingHyp _ hOq wρ univO ε
      ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σO))
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl _).symm) :
    (schemeReadingPullbackIso E hEq ρ wρ).hom ≫ (schemeReadingModulePullbackIso (ι ≫ π) E c).inv ≫
      schemeReadingMap (T := A) (E' := SheafOfModules.unit (structureRingSheaf B S hS U)) c
        ((modulePullbackCompIso B S hS ι π).inv.app E ≫
          (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
          inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
            (modulePullback B S hS π).map σO ≫ τ)) ≫
          (modulePullbackUnitIso B S hS ι).hom) =
    univE ≫ inv univO ≫ (schemeReadingPullbackIso _ hOq ρ wρ).hom ≫
      (schemeReadingModulePullbackIso (ι ≫ π) _ c).inv ≫
      schemeReadingMap (T := A) (E' := SheafOfModules.unit (structureRingSheaf B S hS U)) c
        ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom) := by
  have h := reading_modulePullback_comp_inv_eq ι π τ hEq hOq σE σO c wρ ε univE univO hE hO
  with_reducible exact h

end RatioReading

/-! ### The coordinates as values of `q`, over arbitrary data -/

section Coordinates

/-- Composition shape for the coordinate identity. -/
theorem _root_.CategoryTheory.coord_shape {C : Type*} [Category C]
    {a b c d o e₁ e₂ k t : C} (A : a ⟶ b) (B : b ⟶ c) (Cq : c ⟶ d) (Ua : d ⟶ o)
    (X : a ⟶ e₁) (Y : e₁ ⟶ k) (P : k ⟶ e₂) (Q : e₂ ⟶ t) (W : t ⟶ d) (V : k ⟶ o)
    (hΦ : A ≫ B ≫ Cq = X ≫ Y ≫ P ≫ Q ≫ W) (hU : P ≫ Q ≫ W ≫ Ua = V) :
    A ≫ B ≫ Cq ≫ Ua = X ≫ Y ≫ V := by
  calc A ≫ B ≫ Cq ≫ Ua = (A ≫ B ≫ Cq) ≫ Ua := by simp only [Category.assoc]
    _ = (X ≫ Y ≫ P ≫ Q ≫ W) ≫ Ua := by rw [hΦ]
    _ = X ≫ Y ≫ V := by rw [← hU]; simp only [Category.assoc]

/-- The coordinate vector of `c` is the value of `c` on the pullback of the basis section. -/
theorem _root_.Stacks.RelativeProj.UnitSplitting.coordVector_eq_app {X T : Scheme.{u}}
    {G : X.Modules} {ι : Type u} (e : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ G) {g : T ⟶ X}
    (c : (Scheme.Modules.pullback g).obj G ⟶ Scheme.unitModule T) (j : ι) (x : Γ(G, ⊤))
    (hx : (Stacks.RelativeProj.UnitSplitting.basisMap e j).app ⊤ (1 : Γ(X, ⊤)) = x) :
    Stacks.RelativeProj.UnitSplitting.coordVector e c j =
      c.app ⊤ (pullbackSectionHom g G ⊤ ⊤ le_top x) := by
  subst hx
  have h := Stacks.RelativeProj.pullbackUnitIso_inv_comp_map_app_top_one g
    (Stacks.RelativeProj.UnitSplitting.basisMap e j)
  change c.app ⊤ (((Scheme.Modules.pullbackUnitIso g).inv ≫
    (Scheme.Modules.pullback g).map (Stacks.RelativeProj.UnitSplitting.basisMap e j)).app ⊤
      (1 : Γ(T, ⊤))) = _
  rw [h]

/-- Equal morphisms of `𝒪_T`-modules agree on global sections. -/
private theorem app_top_congr {T : Scheme.{u}} {P Q : T.Modules} {a b : P ⟶ Q} (h : a = b)
    (p : Γ(P, ⊤)) : a.app ⊤ p = b.app ⊤ p := by
  rw [h]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)
  {F : Modules.{u, u} B S hS X.1 X.2} {L : Modules.{u, u} B S hS P.1 P.2}
  (τ : (modulePullback B S hS π).obj F ⟶ L)
  {E : Modules.{u, u} B S hS X.1 X.2} (hEq : E.IsQuasicoherentOnSite)
  (hOq : (SheafOfModules.unit (structureRingSheaf B S hS X) :
    Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
  (σE : E ⟶ F)
  (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
  (d : ChartDiagram B S hS U.1 X.1 (ι ≫ π).hom)
  (wρ : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS X d.V =
    @CategoryStruct.comp _ _
      (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U)) U X
      (chartToSpace B S hS U d.U) (ι ≫ π))

include wρ hEq hOq in
/-- **The coordinates of `f : U_c ⟶ 𝐏(𝓕|_V)` are the values of `q`**, over arbitrary data: if the
inverse images to the chart `U_c` of `π^*σ ≫ τ` read as `g^*σ_V` followed by the pulled-back
tautological quotient along `f` (`hML`, with a common identification `ε` of the targets), then the
value of the ratio `q` on the inverse image of `x ∈ ℰ(V)` is the `j`-th coordinate of `f` for a
split datum `Sp` of `𝓕|_V` with `σ' = ℰ|_V ⟶ 𝓕|_V` and `σ = 𝒪_V ⟶ 𝓕|_V`, when `x` is the `j`-th
basis section of a trivialization `e` of `ℰ|_V`, given the unit compatibility `hbV`, `hbU` of
`AlgebraicGeometry.Space.chartSectionsReadingEquiv` at `V` and at `U_c`. -/
theorem modulePullbackChartSection_value_eq_coordVector
    [(schemeReading F (chartToSpace B S hS X d.V)).IsQuasicoherent]
    [(schemeReading E (chartToSpace B S hS X d.V)).IsQuasicoherent]
    {us : schemeReading F (chartToSpace B S hS X d.V) ⟶ schemeReading E (chartToSpace B S hS X d.V)}
    [Epi us] (Sp : Stacks.RelativeProj.UnitSplitting us)
    (UV : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) (chartToSpace B S hS X d.V) ≅
      Scheme.unitModule (chartScheme d.V))
    (UA : schemeReading (SheafOfModules.unit (structureRingSheaf B S hS U))
      (chartToSpace B S hS U d.U) ≅ Scheme.unitModule (chartScheme d.U))
    (hσ : Sp.σ = UV.inv ≫ schemeReadingMap (chartToSpace B S hS X d.V) σO)
    (hσ' : Sp.σ' = schemeReadingMap (chartToSpace B S hS X d.V) σE)
    (f : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS U.1).obj d.U) ⟶
      Stacks.RelativeProj.projectiveBundle (chartScheme d.V)
        (schemeReading F (chartToSpace B S hS X d.V)))
    (hg : f ≫ Stacks.RelativeProj.projectiveBundleToBase (chartScheme d.V)
        (schemeReading F (chartToSpace B S hS X d.V)) =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
    (hf : Set.range f.base ⊆ Stacks.RelativeProj.splitQuotientComplement us)
    (ε : representedZariskiModule B S hS ((SmallEtale.toOver B S hS U.1).obj d.U)
      ((modulePullback B S hS
        (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
        (chartToSpace B S hS U d.U)).obj ((modulePullback B S hS ι).obj L)) ≅
      (Scheme.Modules.pullback f).obj
        (Stacks.RelativeProj.tautologicalDatum (schemeReading F (chartToSpace B S hS X d.V))).twist)
    (hML : ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ F),
      QuotientReadingHyp M hM wρ
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) d.g.left)).map
          (schemeReadingMap (chartToSpace B S hS X d.V) σ₀) ≫
          (Stacks.RelativeProj.tautologicalDatum
            (schemeReading F (chartToSpace B S hS X d.V))).overQuotientMap f hg) ε
        ((modulePullback B S hS
          (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
          (chartToSpace B S hS U d.U)).map (compPullbackQuotient ι π τ σ₀))
        (QuasiCoherentDescent.pullbackComparison B S hS (chartToSpace B S hS U d.U) (ι ≫ π)
          (@CategoryStruct.comp _ _
            (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
            U X (chartToSpace B S hS U d.U) (ι ≫ π)) rfl M).symm)
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))]
    (hbV : UV.inv.app ⊤ (1 : Γ(chartScheme d.V, ⊤)) =
      chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS X)) d.V
        (1 : (structureRingSheaf B S hS X).obj.obj (op d.V)))
    (hbU : ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS U)).val.obj (op d.U),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS U)) d.U r) = r)
    (hw0 : ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app
      (op d.U) (modulePullbackChartSection B S hS (ι ≫ π)
        (SheafOfModules.unit (structureRingSheaf B S hS X)) d
          (1 : (structureRingSheaf B S hS X).obj.obj (op d.V))) =
      (1 : (structureRingSheaf B S hS U).obj.obj (op d.U)))
    {n : Type u} (e : SheafOfModules.free (R := (chartScheme d.V).ringCatSheaf) n ≅
      schemeReading E (chartToSpace B S hS X d.V)) (j : n) (x : E.val.obj (op d.V))
    (hx : (Stacks.RelativeProj.UnitSplitting.basisMap e j).app ⊤ (1 : Γ(chartScheme d.V, ⊤)) =
      chartSectionsReadingEquiv E d.V x) :
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom).val.app (op d.U)
      (modulePullbackChartSection B S hS (ι ≫ π) E d x) =
      Stacks.RelativeProj.UnitSplitting.coordVector e (Sp.splitCoordMap f hg hf) j := by
  have hU := Sp.isIso_map_comp_overQuotientMap UV (schemeReadingMap (chartToSpace B S hS X d.V) σO)
    hσ f hg hf
  have hΦ := reading_modulePullback_comp_inv_eq_schemeReadingMap ι π τ hEq hOq σE σO
    (A := (SmallEtale.toOver B S hS U.1).obj d.U) (ρ := d.g) (ψY := chartToSpace B S hS X d.V)
    (chartToSpace B S hS U d.U) wρ ε _ _ (hML E hEq σE) (hML _ hOq σO)
  have hunit := reading_unit_eq_rep (ι ≫ π) d wρ hOq UV UA hbV hbU
    ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom) hw0
  have hratio := Sp.splitCoordMap_eq_ratio UV (schemeReadingMap (chartToSpace B S hS X d.V) σO) hσ
    f hg hf
  have hmor := CategoryTheory.coord_shape _ _ _ _ _ _ _ _ _ _ hΦ hunit
  have hval := reading_comp_app_eq_modulePullbackChartSection_value (ι ≫ π) E hEq d wρ UA hbU
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom) x
  rw [Stacks.RelativeProj.UnitSplitting.coordVector_eq_app e _ j _ hx]
  rw [hσ'] at hratio
  exact eq_etale_of_eq_chartScheme
    ((app_top_congr hratio _).trans ((app_top_congr hmor _).symm.trans hval)).symm

end Coordinates

end AlgebraicGeometry.Space

end
