module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSection

/-!
# θ on the structure sheaf

For a chart `W` of an algebraic space `Y`, the identification
`AlgebraicGeometry.Space.chartSectionsReadingEquiv` of the sections of a module over `W` with the
global sections of its scheme reading at `W` is, for `𝒪_Y` and under
`schemeReadingChartIso ≪≫ restrictToChartSchemeUnitIso`, the identity on functions:

* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_unit_one`: `1 ↦ 1`;
* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_unit_apply`: `r ↦ r` for every function `r`
  on `W`.

The unit case is a chase through the four factors of the composite (the étale pullback
comparison, the identity-chart identification, the transport along
`restrictToChartScheme_eq_atIdEtaleChart`, and the unit identification); the transport is handled
by heterogeneous equality of sheafification units over the two equal Zariski presheaves.  The
general case follows from the unit case by the linearity of θ over the functions on the chart
(`AlgebraicGeometry.Space.chartSectionsReadingEquiv_smul`).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.SheafificationUnit

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafifying a morphism of presheaves of modules, on a sheafification unit. -/
theorem sheafification_map_toSheafify {P Q : PresheafOfModules.{u} R.obj} (f : P ⟶ Q)
    (U : Cᵒᵖ) (m : P.obj U) :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).map f).val.app U
        ((CategoryTheory.toSheafify J P.presheaf).app U m) =
      (CategoryTheory.toSheafify J Q.presheaf).app U (f.app U m) :=
  (congrArg (fun φ => φ.app U m)
    ((PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 R.obj)).unit.naturality f)).symm

/-- The counit of the sheafification of presheaves of modules, on a sheafification unit. -/
theorem counitApp_toSheafify (M : _root_.SheafOfModules.{u} R) (U : Cᵒᵖ) (m : M.val.obj U) :
    (EpiMono.counitApp (J := J) M).val.app U
        ((CategoryTheory.toSheafify J M.val.presheaf).app U m) = m :=
  congrArg (fun φ => φ.app U m)
    ((PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 R.obj)).right_triangle_components M)

end Stacks.SheafOfModules.SheafificationUnit

namespace Stacks.SheafOfModules.SheafificationUnit

/-- The restriction maps of the unit sheaf of modules carry `1` to `1`. -/
theorem unit_val_map_one {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {U V : Cᵒᵖ} (f : U ⟶ V) :
    (_root_.SheafOfModules.unit R).val.map f (1 : R.obj.obj U) = (1 : R.obj.obj V) :=
  map_one (R.obj.map f).hom

end Stacks.SheafOfModules.SheafificationUnit

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section IsoPushforward

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F)
  [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(openChartFunctor B S hS F U).IsContinuous
    (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)]

/-- The inverse of the direct-image identification of the chart restriction is the
sheafification unit of the universe-lifted section. -/
theorem restrictToChartSchemeIsoPushforward_inv_app (O : (chartScheme U).Opens)
    (b : M.val.obj (op ((openChartFunctor B S hS F U).obj O))) :
    (restrictToChartSchemeIsoPushforward B S hS hF U M).inv.val.app (op O) b =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
        ((PresheafOfModules.pushforward
          (chartSchemeRestrictionRingHom B S hS F U)).obj
            (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) (ULift.up b) :=
  ((sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF U M)
      O).symm_apply_eq.mpr
    (sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify B S hS hF M U O
      (ULift.up b)).symm)

omit [(openChartFunctor B S hS F U).IsContinuous
    (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)] in
/-- **The identification of the chart restriction of `𝒪` with `𝒪` carries the sheafification
unit of `1` to `1`.** -/
theorem restrictToChartSchemeUnitIso_hom_toSheafify_one :
    (restrictToChartSchemeUnitIso B S hS F hF U).hom.val.app (op ⊤)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
            (SheafOfModules.uliftForPresentation (SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O)))).val).presheaf).app
          (op ⊤) (ULift.up (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).obj.obj
              (op ((openChartFunctor B S hS F U).obj ⊤))))) = (1 : Γ(chartScheme U, ⊤)) := by
  have : IsIso (chartSchemeRestrictionRingHom B S hS F U) :=
    inferInstanceAs (IsIso (Functor.whiskerRight
      (Scheme.restrictFunctorΓ (X := chartScheme U)).inv
      (forget₂ CommRingCat.{u} RingCat.{u})))
  let φ := (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).map
      ((SheafOfModules.forget _).mapIso
        (SheafOfModules.uliftForPresentationSelfIso.{u + 1, u, u, u} (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))))).hom ≫
    (PresheafOfModules.pushforwardUnitIso (chartSchemeRestrictionRingHom B S hS F U)).hom
  have hφ : φ.app (op ⊤) (ULift.up (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj
        (op ((openChartFunctor B S hS F U).obj ⊤)))) =
      (1 : (chartScheme U).ringCatSheaf.obj.obj (op ⊤)) :=
    map_one
      ((asIso (chartSchemeRestrictionRingHom B S hS F U)).app (op ⊤)).ringCatIsoToRingEquiv.symm
  refine Eq.trans (?_ : _ = (Stacks.SheafOfModules.EpiMono.counitApp
      (SheafOfModules.unit (chartScheme U).ringCatSheaf)).val.app (op ⊤)
      (((PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).map φ).val.app
        (op ⊤) ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
            (SheafOfModules.uliftForPresentation (SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O)))).val).presheaf).app
          (op ⊤) (ULift.up (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).obj.obj
              (op ((openChartFunctor B S hS F U).obj ⊤))))))) ?_
  · rfl
  refine (congrArg (fun z => (Stacks.SheafOfModules.EpiMono.counitApp
      (SheafOfModules.unit (chartScheme U).ringCatSheaf)).val.app (op ⊤) z)
    ((Stacks.SheafOfModules.SheafificationUnit.sheafification_map_toSheafify φ (op ⊤) _).trans
      (congrArg (fun w => (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
        (PresheafOfModules.unit (chartScheme U).ringCatSheaf.obj).presheaf).app (op ⊤) w)
          hφ))).trans ?_
  exact Stacks.SheafOfModules.SheafificationUnit.counitApp_toSheafify
    (SheafOfModules.unit (chartScheme U).ringCatSheaf) (op ⊤) _

end IsoPushforward

section IdChart

attribute [local irreducible] AlgebraicGeometry.Space.representedSmallEtaleEquivalence

variable (U : BigFppfOver B S hS)
  [HasSheafify (Opens.grothendieckTopology (chartScheme (idEtaleChart B S hS U))) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (chartScheme (idEtaleChart B S hS U))).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- A section over the top chart, read as a universe-lifted section over the top open chart of
the identity chart. -/
def readingIdChartLift
    (Q : Modules.{u, u} B S hS (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (z : Q.val.obj (op ((selfOpensFunctor B S hS U).obj ⊤))) :
    ((PresheafOfModules.pushforward
      (chartSchemeRestrictionRingHom B S hS (yoneda.obj U) (idEtaleChart B S hS U))).obj
        (SheafOfModules.uliftForPresentation Q).val).presheaf.obj (op ⊤) :=
  ULift.up (Q.val.map (eqToHom (selfOpensFunctor_obj B S hS U ⊤).symm).op z)

/-- The inverse of the identification of the restriction to the identity chart with the Zariski
restriction, on global sections. -/
theorem restrictToChartSchemeIdEtaleChartIso_inv_app_top
    (Q : Modules.{u, u} B S hS (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (z : Q.val.obj (op ((selfOpensFunctor B S hS U).obj ⊤))) :
    (restrictToChartSchemeIdEtaleChartIso B S hS U Q).inv.val.app (op ⊤) z =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme (idEtaleChart B S hS U)))
        ((PresheafOfModules.pushforward
          (chartSchemeRestrictionRingHom B S hS (yoneda.obj U) (idEtaleChart B S hS U))).obj
            (SheafOfModules.uliftForPresentation Q).val).presheaf).app (op ⊤)
        (readingIdChartLift U Q z) :=
  restrictToChartSchemeIsoPushforward_inv_app (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
    Q (idEtaleChart B S hS U) ⊤ (Q.val.map (eqToHom (selfOpensFunctor_obj B S hS U ⊤).symm).op z)

end IdChart

section ZariskiSheafify

variable (X : Scheme.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A transport along an equality of presheaves of modules, after Zariski sheafification, on a
sheafification unit. -/
theorem eqToHom_zariskiSheafify_toSheafify {P₁ P₂ : PresheafOfModules.{u} X.ringCatSheaf.obj}
    (h : P₁ = P₂) (O : X.Opens) (m₁ : P₁.obj (op O)) (m₂ : P₂.obj (op O)) (hm : HEq m₁ m₂) :
    (eqToHom (congrArg (zariskiSheafify X) h)).val.app (op O)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) P₁.presheaf).app (op O) m₁) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P₂.presheaf).app (op O) m₂ := by
  subst h
  cases hm
  rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A transport along an equality of sheaves of modules is, on sections, any heterogeneously equal
section. -/
theorem eqToHom_val_app_of_heq {M₁ M₂ : SheafOfModules.{u} X.ringCatSheaf} (h : M₁ = M₂)
    (O : X.Opens) (x₁ : M₁.val.obj (op O)) (x₂ : M₂.val.obj (op O)) (hx : HEq x₁ x₂) :
    (eqToHom h).val.app (op O) x₁ = x₂ := by
  subst h
  cases hx
  rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Sheafification units of heterogeneously equal sections of equal presheaves are
heterogeneously equal. -/
theorem toSheafify_heq {P₁ P₂ : PresheafOfModules.{u} X.ringCatSheaf.obj} (h : P₁ = P₂)
    (O : X.Opens) (m₁ : P₁.obj (op O)) (m₂ : P₂.obj (op O)) (hm : HEq m₁ m₂) :
    HEq ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) P₁.presheaf).app (op O) m₁)
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) P₂.presheaf).app (op O) m₂) := by
  subst h
  cases hm
  rfl

end ZariskiSheafify


attribute [local irreducible] AlgebraicGeometry.Space.representedSmallEtaleEquivalence in
/-- The reading of an isomorphism of modules on `yoneda.obj T`, on global sections, undoes its
inverse at the top chart. -/
theorem restrictModule_mapIso_inverse_mapIso_hom_app_top (T : BigFppfOver B S hS)
    {P P' : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)} (φ : P ≅ P')
    (z : P'.val.obj (op (readingTopChart T))) :
    ((SmallEtale.restrictModule (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso φ)).hom.app ⊤
        (φ.inv.val.app (op (readingTopChart T)) z) = z :=
  (readingTopSectionsAddEquiv_map T φ.hom _).trans
    (congrArg (fun m : P' ⟶ P' => m.val.app (op (readingTopChart T)) z) φ.inv_hom_id)


/-- θ, unfolded. -/
theorem chartSectionsReadingEquiv_eq_inv {Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1) (x : N.val.obj (op W)) :
    chartSectionsReadingEquiv N W x =
      (chartEtaleComparison N W).inv.val.app (op (readingTopChart (chartFppfObject B S hS Y W)))
        (chartEtaleTopSection N W x) :=
  rfl

attribute [local irreducible] AlgebraicGeometry.Space.representedSmallEtaleEquivalence in
/-- `restrictModule_mapIso_inverse_mapIso_hom_app_top` for modules on the chart space of a
chart. -/
theorem restrictModule_mapIso_inverse_mapIso_hom_app_top_chart {Y : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Y.1)
    {P P' : Modules.{u, u} B S hS (chartSpace B S hS Y W).1 (chartSpace B S hS Y W).2}
    (φ : P ≅ P') (z : P'.val.obj (op (readingTopChart (chartFppfObject B S hS Y W)))) :
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS Y W))
        (chartFppfObject B S hS Y W).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS Y W)).inverse.mapIso
        φ)).hom.app ⊤
        (φ.inv.val.app (op (readingTopChart (chartFppfObject B S hS Y W))) z) = z :=
  restrictModule_mapIso_inverse_mapIso_hom_app_top (chartFppfObject B S hS Y W) φ z

/-- Four composed isomorphisms of modules on a scheme, the first two together, on a section. -/
theorem scheme_modules_iso_trans₂₂_hom_app_eq {X : Scheme.{u}} {M₁ M₂ M₃ M₄ M₅ : X.Modules}
    (e₁ : M₁ ≅ M₂) (e₂ : M₂ ≅ M₃) (e₃ : M₃ ≅ M₄) (e₄ : M₄ ≅ M₅) (U : X.Opens) (y : Γ(M₁, U))
    {y₂ : Γ(M₃, U)} {y₃ : Γ(M₄, U)} {y₄ : Γ(M₅, U)}
    (h₁₂ : (e₁ ≪≫ e₂).hom.app U y = y₂) (h₃ : e₃.hom.val.app (op U) y₂ = y₃)
    (h₄ : e₄.hom.val.app (op U) y₃ = y₄) :
    ((e₁ ≪≫ e₂ ≪≫ e₃) ≪≫ e₄).hom.app U y = y₄ := by
  subst h₁₂ h₃ h₄
  rfl

/-- Two composed isomorphisms of modules on a scheme, on a section, step by step. -/
theorem scheme_modules_iso_trans₂_hom_app_eq {X : Scheme.{u}} {M₁ M₂ M₃ : X.Modules}
    (e₁ : M₁ ≅ M₂) (e₂ : M₂ ≅ M₃) (U : X.Opens) (y : Γ(M₁, U))
    {y₁ : Γ(M₂, U)} {y₂ : Γ(M₃, U)}
    (h₁ : e₁.hom.app U y = y₁) (h₂ : e₂.hom.val.app (op U) y₁ = y₂) :
    (e₁ ≪≫ e₂).hom.app U y = y₂ := by
  subst h₁ h₂
  rfl

/-- Three composed isomorphisms of modules on a scheme, on a section, step by step. -/
theorem scheme_modules_iso_trans₃_hom_app_eq {X : Scheme.{u}} {M₁ M₂ M₃ M₄ : X.Modules}
    (e₁ : M₁ ≅ M₂) (e₂ : M₂ ≅ M₃) (e₃ : M₃ ≅ M₄) (U : X.Opens) (y : Γ(M₁, U))
    {y₁ : Γ(M₂, U)} {y₂ : Γ(M₃, U)} {y₃ : Γ(M₄, U)}
    (h₁ : e₁.hom.app U y = y₁) (h₂ : e₂.hom.val.app (op U) y₁ = y₂)
    (h₃ : e₃.hom.val.app (op U) y₂ = y₃) :
    (e₁ ≪≫ e₂ ≪≫ e₃).hom.app U y = y₃ := by
  subst h₁ h₂ h₃
  rfl

/-- A morphism of modules on a scheme into `𝒪` which sends a section to `1` sends its multiple by a
function to that function. -/
theorem scheme_modules_hom_app_smul_of_eq_one {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (c : Γ(X, ⊤)) (y : Γ(M, ⊤))
    (hy : φ.app ⊤ y = (1 : Γ(X, ⊤))) : φ.app ⊤ (c • y) = c :=
  (Scheme.Modules.Hom.app_smul φ c y).trans (by rw [hy]; exact mul_one c)

section Unit

variable {Y : AlgebraicSpaces B S hS}

attribute [local irreducible] AlgebraicGeometry.Space.representedSmallEtaleEquivalence in
/-- The first two factors of `schemeReadingChartIso`, on the global section of the reading which
comes from a section over the top chart: the sheafification unit of its lift to the identity
chart. -/
theorem schemeReadingChartIso_firstTwo_app_etaleTop (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1)
    [HasSheafify (Opens.grothendieckTopology (chartScheme W)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme W)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (z : ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)).obj N).val.obj
        (op (readingTopChart (chartFppfObject B S hS Y W)))) :
    (((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS Y W))
        (chartFppfObject B S hS Y W).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS Y W)).inverse.mapIso
        ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y W)
          (isEtale_chartToSpace B S hS Y W)).app N))) ≪≫
      (restrictToChartSchemeIdEtaleChartIso B S hS (chartFppfObject B S hS Y W)
        ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
          (isEtale_chartToSpace B S hS Y W)).obj N)).symm).hom.app ⊤
        ((chartEtaleComparison N W).inv.val.app
          (op (readingTopChart (chartFppfObject B S hS Y W))) z) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme
          (idEtaleChart B S hS (chartFppfObject B S hS Y W))))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS
            (yoneda.obj (chartFppfObject B S hS Y W))
            (idEtaleChart B S hS (chartFppfObject B S hS Y W)))).obj
          (SheafOfModules.uliftForPresentation
            ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
            (isEtale_chartToSpace B S hS Y W)).obj N)).val).presheaf).app (op ⊤)
        (readingIdChartLift (chartFppfObject B S hS Y W) ((etaleModulePullback B S hS
          (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).obj N) z) := by
  refine scheme_modules_iso_trans₂_hom_app_eq _ _ ⊤ _ (y₁ := ?y₁) ?h₁ ?h₂
  case h₁ =>
    exact restrictModule_mapIso_inverse_mapIso_hom_app_top_chart W
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).app N) z
  case h₂ =>
    exact restrictToChartSchemeIdEtaleChartIso_inv_app_top (chartFppfObject B S hS Y W)
      ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).obj N) z

/-- The unit section over the top chart, restricted to the top open chart. -/
theorem etale_unit_top_one (W : SmallEtale B S hS Y.1) :
    ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).obj (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).val.map
        (eqToHom (selfOpensFunctor_obj B S hS (chartFppfObject B S hS Y W) ⊤).symm).op
        (chartEtaleTopSection _ W (1 : (structureRingSheaf B S hS Y).obj.obj (op W))) =
      (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj
        (op ((smallEtalePostcomp B S hS (chartToSpace B S hS Y W)
          (isEtale_chartToSpace B S hS Y W)).obj
          ((openChartFunctor B S hS (chartSpace B S hS Y W).1
            (idEtaleChart B S hS (chartFppfObject B S hS Y W))).obj ⊤)))) :=
  (congrArg (fun z => ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).obj (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).val.map
        (eqToHom (selfOpensFunctor_obj B S hS (chartFppfObject B S hS Y W) ⊤).symm).op z)
      (Stacks.SheafOfModules.SheafificationUnit.unit_val_map_one
        (readingTopChartPostcomp W).op)).trans
    (Stacks.SheafOfModules.SheafificationUnit.unit_val_map_one _)

/-- The presheaf of the restriction of the étale pullback to the identity chart of the chart space
is the presheaf of the restriction to the chart. -/
theorem chartZariskiPresheaf_etale_eq (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) :
    (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS
        (yoneda.obj (chartFppfObject B S hS Y W))
        (idEtaleChart B S hS (chartFppfObject B S hS Y W)))).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u}
        ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).obj N)).val =
    (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS Y.1 W)).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val :=
  chartZariskiPresheafOf_etalePresheafPullback B S hS Y W
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} N).val

/-- Lifted unit sections over equal charts are heterogeneously equal. -/
theorem ulift_one_heq {A A' : SmallEtale B S hS Y.1} (h : A = A') :
    HEq (ULift.up.{u} (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op A)))
      (ULift.up.{u} (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op A'))) := by
  subst h
  rfl

/-- The top Zariski open of the identity chart of the chart space, pushed to `Y`, is the top
Zariski open of the chart. -/
theorem smallEtalePostcomp_obj_openChartFunctor_idEtaleChart_top (W : SmallEtale B S hS Y.1) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).obj
      ((openChartFunctor B S hS (chartSpace B S hS Y W).1
        (idEtaleChart B S hS (chartFppfObject B S hS Y W))).obj ⊤) =
      (openChartFunctor B S hS Y.1 W).obj ⊤ :=
  Functor.congr_obj (openChartFunctor_idEtaleChart_comp_smallEtalePostcomp B S hS Y W) ⊤

attribute [local irreducible] AlgebraicGeometry.Space.openChart AlgebraicGeometry.Space.openSub
  AlgebraicGeometry.Space.idEtaleChart in
/-- The lift of the unit section is heterogeneously the lifted unit section. -/
theorem readingIdChartLift_one_heq (W : SmallEtale B S hS Y.1) :
    HEq (readingIdChartLift (chartFppfObject B S hS Y W) ((etaleModulePullback B S hS
        (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))))
        (chartEtaleTopSection _ W (1 : (structureRingSheaf B S hS Y).obj.obj (op W))))
      (ULift.up.{u} (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj
          (op ((openChartFunctor B S hS Y.1 W).obj ⊤)))) :=
  (heq_of_eq (congrArg ULift.up (etale_unit_top_one W))).trans
    (ulift_one_heq (smallEtalePostcomp_obj_openChartFunctor_idEtaleChart_top W))

/-- The transport along `restrictToChartScheme_eq_atIdEtaleChart`, for `𝒪`, carries the
sheafification unit of the lifted unit section over the identity chart to the sheafification unit
of the lifted unit section over the chart. -/
theorem eqToHom_restrictToChartScheme_eq_atIdEtaleChart_unit_toSheafify (W : SmallEtale B S hS Y.1)
    [HasSheafify (Opens.grothendieckTopology (chartScheme W)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme W)).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (eqToHom (restrictToChartScheme_eq_atIdEtaleChart B S hS Y W (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).symm).val.app
        (op ⊤)
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme
          (idEtaleChart B S hS (chartFppfObject B S hS Y W))))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS
            (yoneda.obj (chartFppfObject B S hS Y W))
            (idEtaleChart B S hS (chartFppfObject B S hS Y W)))).obj
          (SheafOfModules.uliftForPresentation
            ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
            (isEtale_chartToSpace B S hS Y W)).obj (SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))))).val).presheaf).app
        (op ⊤)
        (readingIdChartLift (chartFppfObject B S hS Y W) ((etaleModulePullback B S hS
          (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).obj (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))))
          (chartEtaleTopSection _ W (1 : (structureRingSheaf B S hS Y).obj.obj (op W))))) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme W))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS Y.1 W)).obj
          (SheafOfModules.uliftForPresentation (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).val).presheaf).app
        (op ⊤) (ULift.up (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj
            (op ((openChartFunctor B S hS Y.1 W).obj ⊤)))) :=
  eqToHom_val_app_of_heq (chartScheme W)
    (restrictToChartScheme_eq_atIdEtaleChart B S hS Y W _).symm ⊤ _ _
    (toSheafify_heq (chartScheme W) (chartZariskiPresheaf_etale_eq _ W) ⊤ _ _
      (readingIdChartLift_one_heq W))

/-- `chartSectionsReadingEquiv_unit_one`, at the unfolded θ. -/
theorem schemeReadingChartIso_unitIso_etaleTop_one (W : SmallEtale B S hS Y.1) :
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W).hom.app ⊤
        ((chartEtaleComparison _ W).inv.val.app (op (readingTopChart (chartFppfObject B S hS Y W)))
          (chartEtaleTopSection _ W (1 : (structureRingSheaf B S hS Y).obj.obj (op W)))) =
      (1 : Γ(chartScheme W, ⊤)) := by
  let : HasSheafify (Opens.grothendieckTopology (chartScheme W)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme W)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  refine scheme_modules_iso_trans₂₂_hom_app_eq _ _ _ _ ⊤ _ (y₂ := ?y₂) (y₃ := ?y₃) ?h₁₂ ?h₃ ?h₄
  case h₁₂ => exact schemeReadingChartIso_firstTwo_app_etaleTop _ W _
  case h₄ =>
    exact restrictToChartSchemeUnitIso_hom_toSheafify_one (B := B) (S := S) (hS := hS) (F := Y.1)
      (hF := Y.2) (U := W)
  case h₃ =>
    exact eqToHom_restrictToChartScheme_eq_atIdEtaleChart_unit_toSheafify W

/-- **θ carries the unit to the unit**: the reading of the unit section of `𝒪` on a chart,
under the identification of the reading of `𝒪` with `𝒪`, is `1`. -/
theorem chartSectionsReadingEquiv_unit_one (W : SmallEtale B S hS Y.1)
    (o : (structureRingSheaf B S hS Y).obj.obj (op W)) (ho : o = 1) :
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W).hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W o) = (1 : Γ(chartScheme W, ⊤)) := by
  subst ho
  exact (congrArg _ (chartSectionsReadingEquiv_eq_inv _ W _)).trans
    (schemeReadingChartIso_unitIso_etaleTop_one W)

/-- θ on `𝒪`, on a function times the unit section, read through the identification of the
reading of `𝒪` with `𝒪`, is that function. -/
theorem chartSectionsReadingEquiv_unit_smul (W : SmallEtale B S hS Y.1)
    (c : Γ(chartScheme W, ⊤)) (o : (structureRingSheaf B S hS Y).obj.obj (op W)) (ho : o = 1) :
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W).hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W
      (HSMul.hSMul (α := Γ(chartScheme W, ⊤))
        (β := (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).val.obj (op W)) c o)) = c := by
  refine (congrArg _ (chartSectionsReadingEquiv_smul (SheafOfModules.unit _) W c _)).trans ?_
  have h := scheme_modules_hom_app_smul_of_eq_one
    (X := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W)) _ c _
    (chartSectionsReadingEquiv_unit_one W o ho)
  with_reducible exact h

/-- **θ on `𝒪` is the identity**: every function on a chart, read through θ and the
identification of the reading of `𝒪` with `𝒪`, is itself. -/
theorem chartSectionsReadingEquiv_unit_apply (W : SmallEtale B S hS Y.1)
    (r : (structureRingSheaf B S hS Y).obj.obj (op W)) :
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W).hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W r) = r := by
  have h : r = HSMul.hSMul (α := Γ(chartScheme W, ⊤)) (β := (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).val.obj
        (op W)) r (1 : (structureRingSheaf B S hS Y).obj.obj (op W)) := (mul_one r).symm
  exact (congrArg _ (congrArg (chartSectionsReadingEquiv _ W) h)).trans
    (chartSectionsReadingEquiv_unit_smul W r 1 rfl)

end Unit

end AlgebraicGeometry.Space

end
