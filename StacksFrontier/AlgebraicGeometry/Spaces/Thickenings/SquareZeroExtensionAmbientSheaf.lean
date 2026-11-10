module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientCharts

/-!
# The structure sheaf of the ambient space of a square-zero extension

For a square-zero extension `E` of an algebraic space `X` and a charted presentation of the
ambient space, the structure sheaf of the ambient space is identified with the extension
restricted along base change of étale charts to `X`.

## Main definitions

* `ambientSheafHom`: The comparison morphism from the structure sheaf of the ambient space to
  the restricted extension.

## Main results

* `isIso_ambientSheafHom`: The comparison morphism is an isomorphism.
* `ambientSheafHom_comp_π`: Followed by the restricted reduction, the comparison is pullback of
  functions along the cartesian projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The inclusion of the whole chart as an open of itself is an isomorphism of charts. -/
instance isIso_openChartInclusion_top (W : SmallEtale B S hS X.1) :
    IsIso (openChartInclusion B S hS X.1 W ⊤) := by
  have h : IsIso ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map
      (openChartInclusion B S hS X.1 W ⊤)) := by
    change IsIso ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (openChartInclusion B S hS X.1 W ⊤)))
    rw [toScheme_map_toOver_map_openChartInclusion]
    exact (Scheme.topIso _).isIso_hom
  exact isIso_of_reflects_iso _ (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS)

/-- **The global functions on the thickened chart are the sections of the extension.** -/
def thickeningΓIso (W : SmallEtale B S hS X.1) :
    E.A.obj.obj (op W) ≅ Γ(chartThickening B S hS E W, ⊤) :=
  E.A.obj.mapIso (asIso (openChartInclusion B S hS X.1 W ⊤)).op

/-- The identification of global functions is restriction along the inclusion of the whole
chart. -/
theorem thickeningΓIso_hom (W : SmallEtale B S hS X.1) :
    (thickeningΓIso E W).hom = E.A.obj.map (openChartInclusion B S hS X.1 W ⊤).op := rfl

/-- **Naturality of the identification of global functions.** -/
theorem thickeningΓIso_naturality {W₁ W₂ : SmallEtale B S hS X.1} (h : W₁ ⟶ W₂) :
    (thickeningΓIso E W₂).hom ≫ (chartThickeningMap B S hS E h).appTop =
      E.A.obj.map h.op ≫ (thickeningΓIso E W₁).hom := by
  rw [thickeningΓIso_hom, thickeningΓIso_hom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  refine (congrArg (_ ≫ ·) (chartThickeningMap_appLE B S hS E h ⊤ ⊤ le_top)).trans ?_
  refine ((E.A.obj.map_comp _ _).symm).trans (Eq.trans ?_ (E.A.obj.map_comp _ _))
  exact congrArg E.A.obj.map (congrArg Quiver.Hom.op
    (openChartHomOfLE_comp_openChartRestrict_comp_openChartInclusion B S hS X.1 h ⊤ le_top))

/-- On global functions, the inclusion of a chart into its thickening is the reduction. -/
theorem thickeningΓIso_hom_comp_appTop (W : SmallEtale B S hS X.1) :
    (thickeningΓIso E W).hom ≫ (chartImmersion B S hS E W).appTop = E.π.hom.app (op W) := by
  ext a
  change (Scheme.restrictFunctorΓ (X := chartScheme W)).hom.app (op ⊤)
      (E.π.hom.app (op (openChart B S hS X.1 W ⊤))
        (E.A.obj.map (openChartInclusion B S hS X.1 W ⊤).op a)) = _
  have h1 := ConcreteCategory.congr_hom
    (E.π.hom.naturality (openChartInclusion B S hS X.1 W ⊤).op) a
  have h3 := ConcreteCategory.congr_hom (appTop_openChartInclusion_top_restrictFunctorΓ B S hS W)
    (E.π.hom.app (op W) a)
  exact (congrArg ((Scheme.restrictFunctorΓ (X := chartScheme W)).hom.app (op ⊤)) h1).trans h3

attribute [local instance] hasSheafify_bigFppfOver

variable {E} {C : ChartedPresentation B S hS f}
  {hcU : B.Contains (chartThickening B S hS E (presentationChart C.P))}
  {hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P))}

/-- The étale charts of the ambient space which factor through the thickened presenting chart. -/
def ChartFactorable : ObjectProperty (SmallEtale B S hS (ambient E C hcU hcR).1) :=
  fun V => Nonempty (ChartFactor V)

/-- The base change of an étale chart of the ambient space to the thickened presenting chart. -/
def factorChart (V : SmallEtale B S hS (ambient E C hcU hcR).1) :
    SmallEtale B S hS (ambient E C hcU hcR).1 :=
  ⟨CostructuredArrow.mk (yoneda.map (V.2.rep.snd (ambQuot E C hcU hcR)) ≫ ambQuot E C hcU hcR),
    etale_comp_of_scheme B S hS _ _ (V.2.property_snd (ambQuot E C hcU hcR))
      (quotientMap_etale_unconditional B S hS _ _)⟩

/-- The tautological factorization of the base-changed chart. -/
def factorChartFactor (V : SmallEtale B S hS (ambient E C hcU hcR).1) :
    ChartFactor (factorChart V) where
  v := V.2.rep.snd (ambQuot E C hcU hcR)
  fac := rfl
  etale := V.2.property_snd (ambQuot E C hcU hcR)

/-- The base-changed chart is the pullback of the chart along the quotient map. -/
theorem factorChart_isPullback (V : SmallEtale B S hS (ambient E C hcU hcR).1) :
    IsPullback (yoneda.map (V.2.rep.snd (ambQuot E C hcU hcR)))
      (yoneda.map (yoneda.preimage (V.2.rep.fst (ambQuot E C hcU hcR))))
      (ambQuot E C hcU hcR) V.1.hom := by
  rw [Functor.map_preimage]
  exact (V.2.rep.isPullback (ambQuot E C hcU hcR)).flip

/-- The projection of the base-changed chart to the chart. -/
def factorChartHom (V : SmallEtale B S hS (ambient E C hcU hcR).1) : factorChart V ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage
    (V.2.rep.fst (ambQuot E C hcU hcR))) (factorChart_isPullback V).w.symm)

/-- Every étale chart of the ambient space is covered by one factoring through the thickened
presenting chart. -/
instance isCoverDense_chartFactorable :
    (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι.IsCoverDense
      (SmallEtale.topology B S hS (ambient E C hcU hcR).1) := by
  refine Functor.isCoverDense_of_generate_singleton_functor_π_mem _ _ fun V =>
    ⟨⟨factorChart V, ⟨factorChartFactor V⟩⟩, factorChartHom V, ?_⟩
  rw [← Presieve.ofArrows_pUnit.{u + 1}]
  refine SmallEtale.ofArrows_mem_topology B S hS _ (fun _ => factorChart V)
    (fun _ => factorChartHom V) ?_
  have hpb := factorChart_isPullback V
  have hS' := (quotientMap_surjective_unconditional B S hS (ambSource E C hcU hcR)
    (ambTarget E C hcU hcR)).property V.1.hom _ _ hpb
  have hE' := (quotientMap_etale_unconditional B S hS (ambSource E C hcU hcR)
    (ambTarget E C hcU hcR)).property V.1.hom _ _ hpb
  exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2
    ⟨fun x => ⟨⟨⟩, hS'.surj x⟩, fun _ => hE'⟩

variable (i : X ⟶ ambient E C hcU hcR)
  (hi : C.P.toSpace ≫ i.hom = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR)

/-- The extension, restricted along base change of étale charts to `X`: a sheaf of rings on the
small étale site of the ambient space. -/
abbrev baseChangeExtension : Sheaf (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
    CommRingCat.{u} :=
  letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS (ambient E C hcU hcR).1) (SmallEtale.topology B S hS X.1)).obj E.A

/-- On a chart factoring through the thickened presenting chart: global functions on the chart
are global functions on the thickening of its base change, which are sections of the
extension. -/
def ambientChartRingHom (V : SmallEtale B S hS (ambient E C hcU hcR).1) (F : ChartFactor V) :
    Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤) ⟶ E.A.obj.obj (op (chartX i hi V)) :=
  (F.thickenHom (hi := hi)).appTop ≫ (thickeningΓIso E (chartX i hi V)).inv

/-- The map on global functions does not depend on the chosen factorization. -/
theorem ambientChartRingHom_eq (V : SmallEtale B S hS (ambient E C hcU hcR).1)
    (F F' : ChartFactor V) : ambientChartRingHom i hi V F = ambientChartRingHom i hi V F' := by
  rw [ambientChartRingHom, ambientChartRingHom, F.thickenHom_eq F']

/-- The map on global functions is natural in the chart. -/
theorem ambientChartRingHom_naturality {V₁ V₂ : SmallEtale B S hS (ambient E C hcU hcR).1}
    (g : V₁ ⟶ V₂) (F₂ : ChartFactor V₂) :
    ambientChartRingHom i hi V₂ F₂ ≫
        E.A.obj.map ((smallBaseChange B S hS i (ambRep i hi)).map g).op =
      ((BigFppfOver.toScheme B S hS).map g.hom.left).appTop ≫
        ambientChartRingHom i hi V₁ (F₂.precomp g) := by
  have hΓ' : (thickeningΓIso E (chartX i hi V₂)).inv ≫
      E.A.obj.map ((smallBaseChange B S hS i (ambRep i hi)).map g).op =
      (chartThickeningMap B S hS E ((smallBaseChange B S hS i (ambRep i hi)).map g)).appTop ≫
        (thickeningΓIso E (chartX i hi V₁)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc]
    exact (Iso.eq_comp_inv _).2
      (thickeningΓIso_naturality E ((smallBaseChange B S hS i (ambRep i hi)).map g)).symm
  rw [ambientChartRingHom, ambientChartRingHom, Category.assoc, hΓ', ← Category.assoc,
    ← Scheme.Hom.comp_appTop, F₂.thickenHom_naturality g, Scheme.Hom.comp_appTop,
    Category.assoc]

/-- **The comparison of the structure sheaf of the ambient space with the restricted extension**,
on the charts factoring through the thickened presenting chart. -/
def ambientRestrictHom :
    (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι.op ⋙
        (structureSheaf B S hS (ambient E C hcU hcR).1 (ambient E C hcU hcR).2).obj ⟶
      (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι.op ⋙
        (baseChangeExtension i hi).obj where
  app V := ambientChartRingHom i hi V.unop.1 V.unop.2.some
  naturality V₁ V₂ g := by
    change ((BigFppfOver.toScheme B S hS).map g.unop.hom.hom.left).appTop ≫
        ambientChartRingHom i hi V₂.unop.1 V₂.unop.2.some =
      ambientChartRingHom i hi V₁.unop.1 V₁.unop.2.some ≫
        E.A.obj.map ((smallBaseChange B S hS i (ambRep i hi)).map g.unop.hom).op
    rw [ambientChartRingHom_naturality, ambientChartRingHom_eq]

/-- Followed by the reduction, the map on global functions is pullback along the cartesian
projection. -/
theorem ambientChartRingHom_comp_π (V : SmallEtale B S hS (ambient E C hcU hcR).1)
    (F : ChartFactor V) :
    ambientChartRingHom i hi V F ≫ E.π.hom.app (op (chartX i hi V)) =
      ((BigFppfOver.toScheme B S hS).map (chartXProj i hi V)).appTop := by
  have h : (thickeningΓIso E (chartX i hi V)).inv ≫ E.π.hom.app (op (chartX i hi V)) =
      (chartImmersion B S hS E (chartX i hi V)).appTop :=
    (Iso.inv_comp_eq _).2 (thickeningΓIso_hom_comp_appTop E (chartX i hi V)).symm
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans ?_)
  exact (Scheme.Hom.comp_appTop _ _).symm.trans
    (congrArg Scheme.Hom.appTop F.immersion_thickenHom)

/-- **The structure sheaf of the ambient space is the extension restricted along base change of
étale charts**, as a morphism of sheaves of rings; it is an isomorphism. -/
def ambientSheafHom :
    structureSheaf B S hS (ambient E C hcU hcR).1 (ambient E C hcU hcR).2 ⟶
      baseChangeExtension i hi :=
  ⟨Functor.IsCoverDense.restrictHomEquivHom (ambientRestrictHom i hi)⟩

/-- On the charts factoring through the thickened presenting chart, the comparison morphism is
`ambientRestrictHom`. -/
theorem whiskerLeft_ambientSheafHom :
    Functor.whiskerLeft (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι.op
      (ambientSheafHom i hi).hom = ambientRestrictHom i hi :=
  Functor.IsCoverDense.sheafHom_restrict_eq _

/-- The comparison of the structure sheaf of the ambient space with the restricted extension is
an isomorphism. -/
instance isIso_ambientSheafHom : IsIso (ambientSheafHom i hi) := by
  refine Functor.IsCoverDense.iso_of_restrict_iso
    (G := (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι) _ ?_
  rw [whiskerLeft_ambientSheafHom]
  have : ∀ V, IsIso ((ambientRestrictHom i hi).app V) := fun V => by
    change IsIso ((V.unop.2.some.thickenHom (hi := hi)).appTop ≫
      (thickeningΓIso E (chartX i hi V.unop.1)).inv)
    have := ChartFactor.isIso_thickenHom (hi := hi) V.unop.2.some
    have : IsIso ((V.unop.2.some.thickenHom (hi := hi)).appTop) :=
      (Scheme.Γ.mapIso (asIso (V.unop.2.some.thickenHom (hi := hi))).op).isIso_hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The comparison lies over the reductions**: followed by the restricted reduction, it is
pullback of functions along the cartesian projections. -/
theorem ambientSheafHom_comp_π :
    letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
    ambientSheafHom i hi ≫
        ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
          (SmallEtale.topology B S hS X.1)).map E.π =
      smallBaseChangeSharpCommRingCat B S hS i (ambRep i hi) := by
  let := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  refine Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom
    (G := (ChartFactorable (E := E) (C := C) (hcU := hcU) (hcR := hcR)).ι)).symm.injective ?_)
  change Functor.whiskerLeft _ ((ambientSheafHom i hi).hom ≫ _) = Functor.whiskerLeft _ _
  rw [Functor.whiskerLeft_comp, whiskerLeft_ambientSheafHom]
  ext V : 2
  exact ambientChartRingHom_comp_π i hi V.unop.1 V.unop.2.some

end SquareZeroExtension

end AlgebraicGeometry.Space

end
