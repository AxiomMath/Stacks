module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# Restricting a module on an algebraic space to an étale scheme chart

Let `X` be an algebraic space over a scheme `S` and let `U → X` be an étale chart with
underlying scheme `U`.  The Zariski opens of `U` are again étale charts of `X`, so they form a
subsite of the small étale site of `X`, and restricting an `𝒪_X`-module along that inclusion
gives a sheaf of modules on `U`.

## Main definitions

* `AlgebraicGeometry.Space.etaleChartScheme` is the scheme underlying an étale chart.
* `AlgebraicGeometry.Space.chartOpenOver` is a Zariski open of an étale chart, read as a scheme
  over the base, with `AlgebraicGeometry.Space.chartOpenOverι` its inclusion into the chart and
  `AlgebraicGeometry.Space.chartOpenOverMap` the map induced by an inclusion of opens.
* `AlgebraicGeometry.Space.chartOpens` includes the Zariski opens of an étale chart into the
  small étale site of the algebraic space.
* `AlgebraicGeometry.Space.chartRestrictionRingHom` compares the structure sheaf of the chart
  with the restriction of the structure sheaf of the algebraic space along `chartOpens`.
* `AlgebraicGeometry.Space.chartRestrictionPresheaf` is the presheaf of modules of sections of
  an `𝒪_X`-module over the Zariski opens of a chart, and
  `AlgebraicGeometry.Space.restrictToChart` is the restriction `𝓕|_U` of an `𝒪_X`-module to the
  chart, as a sheaf of modules on `U`.

## Main results

* `AlgebraicGeometry.Space.chartOpen_isEtaleChart`: a Zariski open of an étale chart is itself
  an étale chart of the algebraic space.

## Implementation notes

The inclusion of the Zariski opens of `U` into the small étale site is built from the inclusion
of those opens into the schemes over the base: the structure morphism of a Zariski open of `U`
is the composite of an open immersion with the étale structure morphism of the chart, hence
étale, and a Zariski open of a scheme of the ambient category is again in it because its size
does not grow.

Restriction is then the pushforward of presheaves of modules along
`AlgebraicGeometry.Space.chartRestrictionRingHom` followed by sheafification for the Zariski
topology of `U`.  The sections of an `𝒪_X`-module live in a universe `m` independent of the
universe `u` of the schemes, and sheafification on the Zariski site of `U` needs them in a
universe at least `u`; `SheafOfModules.uliftForPresentation` performs that lift, which is an
objectwise identity.

`AlgebraicGeometry.Space.chartOpens_op_comp_ringSheaf` records that restricting the structure
sheaf of the algebraic space along `chartOpens` is, on the nose, the presheaf of functions on
the Zariski opens of the chart.  That equation holds by construction but the elaborator does not
find it while checking `chartRestrictionRingHom`, so it is stated separately and used there.

In `chartRestrictionPresheaf` the two categories of presheaves of modules are named before the
pushforward functor is applied.  The section universe `max u m` of the presheaves is a maximum
of two independent universes, and leaving instance search to recover the categories from the
functor over-constrains it; naming them determines both from the presheaves themselves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)


/-- The scheme underlying an étale chart of `X`. -/
abbrev etaleChartScheme (U : SmallEtale B S hS X) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj U.obj.left

/-- A Zariski open of an étale chart, regarded as a scheme over the base. -/
noncomputable def chartOpenOver (U : SmallEtale B S hS X)
    (V : (etaleChartScheme B S hS U).Opens) : BigFppfOver B S hS :=
  Over.mk (Y := ⟨V.toScheme,
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ V) U.obj.left.left.property⟩)
    (ObjectProperty.homMk V.ι ≫ U.obj.left.hom)

/-- The inclusion of a Zariski open of an étale chart as a morphism over the base. -/
noncomputable def chartOpenOverι (U : SmallEtale B S hS X)
    (V : (etaleChartScheme B S hS U).Opens) :
    chartOpenOver B S hS U V ⟶ U.obj.left :=
  Over.homMk (ObjectProperty.homMk V.ι) rfl

/-- The morphism over the base induced by an inclusion of Zariski opens of an étale chart. -/
noncomputable def chartOpenOverMap (U : SmallEtale B S hS X)
    {V W : (etaleChartScheme B S hS U).Opens} (i : V ⟶ W) :
    chartOpenOver B S hS U V ⟶ chartOpenOver B S hS U W :=
  Over.homMk (ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE i.le)) (by
    apply ObjectProperty.hom_ext
    change (etaleChartScheme B S hS U).homOfLE i.le ≫ W.ι ≫ _ = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

/-- An inclusion of Zariski opens of an étale chart is compatible with their inclusions into
the chart. -/
theorem chartOpenOverMap_comp_ι (U : SmallEtale B S hS X)
    {V W : (etaleChartScheme B S hS U).Opens} (i : V ⟶ W) :
    chartOpenOverMap B S hS U i ≫ chartOpenOverι B S hS U W =
      chartOpenOverι B S hS U V :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_ι _ i.le))

/-- The identity inclusion of a Zariski open of an étale chart induces the identity. -/
theorem chartOpenOverMap_id (U : SmallEtale B S hS X)
    (V : (etaleChartScheme B S hS U).Opens) :
    chartOpenOverMap B S hS U (𝟙 V) = 𝟙 (chartOpenOver B S hS U V) :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_rfl _ _))

/-- Composing inclusions of Zariski opens of an étale chart composes the induced morphisms. -/
theorem chartOpenOverMap_comp (U : SmallEtale B S hS X)
    {V W T : (etaleChartScheme B S hS U).Opens} (i : V ⟶ W) (j : W ⟶ T) :
    chartOpenOverMap B S hS U (i ≫ j) =
      chartOpenOverMap B S hS U i ≫ chartOpenOverMap B S hS U j :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_homOfLE _ i.le j.le).symm)

/-- A Zariski open of an étale chart of `X` is again an étale chart of `X`: its structure
morphism is an open immersion followed by the étale structure morphism of the chart. -/
theorem chartOpen_isEtaleChart (U : SmallEtale B S hS X)
    (V : (etaleChartScheme B S hS U).Opens) :
    IsEtaleChart B S hS X
      (CostructuredArrow.mk (yoneda.map (chartOpenOverι B S hS U V) ≫ U.obj.hom)) := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : P.IsStableUnderBaseChange := ⟨fun sq hg =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (sq.map (BigFppfOver.toScheme B S hS)) hg⟩
  have : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  apply MorphismProperty.IsStableUnderComposition.comp_mem (P := P.presheaf)
    _ _ _ U.property
  apply (P.relative_map_iff (F := yoneda)).2
  show Etale V.ι
  infer_instance

/-- The inclusion of the Zariski opens of an étale chart into the small étale site of `X`. -/
noncomputable def chartOpens (U : SmallEtale B S hS X) :
    (etaleChartScheme B S hS U).Opens ⥤ SmallEtale B S hS X where
  obj V := ⟨CostructuredArrow.mk (yoneda.map (chartOpenOverι B S hS U V) ≫ U.obj.hom),
    chartOpen_isEtaleChart B S hS U V⟩
  map {V W} i := ObjectProperty.homMk (CostructuredArrow.homMk
    (chartOpenOverMap B S hS U i) (by
      change yoneda.map (chartOpenOverMap B S hS U i) ≫
          yoneda.map (chartOpenOverι B S hS U W) ≫ U.obj.hom =
        yoneda.map (chartOpenOverι B S hS U V) ≫ U.obj.hom
      rw [← Category.assoc, ← Functor.map_comp, chartOpenOverMap_comp_ι]))
  map_id V := ObjectProperty.hom_ext _
    (CostructuredArrow.hom_ext _ _ (chartOpenOverMap_id B S hS U V))
  map_comp i j := ObjectProperty.hom_ext _
    (CostructuredArrow.hom_ext _ _ (chartOpenOverMap_comp B S hS U i j))

/-- Restricting the structure sheaf of the algebraic space along the inclusion of the Zariski
opens of an étale chart gives the presheaf of functions on those opens. -/
theorem chartOpens_op_comp_ringSheaf (U : SmallEtale B S hS X) :
    (chartOpens B S hS U).op ⋙
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj =
      ((etaleChartScheme B S hS U).restrictFunctor.op ⋙
          (Over.forget (etaleChartScheme B S hS U)).op ⋙ Scheme.Γ) ⋙
        forget₂ CommRingCat RingCat :=
  rfl

/-- The comparison of the structure sheaf of an étale chart with the restriction of the
structure sheaf of `X` along `AlgebraicGeometry.Space.chartOpens`. -/
noncomputable def chartRestrictionRingHom (U : SmallEtale B S hS X) :
    (etaleChartScheme B S hS U).ringCatSheaf.obj ⟶
      (chartOpens B S hS U).op ⋙
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj :=
  Functor.whiskerRight (Scheme.restrictFunctorΓ (X := etaleChartScheme B S hS U)).inv
      (forget₂ CommRingCat RingCat) ≫
    eqToHom (chartOpens_op_comp_ringSheaf B S hS hX U).symm

/-- The presheaf of modules on the Zariski opens of an étale chart `U` given by the sections of
an `𝒪_X`-module, with its universe raised so that it can be sheafified on `U`. -/
noncomputable def chartRestrictionPresheaf (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    PresheafOfModules.{max u m} (etaleChartScheme B S hS U).ringCatSheaf.obj :=
  letI catSpaceModules : Category (PresheafOfModules.{max u m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj) :=
    inferInstance
  letI catChartModules : Category (PresheafOfModules.{max u m}
      (etaleChartScheme B S hS U).ringCatSheaf.obj) := inferInstance
  @Functor.obj _ catSpaceModules _ catChartModules
    (PresheafOfModules.pushforward.{max u m} (chartRestrictionRingHom B S hS hX U))
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u} G).val

/-- The restriction `𝓕|_U` of an `𝒪_X`-module to an étale scheme chart `U`, obtained by
restricting to the Zariski opens of `U` and taking the associated sheaf of modules. -/
noncomputable def restrictToChart (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    SheafOfModules.{max u m} (etaleChartScheme B S hS U).ringCatSheaf := by
  let J := Opens.grothendieckTopology (etaleChartScheme B S hS U)
  letI : HasSheafify J AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  exact (PresheafOfModules.sheafification.{max u m}
    (𝟙 (etaleChartScheme B S hS U).ringCatSheaf.obj)).obj
    (chartRestrictionPresheaf B S hS hX G U)

end AlgebraicGeometry.Space

end
