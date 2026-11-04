module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGraphLift

/-!
# The chart restriction of a direct-image algebra is natural in the chart

`AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` identifies, for a
representable morphism `p : Z ⟶ X` of algebraic spaces and an étale scheme chart `V` of `X`, the
restriction of the direct-image algebra `p_*𝒪_Z` to the Zariski site of `chartScheme V` with the
direct image of `𝒪_{V ×_X Z}` along the cartesian projection `q_V : V ×_X Z ⟶ V`.  This file
proves that identification **natural in the chart**: for a morphism `h : V₁ ⟶ V₂` of étale scheme
charts the comparison at `V₁` and the comparison at `V₂` agree after transport along
`AlgebraicGeometry.Space.chartSchemeMap h`.

`AlgebraicGeometry.Space.smallBaseChangeOpenChartIso_naturality` is naturality of the underlying
interchange of chart base change with Zariski opens in the **open**; the statement proved here is
the analogue one level up, in the **chart**, and it is the geometric ingredient the double descent
of clause (1) of Stacks 0822 was missing.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso_chart_naturality`: **the interchange of
  chart base change with Zariski opens is natural in the chart.**  This is the geometric content:
  both sides are morphisms into the open chart of `V₂ ×_X Z` cut out by the preimage of a Zariski
  open, which is a fibre product by
  `AlgebraicGeometry.Space.isPullback_openChart_smallBaseChange`, so they agree as soon as they do
  after the two cartesian projections.
* `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartSchemeDirectImageAlgebraPushforwardIso`:
  **naturality of the comparison in the chart**, in the shape
  `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap` consumes: the chart change of the comparison
  at `V₁` is the comparison at `V₂` followed by
  `AlgebraicGeometry.Space.smallBaseChangeChartPushforwardMap`, the direct-image map of the square
  of the two cartesian projections.
* `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartGraphAlgebraMap`: **the algebra map a
  graph carries is natural in the chart.**  The chart change of
  `AlgebraicGeometry.Space.chartGraphAlgebraMap` at `V₁` is the same construction at `V₂` for the
  composed structure morphism `T ⟶ V₁ ⟶ V₂`.  With
  `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartOverAlgebraMap` this is the chart change
  of `AlgebraicGeometry.Space.chartOverAlgebraMap` outright.

## Implementation notes

**The restriction comparison is used in the `inv` direction throughout.**  The one scheme-level
input is `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`, which is
stated for `AlgebraicGeometry.Scheme.restrictFunctorΓ`'s inverse, and the analogue proved here for
a restriction followed by a shrinking of the open —
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_morphismRestrict` — is
likewise.  Every statement below is therefore first proved with the comparison inverted, and the
`hom` form is recovered only at the very end, at the level of morphisms of **algebra sheaves**,
where the objects carry their own names and no coercion is in play.  Doing that conversion on
sections instead does not work: `AlgebraicGeometry.Space.openChart` and
`AlgebraicGeometry.Space.smallBaseChange` are semireducible, the sections over a Zariski open have
the two spellings `Γ(chartScheme (openChart V O))` and `Γ((chartScheme V).restrictFunctor.obj O)`,
and a goal in which the two meet is not type-correct at `implicit` transparency, after which `rw`
stops firing with no error naming the cause.

**The general scheme lemma is proved at variables.**
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_morphismRestrict` mentions no
algebraic space, so nothing in it can unfold into the `Classical.choice` of a representability
witness; at the concrete instance the same `rw` chain exhausts the heartbeat budget at `isDefEq`.
Its proof is written with `CategoryTheory.Category.assoc` and `congrArg` applied as *terms*, which
needs no type-correctness at reducible transparency, for the reason the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeDirectImageAlgebraPushforward` record.

**The naturality in the algebra sheaf is not reproved.**  The first factor of the comparison is the
chart restriction of `AlgebraicGeometry.Space.pushforwardAlgebraChartIso`, a *fixed* morphism of
algebra sheaves on `X`, so its chart naturality is
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_naturality` and nothing is owed for it
here.

**No `stacks` attribute is carried.**  Stacks 03G2 part (4) is registered on
`AlgebraicGeometry.Space.smallBaseChange` and Stacks 03G8 on
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage`; naturality in the
chart of a comparison of two readings of one direct image is a clause of no tag, and Definition
0822 asks for a factorization which is not yet assembled.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry

/-! ### The restriction comparison along a restricted morphism followed by a shrinking -/

/-- **Restricting a morphism of schemes to an open `O` of its target and then shrinking to an
open `W` of the source contained in the preimage of `O`, read through the identification of
`Γ(Y, O)` with the global functions on the open subscheme `O`.**

This is `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` with the
shrinking of the open appended, and the shrinking is absorbed by naturality of the identification
and the definition of `AlgebraicGeometry.Scheme.Hom.appLE`.

It is stated and proved at variables: see the implementation notes for why the same `rw` chain at
the instance this file needs runs out of heartbeats. -/
theorem Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (O : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ O) :
    (Scheme.restrictFunctorΓ (X := Y)).inv.app (op O) ≫
        Scheme.Γ.map (X.homOfLE hW ≫ (f ∣_ O)).op =
      f.appLE O W hW ≫ (Scheme.restrictFunctorΓ (X := X)).inv.app (op W) := by
  refine (congrArg (fun m => (Scheme.restrictFunctorΓ (X := Y)).inv.app (op O) ≫ m)
    (Scheme.Γ.map_comp (f ∣_ O).op (X.homOfLE hW).op)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ Scheme.Γ.map (X.homOfLE hW).op)
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict f O)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => f.app O ≫ m)
    ((Scheme.restrictFunctorΓ (X := X)).inv.naturality (homOfLE hW).op).symm).trans ?_
  exact (Category.assoc _ _ _).symm

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (p : Z ⟶ X)
    (hp : yoneda.relativelyRepresentable p.hom) {V₁ V₂ : SmallEtale B S hS X.1} (h : V₁ ⟶ V₂)

/-! ### The square of the two cartesian projections -/

/-- **The cartesian projections of the base-changed charts commute with the chart maps.**  For a
morphism `h : V₁ ⟶ V₂` of étale scheme charts of `X` the square of `q_{V₁}`, `q_{V₂}`,
`chartSchemeMap h` and the chart map of the base-changed charts commutes.

It is `AlgebraicGeometry.Space.smallBaseChange_map_snd` — the defining property of the base change
of a morphism of charts — read on the underlying schemes. -/
theorem chartSchemeMap_smallBaseChange_map_comp_projection :
    chartSchemeMap ((smallBaseChange B S hS p hp).map h) ≫
        smallBaseChangeSchemeProjection B S hS p hp V₂ =
      smallBaseChangeSchemeProjection B S hS p hp V₁ ≫ chartSchemeMap h :=
  ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B S hS).map
      (smallBaseChange_map_snd B S hS p hp h)).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _))

variable (O : (chartScheme V₂).Opens)

/-- Pulling a Zariski open of `chartScheme V₂` back along `q_{V₁} ≫ chartSchemeMap h` lands in
its preimage along the chart map of the base-changed charts.  The two opens are in fact equal,
by `AlgebraicGeometry.Space.chartSchemeMap_smallBaseChange_map_comp_projection`. -/
theorem smallBaseChangeSchemeProjection_preimage_chart_le :
    smallBaseChangeSchemeProjection B S hS p hp V₁ ⁻¹ᵁ (chartSchemeMap h ⁻¹ᵁ O) ≤
      chartSchemeMap ((smallBaseChange B S hS p hp).map h) ⁻¹ᵁ
        (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O) :=
  le_of_eq (congrArg (fun m : chartScheme ((smallBaseChange B S hS p hp).obj V₁) ⟶
      chartScheme V₂ => m ⁻¹ᵁ O)
    (chartSchemeMap_smallBaseChange_map_comp_projection B S hS p hp h).symm)

/-- **The morphism of open charts of the base-changed charts that `h` induces.**  It restricts the
chart map of `V₁ ×_X Z ⟶ V₂ ×_X Z` to the preimage of a Zariski open of `chartScheme V₂` and the
preimage of its preimage, the shrinking of the open being
`AlgebraicGeometry.Space.smallBaseChangeSchemeProjection_preimage_chart_le`. -/
def smallBaseChangeChartOpenHom :
    openChart B S hS Z.1 ((smallBaseChange B S hS p hp).obj V₁)
        (smallBaseChangeSchemeProjection B S hS p hp V₁ ⁻¹ᵁ (chartSchemeMap h ⁻¹ᵁ O)) ⟶
      openChart B S hS Z.1 ((smallBaseChange B S hS p hp).obj V₂)
        (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O) :=
  openChartHomOfLE B S hS Z.1 ((smallBaseChange B S hS p hp).obj V₁)
      (smallBaseChangeSchemeProjection_preimage_chart_le B S hS p hp h O) ≫
    openChartRestrict B S hS Z.1 ((smallBaseChange B S hS p hp).map h)
      (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O)

/-- **The induced morphism of open charts is compatible with the cartesian projections.**

After cancelling the inclusion of the open this is `AlgebraicGeometry.morphismRestrict_ι` and
`AlgebraicGeometry.Scheme.homOfLE_ι` together with the commuting square
`AlgebraicGeometry.Space.chartSchemeMap_smallBaseChange_map_comp_projection`, exactly as in
`AlgebraicGeometry.Space.openChartSmallBaseChangeHomOfLE_comp_projection`. -/
theorem smallBaseChangeChartOpenHom_comp_projection :
    (SmallEtale.toOver B S hS Z.1).map
          (smallBaseChangeChartOpenHom B S hS p hp h O) ≫
        openChartSmallBaseChangeProjection B S hS p hp V₂ O =
      openChartSmallBaseChangeProjection B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O) ≫
        (SmallEtale.toOver B S hS X.1).map (openChartRestrict B S hS X.1 h O) := by
  refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  change ((chartScheme ((smallBaseChange B S hS p hp).obj V₁)).homOfLE
          (smallBaseChangeSchemeProjection_preimage_chart_le B S hS p hp h O) ≫
        (chartSchemeMap ((smallBaseChange B S hS p hp).map h) ∣_
          (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O))) ≫
      (smallBaseChangeSchemeProjection B S hS p hp V₂ ∣_ O) =
    (smallBaseChangeSchemeProjection B S hS p hp V₁ ∣_ (chartSchemeMap h ⁻¹ᵁ O)) ≫
      (chartSchemeMap h ∣_ O)
  rw [← cancel_mono O.ι]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.homOfLE_ι_assoc]
  rw [chartSchemeMap_smallBaseChange_map_comp_projection]

/-- The two sides of the chart naturality of the interchange agree after the cartesian projection
to `openChart V₂ O`.

On the left this is `AlgebraicGeometry.Space.smallBaseChangeOpenChartLeftIso_hom_comp_projection`
followed by naturality of `AlgebraicGeometry.Space.smallBaseChangeProjection`, on the right the
same triangle together with
`AlgebraicGeometry.Space.smallBaseChangeChartOpenHom_comp_projection`.  It is stated separately
because folding it into the proof of the naturality leaves the two spellings of a base-changed open
chart to be identified against a metavariable, which exhausts the heartbeat budget. -/
theorem smallBaseChangeChartOpenHom_leg :
    (smallBaseChange B S hS p hp ⋙ SmallEtale.toOver B S hS Z.1).map
          (openChartRestrict B S hS X.1 h O) ≫
        (smallBaseChangeOpenChartLeftIso B S hS p hp V₂ O).hom ≫
          openChartSmallBaseChangeProjection B S hS p hp V₂ O =
      (smallBaseChangeOpenChartLeftIso B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O)).hom ≫
        (SmallEtale.toOver B S hS Z.1).map (smallBaseChangeChartOpenHom B S hS p hp h O) ≫
          openChartSmallBaseChangeProjection B S hS p hp V₂ O := by
  rw [smallBaseChangeOpenChartLeftIso_hom_comp_projection,
    smallBaseChangeChartOpenHom_comp_projection, ← Category.assoc,
    smallBaseChangeOpenChartLeftIso_hom_comp_projection]
  exact (smallBaseChangeProjection B S hS p hp).naturality
    (openChartRestrict B S hS X.1 h O)

/-- **The interchange of chart base change with Zariski opens is natural in the chart.**

For a morphism `h : V₁ ⟶ V₂` of étale scheme charts of `X` and a Zariski open `O` of
`chartScheme V₂`, base changing the restricted chart morphism
`openChart V₁ (h⁻¹O) ⟶ openChart V₂ O` and then interchanging is interchanging and then restricting
the chart morphism of the base-changed charts.

Both sides are morphisms into the open chart of `V₂ ×_X Z` cut out by the preimage of `O`, which is
a fibre product of `openChart V₂ O ⟶ X ⟵ Z` by
`AlgebraicGeometry.Space.isPullback_openChart_smallBaseChange`, so they agree as soon as they do
after the two cartesian projections.  After the projection to `Z` this holds of any two morphisms
of charts of `Z` with the same source and target; after the projection to `openChart V₂ O` it is
`AlgebraicGeometry.Space.smallBaseChangeChartOpenHom_leg`.

This is the chart analogue of `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso_naturality`,
which is natural in the open. -/
theorem smallBaseChangeOpenChartIso_chart_naturality :
    (smallBaseChange B S hS p hp).map (openChartRestrict B S hS X.1 h O) ≫
        (smallBaseChangeOpenChartIso B S hS p hp V₂ O).hom =
      (smallBaseChangeOpenChartIso B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O)).hom ≫
        smallBaseChangeChartOpenHom B S hS p hp h O := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (yoneda.map_injective ?_))
  refine (isPullback_openChart_smallBaseChange B S hS p hp V₂ O).hom_ext ?_ ?_
  · exact (CostructuredArrow.w (((smallBaseChange B S hS p hp).map
        (openChartRestrict B S hS X.1 h O) ≫
        (smallBaseChangeOpenChartIso B S hS p hp V₂ O).hom).hom)).trans
      (CostructuredArrow.w
        (((smallBaseChangeOpenChartIso B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O)).hom ≫
          smallBaseChangeChartOpenHom B S hS p hp h O).hom)).symm
  · exact (yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map (smallBaseChangeChartOpenHom_leg B S hS p hp h O)).trans
        (yoneda.map_comp _ _))

/-! ### The chart change of the direct image along the cartesian projection -/

/-- **The direct-image map of the square of the two cartesian projections.**  The square
`AlgebraicGeometry.Space.chartSchemeMap_smallBaseChange_map_comp_projection` reads the chart map of
the base-changed charts as a morphism of schemes over `chartScheme V₂` from
`q_{V₁} ≫ chartSchemeMap h` to `q_{V₂}`, and this is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` of it.

The spellings of its two ends are fixed by the type ascription, and the two objects over the chart
are passed to `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` explicitly: with the type
pushed in the unifier solves them from `?Y.hom =?= smallBaseChangeSchemeProjection …` and unfolds
into the `Classical.choice` of the representability witness, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGraphLift` record. -/
def smallBaseChangeChartPushforwardMap :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V₂) ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V₁ ≫ chartSchemeMap h) :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
    (X := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V₁ ≫ chartSchemeMap h))
    (Y := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V₂))
    (Over.homMk (chartSchemeMap ((smallBaseChange B S hS p hp).map h))
      (chartSchemeMap_smallBaseChange_map_comp_projection B S hS p hp h))

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.smallBaseChangeChartOpenHom`, in the spelling the restriction comparison
uses: the shrinking of the open followed by the restriction of the chart map. -/
theorem structurePresheaf_map_smallBaseChangeChartOpenHom :
    (structurePresheaf B S hS Z.1).map
        (smallBaseChangeChartOpenHom B S hS p hp h O).op =
      Scheme.Γ.map ((chartScheme ((smallBaseChange B S hS p hp).obj V₁)).homOfLE
          (smallBaseChangeSchemeProjection_preimage_chart_le B S hS p hp h O) ≫
        (chartSchemeMap ((smallBaseChange B S hS p hp).map h) ∣_
          (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O))).op :=
  rfl

/-- **The induced morphism of open charts, read through the restriction comparison, is the chart
change of the direct image along the cartesian projection.**

It is
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_morphismRestrict` at the
chart map of the base-changed charts, together with
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app`. -/
theorem restrictFunctorΓ_inv_app_comp_smallBaseChangeChartOpenHom :
    (Scheme.restrictFunctorΓ
            (X := chartScheme ((smallBaseChange B S hS p hp).obj V₂))).inv.app
          (op (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O)) ≫
        (structurePresheaf B S hS Z.1).map
          (smallBaseChangeChartOpenHom B S hS p hp h O).op =
      (smallBaseChangeChartPushforwardMap B S hS p hp h).right.hom.app (op O) ≫
        (Scheme.restrictFunctorΓ
              (X := chartScheme ((smallBaseChange B S hS p hp).obj V₁))).inv.app
            (op (smallBaseChangeSchemeProjection B S hS p hp V₁ ⁻¹ᵁ
              (chartSchemeMap h ⁻¹ᵁ O))) :=
  (congrArg (fun m => (Scheme.restrictFunctorΓ
          (X := chartScheme ((smallBaseChange B S hS p hp).obj V₂))).inv.app
        (op (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O)) ≫ m)
      (structurePresheaf_map_smallBaseChangeChartOpenHom B S hS p hp h O)).trans
    ((Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_morphismRestrict
        (chartSchemeMap ((smallBaseChange B S hS p hp).map h))
        (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O)
        (smallBaseChangeSchemeProjection B S hS p hp V₁ ⁻¹ᵁ (chartSchemeMap h ⁻¹ᵁ O))
        (smallBaseChangeSchemeProjection_preimage_chart_le B S hS p hp h O)).trans
      (congrArg (fun m => m ≫ (Scheme.restrictFunctorΓ
            (X := chartScheme ((smallBaseChange B S hS p hp).obj V₁))).inv.app
          (op (smallBaseChangeSchemeProjection B S hS p hp V₁ ⁻¹ᵁ (chartSchemeMap h ⁻¹ᵁ O))))
        (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app
          (X := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V₁ ≫ chartSchemeMap h))
          (Y := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V₂))
          (Over.homMk (chartSchemeMap ((smallBaseChange B S hS p hp).map h))
            (chartSchemeMap_smallBaseChange_map_comp_projection B S hS p hp h)) O
          (Stacks.AffineAlgebraEquivalence.preimage_le_preimage_preimage _ _)).symm))

/-- A morphism into the image of a composite, composed out of the image of the first factor. -/
private theorem comp_map_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A : D}
    {M N P : C} (u : A ⟶ F.obj M) (a : M ⟶ N) (b : N ⟶ P) :
    u ≫ F.map (a ≫ b) = (u ≫ F.map a) ≫ F.map b := by
  rw [F.map_comp, Category.assoc]

/-! ### Naturality of the comparison in the chart -/

/-- The sections of the inverse of the comparison of sheaves of commutative rings over a Zariski
open: the inverse interchange read through global regular functions, preceded by the restriction
comparison. -/
theorem chartBaseChangeAlgebraPushforwardRingIso_inv_app (V : SmallEtale B S hS X.1)
    (O' : (chartScheme V).Opens) :
    (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V).inv.hom.app (op O') =
      (Scheme.restrictFunctorΓ
            (X := chartScheme ((smallBaseChange B S hS p hp).obj V))).inv.app
          (op (smallBaseChangeSchemeProjection B S hS p hp V ⁻¹ᵁ O')) ≫
        (structurePresheaf B S hS Z.1).map
          (smallBaseChangeOpenChartIso B S hS p hp V O').hom.op :=
  rfl

/-- **The comparison of sheaves of commutative rings is natural in the chart**, on sections over a
Zariski open and with the comparison inverted.

It is `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso_chart_naturality` read through global
regular functions, followed by
`AlgebraicGeometry.Space.restrictFunctorΓ_inv_app_comp_smallBaseChangeChartOpenHom`. -/
theorem chartBaseChangeAlgebraPushforwardRingIso_inv_app_chart_naturality :
    (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₂).inv.hom.app (op O) ≫
        (structurePresheaf B S hS Z.1).map
          ((smallBaseChange B S hS p hp).map (openChartRestrict B S hS X.1 h O)).op =
      (smallBaseChangeChartPushforwardMap B S hS p hp h).right.hom.app (op O) ≫
        (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₁).inv.hom.app
          (op (chartSchemeMap h ⁻¹ᵁ O)) := by
  have key : (structurePresheaf B S hS Z.1).map
          (smallBaseChangeOpenChartIso B S hS p hp V₂ O).hom.op ≫
        (structurePresheaf B S hS Z.1).map
          ((smallBaseChange B S hS p hp).map (openChartRestrict B S hS X.1 h O)).op =
      (structurePresheaf B S hS Z.1).map
          (smallBaseChangeChartOpenHom B S hS p hp h O).op ≫
        (structurePresheaf B S hS Z.1).map
          (smallBaseChangeOpenChartIso B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O)).hom.op :=
    ((structurePresheaf B S hS Z.1).map_comp _ _).symm.trans
      ((congrArg (fun m => (structurePresheaf B S hS Z.1).map (Quiver.Hom.op m))
          (smallBaseChangeOpenChartIso_chart_naturality B S hS p hp h O)).trans
        ((structurePresheaf B S hS Z.1).map_comp _ _))
  rw [chartBaseChangeAlgebraPushforwardRingIso_inv_app,
    chartBaseChangeAlgebraPushforwardRingIso_inv_app]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (Scheme.restrictFunctorΓ
        (X := chartScheme ((smallBaseChange B S hS p hp).obj V₂))).inv.app
      (op (smallBaseChangeSchemeProjection B S hS p hp V₂ ⁻¹ᵁ O)) ≫ m) key).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ (structurePresheaf B S hS Z.1).map
      (smallBaseChangeOpenChartIso B S hS p hp V₁ (chartSchemeMap h ⁻¹ᵁ O)).hom.op)
    (restrictFunctorΓ_inv_app_comp_smallBaseChangeChartOpenHom B S hS p hp h O)).trans ?_
  exact Category.assoc _ _ _

/-- **The comparison of sheaves of commutative rings is natural in the chart**, with the
comparison inverted.  A morphism of sheaves is determined by its sections over the Zariski opens,
and there this is
`AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardRingIso_inv_app_chart_naturality`. -/
theorem chartBaseChangeAlgebraPushforwardRingIso_inv_chart_naturality :
    (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₂).inv ≫
        chartSchemeAlgebraPushforwardComparison B S hS X
          (chartBaseChangeAlgebra B S hS p hp) h =
      (smallBaseChangeChartPushforwardMap B S hS p hp h).right ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
          (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₁).inv :=
  Sheaf.hom_ext (NatTrans.ext (funext fun O =>
    chartBaseChangeAlgebraPushforwardRingIso_inv_app_chart_naturality B S hS p hp h O.unop))

/-- **The comparison of sheaves of algebras is natural in the chart**, with the comparison
inverted.  A morphism of algebra sheaves is determined by its underlying map of sheaves of rings,
and there this is
`AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardRingIso_inv_chart_naturality`. -/
theorem chartBaseChangeAlgebraPushforwardIso_inv_chart_naturality :
    (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₂).inv ≫
        chartSchemeAlgebraPushforwardHom B S hS X (chartBaseChangeAlgebra B S hS p hp) h =
      smallBaseChangeChartPushforwardMap B S hS p hp h ≫
        (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
          (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).inv := by
  ext1
  change (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₂).inv ≫
      (chartSchemeAlgebraPushforwardHom B S hS X
        (chartBaseChangeAlgebra B S hS p hp) h).right =
    (smallBaseChangeChartPushforwardMap B S hS p hp h).right ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
        (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V₁).inv
  rw [chartSchemeAlgebraPushforwardHom_right]
  exact chartBaseChangeAlgebraPushforwardRingIso_inv_chart_naturality B S hS p hp h

/-- **The comparison of sheaves of algebras is natural in the chart.**  The chart change of the
comparison at `V₁` is the comparison at `V₂` followed by the direct-image map of the square of the
two cartesian projections.

This is
`AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardIso_inv_chart_naturality` with the
comparison turned the right way round, which is done here — at the level of morphisms of algebra
sheaves — and not on sections; see the implementation notes. -/
theorem chartSchemeAlgebraPushforwardHom_comp_chartBaseChangeAlgebraPushforwardIso :
    chartSchemeAlgebraPushforwardHom B S hS X (chartBaseChangeAlgebra B S hS p hp) h ≫
        (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
          (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).hom =
      (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₂).hom ≫
        smallBaseChangeChartPushforwardMap B S hS p hp h := by
  refine (congrArg (fun m => m ≫
      (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
        (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).hom)
    ((Iso.inv_comp_eq (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₂)).mp
      (chartBaseChangeAlgebraPushforwardIso_inv_chart_naturality B S hS p hp h))).trans ?_
  refine (Category.assoc _ _ _).trans
    (congrArg (fun m => (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₂).hom ≫ m) ?_)
  refine (Category.assoc _ _ _).trans
    ((congrArg (fun m => smallBaseChangeChartPushforwardMap B S hS p hp h ≫ m) ?_).trans
      (Category.comp_id _))
  exact (((Stacks.AffineAlgebraEquivalence.algebraPushforward
        (chartSchemeMap h)).map_comp _ _).symm.trans
    ((congrArg (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
        (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).inv_hom_id).trans
      ((Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map_id _)))

/-- **Naturality of the chart restriction of a direct-image algebra in the chart.**

For a representable `p : Z ⟶ X` and a morphism `h : V₁ ⟶ V₂` of étale scheme charts of `X`, the
chart change along `h` of `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` at
`V₁` is the comparison at `V₂` followed by
`AlgebraicGeometry.Space.smallBaseChangeChartPushforwardMap`, the direct-image map of the square of
the two cartesian projections.

The chart change is `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap`, which is the shape
`AlgebraicGeometry.Space.chartRelativeSpecLift_comp_chartRelativeSpecChartMap` consumes.

The comparison has two factors and so does the proof: the chart restriction of the *fixed*
morphism of algebra sheaves `AlgebraicGeometry.Space.pushforwardAlgebraChartIso`, for which this
is `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_naturality`, and
`AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardIso`, for which it is
`chartSchemeAlgebraPushforwardHom_comp_chartBaseChangeAlgebraPushforwardIso` and is where the
geometry sits. -/
theorem chartSchemeAlgebraLiftMap_chartSchemeDirectImageAlgebraPushforwardIso :
    chartSchemeAlgebraLiftMap B S hS X (pushforwardAlgebra B S hS (Over.mk p)) h
        (smallBaseChangeSchemeProjection B S hS p hp V₁)
        (chartSchemeDirectImageAlgebraPushforwardIso B S hS p hp V₁).hom =
      (chartSchemeDirectImageAlgebraPushforwardIso B S hS p hp V₂).hom ≫
        smallBaseChangeChartPushforwardMap B S hS p hp h := by
  refine (comp_map_comp_eq (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h))
    (chartSchemeAlgebraPushforwardHom B S hS X (pushforwardAlgebra B S hS (Over.mk p)) h)
    (chartSchemeDirectImageAlgebraChartIso B S hS p hp V₁).hom
    (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).hom).trans ?_
  refine (congrArg (fun m => m ≫
      (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
        (chartBaseChangeAlgebraPushforwardIso B S hS p hp V₁).hom)
    (chartSchemeAlgebraPushforwardHom_naturality B S hS X
      (pushforwardAlgebraChartIso B S hS p hp).hom h).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (chartSchemeDirectImageAlgebraChartIso B S hS p hp V₂).hom ≫ m)
    (chartSchemeAlgebraPushforwardHom_comp_chartBaseChangeAlgebraPushforwardIso
      B S hS p hp h)).trans ?_
  exact (Category.assoc _ _ _).symm

/-! ### The algebra map a graph carries -/

variable (T : BigFppfOver B S hS) (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V₁)
    (z : yoneda.obj T ⟶ Z.1) (hz : z ≫ p.hom = yoneda.map t ≫ V₁.obj.hom)

/-- **The chart change of the algebra map a graph carries is the graph's direct-image map read over
the larger chart.**

`AlgebraicGeometry.Space.chartGraphAlgebraMap` is the comparison followed by
`AlgebraicGeometry.Space.chartGraphPushforwardMap`, so by
`AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartSchemeDirectImageAlgebraPushforwardIso` its
chart change is the comparison at `V₂` followed by the chart change of the graph's direct-image
map.  Together with
`AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartOverAlgebraMap` this computes the chart
change of `AlgebraicGeometry.Space.chartOverAlgebraMap`, which is what the double descent of
clause (1) of Stacks 0822 compares along the two projections of a relation. -/
theorem chartSchemeAlgebraLiftMap_chartGraphAlgebraMap :
    chartSchemeAlgebraLiftMap B S hS X (pushforwardAlgebra B S hS (Over.mk p)) h
        ((BigFppfOver.toScheme B S hS).map t)
        (chartGraphAlgebraMap B S hS p hp V₁ T t z hz) =
      (chartSchemeDirectImageAlgebraPushforwardIso B S hS p hp V₂).hom ≫
        smallBaseChangeChartPushforwardMap B S hS p hp h ≫
          (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
            (chartGraphPushforwardMap B S hS p hp V₁ T t z hz) := by
  refine (comp_map_comp_eq (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h))
    (chartSchemeAlgebraPushforwardHom B S hS X (pushforwardAlgebra B S hS (Over.mk p)) h)
    (chartSchemeDirectImageAlgebraPushforwardIso B S hS p hp V₁).hom
    (chartGraphPushforwardMap B S hS p hp V₁ T t z hz)).trans ?_
  refine (congrArg (fun m => m ≫
      (Stacks.AffineAlgebraEquivalence.algebraPushforward (chartSchemeMap h)).map
        (chartGraphPushforwardMap B S hS p hp V₁ T t z hz))
    (chartSchemeAlgebraLiftMap_chartSchemeDirectImageAlgebraPushforwardIso
      B S hS p hp h)).trans ?_
  exact Category.assoc _ _ _

end Space

end AlgebraicGeometry

end
