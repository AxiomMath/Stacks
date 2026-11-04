module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageChartFactorization

/-!
# The common refinement of two diagrams of étale scheme charts

Fix an étale scheme chart `V` of `G`. A commutative diagram of étale scheme charts over `V` is
an étale scheme chart `W` of `F` together with a morphism of scheme charts of `G` from the chart
`W ⟶ F ⟶ G` to `V` — equivalently, by `AlgebraicGeometry.Space.baseChangeArrowOfChartDiagram`,
an arrow from `W` into the cartesian base change `F ×_G V`.

This file constructs the **fibre product of two such diagrams over `F ×_G V`** and proves the one
statement about it the comparison map of equation 075M needs: that a map of sections attached to
chart diagrams over `V` — an `fSpace`-map in the sense of Stacks 03G3 — takes the same value on
two chart diagrams whenever the two morphisms of `𝒳` reading it at an object `Y` are compatible
with the two morphisms into `u_G V`
(`AlgebraicGeometry.Space.fMap_app_congr_of_comparisonChartHom_eq`).

That statement is what makes the family of sections indexed by the chart diagrams over `V`
compatible, and it cannot be proved by covering `Y`: an object of `𝒳` is an arbitrary scheme
chart of `F`, and the objects coming from étale charts of `F` do not generate a covering sieve of
it. It is proved instead by refinement, which needs no sheaf condition at all: the two morphisms
of `𝒳` come from morphisms of scheme charts of `F`, those factor through the fibre product of the
two diagrams over `F ×_G V`, and over that fibre product the two chart diagrams coincide.

The fibre product is a scheme because a morphism from a representable presheaf to an algebraic
space is representable (`AlgebraicGeometry.IsAlgebraicSpace.diagonal_representable`), and it is an
étale chart of `F` because the arrow of a chart diagram into `F ×_G V` is étale — both its source
and its target being étale over `F`.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramOfChartHom`: the chart diagram over `V` of an étale chart
  `W` of `F` and a morphism of scheme charts of `G` from `W ⟶ F ⟶ G` to `V`. Every chart diagram
  over `V` is of this form, and this is the form in which chart diagrams over `V` are indexed.
* `AlgebraicGeometry.Space.chartDiagramArrowHom`: the arrow of a chart diagram into the cartesian
  base change `F ×_G V`, read as a morphism of presheaves.

## Main results

* `AlgebraicGeometry.Space.isEtale_chartDiagramArrowHom`: the arrow of a chart diagram into the
  cartesian base change `F ×_G V` is étale.
* `AlgebraicGeometry.Space.exists_chartDiagramRefine`: **the fibre product of two chart diagrams
  over `F ×_G V`** — an étale scheme chart of `F` with two morphisms of charts commuting with the
  two vertical morphisms of schemes, through which every pair of morphisms of scheme charts
  agreeing over `V` factors.
* `AlgebraicGeometry.Space.schemeChartHom_comp_eq_of_comparisonChartHom_eq`: two morphisms of
  `𝒳` compatible with the two morphisms into `u_G V` are morphisms of scheme charts of `F`
  agreeing over `V`.
* `AlgebraicGeometry.Space.fMap_app_congr_of_comparisonChartHom_eq`: **the compatibility of the
  values of an `fSpace`-map over the chart diagrams above a fixed chart `V` of `G`.**

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  (ha : schemeChartFunctor B S hS F p eF ⋙ f ≅
    CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor B S hS G q eG)
  (V : SmallEtale B S hS G)

/-! ### Chart diagrams over a fixed chart of the target -/

/-- The commutative diagram of étale scheme charts attached to an étale scheme chart `W` of `F`
and a morphism of scheme charts of `G` from the chart `W ⟶ F ⟶ G` to `V`.

Every diagram of étale scheme charts whose chart of the target is `V` is of this form, by
`AlgebraicGeometry.Space.chartDiagramOfChartHom_eq`: the two data are the same thing, the
commutativity of the diagram being the triangle of the morphism of charts. This is the form in
which the diagrams over a fixed `V` are indexed. -/
def chartDiagramOfChartHom (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    ChartDiagram B S hS F G fSpace.hom where
  U := W
  V := V
  g := ζ.left
  comm := (CostructuredArrow.w ζ).symm

/-- The chart of the source of `AlgebraicGeometry.Space.chartDiagramOfChartHom W ζ` is `W`. -/
@[simp] theorem chartDiagramOfChartHom_U (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ).U = W :=
  rfl

/-- The chart of the target of `AlgebraicGeometry.Space.chartDiagramOfChartHom W ζ` is `V`. -/
@[simp] theorem chartDiagramOfChartHom_V (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ).V = V :=
  rfl

/-- The vertical morphism of schemes of `AlgebraicGeometry.Space.chartDiagramOfChartHom W ζ` is
the morphism of schemes underlying `ζ`. -/
@[simp] theorem chartDiagramOfChartHom_g (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ).g = ζ.left :=
  rfl

/-- Every diagram of étale scheme charts is the diagram of its chart of the source and of the
morphism of scheme charts of `G` its vertical morphism is. -/
theorem chartDiagramOfChartHom_eq (d : ChartDiagram B S hS F G fSpace.hom) :
    chartDiagramOfChartHom B S hS F G hF hG fSpace d.V d.U
        (CostructuredArrow.homMk d.g d.comm.symm) = d :=
  rfl

/-! ### The arrow of a chart diagram into the cartesian base change is étale -/

/-- The arrow into the cartesian base change `F ×_G V` attached to a diagram of étale scheme
charts, read as a morphism of presheaves. -/
noncomputable abbrev chartDiagramArrowHom (d : ChartDiagram B S hS F G fSpace.hom) :
    yoneda.obj ((SmallEtale.toOver B S hS F).obj d.U) ⟶
      ((SpacesEtale.toSpaces B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).obj
        (chartBaseChange B S hS fSpace d.V)).1 :=
  ((SpacesEtale.toSpaces B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).map
    (baseChangeArrowOfChartDiagram B S hS fSpace d)).hom

/-- **The arrow of a diagram of étale scheme charts into the cartesian base change `F ×_G V` is
étale.** Both its source and its target are étale over `F`, and étaleness is cancellable:
`AlgebraicGeometry.Space.isEtale_of_isEtale_over`. -/
theorem isEtale_chartDiagramArrowHom (d : ChartDiagram B S hS F G fSpace.hom) :
    IsEtale B S hS (chartDiagramArrowHom B S hS F G hF hG fSpace d) :=
  isEtale_of_isEtale_over B S hS
    (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS F).obj d.U))
    ((SpacesEtale.toSpaces B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).obj
      (chartBaseChange B S hS fSpace d.V)).property
    hF _ d.U.1.hom (chartBaseChange B S hS fSpace d.V).1.hom.hom
    (isEtale_of_presheaf_etale B S hS d.U.property)
    (chartBaseChange B S hS fSpace d.V).property
    (congrArg (fun k ↦ k.hom)
      (Over.w (baseChangeArrowOfChartDiagram B S hS fSpace d).hom))

/-- The arrow of a diagram of charts into `F ×_G V`, followed by the structure morphism of the
base change, is the structure morphism of the chart of `F`. -/
theorem chartDiagramArrowHom_comp_structure (d : ChartDiagram B S hS F G fSpace.hom) :
    chartDiagramArrowHom B S hS F G hF hG fSpace d ≫
        (chartBaseChange B S hS fSpace d.V).1.hom.hom =
      d.U.1.hom :=
  congrArg (fun k ↦ k.hom) (Over.w (baseChangeArrowOfChartDiagram B S hS fSpace d).hom)

/-- The arrow of a diagram of charts into `F ×_G V`, followed by the cartesian projection, is the
vertical morphism of schemes of the diagram. -/
theorem chartDiagramArrowHom_comp_projection (d : ChartDiagram B S hS F G fSpace.hom) :
    chartDiagramArrowHom B S hS F G hF hG fSpace d ≫
        ((spacesBaseChange B S hS fSpace).projection.app
          ((comparisonFunctor B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).obj d.V)).hom =
      yoneda.map d.g :=
  yoneda_map_baseChangeArrowOfChartDiagram B S hS fSpace d

/-- Two morphisms of presheaves into `F ×_G V` out of a representable presheaf agree as soon as
they agree after the structure morphism to `F` and after the cartesian projection to the chart
`V` of `G`: the base change is a fibre product of algebraic spaces, and a representable presheaf
is an algebraic space. -/
theorem chartBaseChange_hom_ext (T : BigFppfOver B S hS)
    {a b : yoneda.obj T ⟶ ((SpacesEtale.toSpaces B S hS
      (⟨F, hF⟩ : AlgebraicSpaces B S hS)).obj (chartBaseChange B S hS fSpace V)).1}
    (hproj : a ≫ ((spacesBaseChange B S hS fSpace).projection.app
        ((comparisonFunctor B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).obj V)).hom =
      b ≫ ((spacesBaseChange B S hS fSpace).projection.app
        ((comparisonFunctor B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).obj V)).hom)
    (hstr : a ≫ (chartBaseChange B S hS fSpace V).1.hom.hom =
      b ≫ (chartBaseChange B S hS fSpace V).1.hom.hom) :
    a = b := by
  have := ((spacesBaseChange B S hS fSpace).isPullback
    ((comparisonFunctor B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)).obj V)).hom_ext
    (k := (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶
        (SpacesEtale.toSpaces B S hS (⟨F, hF⟩ : AlgebraicSpaces B S hS)).obj
          (chartBaseChange B S hS fSpace V)))
    (l := ObjectProperty.homMk b)
    (ObjectProperty.hom_ext _ hproj) (ObjectProperty.hom_ext _ hstr)
  exact congrArg (fun k ↦ k.hom) this

/-! ### The refinement of two chart diagrams -/

/-- **The fibre product of two diagrams of étale scheme charts over `F ×_G V`.** For two diagrams
of étale scheme charts over the same chart `V` of `G` there are an étale scheme chart `W₃` of `F`
and two morphisms of charts to the two charts of the source which commute with the two vertical
morphisms of schemes, and through which every pair of morphisms of scheme charts into the two
charts commuting with the vertical morphisms factors.

The chart `W₃` is the fibre product of the two arrows into `F ×_G V`, which is representable
because those arrows go from representable presheaves into an algebraic space, and is étale over
`F` because the arrows are étale (`AlgebraicGeometry.Space.isEtale_chartDiagramArrowHom`) and so
is the chart of the other factor. Its universal property is the universal property of a fibre
product of presheaves, so it is available against an arbitrary scheme chart of `F` and not only
against an étale one. -/
theorem exists_chartDiagramRefine (W₁ W₂ : SmallEtale B S hS F)
    (ζ₁ : (CostructuredArrow.map fSpace.hom).obj W₁.1 ⟶ V.1)
    (ζ₂ : (CostructuredArrow.map fSpace.hom).obj W₂.1 ⟶ V.1) :
    ∃ (W₃ : SmallEtale B S hS F) (k₁ : W₃ ⟶ W₁) (k₂ : W₃ ⟶ W₂),
      (SmallEtale.toOver B S hS F).map k₁ ≫ ζ₁.left =
          (SmallEtale.toOver B S hS F).map k₂ ≫ ζ₂.left ∧
        ∀ (Y₀ : CostructuredArrow yoneda F) (μ₁ : Y₀ ⟶ W₁.1) (μ₂ : Y₀ ⟶ W₂.1),
          μ₁.left ≫ ζ₁.left = μ₂.left ≫ ζ₂.left →
          ∃ μ₃ : Y₀ ⟶ W₃.1,
            μ₃ ≫ (SmallEtale.inclusion B S hS F).map k₁ = μ₁ ∧
              μ₃ ≫ (SmallEtale.inclusion B S hS F).map k₂ = μ₂ := by
  set d₁ := chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁ with hd₁
  set d₂ := chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂ with hd₂
  set u₁ := chartDiagramArrowHom B S hS F G hF hG fSpace d₁ with hu₁
  set u₂ := chartDiagramArrowHom B S hS F G hF hG fSpace d₂ with hu₂
  have hpre : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u₁ :=
    presheaf_etale_of_isEtale B S hS (isEtale_chartDiagramArrowHom B S hS F G hF hG fSpace d₁)
  set r := hpre.rep with hr
  have hpb : IsPullback (yoneda.map (r.fst' u₂)) (yoneda.map (r.snd u₂)) u₁ u₂ :=
    hpre.rep.isPullback' u₂
  have hEtSnd : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (r.snd u₂)) :=
    hpre.property_snd u₂
  have hiff : ∀ {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ yoneda.obj W₁.1.left)
      (b : yoneda.obj T ⟶ yoneda.obj W₂.1.left), a ≫ u₁ = b ≫ u₂ ↔
        a ≫ yoneda.map ζ₁.left = b ≫ yoneda.map ζ₂.left ∧ a ≫ W₁.1.hom = b ≫ W₂.1.hom := by
    have e₁ : u₁ ≫ _ = yoneda.map ζ₁.left :=
      chartDiagramArrowHom_comp_projection B S hS F G hF hG fSpace d₁
    have e₂ : u₂ ≫ _ = yoneda.map ζ₂.left :=
      chartDiagramArrowHom_comp_projection B S hS F G hF hG fSpace d₂
    have s₁ : u₁ ≫ _ = W₁.1.hom := chartDiagramArrowHom_comp_structure B S hS F G hF hG fSpace d₁
    have s₂ : u₂ ≫ _ = W₂.1.hom := chartDiagramArrowHom_comp_structure B S hS F G hF hG fSpace d₂
    intro T a b
    refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ chartBaseChange_hom_ext B S hS F G hF hG fSpace V T ?_ ?_⟩
    · exact (congrArg (a ≫ ·) e₁.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans (congrArg (b ≫ ·) e₂))))
    · exact (congrArg (a ≫ ·) s₁.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans (congrArg (b ≫ ·) s₂))))
    · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) e₁).trans
        (h.1.trans ((congrArg (b ≫ ·) e₂).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) s₁).trans
        (h.2.trans ((congrArg (b ≫ ·) s₂).symm.trans (Category.assoc _ _ _).symm)))
  have hstr := ((hiff _ _).mp hpb.w).2
  have hEtW₃ : IsEtale B S hS (yoneda.map (r.snd u₂) ≫ W₂.1.hom) :=
    isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS
        ((presheaf_yoneda_map_etale_iff B S hS (r.snd u₂)).mpr hEtSnd))
      (isEtale_of_presheaf_etale B S hS W₂.property)
  refine ⟨⟨CostructuredArrow.mk (yoneda.map (r.snd u₂) ≫ W₂.1.hom),
      presheaf_etale_of_isEtale B S hS hEtW₃⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk (r.fst' u₂) hstr),
    ObjectProperty.homMk (CostructuredArrow.homMk (r.snd u₂) rfl), ?_, ?_⟩
  · refine yoneda.map_injective ?_
    rw [yoneda.map_comp, yoneda.map_comp]
    exact ((hiff _ _).mp hpb.w).1
  · intro Y₀ μ₁ μ₂ hμ
    have hlift : yoneda.map μ₁.left ≫ u₁ = yoneda.map μ₂.left ≫ u₂ := by
      refine (hiff _ _).mpr ⟨?_, ?_⟩
      · rw [← yoneda.map_comp, ← yoneda.map_comp, hμ]
      · exact (CostructuredArrow.w μ₁).trans (CostructuredArrow.w μ₂).symm
    refine ⟨CostructuredArrow.homMk (r.lift' μ₁.left μ₂.left hlift) ?_, ?_, ?_⟩
    · change yoneda.map (r.lift' μ₁.left μ₂.left hlift) ≫
        (yoneda.map (r.snd u₂) ≫ W₂.1.hom) = Y₀.hom
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ W₂.1.hom)
        (yoneda.map_comp _ _).symm).trans ((congrArg (yoneda.map · ≫ W₂.1.hom)
          (r.lift'_snd μ₁.left μ₂.left hlift)).trans (CostructuredArrow.w μ₂)))
    · exact CostructuredArrow.hom_ext _ _ (r.lift'_fst μ₁.left μ₂.left hlift)
    · exact CostructuredArrow.hom_ext _ _ (r.lift'_snd μ₁.left μ₂.left hlift)

/-! ### The compatibility of the values of an `fSpace`-map over a chart of the target -/

/-- Restriction along a composite is the composite of the restrictions. -/
private theorem map_op_comp_apply {C : Type*} [Category C] (K : Cᵒᵖ ⥤ Type u) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : K.obj (op Z)) :
    K.map (a ≫ b).op x = K.map a.op (K.map b.op x) := by
  rw [op_comp, K.map_comp]
  rfl

/-- **The morphism of scheme charts of `G` that a morphism of `𝒳` into the image of an étale
chart induces.** If two morphisms of `𝒳` out of an object `Y` into the images of two étale charts
of `F` are compatible with the two morphisms into `u_G V` attached to two chart diagrams, then the
two morphisms of scheme charts of `F` they are — `AlgebraicGeometry.Space.schemeChartFunctor`
being an equivalence — agree after the two vertical morphisms of schemes.

This is `AlgebraicGeometry.Space.comparisonChartHom_comp_schemeChartFunctor_map`, which writes
each composite as the compatibility `ha` at the chart followed by the image of a morphism of
scheme charts of `G`, together with faithfulness of `schemeChartFunctor`. -/
theorem schemeChartHom_comp_eq_of_comparisonChartHom_eq
    (W₁ W₂ : SmallEtale B S hS F)
    (ζ₁ : (CostructuredArrow.map fSpace.hom).obj W₁.1 ⟶ V.1)
    (ζ₂ : (CostructuredArrow.map fSpace.hom).obj W₂.1 ⟶ V.1)
    (Y₀ : CostructuredArrow yoneda F) (μ₁ : Y₀ ⟶ W₁.1) (μ₂ : Y₀ ⟶ W₂.1)
    (hn : f.map ((schemeChartFunctor B S hS F p eF).map μ₁) ≫
          comparisonChartHom B S hS p q eF eG f fSpace ha
            (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁) =
        f.map ((schemeChartFunctor B S hS F p eF).map μ₂) ≫
          comparisonChartHom B S hS p q eF eG f fSpace ha
            (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂)) :
    μ₁.left ≫ ζ₁.left = μ₂.left ≫ ζ₂.left := by
  have key : ∀ {W : SmallEtale B S hS F} (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1)
      (μ : Y₀ ⟶ W.1),
      f.map ((schemeChartFunctor B S hS F p eF).map μ) ≫
          comparisonChartHom B S hS p q eF eG f fSpace ha
            (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) =
        ha.hom.app Y₀ ≫ (schemeChartFunctor B S hS G q eG).map
          ((CostructuredArrow.map fSpace.hom).map μ ≫ ζ) := fun ζ μ ↦
    comparisonChartHom_comp_schemeChartFunctor_map B S hS F G p q hF hG eF eG f fSpace ha
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V _ ζ) Y₀ μ
  have hξ := (schemeChartFunctor B S hS G q eG).map_injective
    ((NatIso.cancel_natIso_hom_left ha _ _).mp ((key ζ₁ μ₁).symm.trans (hn.trans (key ζ₂ μ₂))))
  exact congrArg (fun m ↦ CostructuredArrow.Hom.left m) hξ

/-- **The values of an `fSpace`-map over the diagrams of étale scheme charts above a fixed chart
`V` of `G` are compatible.** Let `Y` be an object of `𝒳` and let `n₁`, `n₂` be morphisms of `𝒳`
from `Y` into the objects attached to the charts of two diagrams over `V`, compatible with the two
morphisms into `u_G V` the diagrams provide. Then the two values of the map of sections restrict
along `n₁` and along `n₂` to the same section over `Y`.

No sheaf condition is used, and none would help: an object of `𝒳` is an arbitrary scheme chart of
`F`, so it is not covered by the objects coming from étale charts of `F` in any sieve generated by
morphisms out of them. What is used is the **refinement**
`AlgebraicGeometry.Space.exists_chartDiagramRefine`: the two morphisms of `𝒳` are morphisms of
scheme charts of `F`, and compatibility means they agree over `V`, so they factor through the
fibre product of the two diagrams over `F ×_G V` — over which the two diagrams of charts, having
the same chart and the same vertical morphism, are one and the same diagram. -/
theorem fMap_app_congr_of_comparisonChartHom_eq
    (K : 𝒳ᵒᵖ ⥤ Type u) (Qp : (SmallEtale B S hS G)ᵒᵖ ⥤ Type u)
    (ρ : FMap B S hS F G fSpace.hom ((restrictionFunctor B S hS F p eF).op ⋙ K) Qp)
    (t : Qp.obj (op V)) (W₁ W₂ : SmallEtale B S hS F)
    (ζ₁ : (CostructuredArrow.map fSpace.hom).obj W₁.1 ⟶ V.1)
    (ζ₂ : (CostructuredArrow.map fSpace.hom).obj W₂.1 ⟶ V.1)
    (Y : 𝒳) (n₁ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₁)
    (n₂ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₂)
    (hn : f.map n₁ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁) =
        f.map n₂ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂)) :
    K.map n₁.op (ρ.app (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁) t) =
      K.map n₂.op (ρ.app (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂) t) := by
  obtain ⟨Y₀, ⟨ι⟩⟩ : ∃ Y₀ : CostructuredArrow yoneda F,
      Nonempty ((schemeChartFunctor B S hS F p eF).obj Y₀ ≅ Y) :=
    ⟨(schemeChartFunctor B S hS F p eF).objPreimage Y,
      ⟨(schemeChartFunctor B S hS F p eF).objObjPreimageIso Y⟩⟩
  -- the two morphisms of `𝒳` are the images of morphisms of scheme charts, up to `ι`
  have hpre : ∀ {W : SmallEtale B S hS F} (n : Y ⟶ (restrictionFunctor B S hS F p eF).obj W),
      ∃ μ : Y₀ ⟶ W.1, n = ι.inv ≫ (schemeChartFunctor B S hS F p eF).map μ := fun n ↦
    ⟨(schemeChartFunctor B S hS F p eF).preimage (ι.hom ≫ n), by
      rw [(schemeChartFunctor B S hS F p eF).map_preimage]
      exact (ι.inv_hom_id_assoc n).symm⟩
  obtain ⟨μ₁, rfl⟩ := hpre n₁
  obtain ⟨μ₂, rfl⟩ := hpre n₂
  -- they agree over `V`
  have hμ : μ₁.left ≫ ζ₁.left = μ₂.left ≫ ζ₂.left := by
    refine schemeChartHom_comp_eq_of_comparisonChartHom_eq B S hS F G p q hF hG eF eG f fSpace
      ha V W₁ W₂ ζ₁ ζ₂ Y₀ μ₁ μ₂ ?_
    erw [f.map_comp, f.map_comp, Category.assoc, Category.assoc] at hn
    exact (cancel_epi (f.map ι.inv)).mp hn
  -- so they factor through the refinement
  obtain ⟨W₃, k₁, k₂, hV, hlift⟩ := exists_chartDiagramRefine B S hS F G hF hG fSpace V
    W₁ W₂ ζ₁ ζ₂
  obtain ⟨μ₃, hμ₃₁, hμ₃₂⟩ := hlift Y₀ μ₁ μ₂ hμ
  -- and over the refinement the two diagrams of charts coincide
  have hres : ∀ {W : SmallEtale B S hS F}
      (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) (k : W₃ ⟶ W),
      K.map (ι.inv ≫ (schemeChartFunctor B S hS F p eF).map
          (μ₃ ≫ (SmallEtale.inclusion B S hS F).map k)).op
        (ρ.app (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) t) =
        K.map (ι.inv ≫ (schemeChartFunctor B S hS F p eF).map μ₃).op
          (ρ.app (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₃
            ((CostructuredArrow.map fSpace.hom).map
              ((SmallEtale.inclusion B S hS F).map k) ≫ ζ)) t) := by
    intro W ζ k
    have hnat := ρ.naturality (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ)
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₃
        ((CostructuredArrow.map fSpace.hom).map ((SmallEtale.inclusion B S hS F).map k) ≫ ζ))
      k (𝟙 V) (by simp) t
    rw [Functor.map_comp, ← Category.assoc]
    refine (map_op_comp_apply K _ _ _).trans ?_
    have hid : Qp.map (𝟙 V).op t = t := by simp
    exact congrArg _ ((congrArg (ρ.app _) hid.symm).trans hnat).symm
  rw [← hμ₃₁, ← hμ₃₂]
  refine (hres ζ₁ k₁).trans (Eq.trans ?_ (hres ζ₂ k₂).symm)
  exact congrArg (fun z ↦ K.map (ι.inv ≫ (schemeChartFunctor B S hS F p eF).map μ₃).op z)
    (FMap.app_congr B S hS fSpace ρ hV t)

end AlgebraicGeometry.Space

end
