module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartExt
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientToBase

/-!
# The thickened quotient realizes the algebra structure

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the small
étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT), realized by
the thickening `i : X ⟶ X' = U'/R'` with `i⁻¹𝒪_{X'} ≅ 𝒜` and the morphism `h : X' ⟶ Y` with
`i ≫ h = f`. The algebra structure `f⁻¹𝒪_Y ⟶ 𝒜` is the composite
`f⁻¹𝒪_Y = (i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y ⟶ i⁻¹𝒪_{X'} ≅ 𝒜` of the comparison of Stacks 03G8, the
inverse image of the structure map of `h`, and the identification of the structure sheaf.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.toBase_eq_thickeningQuotientToBase`: the algebra
  structure `f⁻¹𝒪_Y ⟶ 𝒜` of `E` is the composite above.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of global functions along the chart morphism named by a chart diagram is pullback
along its vertical morphism. -/
theorem chartPullback_indexOfChartDiagram_appTop {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 k.hom) (x : Γ(chartScheme d.V, ⊤)) :
    chartPullback B S hS k d.V (indexOfChartDiagram B S hS k d) x = d.schemeMap.appTop x := by
  rw [chartPullback, chartBaseChangeMap_indexOfChartDiagram]
  rfl

/-- Along an equality `f' = f` of morphisms, the chart components of `eqToHom _ ≫ φ` over `f`
agree with those of `φ` over `f'` at indices with the same chart base change map. -/
theorem inverseImageHomChartRingHom_eqToHom {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y}
    (hf : f' = f) (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (φ : (smallEtaleRingedToposHom B S hS f').toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    {T : SmallEtale B S hS X.1}
    (a : (comparisonFunctor B S hS X).obj T ⟶ chartBaseChange B S hS f V)
    (a' : (comparisonFunctor B S hS X).obj T ⟶ chartBaseChange B S hS f' V)
    (ha : chartBaseChangeMap B S hS f V (StructuredArrow.mk a.op) =
      chartBaseChangeMap B S hS f' V (StructuredArrow.mk a'.op))
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A
        (eqToHom (congrArg
          (fun φ ↦ (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImageRing.obj
            (smallEtaleRingedTopos B S hS Y).O) hf.symm) ≫ φ) V (StructuredArrow.mk a.op) x =
      inverseImageHomChartRingHom B S hS f' A φ V (StructuredArrow.mk a'.op) x := by
  subst hf
  obtain rfl := chartBaseChangeMap_injective B S hS _ ha
  rw [eqToHom_refl, Category.id_comp]

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property) (Q : Presentation B S hS Y.obj Y.property)
  (gU : P.U ⟶ Q.U) (hgU : P.toSpace ≫ f.hom = yoneda.map gU ≫ Q.toSpace)
  (gR : P.R ⟶ Q.R) (hgt : gR ≫ Q.target = P.target ≫ gU) (hgs : gR ≫ Q.source = P.source ≫ gU)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- The chart component of `i⁻¹𝒪_{X'} ≅ 𝒜` on the chart `W ⟶ W'` is `Γ(W', ⊤) ≅ 𝒜(W)`. -/
theorem inverseImageHomChartRingHom_quotientSheafIso_hom (W : OverPresentation P)
    (x : (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O.obj.obj
      (op (E.thickenedChartDiagram P hU hR W).V)) :
    inverseImageHomChartRingHom B S hS (E.thickeningImmersion P hU hR) E.A
        (E.quotientSheafIso P hU hR).hom (E.thickenedChartDiagram P hU hR W).V
        (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) x =
      (E.chartRealizedSchemeΓIso W.obj).inv x := by
  let t := (smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)).toToposHom
  have he : t.ringAdjunction.homEquiv _ _ (E.quotientSheafIso P hU hR).hom ≫
      (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) E.A).hom =
        (E.structureIsoRingDirectImageRan P hU hR).hom := by
    change t.ringAdjunction.homEquiv _ _ ((t.ringAdjunction.homEquiv _ _).symm
      (E.structureIsoPushforward P hU hR).hom) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _))
  change ringDirectImageRanChartProjection B S hS _ E.A _ _
    ((t.ringAdjunction.homEquiv _ _ (E.quotientSheafIso P hU hR).hom ≫
      (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) E.A).hom).hom.app _ x) = _
  rw [he]
  have hw := congrArg (fun α ↦ α.app (op W))
    (E.whiskerLeft_structureIsoRingDirectImageRan_hom P hU hR)
  have hx := ConcreteCategory.congr_hom hw x
  change (E.structureIsoRingDirectImageRan P hU hR).hom.hom.app _ x =
    (E.thickenedChartRingEquiv P hU hR E.A W).symm ((E.chartRealizedSchemeΓIso W.obj).inv x) at hx
  rw [hx]
  exact (E.thickenedChartRingEquiv P hU hR E.A W).apply_symm_apply _

/-- **`W' ⟶ X' ⟶ Y` is `W' ⟶ V ⟶ Y`** for a chart `W` of `X` over `U` and any chart diagram
`W ⟶ V` over `f`. -/
theorem thickenedChartHom_comp_thickeningQuotientToBase (W : OverPresentation P)
    {V : SmallEtale B S hS Y.1}
    (g : (SmallEtale.toOver B S hS X.1).obj W.obj ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (c : W.obj.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom) :
    ((E.thickenedChartFunctor P hU hR).obj W).obj.hom ≫
        (E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR).hom =
      yoneda.map (E.chartRealizedSchemeOverToBase ⟨W.obj, V, g, c⟩
        (E.contains_chartRealizedScheme_of_hom (Classical.choice W.property) hU)) ≫ V.obj.hom := by
  let a := Classical.choice W.property
  have hW := E.contains_chartRealizedScheme_of_hom a hU
  let d₀ := thickeningChartDiagram P Q gU hgU
  let g₀ : (SmallEtale.toOver B S hS X.1).obj W.obj ⟶
      (SmallEtale.toOver B S hS Y.1).obj (presentationChart Q) :=
    (SmallEtale.toOver B S hS X.1).map a ≫ d₀.g
  have ca : W.obj.1.hom ≫ f.hom = yoneda.map g₀ ≫ (presentationChart Q).1.hom :=
    (congrArg (· ≫ f.hom) (CostructuredArrow.w a.hom).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (yoneda.map ((SmallEtale.toOver B S hS X.1).map a) ≫ ·) d₀.comm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (presentationChart Q).1.hom) (yoneda.map_comp _ _).symm))))
  have key : E.chartRealizedSchemeOverMap hS a hU hW ≫ E.thickeningChartToBase P Q gU hgU hU =
      E.chartRealizedSchemeOverToBase ⟨W.obj, presentationChart Q, g₀, ca⟩ hW := by
    refine BigFppfOver.map_toScheme_injective B S hS ?_
    change (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
    refine (E.chartRealizedSchemeMap_comp_chartRealizedSchemeToBase E.toBase E.toBase_π
      d₀ ⟨W.obj, presentationChart Q, g₀, ca⟩ a (𝟙 _)
      ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
        ((SmallEtale.toOver B S hS Y.1).map_id _).symm))).trans ?_
    exact (congrArg (_ ≫ ·) ((BigFppfOver.toScheme B S hS).map_id _)).trans (Category.comp_id _)
  change (yoneda.map (E.chartRealizedSchemeOverMap hS a hU hW) ≫
    E.thickeningQuotientMap P hU hR) ≫ _ = _
  rw [Category.assoc, thickeningQuotientMap_comp_thickeningQuotientToBase, ← Category.assoc,
    ← Functor.map_comp, key]
  exact E.chartRealizedSchemeOverToBase_toSpace_eq _ g ca c hW

omit E in
/-- The restriction of a chart diagram to the whole of its target chart. -/
theorem restrictChartOpens_top_comm (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (SmallEtale.toOver B S hS X.1).map (chartOpensTopHom B S hS X d.U) ≫ d.g =
      (d.restrictChartOpens ⊤).g ≫
        (SmallEtale.toOver B S hS Y.1).map (chartOpensTopHom B S hS Y d.V) := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change (d.schemeMap ⁻¹ᵁ ⊤).ι ≫ d.schemeMap = (d.schemeMap ∣_ ⊤) ≫ (⊤ : (chartScheme d.V).Opens).ι
  rw [morphismRestrict_ι]

/-- **The global sections of `W' ⟶ V` are the chart component of the algebra structure**, read on
`W` through `𝒜(W) ⟶ 𝒜(W|_⊤) = Γ(W', ⊤)`. -/
theorem chartRealizedSchemeToBase_appTop (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : Γ(chartScheme d.V, ⊤)) :
    (E.chartRealizedSchemeToBase E.toBase E.toBase_π d).appTop x =
      (E.chartRealizedSchemeΓIso d.U).hom
        (inverseImageHomChartRingHom B S hS f E.A E.toBase d.V
          (indexOfChartDiagram B S hS f d) x) :=
  inverseImageHomChartRingHom_naturality B S hS f E.A E.toBase d (d.restrictChartOpens ⊤) _
    (chartOpensTopHom B S hS Y d.V) (restrictChartOpens_top_comm d) x

/-- **The algebra structure of the extension is realized by `X' ⟶ Y`**: it is the composite
`f⁻¹𝒪_Y = (i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y ⟶ i⁻¹𝒪_{X'} ≅ 𝒜` of the comparison of Stacks 03G8, the inverse
image of the structure map of `h : X' ⟶ Y`, and `i⁻¹𝒪_{X'} ≅ 𝒜`. -/
theorem toBase_eq_thickeningQuotientToBase :
    E.toBase =
      eqToHom (congrArg (fun φ ↦ (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImageRing.obj
          (smallEtaleRingedTopos B S hS Y).O)
          (E.thickeningImmersion_comp_thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR).symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (E.thickeningImmersion P hU hR)
          (E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR)).inv.app
            (smallEtaleRingedTopos B S hS Y).O ≫
        (smallEtaleInverseImageRing B S hS (E.thickeningImmersion P hU hR)).map
          (smallEtaleRingedToposHom B S hS
            (E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR)).fSharpInverseImage ≫
        (E.quotientSheafIso P hU hR).hom := by
  let i := E.thickeningImmersion P hU hR
  let h := E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR
  refine inverseImageHomChartRingHom_ext_of_isCoverDense f E.A (overPresentationChart P).ι
    (fun W V a x ↦ ?_)
  have hW := E.contains_chartRealizedScheme_of_hom (Classical.choice W.property) hU
  let j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
    StructuredArrow.mk (Y := op W.obj) a.op
  let g₁ := chartBaseChangeMap B S hS f V j
  have c₁ := (chartDiagramOfIndex B S hS f V j).comm
  let d : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W.obj, V, g₁, c₁⟩
  let dh : ChartDiagram B S hS (E.thickeningQuotient hS P hU hR).1 Y.1 h.hom :=
    ⟨(E.thickenedChartFunctor P hU hR).obj W, V, E.chartRealizedSchemeOverToBase d hW,
      E.thickenedChartHom_comp_thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR W g₁ c₁⟩
  let tcd := E.thickenedChartDiagram P hU hR W
  have hga : chartBaseChangeMap B S hS f V j = tcd.g ≫ dh.g := by
    refine BigFppfOver.map_toScheme_injective B S hS ?_
    change (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    refine Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp _ _).symm
    exact ((congrArg₂ (· ≫ ·) (E.toScheme_map_chartInclusionOver W.obj hW)
      (E.toScheme_map_chartRealizedSchemeOverToBase d hW)).trans
        (E.chartInclusion_comp_chartRealizedSchemeToBase _ _ d)).symm
  have ha : chartBaseChangeMap B S hS f V (StructuredArrow.mk a.op) =
      chartBaseChangeMap B S hS (i ≫ h) V (StructuredArrow.mk
        (chartLift B S hS i tcd ≫ chartBaseChangeComp B S hS i h V
          (indexOfChartDiagram B S hS h dh)).op) :=
    hga.trans ((chartBaseChangeMap_comp_chart B S hS i h V
      (indexOfChartDiagram B S hS h dh) (indexOfChartDiagram B S hS i tcd)).trans
      (congrArg₂ (· ≫ ·) (chartBaseChangeMap_indexOfChartDiagram B S hS i tcd)
        (chartBaseChangeMap_indexOfChartDiagram B S hS h dh))).symm
  have hpull : chartPullback B S hS h V (indexOfChartDiagram B S hS h dh) x =
      (E.chartRealizedSchemeToBase E.toBase E.toBase_π d).appTop x :=
    (chartPullback_indexOfChartDiagram_appTop h dh x).trans
      (congrArg (fun m ↦ m.appTop x) (E.toScheme_map_chartRealizedSchemeOverToBase d hW))
  refine Eq.trans ?_ (inverseImageHomChartRingHom_eqToHom
    (E.thickeningImmersion_comp_thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR) E.A _ V a _
      ha x).symm
  refine Eq.trans ?_ (inverseImageHomChartRingHom_compInverseImage B S hS i h E.A
    (E.quotientSheafIso P hU hR).hom V (indexOfChartDiagram B S hS h dh)
    (indexOfChartDiagram B S hS i tcd) x).symm
  refine Eq.trans ?_ (E.inverseImageHomChartRingHom_quotientSheafIso_hom P hU hR W _).symm
  refine Eq.trans ?_ (congrArg (E.chartRealizedSchemeΓIso W.obj).inv
    (hpull.trans (E.chartRealizedSchemeToBase_appTop d x))).symm
  refine Eq.trans ?_ (Iso.hom_inv_id_apply (E.chartRealizedSchemeΓIso W.obj) _).symm
  exact (inverseImageHomChartRingHom_congr_hom E.A E.toBase V _ _
    (chartLift_unique B S hS f d a (yoneda_map_chartBaseChangeMap B S hS f V j).symm).symm x).symm

end SquareZeroExtension

end AlgebraicGeometry.Space

end
