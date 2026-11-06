module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionStructureMap

/-!
# Chart thickenings map compatibly to the charts of a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces and `E` a square-zero extension
of the small étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT).
For a chart diagram `W ⟶ V` over `f` and a chart diagram `V ⟶ T` over `g`, the morphism
`W' ⟶ V` given by the algebra structure, followed by `V ⟶ T`, is the morphism `W' ⟶ T` given by
the composed algebra structure over `(f ≫ g)⁻¹𝒪_Z`
(`AlgebraicGeometry.Space.SquareZeroExtension.compToBase`). For `Z` the base `S` this says that
`W' ⟶ V` is a morphism over `S`, for the structure morphisms of the chart thickenings
(`AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeToBaseScheme`).

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeToBase_comp_schemeMap`: the
  composition formula.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeToBase_comp_toBase`: `W' ⟶ V` is
  a morphism over `S`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f) (g : Y ⟶ Z)
  (e : ChartDiagram B S hS Y.1 Z.1 g.hom) {U : SmallEtale B S hS X.1}
  (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj e.U)
  (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ e.U.1.hom)

/-- The morphism `W' ⟶ V` given by an algebra structure depends only on the vertical morphism
of the chart diagram. -/
theorem chartRealizedSchemeToBase_congr_g {Z : AlgebraicSpaces B S hS} {k : X ⟶ Z}
    (φ : (smallEtaleRingedToposHom B S hS k).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Z).O ⟶ E.A)
    (hφ : φ ≫ E.π = (smallEtaleRingedToposHom B S hS k).fSharpInverseImage)
    {V : SmallEtale B S hS Z.1}
    (b b' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hb : U.1.hom ≫ k.hom = yoneda.map b ≫ V.1.hom)
    (hb' : U.1.hom ≫ k.hom = yoneda.map b' ≫ V.1.hom) (h : b = b') :
    E.chartRealizedSchemeToBase φ hφ ⟨U, V, b, hb⟩ =
      E.chartRealizedSchemeToBase φ hφ ⟨U, V, b', hb'⟩ := by
  subst h
  rfl

/-- The scheme map of a composed chart diagram is the composite of the scheme maps. -/
private theorem schemeMap_chartDiagram_comp :
    (ChartDiagram.comp B S hS f g a e.g ha e.comm).schemeMap =
      (BigFppfOver.toScheme B S hS).map a ≫ e.schemeMap :=
  (BigFppfOver.toScheme B S hS).map_comp a e.g

omit E in
/-- The preimage of `O` under the composed vertical morphism is contained in the iterated
preimage (they are equal). -/
theorem preimage_chartDiagram_comp_le (O : (chartScheme e.V).Opens) :
    (ChartDiagram.comp B S hS f g a e.g ha e.comm).schemeMap ⁻¹ᵁ O ≤
      (ChartDiagram.schemeMap ⟨U, e.U, a, ha⟩) ⁻¹ᵁ (e.schemeMap ⁻¹ᵁ O) := by
  intro y hy
  rwa [schemeMap_chartDiagram_comp g e a ha] at hy

omit E in
/-- The restriction of a composed chart diagram maps to the composite of the restrictions. -/
theorem restrictChartOpens_chartDiagram_comp_comm (O : (chartScheme e.V).Opens) :
    (SmallEtale.toOver B S hS X.1).map ((chartOpens B S hS U).map
        (homOfLE (preimage_chartDiagram_comp_le g e a ha O))) ≫
      (ChartDiagram.restrictChartOpens ⟨U, e.U, a, ha⟩ (e.schemeMap ⁻¹ᵁ O)).g ≫
        (e.restrictChartOpens O).g =
      ((ChartDiagram.comp B S hS f g a e.g ha e.comm).restrictChartOpens O).g := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show (chartScheme U).homOfLE (preimage_chartDiagram_comp_le g e a ha O) ≫
      (((BigFppfOver.toScheme B S hS).map a ∣_ (e.schemeMap ⁻¹ᵁ O)) ≫ (e.schemeMap ∣_ O)) =
    ((BigFppfOver.toScheme B S hS).map (a ≫ e.g) ∣_ O)
  refine (cancel_mono (Scheme.Opens.ι O)).1 ?_
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
  refine (Scheme.homOfLE_ι_assoc _ _ _).trans (Eq.trans ?_
    (morphismRestrict_ι ((BigFppfOver.toScheme B S hS).map (a ≫ e.g)) O).symm)
  exact congrArg (_ ≫ ·) ((BigFppfOver.toScheme B S hS).map_comp a e.g).symm

omit E in
/-- The chart component at an index depends only on the morphism of the index. -/
theorem inverseImageHomChartRingHom_congr_hom {Z : AlgebraicSpaces B S hS} {k : X ⟶ Z}
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (φ : (smallEtaleRingedToposHom B S hS k).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Z).O ⟶ A) (W : SmallEtale B S hS Z.1)
    {T : SmallEtale B S hS X.1}
    (L L' : (comparisonFunctor B S hS X).obj T ⟶ chartBaseChange B S hS k W) (h : L = L')
    (x : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op W)) :
    inverseImageHomChartRingHom B S hS k A φ W (StructuredArrow.mk (Y := op T) L.op) x =
      inverseImageHomChartRingHom B S hS k A φ W (StructuredArrow.mk (Y := op T) L'.op) x := by
  subst h
  rfl

/-- **The chart components of the composed algebra structure**, on a composed chart diagram
restricted to a Zariski open `O` of `T`: pull back along `V ⟶ T`, apply the component of the
algebra structure on the diagram over `f`, and restrict to the preimage of `O` (which is the
iterated preimage). -/
theorem chartBaseRingHom_compToBase (O : (chartScheme e.V).Opens) (x : Γ(chartScheme e.V, O)) :
    E.chartBaseRingHom (E.compToBase g) (ChartDiagram.comp B S hS f g a e.g ha e.comm) O x =
      E.A.obj.map ((chartOpens B S hS U).map
          (homOfLE (preimage_chartDiagram_comp_le g e a ha O))).op
        (E.chartBaseRingHom E.toBase ⟨U, e.U, a, ha⟩ (e.schemeMap ⁻¹ᵁ O)
          (e.schemeMap.app O x)) := by
  let d : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨U, e.U, a, ha⟩
  have hpull : chartPullback B S hS g (e.restrictChartOpens O).V
      (indexOfChartDiagram B S hS g (e.restrictChartOpens O)) (O.topIso.inv x) =
      (e.schemeMap ⁻¹ᵁ O).topIso.inv (e.schemeMap.app O x) := by
    refine Eq.trans ?_ (morphismRestrict_appTop_topIso_apply e.schemeMap O x)
    unfold chartPullback
    rw [chartBaseChangeMap_indexOfChartDiagram]
    rfl
  have hn := inverseImageHomChartRingHom_naturality B S hS (f ≫ g) E.A (E.compToBase g)
    (ChartDiagram.comp B S hS f g (d.restrictChartOpens (e.schemeMap ⁻¹ᵁ O)).g
      (e.restrictChartOpens O).g (d.restrictChartOpens (e.schemeMap ⁻¹ᵁ O)).comm
      (e.restrictChartOpens O).comm)
    ((ChartDiagram.comp B S hS f g a e.g ha e.comm).restrictChartOpens O)
    ((chartOpens B S hS U).map (homOfLE (preimage_chartDiagram_comp_le g e a ha O))) (𝟙 _)
    ((Category.assoc _ _ _).symm.trans
      ((restrictChartOpens_chartDiagram_comp_comm g e a ha O).trans
        ((Category.comp_id _).symm.trans
          (congrArg _ ((SmallEtale.toOver B S hS Z.1).map_id _).symm))))
    (O.topIso.inv x)
  refine Eq.trans ?_ (hn.trans (congrArg (E.A.obj.map _) ?_))
  · exact congrArg (inverseImageHomChartRingHom B S hS (f ≫ g) E.A (E.compToBase g) _ _)
      (ConcreteCategory.congr_hom ((smallEtaleRingedTopos B S hS Z).O.obj.map_id _) _).symm
  refine (inverseImageHomChartRingHom_congr_hom E.A (E.compToBase g) _ _ _
    (chartLift_chartDiagram_comp B S hS f g _ _ (d.restrictChartOpens (e.schemeMap ⁻¹ᵁ O)).comm
      (e.restrictChartOpens O).comm) _).trans ?_
  refine (inverseImageHomChartRingHom_compInverseImage B S hS f g E.A E.toBase _
    (indexOfChartDiagram B S hS g (e.restrictChartOpens O))
    (indexOfChartDiagram B S hS f (d.restrictChartOpens (e.schemeMap ⁻¹ᵁ O)))
    (O.topIso.inv x)).trans ?_
  rw [hpull]
  rfl

/-- **`W' ⟶ V ⟶ T` is the morphism given by the composed algebra structure.** For a chart diagram
`a : W ⟶ V` over `f` and a chart diagram `V ⟶ T` over `g`, the morphism from the chart
thickening `W'` to `V` given by the `f⁻¹𝒪_Y`-algebra structure, followed by `V ⟶ T`, is the
morphism `W' ⟶ T` given by the `(f ≫ g)⁻¹𝒪_Z`-algebra structure `E.compToBase g`. -/
theorem chartRealizedSchemeToBase_comp_schemeMap :
    E.chartRealizedSchemeToBase E.toBase E.toBase_π ⟨U, e.U, a, ha⟩ ≫ e.schemeMap =
      E.chartRealizedSchemeToBase (E.compToBase g) (E.compToBase_π g)
        (ChartDiagram.comp B S hS f g a e.g ha e.comm) := by
  refine Scheme.Hom.ext ?_ (fun O ↦ ?_)
  · exact congrArg (·.base) (schemeMap_chartDiagram_comp g e a ha).symm
  ext x
  refine Eq.trans ?_ (E.chartBaseRingHom_compToBase g e a ha O x).symm
  rfl

/-- **The morphisms `W' ⟶ V` are morphisms over `S`.** For a chart diagram `a : W ⟶ V` over
`f`, the morphism from the chart thickening `W'` to `V` given by the algebra structure, followed
by the structure morphism of `V`, is the structure morphism
`E.chartRealizedSchemeToBaseScheme W` of `W'`. -/
theorem chartRealizedSchemeToBase_comp_toBase {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom) :
    E.chartRealizedSchemeToBase E.toBase E.toBase_π ⟨U, V, a, ha⟩ ≫
        (baseSpaceChartDiagram (toBaseAlgebraicSpace Y) V).schemeMap =
      E.chartRealizedSchemeToBaseScheme U := by
  refine (E.chartRealizedSchemeToBase_comp_schemeMap (toBaseAlgebraicSpace Y)
    (baseSpaceChartDiagram (toBaseAlgebraicSpace Y) V) a ha).trans ?_
  exact E.chartRealizedSchemeToBase_congr_g (E.compToBase _) (E.compToBase_π _) _ _ _ _
    (Over.mkIdTerminal.hom_ext _ _)

end AlgebraicGeometry.Space.SquareZeroExtension

end
