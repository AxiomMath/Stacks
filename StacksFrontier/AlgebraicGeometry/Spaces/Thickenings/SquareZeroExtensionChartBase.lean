module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RingSheafChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPulledBackSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickeningMap

/-!
# Chart thickenings of a square-zero extension map to the charts of the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension
`0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of the small étale structure sheaf of `X` by a quasi-coherent ideal, as an
algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT). For a commuting square of étale scheme charts
`g : W ⟶ V` over `f` (a chart diagram), the `f⁻¹𝒪_Y`-algebra structure of `𝒜` gives, on every
Zariski open `O` of `V`, a ring homomorphism `Γ(V, O) ⟶ 𝒜(W|_{g⁻¹O})` lifting `g♯`. These form a
map `𝒪_V ⟶ g_*(𝒜|_{W_Zar})`, and therefore a morphism `W' ⟶ V` from the chart thickening of `W`
extending `g`.

This is the step of the proof of Stacks 05ZT which maps the chart thickenings to the base.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.restrictChartOpens`: a chart diagram restricted to a
  Zariski open of its chart of `Y` and the preimage.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartBaseMap`: the map
  `𝒪_V ⟶ g_*(𝒜|_{W_Zar})`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeToBase`: the morphism `W' ⟶ V`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.π_inverseImageHomChartRingHom_toBase`: the chart
  components of the algebra structure lift pullback of functions.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartInclusion_comp_chartRealizedSchemeToBase`: the
  morphism `W' ⟶ V` extends `g`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- A chart diagram `g : W ⟶ V` restricted to a Zariski open `O` of `V` and its preimage
`g⁻¹O` in `W`. -/
noncomputable def ChartDiagram.restrictChartOpens (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (O : (chartScheme d.V).Opens) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (chartOpens B S hS d.U).obj (d.schemeMap ⁻¹ᵁ O)
  V := (chartOpens B S hS d.V).obj O
  g := chartOpenOverRestrict B S hS d.U d.V d.g O
  comm := by
    change (yoneda.map (chartOpenOverι B S hS d.U _) ≫ d.U.obj.hom) ≫ f.hom =
      yoneda.map (chartOpenOverRestrict B S hS d.U d.V d.g O) ≫
        yoneda.map (chartOpenOverι B S hS d.V O) ≫ d.V.obj.hom
    rw [Category.assoc, d.comm, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, chartOpenOverRestrict_comp_ι]

/-- The scheme morphism of the chart diagram restricted to `O` is the restriction `g ∣_ O`. -/
theorem ChartDiagram.restrictChartOpens_schemeMap (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (O : (chartScheme d.V).Opens) :
    (d.restrictChartOpens O).schemeMap = d.schemeMap ∣_ O :=
  rfl

/-- The restricted chart diagrams are compatible with shrinking the open. -/
theorem ChartDiagram.restrictChartOpens_comm (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {O O' : (chartScheme d.V).Opens} (i : O' ⟶ O) :
    (SmallEtale.toOver B S hS X.1).map ((chartOpens B S hS d.U).map
        ((Opens.map d.schemeMap.base).map i)) ≫ (d.restrictChartOpens O).g =
      (d.restrictChartOpens O').g ≫
        (SmallEtale.toOver B S hS Y.1).map ((chartOpens B S hS d.V).map i) := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show (chartScheme d.U).homOfLE ((Opens.map d.schemeMap.base).map i).le ≫
      (d.schemeMap ∣_ O) = (d.schemeMap ∣_ O') ≫ (chartScheme d.V).homOfLE i.le
  rw [← cancel_mono (Scheme.Opens.ι O), Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

section Naturality

variable (d d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
  (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
    d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)

include h in
/-- For a morphism `(i, j) : d' ⟶ d` of chart diagrams, the underlying square of scheme
morphisms commutes. -/
theorem chartSchemeMap_comp_schemeMap :
    chartSchemeMap i ≫ d.schemeMap = d'.schemeMap ≫ chartSchemeMap j :=
  ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B S hS).map h).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _))

include h in
/-- For a morphism `(i, j) : d' ⟶ d` of chart diagrams and a Zariski open `O` of the chart of
`d`, the preimage of `O` in the source chart of `d'` along `d'` and `j` is contained in its
preimage along `i` and `d`. -/
theorem preimage_le_preimage_of_comm (O : (chartScheme d.V).Opens) :
    d'.schemeMap ⁻¹ᵁ (chartSchemeMap j ⁻¹ᵁ O) ≤ chartSchemeMap i ⁻¹ᵁ (d.schemeMap ⁻¹ᵁ O) := by
  have e := chartSchemeMap_comp_schemeMap d d' i j h
  intro x hx
  show (chartSchemeMap i ≫ d.schemeMap) x ∈ O
  rw [e]
  exact hx

/-- The morphism of restricted chart diagrams over a morphism of chart diagrams. -/
theorem restrictChartOpens_comm_of_comm (O : (chartScheme d.V).Opens) :
    (SmallEtale.toOver B S hS X.1).map ((chartOpens B S hS d'.U).map
        (homOfLE (preimage_le_preimage_of_comm d d' i j h O)) ≫
          chartOpensRestrict B S hS i (d.schemeMap ⁻¹ᵁ O)) ≫ (d.restrictChartOpens O).g =
      (d'.restrictChartOpens (chartSchemeMap j ⁻¹ᵁ O)).g ≫
        (SmallEtale.toOver B S hS Y.1).map (chartOpensRestrict B S hS j O) := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show ((chartScheme d'.U).homOfLE (preimage_le_preimage_of_comm d d' i j h O) ≫
      (chartSchemeMap i ∣_ (d.schemeMap ⁻¹ᵁ O))) ≫ (d.schemeMap ∣_ O) =
    (d'.schemeMap ∣_ (chartSchemeMap j ⁻¹ᵁ O)) ≫ (chartSchemeMap j ∣_ O)
  rw [← cancel_mono (Scheme.Opens.ι O)]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.homOfLE_ι_assoc]
  rw [chartSchemeMap_comp_schemeMap d d' i j h]

end Naturality

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable {Z : AlgebraicSpaces B S hS} {k : X ⟶ Z}
  (φ : (smallEtaleRingedToposHom B S hS k).toToposHom.inverseImageRing.obj
    (smallEtaleRingedTopos B S hS Z).O ⟶ E.A)
  (hφ : φ ≫ E.π = (smallEtaleRingedToposHom B S hS k).fSharpInverseImage)

include hφ in
/-- **The chart components of the algebra structure lift pullback of functions**: the
`f⁻¹𝒪_Y`-algebra structure of `𝒜` (or any map `φ : k⁻¹𝒪_Z ⟶ 𝒜` lifting the structure map of
some `k : X ⟶ Z`), read on a chart diagram, followed by `𝒜 ⟶ 𝒪_X`, is pullback
of functions along the scheme morphism of the diagram. -/
theorem π_inverseImageHomChartRingHom_toBase (d : ChartDiagram B S hS X.1 Z.1 k.hom)
    (x : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op d.V)) :
    E.π.hom.app (op d.U) (inverseImageHomChartRingHom B S hS k E.A φ d.V
        (indexOfChartDiagram B S hS k d) x) =
      d.schemeMap.appTop x := by
  refine ((inverseImageHomChartRingHom_comp B S hS k E.A φ E.π d.V
    (indexOfChartDiagram B S hS k d) x).symm.trans ?_)
  refine (congrArg (fun ψ ↦ inverseImageHomChartRingHom B S hS k _ ψ d.V
    (indexOfChartDiagram B S hS k d) x) hφ).trans ?_
  refine (inverseImageHomChartRingHom_fSharpInverseImage B S hS k d.V
    (indexOfChartDiagram B S hS k d) x).trans ?_
  unfold chartPullback
  rw [chartBaseChangeMap_indexOfChartDiagram]
  rfl

/-- The ring homomorphism `Γ(V, O) ⟶ 𝒜(W|_{g⁻¹O})` given by the algebra structure on a chart
diagram `g : W ⟶ V` and a Zariski open `O` of `V`. -/
noncomputable def chartBaseRingHom (d : ChartDiagram B S hS X.1 Z.1 k.hom)
    (O : (chartScheme d.V).Opens) :
    Γ(chartScheme d.V, O) →+* (E.chartSheaf d.U).presheaf.obj (op (d.schemeMap ⁻¹ᵁ O)) :=
  (inverseImageHomChartRingHom B S hS k E.A φ (d.restrictChartOpens O).V
    (indexOfChartDiagram B S hS k (d.restrictChartOpens O))).comp O.topIso.inv.hom

include hφ in
/-- The ring homomorphism `Γ(V, O) ⟶ 𝒜(W|_{g⁻¹O})` followed by `𝒜 ⟶ 𝒪_X` is `g♯` on `O`. -/
theorem chartπ_chartBaseRingHom (d : ChartDiagram B S hS X.1 Z.1 k.hom)
    (O : (chartScheme d.V).Opens) (a : Γ(chartScheme d.V, O)) :
    (E.chartπ d.U).hom.app (op (d.schemeMap ⁻¹ᵁ O)) (E.chartBaseRingHom φ d O a) =
      d.schemeMap.app O a := by
  rw [chartπ_apply']
  refine (congrArg (chartΓEquiv d.U (op (d.schemeMap ⁻¹ᵁ O)))
    (E.π_inverseImageHomChartRingHom_toBase φ hφ (d.restrictChartOpens O) _)).trans ?_
  show (d.schemeMap ⁻¹ᵁ O).topIso.hom ((d.schemeMap ∣_ O).appTop (O.topIso.inv a)) = _
  rw [morphismRestrict_appTop_topIso_apply]
  exact ConcreteCategory.congr_hom (d.schemeMap ⁻¹ᵁ O).topIso.inv_hom_id _

/-- The naturality of the chart components of `φ`, for sections related by the restriction along
`j`. -/
private theorem inverseImageHomChartRingHom_naturality_of_eq
    (d d' : ChartDiagram B S hS X.1 Z.1 k.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Z.1).map j)
    (x : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op d.V))
    (y : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op d'.V))
    (hy : y = (smallEtaleRingedTopos B S hS Z).O.obj.map j.op x) :
    inverseImageHomChartRingHom B S hS k E.A φ d'.V (indexOfChartDiagram B S hS k d') y =
      E.A.obj.map i.op (inverseImageHomChartRingHom B S hS k E.A φ d.V
        (indexOfChartDiagram B S hS k d) x) :=
  hy ▸ inverseImageHomChartRingHom_naturality B S hS k E.A φ d d' i j h x

/-- The ring homomorphisms `Γ(V, O) ⟶ 𝒜(W|_{g⁻¹O})` are compatible with shrinking `O`. -/
theorem chartBaseRingHom_naturality (d : ChartDiagram B S hS X.1 Z.1 k.hom)
    {O O' : (chartScheme d.V).Opens} (i : O' ⟶ O) (a : Γ(chartScheme d.V, O)) :
    E.chartBaseRingHom φ d O' ((chartScheme d.V).presheaf.map i.op a) =
      (E.chartSheaf d.U).presheaf.map ((Opens.map d.schemeMap.base).map i).op
        (E.chartBaseRingHom φ d O a) := by
  have hΓ : O'.topIso.inv ((chartScheme d.V).presheaf.map i.op a) =
      (smallEtaleRingedTopos B S hS Z).O.obj.map ((chartOpens B S hS d.V).map i).op
        (O.topIso.inv a) :=
    ConcreteCategory.congr_hom ((Scheme.restrictFunctorΓ (X := chartScheme d.V)).inv.naturality
      i.op) a
  exact inverseImageHomChartRingHom_naturality_of_eq E φ (d.restrictChartOpens O)
    (d.restrictChartOpens O') ((chartOpens B S hS d.U).map ((Opens.map d.schemeMap.base).map i))
    ((chartOpens B S hS d.V).map i) (d.restrictChartOpens_comm i) _ _ hΓ

/-- **The map `𝒪_V ⟶ g_*(𝒜|_{W_Zar})`** given by the algebra structure of the extension on a
chart diagram `g : W ⟶ V`. -/
noncomputable def chartBaseMap (d : ChartDiagram B S hS X.1 Z.1 k.hom) :
    (chartScheme d.V).presheaf ⟶ d.schemeMap.base _* (E.chartSheaf d.U).presheaf where
  app O := CommRingCat.ofHom (E.chartBaseRingHom φ d O.unop)
  naturality O O' i := by
    ext a
    exact E.chartBaseRingHom_naturality φ d i.unop a

/-- The component of `chartBaseMap` at a Zariski open `O` is `chartBaseRingHom` at `O`. -/
theorem chartBaseMap_app (d : ChartDiagram B S hS X.1 Z.1 k.hom) (O : (chartScheme d.V).Opens)
    (a : Γ(chartScheme d.V, O)) :
    (E.chartBaseMap φ d).app (op O) a = E.chartBaseRingHom φ d O a :=
  rfl

include hφ in
/-- **The morphism `W' ⟶ V` from the chart thickening of `W` to the chart of `Y`** of a chart
diagram `g : W ⟶ V`: the morphism `g` on spaces and the algebra structure of the extension on
sections. -/
noncomputable def chartRealizedSchemeToBase (d : ChartDiagram B S hS X.1 Z.1 k.hom) :
    E.chartRealizedScheme d.U ⟶ chartScheme d.V :=
  Scheme.realizedMapTo (E.chartExtension d.U) d.schemeMap (E.chartBaseMap φ d)
    (fun O a ↦ E.chartπ_chartBaseRingHom φ hφ d O a)

/-- The morphism `W' ⟶ V` is `g` on underlying topological spaces. -/
theorem chartRealizedSchemeToBase_base (d : ChartDiagram B S hS X.1 Z.1 k.hom) :
    (E.chartRealizedSchemeToBase φ hφ d).base = d.schemeMap.base :=
  rfl

/-- The morphism `W' ⟶ V` extends `g : W ⟶ V`. -/
theorem chartInclusion_comp_chartRealizedSchemeToBase (d : ChartDiagram B S hS X.1 Z.1 k.hom) :
    E.chartInclusion d.U ≫ E.chartRealizedSchemeToBase φ hφ d = d.schemeMap :=
  Scheme.realizedInclusion_comp_realizedMapTo _ _ _ _

/-- **The morphisms `W' ⟶ V` are compatible with morphisms of chart diagrams**: for a morphism
`(i, j) : d' ⟶ d` of chart diagrams the square of `W'_{d'} ⟶ W'_d`, the two morphisms to the
charts of `Y` and `j` commutes. -/
theorem chartRealizedSchemeMap_comp_chartRealizedSchemeToBase
    (d d' : ChartDiagram B S hS X.1 Z.1 k.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Z.1).map j) :
    E.chartRealizedSchemeMap i ≫ E.chartRealizedSchemeToBase φ hφ d =
      E.chartRealizedSchemeToBase φ hφ d' ≫ chartSchemeMap j := by
  refine Scheme.Hom.ext ?_ (fun O ↦ ?_)
  · show (chartSchemeMap i ≫ d.schemeMap).base = (d'.schemeMap ≫ chartSchemeMap j).base
    exact congrArg (fun q ↦ q.base) (chartSchemeMap_comp_schemeMap d d' i j h)
  ext a
  have hΓ : (chartSchemeMap j ⁻¹ᵁ O).topIso.inv ((chartSchemeMap j).app O a) =
      (smallEtaleRingedTopos B S hS Z).O.obj.map (chartOpensRestrict B S hS j O).op
        (O.topIso.inv a) :=
    (morphismRestrict_appTop_topIso_apply (chartSchemeMap j) O a).symm
  refine Eq.trans ?_ (inverseImageHomChartRingHom_naturality_of_eq E φ (d.restrictChartOpens O)
    (d'.restrictChartOpens (chartSchemeMap j ⁻¹ᵁ O))
    ((chartOpens B S hS d'.U).map (homOfLE (preimage_le_preimage_of_comm d d' i j h O)) ≫
      chartOpensRestrict B S hS i (d.schemeMap ⁻¹ᵁ O)) (chartOpensRestrict B S hS j O)
    (restrictChartOpens_comm_of_comm d d' i j h O) _ _ hΓ).symm
  show E.A.val.map _ (E.A.val.map (chartOpensRestrict B S hS i (d.schemeMap ⁻¹ᵁ O)).op
    (E.chartBaseRingHom φ d O a)) = _
  exact (ConcreteCategory.congr_hom (E.A.val.map_comp (chartOpensRestrict B S hS i _).op
    ((chartOpens B S hS d'.U).map (homOfLE (preimage_le_preimage_of_comm d d' i j h O))).op)
    _).symm

end AlgebraicGeometry.Space.SquareZeroExtension

end
