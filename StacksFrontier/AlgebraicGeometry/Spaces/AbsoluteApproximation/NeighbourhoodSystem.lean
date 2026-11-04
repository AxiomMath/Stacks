module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStepSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientSchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject

/-!
# The system of étale neighbourhoods of the open part, extended by Stacks 07RN

In the problem step of the proof of Stacks 07SU the étale neighbourhood `W = f⁻¹(U) ⊆ V` of the
open part `U ⊆ X` has been descended to an étale morphism `w_k : W_k ⟶ U_k` from a quasi-compact
scheme at a stage `k` of the system `U_i = V_i/R_i` approximating `U`
(`AlgebraicGeometry.Space.EtaleRelationSystem.exists_schemeStage_of_isEtale`). Setting
`W_i = W_k ×_{U_k} U_i` for `i ≥ k`, the proof observes that `W = lim_{i ≥ k} W_i`, that the
`W_i` are schemes of finite type over `Spec ℤ` with affine transition morphisms, and applies
Stacks 07RN to `W = lim W_i` and the open immersion `W ⊆ V`.

This file proves those properties of the chart system `W_i` and carries out the application of
Stacks 07RN.

## Main results

* `AlgebraicGeometry.Space.isPullback_stageChartMap`: the transition squares of a chart system
  are cartesian.
* `AlgebraicGeometry.Space.EtaleRelationSystem.isAffineHom_stageChartMap`,
  `AlgebraicGeometry.Space.EtaleRelationSystem.compactSpace_stageChart`,
  `AlgebraicGeometry.Space.EtaleRelationSystem.locallyOfFiniteType_stageChart`: the chart system
  of an étale morphism from a quasi-compact scheme into a stage of a system of étale quotients of
  finite type has affine transition morphisms and quasi-compact stages of finite type over
  `Spec ℤ`.
* `AlgebraicGeometry.Space.EtaleRelationSystem.exists_finiteTypeApproximation_nbhd`: Stacks 07RN
  applied to the chart system and an open immersion of its limit into a quasi-compact
  quasi-separated scheme.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {J : Type u} [Category.{u} J] (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hrep : ∀ {i j : J} (g : i ⟶ j), yoneda.relativelyRepresentable (D.map g))
  (i₀ : J) {Y₀ : BigFppfOver B S hS} (q₀ : yoneda.obj Y₀ ⟶ D.obj i₀)

/-- **The transition squares of a chart system are cartesian**: the chart at `j` is the base
change of the chart at `k` along the transition morphism `D_j ⟶ D_k`. -/
theorem isPullback_stageChartMap {j k : Over i₀} (e : j ⟶ k) :
    IsPullback (yoneda.map (stageChartMap D hrep i₀ q₀ e)) (stageChartToStage D hrep i₀ q₀ j)
      (stageChartToStage D hrep i₀ q₀ k) (D.map e.left) := by
  refine IsPullback.of_right ?_ (stageChartMap_toStage D hrep i₀ q₀ e)
    (isPullback_stageChartToStage D hrep i₀ q₀ k).flip
  rw [← yoneda.map_comp, stageChartMap_toBase, ← D.map_comp, Over.w e]
  exact (isPullback_stageChartToStage D hrep i₀ q₀ j).flip

end Chart

namespace EtaleRelationSystem

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {J : Type u} [Category.{u} J] [IsCofiltered J] (E : EtaleRelationSystem B S hS J)
  (hobj : ∀ {i j : J} (g : i ⟶ j),
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
  (i₀ : J) {Y₀ : BigFppfOver B S hS} (q₀ : yoneda.obj Y₀ ⟶ E.quotient.obj i₀)

/-- The transition maps of a system of étale quotients with affine objects are affine. -/
private theorem presheaf_isAffineHom_quotient_map {J : Type u} [Category.{u} J]
    (E : EtaleRelationSystem B S hS J)
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    {i j : J} (g : i ⟶ j) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (E.quotient.map g) := by
  have h := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (E.quotient.map g)
    (E.isAlgebraicSpace_quotient_obj _) (E.isAlgebraicSpace_quotient_obj _)).out 2 1).mp
      (E.isAffineHom_quotient_map hobj g)
  exact h.2

omit [IsCofiltered J] in
include hobj in
/-- The transition morphisms of the chart system of a morphism into a stage of a system of étale
quotients are affine. -/
theorem isAffineHom_stageChartMap {j k : Over i₀} (e : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
      (stageChartMap E.quotient (E.relativelyRepresentable_quotient_map hobj) i₀ q₀ e)) :=
  (presheaf_isAffineHom_quotient_map E hobj e.left).property _ _ _
    (isPullback_stageChartMap E.quotient _ i₀ q₀ e).flip

omit [IsCofiltered J] in
include hobj in
/-- The projections of the chart system to its base object are affine. -/
theorem isAffineHom_stageChartToBase (j : Over i₀) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
      (stageChartToBase E.quotient (E.relativelyRepresentable_quotient_map hobj) i₀ q₀ j)) :=
  (presheaf_isAffineHom_quotient_map E hobj j.hom).property _ _ _
    (isPullback_stageChartToStage E.quotient _ i₀ q₀ j)

omit [IsCofiltered J] in
include hobj in
/-- The stages of the chart system of a morphism from a quasi-compact object are quasi-compact. -/
theorem compactSpace_stageChart [CompactSpace ((BigFppfOver.toScheme B S hS).obj Y₀)]
    (j : Over i₀) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (quotientStageChart E.quotient (E.relativelyRepresentable_quotient_map hobj) i₀ q₀ j)) := by
  have := E.isAffineHom_stageChartToBase hobj i₀ q₀ j
  exact QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map
    (stageChartToBase E.quotient (E.relativelyRepresentable_quotient_map hobj) i₀ q₀ j))

omit [IsCofiltered J] in
/-- The projections of the chart system of an étale morphism to the stages are étale. -/
theorem presheaf_etale_stageChartToStage
    (hq₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q₀)
    (hrep : ∀ {i j : J} (g : i ⟶ j), yoneda.relativelyRepresentable (E.quotient.map g))
    (j : Over i₀) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (stageChartToStage E.quotient hrep i₀ q₀ j) := by
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback (isPullback_stageChartToStage E.quotient hrep i₀ q₀ j).flip
    hq₀

omit [IsCofiltered J] in
/-- The stages of the chart system of an étale morphism into a stage of a system of étale
quotients of finite type are of finite type over `Spec ℤ`. -/
theorem locallyOfFiniteType_stageChart
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B S hS).obj (E.obj.obj j))))
    (hq₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q₀)
    (hrep : ∀ {i j : J} (g : i ⟶ j), yoneda.relativelyRepresentable (E.quotient.map g))
    (j : Over i₀) :
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B S hS).obj
      (quotientStageChart E.quotient hrep i₀ q₀ j))) :=
  E.locallyOfFiniteType_of_presheaf_etale j.left (hlft j.left) _
    (E.presheaf_etale_stageChartToStage i₀ q₀ hq₀ hrep j)

include hobj in
/-- **A system cartesian over a system of étale quotients has its limit computed in schemes.**
Let `D` be an inverse system of objects of the site with a morphism `d : D ⟶ V/R` to the system of
quotients of `E` whose naturality squares are cartesian, and whose stage `D_{i₀}` is
quasi-compact and quasi-separated. Then a cone over `D` whose apex is the base change
`D_{i₀} ×_{V_{i₀}/R_{i₀}} lim_j V_j/R_j` is a limit in schemes. -/
theorem isLimit_of_isPullback_quotient
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (D : J ⥤ BigFppfOver B S hS) (d : D ⋙ yoneda ⟶ E.quotient)
    (hd : ∀ ⦃i j : J⦄ (u : i ⟶ j),
      IsPullback (yoneda.map (D.map u)) (d.app i) (d.app j) (E.quotient.map u))
    (i₀ : J) [CompactSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i₀))]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (D.obj i₀))]
    (c : Cone D) (p : yoneda.obj c.pt ⟶ limit E.quotient)
    (hp : ∀ j, yoneda.map (c.π.app j) ≫ d.app j = p ≫ limit.π E.quotient j)
    (hL : IsPullback p (yoneda.map (c.π.app i₀)) (limit.π E.quotient i₀) (d.app i₀)) :
    Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) := by
  obtain ⟨h⟩ := E.chartLimitsInSchemes hobj cV hV i₀ (D.obj i₀) (d.app i₀) (Over.post D)
    (fun j => d.app j.left) (fun {j k} e => d.naturality e.left) (fun j => (hd j.hom).flip)
    (c.overPost i₀) p hL (fun j => hp j.left)
  exact ⟨(Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) _) h⟩

end EtaleRelationSystem

/-! ### Index conversions and objects over `Spec ℤ` -/

/-- The opposite of a preorder, as its order dual. -/
@[simps]
def opToDual (P : Type u) [Preorder P] : Pᵒᵖ ⥤ Pᵒᵈ where
  obj j := OrderDual.toDual j.unop
  map f := homOfLE (leOfHom f.unop)

section OverIntegers

variable (B) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A system of schemes lying in the site, as a system of objects of the site over `Spec ℤ`. -/
@[simps!]
noncomputable def overIntegersLift {K : Type*} [Category K] (D : K ⥤ Scheme.{u})
    (hD : ∀ j, B.Contains (D.obj j)) : K ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  Functor.toOver (ObjectProperty.lift _ D hD) (B.obj hZ)
    (fun _j ↦ ObjectProperty.homMk (terminal.from _))
    (fun {_j _k} _u ↦ ObjectProperty.hom_ext _ (terminal.hom_ext _ _))

/-- The underlying scheme of an object of `overIntegersLift B hZ D hD` is the corresponding object
of `D`. -/
lemma toScheme_obj_overIntegersLift {K : Type*} [Category K] (D : K ⥤ Scheme.{u})
    (hD : ∀ j, B.Contains (D.obj j)) (j : K) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (overIntegersLift B hZ D hD |>.obj j) =
      D.obj j := rfl

/-- The underlying morphism of schemes of a transition map of `overIntegersLift B hZ D hD` is the
corresponding transition map of `D`. -/
lemma toScheme_map_overIntegersLift {K : Type*} [Category K] (D : K ⥤ Scheme.{u})
    (hD : ∀ j, B.Contains (D.obj j)) {j k : K} (u : j ⟶ k) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (overIntegersLift B hZ D hD |>.map u) =
      D.map u := rfl

variable {B hZ} in
/-- A morphism of schemes between objects of the site over `Spec ℤ` is a morphism of the site. -/
noncomputable def overIntegersHom {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj X ⟶
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y) : X ⟶ Y :=
  Over.homMk (ObjectProperty.homMk φ) (ObjectProperty.hom_ext _ (terminal.hom_ext _ _))

variable {B hZ} in
/-- The underlying morphism of schemes of `overIntegersHom φ` is `φ`. -/
@[simp]
lemma toScheme_map_overIntegersHom {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj X ⟶
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Y) :
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (overIntegersHom φ) = φ := rfl

include hZ in
/-- A scheme quasi-compact and locally of finite type over `Spec ℤ` lies in the site. -/
lemma contains_of_locallyOfFiniteType_terminal (X : Scheme.{u})
    [LocallyOfFiniteType (terminal.from X)] [QuasiCompact (terminal.from X)] : B.Contains X :=
  contains_of_locallyOfFiniteType_of_quasiCompact B (⊤_ Scheme.{u}) hZ
    (Y₀ := Over.mk (𝟙 (B.obj hZ))) (terminal.from X)

end OverIntegers

/-! ### The chart system of the descended neighbourhood, and Stacks 07RN -/

namespace EtaleRelationSystem

section Approximation

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (E : EtaleRelationSystem B (⊤_ Scheme.{u}) hZ Iᵒᵖ)
  (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E.obj.map g)))
  (k : I) {Wk : BigFppfOver B (⊤_ Scheme.{u}) hZ} (wk : yoneda.obj Wk ⟶ E.quotient.obj (op k))

/-- **The chart system `W_i = W_k ×_{U_k} U_i` of `w_k : W_k ⟶ U_k`**, indexed by the tail of
`k`, as an inverse system of schemes. -/
noncomputable abbrev nbhdTailDiagram : (Tail k)ᵒᵈ ⥤ Scheme.{u} :=
  tailToOver k ⋙ stageChartOverDiagram E.quotient (E.relativelyRepresentable_quotient_map hobj)
    (op k) wk ⋙ Over.forget Wk ⋙ BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition maps of the chart system `nbhdTailDiagram` are affine. -/
lemma isAffineHom_nbhdTailDiagram_map {i j : (Tail k)ᵒᵈ} (v : i ⟶ j) :
    _root_.AlgebraicGeometry.IsAffineHom ((E.nbhdTailDiagram hZ hobj k wk).map v) :=
  E.isAffineHom_stageChartMap hobj (op k) wk ((tailToOver k).map v)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- If every scheme of the system `E` is locally of finite type over `Spec ℤ` and `w_k` is étale,
then every scheme of the chart system `nbhdTailDiagram` is locally of finite type over `Spec ℤ`. -/
lemma locallyOfFiniteType_nbhdTailDiagram_obj
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    (hwk : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf wk) (i : (Tail k)ᵒᵈ) :
    LocallyOfFiniteType (terminal.from ((E.nbhdTailDiagram hZ hobj k wk).obj i)) :=
  E.locallyOfFiniteType_stageChart (op k) wk hlft hwk
    (E.relativelyRepresentable_quotient_map hobj) _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- If `W_k` is quasi-compact, then every scheme of the chart system `nbhdTailDiagram` is
quasi-compact over `Spec ℤ`. -/
lemma quasiCompact_nbhdTailDiagram_obj
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)] (i : (Tail k)ᵒᵈ) :
    QuasiCompact (terminal.from ((E.nbhdTailDiagram hZ hobj k wk).obj i)) := by
  have : CompactSpace ((E.nbhdTailDiagram hZ hobj k wk).obj i) :=
    E.compactSpace_stageChart hobj (op k) wk ((tailToOver k).obj i)
  exact quasiCompact_of_compactSpace _

variable {Ws : BigFppfOver B (⊤_ Scheme.{u}) hZ} (w : yoneda.obj Ws ⟶ limit E.quotient)
  (g : Ws ⟶ Wk) (hL : IsPullback w (yoneda.map g) (limit.π E.quotient (op k)) wk)

/-- The cone from the base change `U ×_{U_k} W_k` to the chart system of `w_k`. -/
noncomputable abbrev nbhdTailCone : Cone (E.nbhdTailDiagram hZ hobj k wk) :=
  ((Over.forget Wk ⋙ BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
    (stageChartOverCone E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk w g
      hL)).whisker (tailToOver k)

/-- The legs of `AlgebraicGeometry.Space.EtaleRelationSystem.nbhdTailCone`, when the base
change `U ×_{U_k} W_k` is the object of the site given by an open `W` of a scheme. -/
noncomputable def nbhdTailπ {Vs : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (Wo : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs).Opens)
    (w : yoneda.obj (openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo) ⟶ limit E.quotient)
    (g : openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo ⟶ Wk)
    (hL : IsPullback w (yoneda.map g) (limit.π E.quotient (op k)) wk) :
    (Functor.const (Tail k)ᵒᵈ).obj (Wo : Scheme.{u}) ⟶ E.nbhdTailDiagram hZ hobj k wk :=
  (E.nbhdTailCone hZ hobj k wk w g hL).π

/-- **`W = lim_{i ≥ k} W_i` in schemes.** -/
theorem isLimit_nbhdTailCone
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    (hwk : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf wk)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)]
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV)) :
    Nonempty (IsLimit (E.nbhdTailCone hZ hobj k wk w g hL)) := by
  have := E.locallyOfFiniteType_of_presheaf_etale (op k) (hlft _) wk hwk
  have := quasiSeparatedSpace_of_locallyOfFiniteType_terminal
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)
  obtain ⟨h⟩ := E.isLimit_stageChartCone hobj cV hV (op k) wk w g hL
  exact ⟨(Functor.Initial.isLimitWhiskerEquiv (tailToOver k) _).symm h⟩

/-- **Stacks 07RN applied to `W = lim_{i ≥ k} W_i` and the open immersion `W ⊆ V`**, with a
cofinal reindexing. Here `V` is a quasi-compact quasi-separated object of the site and `W` the
object of the site given by a quasi-compact open of `V`. -/
theorem exists_finiteTypeApproximation_nbhd
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    (hwk : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf wk)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)]
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV))
    (Vs : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs)]
    (Wo : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs).Opens) [CompactSpace Wo]
    (w : yoneda.obj (openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo) ⟶ limit E.quotient)
    (g : openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo ⟶ Wk)
    (hL : IsPullback w (yoneda.map g) (limit.π E.quotient (op k)) wk) :
    ∃ Q : Scheme.FiniteTypeApproximation (E.nbhdTailDiagram hZ hobj k wk)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs) Wo
      (E.nbhdTailπ hZ hobj k wk Wo w g hL), Scheme.FiniteTypeApproximation.IsCofinal Q := by
  have : ∀ {i j : (Tail k)ᵒᵈ} (v : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((E.nbhdTailDiagram hZ hobj k wk).map v) :=
    fun v => E.isAffineHom_nbhdTailDiagram_map hZ hobj k wk v
  have : ∀ i, LocallyOfFiniteType (terminal.from ((E.nbhdTailDiagram hZ hobj k wk).obj i)) :=
    E.locallyOfFiniteType_nbhdTailDiagram_obj hZ hobj k wk hlft hwk
  have : ∀ i, QuasiCompact (terminal.from ((E.nbhdTailDiagram hZ hobj k wk).obj i)) :=
    E.quasiCompact_nbhdTailDiagram_obj hZ hobj k wk
  obtain ⟨h⟩ := E.isLimit_nbhdTailCone hZ hobj k wk w g hL hlft hwk cV hV
  exact Scheme.FiniteTypeApproximation.exists_isCofinal_of_isLimit _ _ Wo _ h

end Approximation

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
