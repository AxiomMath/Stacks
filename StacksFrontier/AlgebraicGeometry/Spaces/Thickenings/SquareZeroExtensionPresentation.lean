module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationNormalisation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartToBase

/-!
# The thickened presentation of a square-zero extension

A charted presentation of a morphism of algebraic spaces `f : X ⟶ Y` consists of étale
presentations of `X` and `Y` together with a morphism between their presenting schemes lying over
`f`. Given a square-zero extension of `X` along `f`, the presenting chart and the relation chart
of the presentation of `X` thicken, and the thickened charts acquire structure morphisms to `S`
compatible with the two legs of the relation.

## Main definitions

* `AlgebraicGeometry.Space.ChartedPresentation`: étale presentations of the source and target of
  a morphism, with a morphism of presenting schemes over it.
* `AlgebraicGeometry.Space.ChartedPresentation.β`: the induced morphism of relation schemes.
* `AlgebraicGeometry.Space.SquareZeroExtension.presentationThickeningToBase`: the structure
  morphism to `S` of the thickened presenting chart.
* `AlgebraicGeometry.Space.SquareZeroExtension.relationThickeningToBase`: the structure morphism
  to `S` of the thickened relation chart.

## Main results

* `AlgebraicGeometry.Space.nonempty_chartedPresentation`: every morphism of algebraic spaces has a
  charted presentation.
* `AlgebraicGeometry.Space.SquareZeroExtension.target_comp_presentationThickeningToBase`: the two
  legs of the thickened relation have the same composite with the structure morphism to `S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Joint monicity lifts across a thickening of the source of an étale map.** -/
theorem _root_.AlgebraicGeometry.eq_of_isPullback_thickening {U R U' R' T : Scheme.{u}}
    (iU : U ⟶ U') (iR : R ⟶ R') (s t : R ⟶ U) (s' t' : R' ⟶ U') (p : R' ⟶ T)
    (hs : IsPullback iR s s' iU)
    (ht : iR ≫ t' = t ≫ iU) [FormallyUnramified s']
    (hiU : Stacks.Thickenings.IsFirstOrderThickening iU)
    (hst : ∀ ⦃Z : Scheme.{u}⦄ (a b : Z ⟶ R), a ≫ iR ≫ p = b ≫ iR ≫ p → a ≫ s = b ≫ s →
      a ≫ t = b ≫ t → a = b)
    {Z : Scheme.{u}} (a b : Z ⟶ R') (hp : a ≫ p = b ≫ p) (has : a ≫ s' = b ≫ s')
    (hat : a ≫ t' = b ≫ t') : a = b := by
  have := hiU.1
  let z := pullback.fst (a ≫ s') iU
  have hz : Stacks.Thickenings.IsFirstOrderThickening z :=
    Stacks.Thickenings.isFirstOrderThickening_of_isPullback (IsPullback.of_hasPullback _ _) hiU
  have := hz.1
  let a₀ := hs.lift (z ≫ a) (pullback.snd (a ≫ s') iU)
    (by rw [Category.assoc]; exact pullback.condition)
  let b₀ := hs.lift (z ≫ b) (pullback.snd (a ≫ s') iU)
    (by rw [Category.assoc, ← has]; exact pullback.condition)
  have ea : a₀ ≫ iR = z ≫ a := hs.lift_fst _ _ _
  have eb : b₀ ≫ iR = z ≫ b := hs.lift_fst _ _ _
  have h₂ : a₀ ≫ t = b₀ ≫ t := (cancel_mono iU).mp <| by
    rw [Category.assoc, Category.assoc, ← ht, reassoc_of% ea, reassoc_of% eb, hat]
  refine FormallyUnramified.hom_ext z ⟨2, hz.2⟩ s' ?_ has
  rw [← ea, ← eb, hst a₀ b₀ (by rw [reassoc_of% ea, reassoc_of% eb, hp])
    (by rw [hs.lift_snd, hs.lift_snd]) h₂]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A presentation of a morphism of algebraic spaces**: étale presentations of the source and
of the target, together with a morphism of their presenting schemes over the morphism. -/
structure ChartedPresentation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) where
  /-- The presentation of the source. -/
  P : Presentation B S hS X.1 X.2
  /-- The presentation of the target. -/
  Q : Presentation B S hS Y.1 Y.2
  /-- The morphism of presenting schemes. -/
  α : P.U ⟶ Q.U
  /-- It lies over `f`. -/
  comm : P.toSpace ≫ f.hom = yoneda.map α ≫ Q.toSpace

/-- Every morphism of algebraic spaces has a charted presentation: the atlas of the source can be
chosen to map to the atlas of a presentation of the target (Stacks 02X1). -/
theorem nonempty_chartedPresentation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Nonempty (ChartedPresentation B S hS f) := by
  let Q := presentationOfIsAlgebraicSpace B S hS Y.1 Y.2
  obtain ⟨U, p, α, hcomm, hsurj, het⟩ :=
    exists_surjective_etale_chart_lift B S hS X.2 f.hom Q.U Q.toSpace Q.surjective Q.etale
  exact ⟨⟨presentationOfAtlas B S hS X.1 X.2 U p hsurj het, Q, α, hcomm⟩⟩

namespace ChartedPresentation

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (C : ChartedPresentation B S hS f)

/-- The diagram of étale charts formed by the two presenting schemes. -/
def diagram : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := presentationChart C.P
  V := presentationChart C.Q
  g := C.α
  comm := C.comm

/-- The two legs of the relation of the source presentation, followed by `α`, agree in `Y`. -/
theorem toSpace_relation_comm :
    yoneda.map (C.P.target ≫ C.α) ≫ C.Q.toSpace = yoneda.map (C.P.source ≫ C.α) ≫ C.Q.toSpace := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← C.comm,
    ← Category.assoc, ← Category.assoc, C.P.isPullback.w]

/-- The morphism of relation schemes induced by the morphism of presenting schemes. -/
def β : C.P.R ⟶ C.Q.R :=
  yoneda.preimage (C.Q.isPullback.lift (yoneda.map (C.P.target ≫ C.α))
    (yoneda.map (C.P.source ≫ C.α)) C.toSpace_relation_comm)

/-- `β` is compatible with the target legs of the two relations. -/
theorem β_target : C.β ≫ C.Q.target = C.P.target ≫ C.α := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, β, yoneda.map_preimage, C.Q.isPullback.lift_fst]

/-- `β` is compatible with the source legs of the two relations. -/
theorem β_source : C.β ≫ C.Q.source = C.P.source ≫ C.α := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, β, yoneda.map_preimage, C.Q.isPullback.lift_snd]

/-- The diagram of étale charts formed by the two relation schemes. -/
def relationDiagram : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := presentationRelationChart C.P
  V := presentationRelationChart C.Q
  g := C.β
  comm := by
    change (yoneda.map C.P.source ≫ C.P.toSpace) ≫ f.hom =
      yoneda.map C.β ≫ yoneda.map C.Q.source ≫ C.Q.toSpace
    rw [Category.assoc, C.comm, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp, β_source]


end ChartedPresentation

namespace SquareZeroExtension

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)

/-- The structure morphism to `S` of the thickened presenting chart, through the presenting
scheme of the target. -/
def presentationThickeningToBase :
    chartThickening B S hS E (presentationChart C.P) ⟶ S :=
  chartMapGen B S hS E C.diagram ≫ B.inclusion.map C.Q.U.hom

/-- The structure morphism to `S` of the thickened relation chart, through the source leg. -/
def relationThickeningToBase :
    chartThickening B S hS E (presentationRelationChart C.P) ⟶ S :=
  chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫
    presentationThickeningToBase E C

/-- The two legs of the relation of a presentation have the same composite with the structure
morphism of the presenting scheme. -/
theorem chartSchemeMap_relationHom_comp_toBase (Q : Presentation B S hS Y.1 Y.2) :
    chartSchemeMap (presentationRelationTargetHom Q) ≫ B.inclusion.map Q.U.hom =
      chartSchemeMap (presentationRelationSourceHom Q) ≫ B.inclusion.map Q.U.hom := by
  show B.inclusion.map Q.target.left ≫ B.inclusion.map Q.U.hom =
    B.inclusion.map Q.source.left ≫ B.inclusion.map Q.U.hom
  rw [← Functor.map_comp, ← Functor.map_comp, Over.w Q.target, Over.w Q.source]

/-- Thickening a leg of the relation and mapping to the target chart agrees with mapping the
thickened relation chart and then the corresponding leg of the target relation. -/
private theorem chartThickeningMap_comp_chartMapGen_relation
    (p : presentationRelationChart C.P ⟶ presentationChart C.P)
    (q : presentationRelationChart C.Q ⟶ presentationChart C.Q)
    (h : (SmallEtale.toOver B S hS X.1).map p ≫ C.α = C.β ≫ (SmallEtale.toOver B S hS Y.1).map q) :
    chartThickeningMap B S hS E p ≫ chartMapGen B S hS E C.diagram =
      chartMapGen B S hS E C.relationDiagram ≫ chartSchemeMap q :=
  (chartThickeningMap_comp_chartMapGen B S hS E C.diagram p).trans
    ((chartMapGen_mk_congr B S hS E (U := presentationRelationChart C.P)
      (V := presentationChart C.Q) (g' := C.β ≫ (SmallEtale.toOver B S hS Y.1).map q) _
      (ChartDiagram.postcomp' B S hS C.relationDiagram q).comm h).trans
      (chartMapGen_postcomp B S hS E C.relationDiagram q))

/-- **The two legs of the thickened relation have the same composite with the structure
morphism** to `S` of the thickened presenting chart. -/
theorem target_comp_presentationThickeningToBase :
    chartThickeningMap B S hS E (presentationRelationTargetHom C.P) ≫
        presentationThickeningToBase E C = relationThickeningToBase E C := by
  have h1 := chartThickeningMap_comp_chartMapGen_relation E C (presentationRelationTargetHom C.P)
    (presentationRelationTargetHom C.Q) C.β_target.symm
  have h2 := chartThickeningMap_comp_chartMapGen_relation E C (presentationRelationSourceHom C.P)
    (presentationRelationSourceHom C.Q) C.β_source.symm
  rw [relationThickeningToBase, presentationThickeningToBase]
  erw [← Category.assoc, ← Category.assoc, h1, h2, Category.assoc, Category.assoc,
    chartSchemeMap_relationHom_comp_toBase]
  rfl

/-- The structure morphism of the thickened presenting chart extends that of the presenting
scheme. -/
theorem chartImmersion_comp_presentationThickeningToBase :
    chartImmersion B S hS E (presentationChart C.P) ≫ presentationThickeningToBase E C =
      B.inclusion.map C.P.U.hom := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ B.inclusion.map C.Q.U.hom)
    (chartImmersion_comp_chartMapGen B S hS E C.diagram)).trans ?_
  show B.inclusion.map C.α.left ≫ B.inclusion.map C.Q.U.hom = _
  rw [← Functor.map_comp, Over.w C.α]

/-- The structure morphism of the thickened relation chart extends that of the relation
scheme. -/
theorem chartImmersion_comp_relationThickeningToBase :
    chartImmersion B S hS E (presentationRelationChart C.P) ≫ relationThickeningToBase E C =
      B.inclusion.map C.P.R.hom := by
  rw [relationThickeningToBase, ← Category.assoc, chartImmersion_comp_chartThickeningMap,
    Category.assoc, chartImmersion_comp_presentationThickeningToBase]
  show B.inclusion.map C.P.source.left ≫ B.inclusion.map C.P.U.hom = _
  rw [← Functor.map_comp, Over.w C.P.source]

end SquareZeroExtension

end Space

end AlgebraicGeometry

end
