module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.NeighbourhoodSystem

/-!
# The glued relations of the problem step of Stacks 07SU

In the problem step of the proof of Stacks 07SU, Stacks 07RN has extended the system
`W_i = W_k ×_{U_k} U_i` of étale neighbourhoods of the open part to a system `V_j ⊇ W_j` of
schemes of finite type over `Spec ℤ` with limit `V`, indexed by a directed set `J` mapping
cofinally to the tail of `k`
(`AlgebraicGeometry.Space.EtaleRelationSystem.exists_finiteTypeApproximation_nbhd`).
This file assembles from it the data of the glued relations
`R_j = V_j ∪_{W_j} (W_j ×_{U_j} W_j)`
(`AlgebraicGeometry.Space.GluedNeighbourhoodRelationData`), and
computes the limits of the systems `V_j`, `W_j` and `W_j ×_{U_j} W_j` in schemes.

## Main definitions

* `AlgebraicGeometry.Space.EtaleRelationSystem.problemStepData`: the data of the glued relations.

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.isLimit_problemStepAmbientCone`: `V = lim V_j`.
* `AlgebraicGeometry.Space.EtaleRelationSystem.isLimit_problemStepNbhdCone`: `W = lim W_j`.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.isLimit_kernelPairCone`:
  `W ×_U W = lim W_j ×_{U_j} W_j`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

/-- The functor `Pᵒᵖ ⥤ Pᵒᵈ` of a preorder `P` is full. -/
instance (P : Type u) [Preorder P] : (opToDual P).Full where
  map_surjective f := ⟨(homOfLE (leOfHom f)).op, rfl⟩

/-- The functor `Pᵒᵖ ⥤ Pᵒᵈ` of a preorder `P` is faithful. -/
instance (P : Type u) [Preorder P] : (opToDual P).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The functor `Pᵒᵖ ⥤ Pᵒᵈ` of a nonempty directed preorder `P` is initial. -/
instance (P : Type u) [Preorder P] [IsDirected P (· ≤ ·)] [Nonempty P] : (opToDual P).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun d =>
    ⟨op (OrderDual.ofDual d), ⟨𝟙 _⟩⟩

namespace EtaleRelationSystem

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (E : EtaleRelationSystem B (⊤_ Scheme.{u}) hZ Iᵒᵖ)
  (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E.obj.map g)))
  (k : I) {Wk : BigFppfOver B (⊤_ Scheme.{u}) hZ} (wk : yoneda.obj Wk ⟶ E.quotient.obj (op k))
  (hwk : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf wk)
  (Vs : BigFppfOver B (⊤_ Scheme.{u}) hZ)
  (Wo : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs).Opens)
  (w : yoneda.obj (openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo) ⟶ limit E.quotient)
  (g : openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo ⟶ Wk)
  (hL : IsPullback w (yoneda.map g) (limit.π E.quotient (op k)) wk)
  (Q : Scheme.FiniteTypeApproximation (E.nbhdTailDiagram hZ hobj k wk)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs) Wo
      (E.nbhdTailπ hZ hobj k wk Wo w g hL))

/-- The preorder on the index set `J` of the approximation `Q`. -/
instance : Preorder Q.indexType := Q.indexPreorder

/-- The index set `J` of the approximation `Q` is nonempty. -/
instance : Nonempty Q.indexType := Q.indexNonempty

/-- The index set `J` of the approximation `Q` is directed. -/
instance : IsDirected Q.indexType (· ≤ ·) := Q.indexDirected


/-- The chart system `W_i` of `w_k`, as objects of the site, over the tail of `k`. -/
noncomputable abbrev nbhdTailSite : (Tail k)ᵒᵈ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  tailToOver k ⋙ stageChartOverDiagram E.quotient (E.relativelyRepresentable_quotient_map hobj)
    (op k) wk ⋙ Over.forget Wk

/-- The projections `W_i ⟶ U_i` of the chart system. -/
@[simps]
noncomputable def nbhdTailToBase :
    E.nbhdTailSite hZ hobj k wk ⋙ yoneda ⟶ tailToOver k ⋙ Over.forget (op k) ⋙ E.quotient where
  app i := stageChartToStage E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk
    ((tailToOver k).obj i)
  naturality _ _ v := stageChartMap_toStage E.quotient _ (op k) wk ((tailToOver k).map v)

/-- The reindexing `J ⟶ {i | k ≤ i}` of Stacks 07RN, on opposite categories. -/
noncomputable abbrev problemStepIndex : Q.indexTypeᵒᵖ ⥤ (Tail k)ᵒᵈ :=
  opToDual Q.indexType ⋙ Q.index.monotone.dual.functor

/-- Each scheme `V_j` of the approximation `Q` lies in the big fppf site `B`. -/
lemma contains_problemStepAmbient (j : Q.indexTypeᵒᵖ) :
    B.Contains ((opToDual Q.indexType ⋙ Q.ambient).obj j) := by
  have : LocallyOfFiniteType (terminal.from ((opToDual Q.indexType ⋙ Q.ambient).obj j)) :=
    Q.locallyOfFiniteType _
  have : QuasiCompact (terminal.from ((opToDual Q.indexType ⋙ Q.ambient).obj j)) :=
    Q.quasiCompact _
  exact contains_of_locallyOfFiniteType_terminal B hZ _

/-- **The data of the glued relations** `R_j = V_j ∪_{W_j} (W_j ×_{U_j} W_j)` of the problem step
of Stacks 07SU. -/
noncomputable def problemStepData :
    GluedNeighbourhoodRelationData B (⊤_ Scheme.{u}) hZ Q.indexTypeᵒᵖ where
  base := E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q ⋙ tailToOver k ⋙ Over.forget (op k) ⋙
    E.quotient
  nbhd := E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q ⋙ E.nbhdTailSite hZ hobj k wk
  ambient := overIntegersLift B hZ (opToDual Q.indexType ⋙ Q.ambient)
    (E.contains_problemStepAmbient hZ hobj k wk Vs Wo w g hL Q)
  toBase := Functor.whiskerLeft (E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q)
    (E.nbhdTailToBase hZ hobj k wk)
  etale_toBase j := E.presheaf_etale_stageChartToStage (op k) wk hwk
    (E.relativelyRepresentable_quotient_map hobj) _
  isPullback_toBase i j u :=
    isPullback_stageChartMap E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk _
  incl :=
    { app j := overIntegersHom ((Q.comparison.inv ≫ Q.inclusion).app (OrderDual.toDual j.unop))
      naturality {i j} u := by
        apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
        simp only [Functor.map_comp]
        exact (Q.comparison.inv ≫ Q.inclusion).naturality ((opToDual Q.indexType).map u) }
  isOpenImmersion_incl j := by
    have := Q.inclusion_isOpenImmersion (OrderDual.toDual j.unop)
    change _root_.AlgebraicGeometry.IsOpenImmersion
      (Q.comparison.inv.app (OrderDual.toDual j.unop) ≫ Q.inclusion.app (OrderDual.toDual j.unop))
    infer_instance
  isPullback_incl i j u := by
    change IsPullback ((Q.index.monotone.dual.functor ⋙ E.nbhdTailDiagram hZ hobj k wk).map
        ((opToDual Q.indexType).map u))
      ((Q.comparison.inv ≫ Q.inclusion).app (OrderDual.toDual i.unop))
      ((Q.comparison.inv ≫ Q.inclusion).app (OrderDual.toDual j.unop))
      (Q.ambient.map ((opToDual Q.indexType).map u))
    exact (IsPullback.of_vert_isIso ⟨Q.comparison.inv.naturality _⟩).paste_vert
      (Q.transition_isPullback ((opToDual Q.indexType).map u))

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
