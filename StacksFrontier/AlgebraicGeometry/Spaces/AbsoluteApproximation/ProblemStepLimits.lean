module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.ProblemStepSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# The limits of the systems of the problem step of Stacks 07SU

In the problem step of the proof of Stacks 07SU the systems `V_j`, `W_j` and
`W_j ×_{U_j} W_j` of the glued relations `R_j = V_j ∪_{W_j} (W_j ×_{U_j} W_j)`
(`AlgebraicGeometry.Space.EtaleRelationSystem.problemStepData`) have the limits `V`, `W` and
`W ×_U W` in schemes: "by construction `lim W_i ×_{U_i} W_i = W ×_U W` and `V = lim V_i`".
This file proves these three statements.

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.initial_problemStepBaseIndex`: the reindexing of
  Stacks 07RN, followed by the inclusion of the tail of `k`, is initial; this is where the
  cofinality of the reindexing is used.
* `AlgebraicGeometry.Space.EtaleRelationSystem.isLimit_problemStepAmbientCone`: `V = lim V_j`.
* `AlgebraicGeometry.Space.EtaleRelationSystem.isLimit_problemStepNbhdCone`: `W = lim W_j`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

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

/-- The reindexing `J ⟶ I` of the problem step: the reindexing of Stacks 07RN followed by the
inclusion of the tail of `k`. -/
noncomputable abbrev problemStepBaseIndex : Q.indexTypeᵒᵖ ⥤ Iᵒᵖ :=
  E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q ⋙ tailToOver k ⋙ Over.forget (op k)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The reindexing `J ⟶ {i | k ≤ i}` of the problem step is initial when the approximation `Q` is
cofinal. -/
lemma initial_problemStepIndex (hQ : Q.IsCofinal) :
    (E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q).Initial := by
  have : (Q.index.monotone.dual.functor).Initial :=
    (Monotone.initial_functor_iff _).2 fun t => by
      obtain ⟨j, hj⟩ := hQ (OrderDual.ofDual t)
      exact ⟨OrderDual.toDual j, hj⟩
  infer_instance

/-- **The reindexing of the problem step is initial**, the reindexing of Stacks 07RN being
cofinal. -/
lemma initial_problemStepBaseIndex (hQ : Q.IsCofinal) :
    (E.problemStepBaseIndex hZ hobj k wk Vs Wo w g hL Q).Initial := by
  have := E.initial_problemStepIndex hZ hobj k wk Vs Wo w g hL Q hQ
  infer_instance

/-- The cone from `V` to the system `V_j` of the problem step. -/
@[simps]
noncomputable def problemStepAmbientCone :
    Cone (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).ambient where
  pt := Vs
  π :=
    { app j := overIntegersHom (Q.ambientCone.app (OrderDual.toDual j.unop))
      naturality {i j} u := by
        apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.map_comp]
        exact Q.ambientCone.naturality ((opToDual Q.indexType).map u) }

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **`V = lim V_j` in schemes.** -/
theorem isLimit_problemStepAmbientCone :
    Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
      (E.problemStepAmbientCone hZ hobj k wk hwk Vs Wo w g hL Q))) :=
  ⟨(Functor.Initial.isLimitWhiskerEquiv (opToDual Q.indexType) _).symm Q.ambientCone_isLimit⟩

include hwk in
/-- **`W = lim W_j` in schemes.** -/
theorem isLimit_problemStepNbhdCone (hQ : Q.IsCofinal)
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)]
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV)) :
    Nonempty (IsLimit ((E.nbhdTailCone hZ hobj k wk w g hL).whisker
      (E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q))) := by
  have := E.initial_problemStepIndex hZ hobj k wk Vs Wo w g hL Q hQ
  obtain ⟨h⟩ := E.isLimit_nbhdTailCone hZ hobj k wk w g hL hlft hwk cV hV
  exact ⟨(Functor.Initial.isLimitWhiskerEquiv _ _).symm h⟩

/-- The reindexing `J ⟶ {i ≥ k}` of the problem step, into the stages over `k`. -/
noncomputable abbrev problemStepOverIndex : Q.indexTypeᵒᵖ ⥤ Over (op k) :=
  E.problemStepIndex hZ hobj k wk Vs Wo w g hL Q ⋙ tailToOver k

/-- The legs `W ⟶ W_j` of the problem step, as morphisms of the site. -/
noncomputable abbrev problemStepNbhdLeg (j : Q.indexTypeᵒᵖ) :
    openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo ⟶
      (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).nbhd.obj j :=
  stageChartLeg E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk w g hL
    ((E.problemStepOverIndex hZ hobj k wk Vs Wo w g hL Q).obj j)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The leg `W ⟶ W_j` followed by `W_j ⟶ U_j` is the composite `W ⟶ U ⟶ U_j`. -/
lemma problemStepNbhdLeg_toBase (j : Q.indexTypeᵒᵖ) :
    yoneda.map (E.problemStepNbhdLeg hZ hobj k wk hwk Vs Wo w g hL Q j) ≫
      (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).toBase.app j =
    w ≫ limit.π E.quotient ((E.problemStepBaseIndex hZ hobj k wk Vs Wo w g hL Q).obj j) :=
  stageChartLeg_toStage E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk w g hL _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The legs `W ⟶ W_j` are compatible with the transition maps of the system `W_j`. -/
lemma problemStepNbhdLeg_map {i j : Q.indexTypeᵒᵖ} (u : i ⟶ j) :
    E.problemStepNbhdLeg hZ hobj k wk hwk Vs Wo w g hL Q i ≫
      (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).nbhd.map u =
    E.problemStepNbhdLeg hZ hobj k wk hwk Vs Wo w g hL Q j :=
  stageChartLeg_chartMap E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk w g hL _

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **`W = U ×_{U_j} W_j` at every stage `j` of the problem step.** -/
lemma isPullback_problemStepNbhdLeg (j : Q.indexTypeᵒᵖ) :
    IsPullback w (yoneda.map (E.problemStepNbhdLeg hZ hobj k wk hwk Vs Wo w g hL Q j))
      (limit.π E.quotient ((E.problemStepBaseIndex hZ hobj k wk Vs Wo w g hL Q).obj j))
      ((E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).toBase.app j) :=
  isPullback_stageChartLeg E.quotient (E.relativelyRepresentable_quotient_map hobj) (op k) wk w g hL
    ((E.problemStepOverIndex hZ hobj k wk Vs Wo w g hL Q).obj j)


/-- The cone from `W` to the system `W_j` of the problem step, in the site. -/
@[simps]
noncomputable def problemStepNbhdCone :
    Cone (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).nbhd where
  pt := openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo
  π :=
    { app j := E.problemStepNbhdLeg hZ hobj k wk hwk Vs Wo w g hL Q j
      naturality {i j} u := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (E.problemStepNbhdLeg_map hZ hobj k wk hwk Vs Wo w g hL Q u).symm }

include hwk in
/-- **`W = lim W_j` in schemes**, for the cone in the site. -/
theorem isLimit_problemStepNbhdCone' (hQ : Q.IsCofinal)
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)]
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV)) :
    Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
      (E.problemStepNbhdCone hZ hobj k wk hwk Vs Wo w g hL Q))) :=
  E.isLimit_problemStepNbhdCone hZ hobj k wk hwk Vs Wo w g hL Q hQ hlft cV hV

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The inclusion `W ⟶ V` is compatible with the inclusions `W_j ⟶ V_j`. -/
lemma problemStep_incl_π (j : Q.indexTypeᵒᵖ) :
    openSiteObjectHom B (⊤_ Scheme.{u}) hZ Vs Wo ≫
        (E.problemStepAmbientCone hZ hobj k wk hwk Vs Wo w g hL Q).π.app j =
      (E.problemStepNbhdCone hZ hobj k wk hwk Vs Wo w g hL Q).π.app j ≫
        (E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).incl.app j := by
  apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
  change (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (openSiteObjectHom B (⊤_ Scheme.{u}) hZ Vs Wo) ≫
      Q.ambientCone.app (OrderDual.toDual j.unop) =
    (E.nbhdTailπ hZ hobj k wk Wo w g hL).app (Q.index.monotone.dual.functor.obj
        (OrderDual.toDual j.unop)) ≫
      (Q.comparison.inv ≫ Q.inclusion).app (OrderDual.toDual j.unop)
  rw [map_openSiteObjectHom, NatTrans.comp_app]
  have h₁ := Q.inclusion_compatibility (OrderDual.toDual j.unop)
  have h₂ := Q.comparison_compatibility (OrderDual.toDual j.unop)
  have h₃ : Q.openCone.app (OrderDual.toDual j.unop) =
      (E.nbhdTailπ hZ hobj k wk Wo w g hL).app (Q.index.monotone.dual.functor.obj
        (OrderDual.toDual j.unop)) ≫ Q.comparison.inv.app (OrderDual.toDual j.unop) := by
    rw [← h₂, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [h₃, Category.assoc] at h₁
  exact h₁

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The kernel pairs `W_j ×_{U_j} W_j` are quasi-compact**, the `W_j` being quasi-compact and
the `U_j` quasi-separated. -/
theorem compactSpace_problemStepKernelPair
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk)]
    (hqs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (E.quotient.obj j))
    (j : Q.indexTypeᵒᵖ) :
    CompactSpace ((E.problemStepData hZ hobj k wk hwk Vs Wo w g hL Q).kernelPairScheme.obj j) :=
  compactSpace_of_isAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (hqs _)
    (KernelPairSystem.isPullback_app _ _ _ j)
    (E.compactSpace_stageChart hobj (op k) wk _) (E.compactSpace_stageChart hobj (op k) wk _)

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
