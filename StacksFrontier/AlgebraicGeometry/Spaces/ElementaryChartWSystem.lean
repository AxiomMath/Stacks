module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedQuotientFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximationStrata
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStepSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The reindexing step of Stacks 07SU, from a system of étale charts over the stages

This file solves the problem posed in the proof of absolute Noetherian approximation,
Stacks 07SU (`AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`),
from one explicit input: the system of étale charts `W_i ⟶ U_i` over the stages of a Noetherian
approximation `U = lim U_i` of the open part, with `W = W_i ×_{U_i} U` and `W = lim W_i`
(`AlgebraicGeometry.Space.ElementaryChart.WSystem`). In the source that system is produced by
Stacks 07SK, 07SL and 07SR; here its existence is the proposition
`AlgebraicGeometry.Space.ElementaryChart.HasWSystems`, taken as an explicit argument.

Given it, the source "applies Stacks 07RN to `W = lim W_i` and the inclusion `W ⊆ V`" and
"replaces `I` by the directed set `J` found in that lemma"; this is done with the cofinal form
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.exists_isCofinal_of_isLimit`, and the output
is assembled into an `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem`, to which
`AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.hasNoetherianApproximation_of_finiteType`
applies.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryChart.WSystem`: the system of étale charts over the stages.
* `AlgebraicGeometry.Space.ElementaryChart.HasWSystems`: every elementary chart of the problem has
  one, over some Noetherian approximation of its open part.

## Main results

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.preimage_opensRange_inclusion_eq`: in the
  output of Stacks 07RN, the open `U` is the inverse image of each open stage.
* `AlgebraicGeometry.Space.noetherianApproximationExtendsOverElementaryChart_of_hasWSystems`: the
  problem of the source is solved by the W-systems.
* `AlgebraicGeometry.Space.hasNoetherianApproximation_of_hasWSystems`: Stacks 07SU over `Spec ℤ`,
  given the W-systems.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder indexNonempty indexDirected

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {U : S.Opens}
  {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D} (Q : FiniteTypeApproximation D S U p)

/-- The limit cone to the ambient stages commutes with the transition morphisms. -/
@[reassoc]
theorem ambientCone_comp_map {j k : Q.indexTypeᵒᵈ} (f : j ⟶ k) :
    Q.ambientCone.app j ≫ Q.ambient.map f = Q.ambientCone.app k := by
  simpa using (Q.ambientCone.naturality f).symm

/-- A morphism `t : T ⟶ S` whose composite with one ambient stage factors through the open stage
factors through the open stage at every index. -/
theorem exists_comp_inclusion_eq {T : Scheme.{u}} (t : T ⟶ S) (j₀ : Q.indexType)
    (h₀ : ∃ l₀ : T ⟶ Q.openPart.obj (OrderDual.toDual j₀),
      l₀ ≫ Q.inclusion.app (OrderDual.toDual j₀) = t ≫ Q.ambientCone.app (OrderDual.toDual j₀))
    (k : Q.indexType) :
    ∃ l : T ⟶ Q.openPart.obj (OrderDual.toDual k),
      l ≫ Q.inclusion.app (OrderDual.toDual k) = t ≫ Q.ambientCone.app (OrderDual.toDual k) := by
  obtain ⟨l₀, hl₀⟩ := h₀
  obtain ⟨m, hkm, hjm⟩ := Q.indexDirected.directed k j₀
  let f₀ : OrderDual.toDual m ⟶ OrderDual.toDual j₀ := homOfLE hjm
  let g : OrderDual.toDual m ⟶ OrderDual.toDual k := homOfLE hkm
  have hpb := Q.transition_isPullback f₀
  have hw : l₀ ≫ Q.inclusion.app (OrderDual.toDual j₀) =
      (t ≫ Q.ambientCone.app (OrderDual.toDual m)) ≫ Q.ambient.map f₀ := by
    rw [hl₀, Category.assoc, ambientCone_comp_map]
  refine ⟨hpb.lift l₀ _ hw ≫ Q.openPart.map g, ?_⟩
  rw [Category.assoc, Q.inclusion.naturality g, ← Category.assoc, hpb.lift_snd, Category.assoc,
    ambientCone_comp_map]

/-- **A morphism into the limit which lands in one open stage lands in the open part.** If the
composite of `t : T ⟶ S` with one ambient stage factors through the open stage, then `t`
factors through `U`: the factorisations at all stages form a cone over the open stages, whose
limit is `U`. -/
theorem exists_comp_ι_eq {T : Scheme.{u}} (t : T ⟶ S) (j₀ : Q.indexType)
    (h₀ : ∃ l₀ : T ⟶ Q.openPart.obj (OrderDual.toDual j₀),
      l₀ ≫ Q.inclusion.app (OrderDual.toDual j₀) = t ≫ Q.ambientCone.app (OrderDual.toDual j₀)) :
    ∃ w : T ⟶ (U : Scheme.{u}), w ≫ U.ι = t := by
  obtain ⟨l, hl⟩ : ∃ l : ∀ k : Q.indexTypeᵒᵈ, T ⟶ Q.openPart.obj k,
      ∀ k, l k ≫ Q.inclusion.app k = t ≫ Q.ambientCone.app k :=
    ⟨fun k ↦ (Q.exists_comp_inclusion_eq t j₀ h₀ (OrderDual.ofDual k)).choose,
      fun k ↦ (Q.exists_comp_inclusion_eq t j₀ h₀ (OrderDual.ofDual k)).choose_spec⟩
  let c : Cone Q.openPart :=
    { pt := T
      π :=
        { app := l
          naturality := fun k k' g ↦ by
            have := Q.inclusion_isOpenImmersion k'
            rw [← cancel_mono (Q.inclusion.app k')]
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc]
            rw [hl k', Q.inclusion.naturality g, ← Category.assoc, hl k, Category.assoc,
              ambientCone_comp_map] } }
  refine ⟨Q.openCone_isLimit.lift c, Q.ambientCone_isLimit.hom_ext fun k ↦ ?_⟩
  change (Q.openCone_isLimit.lift c ≫ U.ι) ≫ Q.ambientCone.app k = t ≫ Q.ambientCone.app k
  have hfac : Q.openCone_isLimit.lift c ≫ Q.openCone.app k = l k :=
    Q.openCone_isLimit.fac c k
  rw [Category.assoc, Q.inclusion_compatibility, ← Category.assoc, hfac, hl k]

/-- **In the output of Stacks 07RN the open part is the inverse image of each open stage.** -/
theorem preimage_opensRange_inclusion_eq (j : Q.indexType) :
    Q.ambientCone.app (OrderDual.toDual j) ⁻¹ᵁ
        (Q.inclusion.app (OrderDual.toDual j)).opensRange
          (H := Q.inclusion_isOpenImmersion (OrderDual.toDual j)) = U := by
  have := Q.inclusion_isOpenImmersion (OrderDual.toDual j)
  refine le_antisymm ?_ ?_
  · intro x hx
    set O := Q.ambientCone.app (OrderDual.toDual j) ⁻¹ᵁ
      (Q.inclusion.app (OrderDual.toDual j)).opensRange
    have hrange : Set.range (O.ι ≫ Q.ambientCone.app (OrderDual.toDual j)) ⊆
        Set.range (Q.inclusion.app (OrderDual.toDual j)) := by
      rintro _ ⟨y, rfl⟩
      exact y.2
    obtain ⟨w, hw⟩ := Q.exists_comp_ι_eq O.ι j
      ⟨IsOpenImmersion.lift (Q.inclusion.app (OrderDual.toDual j))
          (O.ι ≫ Q.ambientCone.app (OrderDual.toDual j)) hrange,
        IsOpenImmersion.lift_fac _ _ _⟩
    have : x ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hx
    obtain ⟨y, rfl⟩ := this
    rw [← hw, Scheme.Hom.comp_apply]
    exact (w y).2
  · intro x hx
    change Q.ambientCone.app (OrderDual.toDual j) x ∈
      Set.range (Q.inclusion.app (OrderDual.toDual j))
    have h2 := congrArg
      (fun f : (U : Scheme.{u}) ⟶ Q.ambient.obj (OrderDual.toDual j) ↦ f ⟨x, hx⟩)
      (Q.inclusion_compatibility (OrderDual.toDual j))
    simp only at h2
    exact ⟨_, h2.symm⟩

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "F" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

/-- **A scheme étale over a space of finite type over `ℤ` is locally of finite type over `ℤ`.**
The structure morphism of the scheme is the composite of the étale morphism, which is locally of
finite type (Stacks 06LT), with that of the space (Stacks 03XG). -/
theorem locallyOfFiniteType_terminal_of_etale {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ U)
    (hUft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ U)))
    {W : BigFppfOver B (⊤_ Scheme.{u}) hZ} (q : yoneda.obj W ⟶ U)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (F))) q) :
    LocallyOfFiniteType (terminal.from ((F).obj W)) := by
  have h1 : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from U) :=
    (isLocallyOfFiniteType_terminal_iff_of_iso B (⊤_ Scheme.{u}) hZ
      (viewOverIntegersOfTerminalIso U)).mp hUft.1
  have h2 : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ q :=
    isLocallyOfFiniteType_of_isEtale' B (⊤_ Scheme.{u}) hZ q
      (isEtale_of_presheaf_etale B (⊤_ Scheme.{u}) hZ hq)
  have h3 := isLocallyOfFiniteType_comp' B (⊤_ Scheme.{u}) hZ q (terminal.from U) hU
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) h2 h1
  rw [show q ≫ terminal.from U = terminal.from (yoneda.obj W) from terminal.hom_ext _ _] at h3
  have h4 : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (yoneda.map (terminal.from W)) :=
    holdsOnEveryEtaleChart_of_isTerminal B (⊤_ Scheme.{u}) hZ terminalIsTerminal
      (isTerminal_yoneda_obj_terminal B (⊤_ Scheme.{u}) hZ) _ _ h3
  have h5 := (isLocallyOfFiniteType_yoneda_map_iff B (⊤_ Scheme.{u}) hZ _).mp h4
  rw [show terminal.from ((F).obj W) = (F).map (terminal.from W) ≫
    (toSchemeTerminalIso B (⊤_ Scheme.{u}) hZ).hom from terminal.hom_ext _ _]
  infer_instance

namespace ElementaryChart

variable {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}

/-- **The system of étale charts over the stages, the "W-system" of the proof of Stacks 07SU.**
For an elementary chart `f : V ⟶ X` with open part `U` and inverse image `W ⊆ V`, and a Noetherian
approximation `U = lim U_i`: objects `W_i` of the site with étale morphisms `p_i : W_i ⟶ U_i`,
forming a system over the stages with cartesian transition squares
`W_i = W_j ×_{U_j} U_i`, with `W = W_i ×_{U_i} U` for every `i`, each `W_i` quasi-compact, and
`W = lim W_i` as schemes. In the source this is the output of Stacks 07SK, 07SL and 07SR: "an
étale morphism `W_0 ⟶ U_0` of finite presentation whose base change to `U` produces `W`",
`W_i = W_0 ×_{U_0} U_i`, "`W = lim W_i`", "we may assume the `W_i` are schemes". -/
structure WSystem (C : ElementaryChart X V)
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor) where
  /-- The charts `W_i`. -/
  Wd : A.Iᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ
  /-- The étale morphisms `W_i ⟶ U_i`. -/
  p : Wd ⋙ yoneda ⟶ A.diagram
  /-- The projections `W ⟶ W_i`. -/
  w : (Functor.const A.Iᵒᵖ).obj C.W ⟶ Wd
  /-- Each `p_i : W_i ⟶ U_i` is étale. -/
  etale_p : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (F))) (p.app i)
  /-- The transition squares are cartesian: `W_i = W_j ×_{U_j} U_i`. -/
  isPullback_map : ∀ ⦃i j : A.Iᵒᵖ⦄ (g : i ⟶ j),
    IsPullback (yoneda.map (Wd.map g)) (p.app i) (p.app j) (A.diagram.map g)
  /-- The square exhibits `W` as `W_i ×_{U_i} U`. -/
  isPullback_w : ∀ i, IsPullback (yoneda.map (w.app i)) C.p (p.app i) (A.π.app i)
  /-- Each `W_i` is quasi-compact. -/
  compactSpace : ∀ i, CompactSpace ((F).obj (Wd.obj i))
  /-- The projections exhibit `W` as the limit of the `W_i` as schemes. -/
  isLimit : IsLimit ((F).mapCone (Cone.mk C.W w))

variable (B hZ) in
/-- **The W-systems exist.** For every elementary chart of the problem posed in the proof of
Stacks 07SU (the hypotheses of
`AlgebraicGeometry.Space.NoetherianApproximationExtendsOverElementaryChart`), some Noetherian
approximation of its open part carries a W-system
(`AlgebraicGeometry.Space.ElementaryChart.WSystem`).
This is what Stacks 07SK, 07SL and 07SR supply in the source. -/
def HasWSystems : Prop :=
  ∀ (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (C : ElementaryChart X V),
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X →
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X →
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X →
    CompactSpace ((F).obj V) →
    Scheme.IsSeparated ((F).obj V) →
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f →
    IsOpenSubspace B (⊤_ Scheme.{u}) hZ C.U →
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor →
    ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor, Nonempty (C.WSystem A)

/-- The open subscheme `W ⊆ V` of an elementary chart. -/
noncomputable abbrev openW (C : ElementaryChart X V) : ((F).obj V).Opens := ((F).map C.j).opensRange

namespace WSystem

variable {C : ElementaryChart X V}
  {A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ C.U.toFunctor} (WS : C.WSystem A)

/-- The transition morphisms of the `W_i` are affine: they are base changes of those of the
`U_i`. -/
theorem isAffineHom_map {i j : A.Iᵒᵖ} (g : i ⟶ j) :
    _root_.AlgebraicGeometry.IsAffineHom ((F).map (WS.Wd.map g)) :=
  isAffineHom_toScheme_map_of_isAffineHom B (⊤_ Scheme.{u}) hZ _
    (IsAffineHom.of_isPullback (WS.isPullback_map g).flip (A.isAffineHom_map g))

/-- The `W_i` as an inverse system of schemes, indexed by the order dual. -/
noncomputable abbrev schemeDiagram : A.Iᵒᵈ ⥤ Scheme.{u} :=
  (orderDualEquivalence A.I).functor ⋙ WS.Wd ⋙ F

/-- The cone from the open subscheme `W ⊆ V` to the `W_i`. -/
noncomputable def schemeCone :
    (Functor.const A.Iᵒᵈ).obj (C.openW : Scheme.{u}) ⟶ WS.schemeDiagram where
  app i := ((F).map C.j).isoOpensRange.inv ≫
    (F).map (WS.w.app ((orderDualEquivalence A.I).functor.obj i))
  naturality i j g := by
    have h := WS.w.naturality ((orderDualEquivalence A.I).functor.map g)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
    refine (Category.id_comp _).trans ?_
    change _ = _ ≫ (F).map (WS.Wd.map ((orderDualEquivalence A.I).functor.map g))
    rw [Category.assoc, ← Functor.map_comp, ← h]

/-- The cone from `W ⊆ V` to the `W_i` is a limit cone. -/
noncomputable def isLimit_schemeCone : IsLimit (Cone.mk _ WS.schemeCone) :=
  (WS.isLimit.whiskerEquivalence (orderDualEquivalence A.I)).ofIsoLimit
    (Cone.ext ((F).map C.j).isoOpensRange (fun _ ↦ (Iso.hom_inv_id_assoc _ _).symm))

include WS in
/-- The scheme `W` is quasi-compact. -/
theorem compactSpace_W : CompactSpace ((F).obj C.W) := by
  have := A.isCofiltered_op
  have : ∀ {i j : A.Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((WS.Wd ⋙ F).map g) := fun g ↦ WS.isAffineHom_map g
  have : ∀ i, CompactSpace ((WS.Wd ⋙ F).obj i) := fun i ↦ WS.compactSpace i
  exact Scheme.compactSpace_of_isLimit (WS.Wd ⋙ F) _ WS.isLimit

include WS in
/-- The open subscheme `W ⊆ V` is quasi-compact. -/
theorem compactSpace_openW : CompactSpace (C.openW : Scheme.{u}) := by
  have := WS.compactSpace_W
  exact ((F).map C.j).isoOpensRange.hom.homeomorph.compactSpace

/-! ### The stage system from the output of Stacks 07RN -/

section Stages

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

variable (Q : Scheme.FiniteTypeApproximation WS.schemeDiagram
  ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) C.openW WS.schemeCone)

/-- The ambient stages are objects of the site: they are of finite type over `ℤ` (Stacks 000R). -/
theorem contains_ambient (j : Q.indexType) : B.Contains (Q.ambient.obj (OrderDual.toDual j)) := by
  have := Q.locallyOfFiniteType (OrderDual.toDual j)
  have := Q.quasiCompact (OrderDual.toDual j)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (terminal.from _) hZ

/-- The ambient stage `V_j`, as an object of the site. -/
noncomputable abbrev stageV (j : Q.indexType) : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  BigFppfOver.mk B (⊤_ Scheme.{u}) hZ (WS.contains_ambient Q j) (terminal.from _)

/-- The open immersion `W_{i(j)} ⟶ V_j` of schemes. -/
noncomputable abbrev stageJ (j : Q.indexType) :
    (F).obj (WS.Wd.obj (op (Q.index j))) ⟶ Q.ambient.obj (OrderDual.toDual j) :=
  Q.comparison.inv.app (OrderDual.toDual j) ≫ Q.inclusion.app (OrderDual.toDual j)

/-- The morphism `W_{i(j)} ⟶ V_j` is an open immersion. -/
instance isOpenImmersion_stageJ (j : Q.indexType) :
    _root_.AlgebraicGeometry.IsOpenImmersion (WS.stageJ Q j) := by
  have := Q.inclusion_isOpenImmersion (OrderDual.toDual j)
  have hiso : IsIso (Q.comparison.inv.app (OrderDual.toDual j)) :=
    (Q.comparison.app (OrderDual.toDual j)).isIso_inv
  exact @_root_.AlgebraicGeometry.IsOpenImmersion.comp _ _ _ _ _
    (@_root_.AlgebraicGeometry.IsOpenImmersion.of_isIso _ _ _ hiso) this

/-- The image of `W_{i(j)} ⟶ V_j` is the open stage at `j`. -/
theorem opensRange_stageJ (j : Q.indexType) :
    (WS.stageJ Q j).opensRange =
      (Q.inclusion.app (OrderDual.toDual j)).opensRange
        (H := Q.inclusion_isOpenImmersion (OrderDual.toDual j)) := by
  have := Q.inclusion_isOpenImmersion (OrderDual.toDual j)
  exact @Scheme.Hom.opensRange_comp_of_isIso _ _ _ _ _
    (Q.comparison.app (OrderDual.toDual j)).isIso_inv this

/-- The extended relation at the stage `j`: `R_j = V_j ⊔_{W_j} (W_j ×_{U_j} W_j)`. -/
noncomputable def stageE (j : Q.indexType) :
    OpenKernelPairExtension B (⊤_ Scheme.{u}) hZ (A.diagram.obj (op (Q.index j)))
      (WS.stageV Q j) (WS.Wd.obj (op (Q.index j))) where
  j := homOfScheme (WS.stageJ Q j) (terminal.hom_ext _ _)
  isOpenImmersion_j := WS.isOpenImmersion_stageJ Q j
  p := WS.p.app (op (Q.index j))
  Q := (WS.etale_p (op (Q.index j))).rep.pullback (WS.p.app (op (Q.index j)))
  q₁ := (WS.etale_p (op (Q.index j))).rep.fst' (WS.p.app (op (Q.index j)))
  q₂ := (WS.etale_p (op (Q.index j))).rep.snd (WS.p.app (op (Q.index j)))
  isPullback := (WS.etale_p (op (Q.index j))).rep.isPullback' (WS.p.app (op (Q.index j)))
  etale_q₁ := (WS.etale_p (op (Q.index j))).property _ _ _
    ((WS.etale_p (op (Q.index j))).rep.isPullback' (WS.p.app (op (Q.index j)))).flip
  etale_q₂ := (WS.etale_p (op (Q.index j))).property _ _ _
    ((WS.etale_p (op (Q.index j))).rep.isPullback' (WS.p.app (op (Q.index j))))

/-- The square formed by `W ⟶ W_{i(j)} ⟶ V_j` and `W ⟶ V ⟶ V_j` commutes. -/
theorem comm_j_scheme (j : Q.indexType) :
    (F).map (WS.w.app (op (Q.index j))) ≫ WS.stageJ Q j =
      (F).map C.j ≫ Q.ambientCone.app (OrderDual.toDual j) := by
  have h1 := Q.comparison_compatibility (OrderDual.toDual j)
  have h2 : Q.openCone.app (OrderDual.toDual j) =
      WS.schemeCone.app (Q.index.monotone.dual.functor.obj (OrderDual.toDual j)) ≫
        Q.comparison.inv.app (OrderDual.toDual j) := by
    rw [← h1, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← ((F).map C.j).isoOpensRange_hom_ι, Category.assoc, Q.inclusion_compatibility, h2]
  simp only [schemeCone, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The map from the elementary chart to the stage `j`. -/
noncomputable def stageM (j : Q.indexType) : C.StageMap (WS.stageE Q j) where
  v := homOfScheme (Q.ambientCone.app (OrderDual.toDual j)) (terminal.hom_ext _ _)
  w := WS.w.app (op (Q.index j))
  u := A.π.app (op (Q.index j))
  comm_j := BigFppfOver.map_toScheme_injective B (⊤_ Scheme.{u}) hZ (by
    simp only [Functor.map_comp]
    exact WS.comm_j_scheme Q j)
  comm_p := (WS.isPullback_w (op (Q.index j))).w

/-- The open immersions `W_{i(j)} ⟶ V_j` commute with the transition morphisms. -/
theorem stageJ_comp_map {i i' : Q.indexType} (h : i ≤ i') :
    WS.stageJ Q i' ≫
        Q.ambient.map (homOfLE (OrderDual.toDual_le_toDual.mpr (h))) =
      (F).map (WS.Wd.map (homOfLE (Q.index.monotone h)).op) ≫ WS.stageJ Q i := by
  have e1 := Q.inclusion.naturality
    (homOfLE (OrderDual.toDual_le_toDual.mpr (h)))
  have e2 := Q.comparison.inv.naturality
    (homOfLE (OrderDual.toDual_le_toDual.mpr (h)))
  exact (Category.assoc _ _ _).trans ((congrArg (Q.comparison.inv.app _ ≫ ·) e1.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.inclusion.app _) e2.symm).trans
      (Category.assoc _ _ _))))

/-- The transition from the stage `i'` to the stage `i ≤ i'`. -/
noncomputable def stageT {i i' : Q.indexType} (h : i ≤ i') :
    OpenKernelPairExtension.Transition (WS.stageE Q i') (WS.stageE Q i) where
  v := homOfScheme
    (Q.ambient.map (homOfLE (OrderDual.toDual_le_toDual.mpr (h))))
    (terminal.hom_ext _ _)
  k := WS.Wd.map (homOfLE (Q.index.monotone h)).op
  u := A.diagram.map (homOfLE (Q.index.monotone h)).op
  isPullback_j := by
    refine isPullback_of_isPullback_map (BigFppfOver.map_toScheme_injective B _ hZ ?_) ?_
    · simp only [Functor.map_comp]
      exact (WS.stageJ_comp_map Q h).symm
    · refine _root_.AlgebraicGeometry.IsOpenImmersion.isPullback _ (WS.stageJ Q i')
        (WS.stageJ Q i) _
        (WS.stageJ_comp_map Q h) ?_
      rw [WS.opensRange_stageJ, WS.opensRange_stageJ]
      have := Q.inclusion_isOpenImmersion (OrderDual.toDual i)
      have := Q.inclusion_isOpenImmersion (OrderDual.toDual i')
      exact preimage_opensRange_of_isPullback (Q.transition_isPullback _).flip
  isPullback_p := WS.isPullback_map _

/-- The chart `W ⟶ V` is the base change of `W_{i(j)} ⟶ V_j` along `V ⟶ V_j`. -/
theorem isPullback_stageW (j : Q.indexType) :
    IsPullback (WS.stageM Q j).w C.j (WS.stageE Q j).j (WS.stageM Q j).v := by
  refine isPullback_of_isPullback_map (WS.stageM Q j).comm_j ?_
  refine _root_.AlgebraicGeometry.IsOpenImmersion.isPullback _ ((F).map C.j) (WS.stageJ Q j) _
    (WS.comm_j_scheme Q j).symm ?_
  rw [WS.opensRange_stageJ]
  exact Q.preimage_opensRange_inclusion_eq j

/-- The composite of two transition morphisms of the ambient stages is the transition morphism. -/
theorem ambient_map_comp_eq {i i' i'' : Q.indexType} (h : i ≤ i') (h' : i' ≤ i'') :
    Q.ambient.map (homOfLE (OrderDual.toDual_le_toDual.mpr (h'))) ≫
        Q.ambient.map (homOfLE (OrderDual.toDual_le_toDual.mpr (h))) =
      Q.ambient.map (homOfLE (OrderDual.toDual_le_toDual.mpr (h.trans h'))) := by
  rw [← Functor.map_comp]
  rfl

/-- **The stage system of Stacks 07SU**, built from the output of Stacks 07RN applied to
`W = lim W_i` and `W ⊆ V`, along a cofinal reindexing. -/
noncomputable def stageSystem (hQ : Q.IsCofinal) : C.LimitStageSystem Q.indexType where
  Ui j := A.diagram.obj (op (Q.index j))
  Vi j := WS.stageV Q j
  Wi j := WS.Wd.obj (op (Q.index j))
  E j := WS.stageE Q j
  M j := WS.stageM Q j
  T h := WS.stageT Q h
  comm_v h := BigFppfOver.map_toScheme_injective B _ hZ (by
    simp only [Functor.map_comp]
    exact Q.ambientCone_comp_map _)
  comm_w h := by
    have := WS.w.naturality (homOfLE (Q.index.monotone h)).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm
  comm_u h := by
    have := A.π.naturality (homOfLE (Q.index.monotone h)).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm
  isPullback_w j := WS.isPullback_stageW Q j
  hom_ext_V i₀ Y x y hxy := by
    refine BigFppfOver.map_toScheme_injective B _ hZ (Q.ambientCone_isLimit.hom_ext fun k ↦ ?_)
    obtain ⟨m, hkm, hm⟩ := Q.indexDirected.directed (OrderDual.ofDual k) i₀
    have e := congrArg (fun a ↦ (F).map a) (hxy m hm)
    simp only [Functor.map_comp] at e
    change (F).map x ≫ Q.ambientCone.app k = (F).map y ≫ Q.ambientCone.app k
    rw [← Q.ambientCone_comp_map (homOfLE (OrderDual.toDual_le.mpr hkm)),
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) e
  hom_ext_U i₀ Y x y hxy := by
    refine A.isLimit.hom_ext fun k ↦ ?_
    obtain ⟨j, hj⟩ := hQ k.unop
    obtain ⟨m, hjm, hm⟩ := Q.indexDirected.directed j i₀
    have hk : k.unop ≤ Q.index m := hj.trans (Q.index.monotone hjm)
    have e := A.π.naturality (homOfLE hk).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at e
    change x ≫ A.π.app k = y ≫ A.π.app k
    rw [show A.π.app k = A.π.app (op (Q.index m)) ≫ A.diagram.map (homOfLE hk).op from e,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) (hxy m hm)
  v_refl i := BigFppfOver.map_toScheme_injective B _ hZ (by
    exact (Q.ambient.map_id (OrderDual.toDual i)).trans ((F).map_id (WS.stageV Q i)).symm)
  v_trans h h' := BigFppfOver.map_toScheme_injective B _ hZ (by
    simp only [Functor.map_comp]
    exact WS.ambient_map_comp_eq Q h h')
  isAffineHom_v h := Q.transition_affine _
  lift_V i₀ Y x hx := by
    have key (k : Q.indexTypeᵒᵈ) (n n' : Q.indexType) (hn : i₀ ≤ n) (hn' : i₀ ≤ n')
        (hkn : OrderDual.ofDual k ≤ n) (hkn' : OrderDual.ofDual k ≤ n') :
        (F).map (x n hn) ≫ Q.ambient.map (homOfLE (OrderDual.toDual_le.mpr hkn)) =
          (F).map (x n' hn') ≫ Q.ambient.map (homOfLE (OrderDual.toDual_le.mpr hkn')) := by
      obtain ⟨r, hnr, hn'r⟩ := Q.indexDirected.directed n n'
      have hr : i₀ ≤ r := hn.trans hnr
      have e := congrArg (fun a ↦ (F).map a) (hx n r hn hr hnr)
      have e' := congrArg (fun a ↦ (F).map a) (hx n' r hn' hr hn'r)
      simp only [Functor.map_comp] at e e'
      exact ((congrArg (· ≫ _) e.symm).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Q.ambient.map_comp _ _).symm))).trans
        ((congrArg (· ≫ _) e'.symm).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Q.ambient.map_comp _ _).symm))).symm
    choose m hkm hm using fun k : Q.indexTypeᵒᵈ ↦ Q.indexDirected.directed (OrderDual.ofDual k) i₀
    let c : Cone Q.ambient :=
      { pt := (F).obj Y
        π :=
          { app := fun k ↦ (F).map (x (m k) (hm k)) ≫
              Q.ambient.map (homOfLE (OrderDual.toDual_le.mpr (hkm k)))
            naturality := fun k k' g ↦ (Category.id_comp _).trans
              ((key k' (m k') (m k) (hm k') (hm k) (hkm k')
                ((show OrderDual.ofDual k' ≤ OrderDual.ofDual k from leOfHom g).trans
                  (hkm k))).trans
                ((congrArg (_ ≫ ·) (Q.ambient.map_comp _ _)).trans
                  (Category.assoc _ _ _).symm)) } }
    refine ⟨homOfScheme (Q.ambientCone_isLimit.lift c) (terminal.hom_ext _ _), fun i hi ↦ ?_⟩
    refine BigFppfOver.map_toScheme_injective B _ hZ ?_
    simp only [Functor.map_comp]
    exact (Q.ambientCone_isLimit.fac c (OrderDual.toDual i)).trans
      ((key (OrderDual.toDual i) (m (OrderDual.toDual i)) i (hm _) hi (hkm _) le_rfl).trans
        ((congrArg (_ ≫ ·) (Q.ambient.map_id _)).trans (Category.comp_id _)))

end Stages

/-- **The problem posed in the proof of Stacks 07SU is solved by a W-system.** If the chart
`f : V ⟶ X` is surjective, `V` is quasi-compact and quasi-separated, and the open part `U` has a
Noetherian approximation carrying a W-system, then `X` has a Noetherian approximation: Stacks 07RN
(with cofinal reindexing) extends `W = lim W_i` to `V = lim V_j`, and the quotients
`X_j = V_j/R_j` approximate `X`. -/
theorem hasNoetherianApproximation (WS : C.WSystem A) (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    [CompactSpace ((F).obj V)] [QuasiSeparatedSpace ((F).obj V)] :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  have : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have : ∀ {i j : A.Iᵒᵈ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom (WS.schemeDiagram.map g) :=
    fun g ↦ WS.isAffineHom_map _
  have : ∀ i, LocallyOfFiniteType (terminal.from (WS.schemeDiagram.obj i)) := fun i ↦
    locallyOfFiniteType_terminal_of_etale (A.isAlgebraicSpace _) (A.isFiniteTypeOverIntegers _)
      (WS.p.app _) (WS.etale_p _)
  have : ∀ i, CompactSpace (WS.schemeDiagram.obj i) := fun i ↦ WS.compactSpace _
  have : ∀ i, QuasiCompact (terminal.from (WS.schemeDiagram.obj i)) := fun i ↦ inferInstance
  have := WS.compactSpace_openW
  obtain ⟨Q, hQ⟩ :=
    Scheme.FiniteTypeApproximation.exists_isCofinal_of_isLimit WS.schemeDiagram
      ((F).obj V) C.openW WS.schemeCone WS.isLimit_schemeCone
  let := Q.indexPreorder
  let := Q.indexNonempty
  let := Q.indexDirected
  refine (WS.stageSystem Q hQ).hasNoetherianApproximation_of_finiteType hX.isSheaf hsurj
    (fun j ↦ A.isAlgebraicSpace _) (fun j ↦ A.isAbsolutelyQuasiSeparated _)
    (fun j ↦ Q.locallyOfFiniteType _) (fun j ↦ ?_) (fun j ↦ WS.compactSpace _)
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ (Q.quasiCompact (OrderDual.toDual j))
    inferInstance

end WSystem

end ElementaryChart

open ElementaryChart in
/-- **The reindexing step of Stacks 07SU.** The W-systems
(`AlgebraicGeometry.Space.ElementaryChart.HasWSystems`, what Stacks 07SK, 07SL and 07SR supply in
the source) solve the problem posed in the proof of Stacks 07SU for every stratum. -/
theorem noetherianApproximationExtendsOverElementaryChart_of_hasWSystems
    (hW : HasWSystems B hZ) : NoetherianApproximationExtendsOverElementaryChart B hZ := by
  intro X V C hX hqc hqs hVc hVsep hsurj hU hUapprox
  obtain ⟨A, ⟨WS⟩⟩ := hW X V C hX hqc hqs hVc hVsep hsurj hU hUapprox
  exact WS.hasNoetherianApproximation hX hsurj

/-- **Stacks 07SU over `Spec ℤ`, given the W-systems.** Every quasi-compact quasi-separated
algebraic space over `Spec ℤ` is the limit of a directed inverse system of algebraic spaces with
affine transition morphisms, each quasi-separated and of finite type over `ℤ`, as soon as the
W-systems of the proof exist (`AlgebraicGeometry.Space.ElementaryChart.HasWSystems`, the output of
Stacks 07SK, 07SL and 07SR in the source). Everything else in the proof (Stacks 07ST, 07RN,
02WW, 07S4, 040W, 040Y, 07S3, 03WG, 0262) is proved. -/
theorem hasNoetherianApproximation_of_hasWSystems (hW : ElementaryChart.HasWSystems B hZ)
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  hasNoetherianApproximation_of_extendsOverElementaryChart
    (noetherianApproximationExtendsOverElementaryChart_of_hasWSystems hW)
    (fun Y hY ↦ hasNoetherianApproximation_sheafify_bot Y hY) X hX hqc hqs

end AlgebraicGeometry.Space

end
