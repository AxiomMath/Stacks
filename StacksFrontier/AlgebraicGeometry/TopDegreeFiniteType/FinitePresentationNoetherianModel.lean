module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue

/-!
# Noetherian models of a proper morphism of finite presentation over an affine base

Paragraph four of the proof of [Stacks, Tag 0EX4], which is also the proof of
[Stacks, Tag 0EX5], begins by replacing an affine base `Y` by a Noetherian one. This file
carries out that replacement and nothing else: it produces, for a proper morphism `g : X ⟶ Y`
of finite presentation onto an **affine** base all of whose fibres have dimension at most `d`
and a finitely presented `𝒪_X`-module `G`, a cartesian square

```
X  ⟶  X₀
↓ g     ↓ g₀
Y  ⟶  S₀
```

with `S₀` affine **and Noetherian**, `g₀` proper and of finite presentation with all fibres of
dimension at most `d`, together with a finitely presented `𝒪_{X₀}`-module `G₀` pulling back to
`G`.

## Main results

* `Stacks.AlgebraicGeometry.NoetherianModel.exists_noetherianModel`: the statement just
  described.

## Implementation notes

The route is the source's, and every input is already in this development:

* `AlgebraicGeometry.exists_limitNoetherianSituation_of_isAffine` writes `Y = lim Sᵢ` as a
  cofiltered limit of Noetherian affine schemes with affine transition morphisms — the affine
  case of [Stacks, Tag 01ZA];
* `AlgebraicGeometry.exists_isProper_finitePresentation_overPullbackObj_of_isLimit` descends
  `g` to a proper morphism of finite presentation over a stage — [Stacks, Tags 01ZM and 081F];
* `AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall`
  makes the fibre bound hold at a later stage — [Stacks, Tag 05M5];
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`
  descends `G` — [Stacks, Tag 01ZR].

The last two are statements about a cofiltered diagram whose limit is `X`, not `Y`. That
diagram is `modelDiagram`: the stages are the base changes of the model along the transition
morphisms out of its stage, indexed by the slice category over that stage, and `modelCone` is
the cone over it with vertex `X`. `Over.forget` out of a slice of a cofiltered category is an
initial functor, so that cone is limiting as soon as the original one is, which is
`modelConeIsLimit`.

No `@[stacks]` attribute is attached. Nothing here is a Stacks statement: the four results
named above carry the four tags, and their assembly is a step inside the proof of
[Stacks, Tag 0EX5] rather than a statement the source makes.

## References

* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NoetherianModel

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (i₀ : I) (M : Over (D.obj i₀))

/-- **The diagram of base changes of a model.** Given a model `M` over the stage `D.obj i₀`,
this is the diagram over the slice category `Over i₀` whose value at `(i, i ⟶ i₀)` is the base
change `(D.obj i) ×_{D.obj i₀} M.left`. -/
noncomputable abbrev modelDiagram : Over i₀ ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback M.hom ⋙ Over.forget M.left

/-- **The structure morphisms of the diagram of base changes**, as a natural transformation to
the diagram of bases. Its component at a stage is the first projection of the pullback. -/
noncomputable def modelProjection : modelDiagram D i₀ M ⟶ Over.forget i₀ ⋙ D where
  app stage := pullback.fst (D.map stage.hom) M.hom
  naturality stage next transition := by
    dsimp [Over.post]
    simp only [Over.pullback_map_left, Over.mk_left, Over.mk_hom, Over.homMk_left]
    exact pullback.lift_fst _ _ _

/-- **The cone over the diagram of base changes induced by a cone over the original diagram.**
Its vertex is the base change of `M` along the projection of the cone to the stage `i₀`. -/
noncomputable abbrev modelCone (c : Cone D) : Cone (modelDiagram D i₀ M) :=
  (Over.pullback M.hom ⋙ Over.forget M.left).mapCone (c.overPost i₀)

/-- **The cone over the diagram of base changes is limiting.** Pullback along a fixed morphism
preserves limits, and `Cone.overPost` carries a limiting cone to a limiting cone. -/
noncomputable def modelConeIsLimit [IsCofiltered I] (c : Cone D) (hc : IsLimit c) :
    IsLimit (modelCone D i₀ M c) :=
  isLimitOfPreserves (Over.pullback M.hom ⋙ Over.forget M.left) (hc.overPost i₀)

/-- **Each transition square of the diagram of base changes is cartesian.** Base changing a
model twice in a row is base changing it once along the composite. -/
theorem modelTransition_isPullback {stage next : Over i₀} (t : stage ⟶ next) :
    IsPullback ((modelDiagram D i₀ M).map t) ((modelProjection D i₀ M).app stage)
      ((modelProjection D i₀ M).app next) (D.map t.left) := by
  have hsnd : (modelDiagram D i₀ M).map t ≫ pullback.snd (D.map next.hom) M.hom =
      pullback.snd (D.map stage.hom) M.hom := pullback.lift_snd _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map next.hom) M.hom)
    (h₂₂ := D.map next.hom) (v₁₃ := M.hom) ?_ ((modelProjection D i₀ M).naturality t)
    (IsPullback.of_hasPullback (D.map next.hom) M.hom).flip
  show IsPullback ((modelDiagram D i₀ M).map t ≫ pullback.snd (D.map next.hom) M.hom)
      (pullback.fst (D.map stage.hom) M.hom) M.hom (D.map t.left ≫ D.map next.hom)
  rw [hsnd, ← D.map_comp, Over.w t]
  exact (IsPullback.of_hasPullback (D.map stage.hom) M.hom).flip

/-- **Each leg of the cone over the diagram of base changes sits in a cartesian square** over
the corresponding leg of the original cone. -/
theorem modelCone_isPullback (c : Cone D) (stage : Over i₀) :
    IsPullback ((modelCone D i₀ M c).π.app stage) (pullback.fst (c.π.app i₀) M.hom)
      ((modelProjection D i₀ M).app stage) (c.π.app stage.left) := by
  have hsnd : (modelCone D i₀ M c).π.app stage ≫ pullback.snd (D.map stage.hom) M.hom =
      pullback.snd (c.π.app i₀) M.hom := pullback.lift_snd _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map stage.hom) M.hom)
    (h₂₂ := D.map stage.hom) (v₁₃ := M.hom) ?_ ?_
    (IsPullback.of_hasPullback (D.map stage.hom) M.hom).flip
  · show IsPullback ((modelCone D i₀ M c).π.app stage ≫ pullback.snd (D.map stage.hom) M.hom)
        (pullback.fst (c.π.app i₀) M.hom) M.hom (c.π.app stage.left ≫ D.map stage.hom)
    rw [hsnd, c.w]
    exact (IsPullback.of_hasPullback (c.π.app i₀) M.hom).flip
  · show pullback.lift (pullback.fst (c.π.app i₀) M.hom ≫ c.π.app stage.left)
      (pullback.snd (c.π.app i₀) M.hom) _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _

variable {D i₀ M}

/-- **A scheme exhibited as a base change of the model is the vertex of the cone over the
diagram of base changes.** -/
noncomputable def modelLimitIso (c : Cone D) {X : Scheme.{u}} (q : X ⟶ M.left) (g : X ⟶ c.pt)
    (sq : IsPullback q g M.hom (c.π.app i₀)) : X ≅ (modelCone D i₀ M c).pt :=
  sq.flip.isoPullback

/-- The isomorphism `modelLimitIso c q g sq` followed by the first projection of the pullback
is `g`. -/
@[reassoc (attr := simp)] theorem modelLimitIso_hom_comp_fst (c : Cone D)
    {X : Scheme.{u}} (q : X ⟶ M.left)
    (g : X ⟶ c.pt) (sq : IsPullback q g M.hom (c.π.app i₀)) :
    (modelLimitIso c q g sq).hom ≫ pullback.fst (c.π.app i₀) M.hom = g :=
  sq.flip.isoPullback_hom_fst

/-- The isomorphism `modelLimitIso c q g sq` followed by the second projection of the pullback
is `q`. -/
@[reassoc (attr := simp)] theorem modelLimitIso_hom_comp_snd (c : Cone D)
    {X : Scheme.{u}} (q : X ⟶ M.left)
    (g : X ⟶ c.pt) (sq : IsPullback q g M.hom (c.π.app i₀)) :
    (modelLimitIso c q g sq).hom ≫ pullback.snd (c.π.app i₀) M.hom = q :=
  sq.flip.isoPullback_hom_snd

/-- The leg `modelLimitIso c q g sq ≫ (modelCone D i₀ M c).π.app stage` of a base change of the
model sits in a cartesian square over `g` and the leg of `c` at the stage. -/
private theorem isPullback_modelLimitIso_comp_modelCone_π (c : Cone D) {X : Scheme.{u}}
    (q : X ⟶ M.left) (g : X ⟶ c.pt) (sq : IsPullback q g M.hom (c.π.app i₀))
    (stage : Over i₀) :
    IsPullback ((modelLimitIso c q g sq).hom ≫ (modelCone D i₀ M c).π.app stage) g
      ((modelProjection D i₀ M).app stage) (c.π.app stage.left) := by
  refine (modelCone_isPullback D i₀ M c stage).of_iso' (modelLimitIso c q g sq)
    (.refl _) (.refl _) (.refl _) (by rw [Iso.refl_hom, Category.comp_id]) ?_
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) (by simp)
  rw [Iso.refl_hom, Category.comp_id]
  exact modelLimitIso_hom_comp_fst c q g sq

variable (D i₀ M)

/-- **[Stacks, Tag 05M5] at a model.** If the base change of the model to the limit has all
fibres of dimension at most `d`, then so does its base change to some stage. -/
theorem exists_forall_topologicalKrullDim_fiber_le_modelProjection [IsCofiltered I]
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)] [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] [IsProper M.hom]
    (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}} (q : X ⟶ M.left) (g : X ⟶ c.pt)
    (sq : IsPullback q g M.hom (c.π.app i₀)) (d : ℕ)
    (hdim : ∀ y : c.pt, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ stage : Over i₀, ∀ s : D.obj stage.left,
      topologicalKrullDim (((modelProjection D i₀ M).app stage).fiber s) ≤ (d : WithBot ℕ∞) := by
  set source := modelDiagram D i₀ M
  set target := Over.forget i₀ ⋙ D
  set projection := modelProjection D i₀ M
  have htraff : ∀ {stage next : Over i₀} (t : stage ⟶ next), IsAffineHom (target.map t) :=
    fun t => inferInstanceAs (IsAffineHom (D.map t.left))
  have htcpt : ∀ stage : Over i₀, CompactSpace (target.obj stage) :=
    fun stage => inferInstanceAs (CompactSpace (D.obj stage.left))
  have htqs : ∀ stage : Over i₀, QuasiSeparatedSpace (target.obj stage) :=
    fun stage => inferInstanceAs (QuasiSeparatedSpace (D.obj stage.left))
  have hproper : ∀ stage : Over i₀, IsProper (projection.app stage) :=
    fun stage => inferInstanceAs (IsProper (pullback.fst (D.map stage.hom) M.hom))
  have hft : ∀ stage : Over i₀, LocallyOfFiniteType (projection.app stage) :=
    fun stage => (hproper stage).toLocallyOfFiniteType
  have hqc : ∀ stage : Over i₀, QuasiCompact (projection.app stage) :=
    fun stage => have := hproper stage; inferInstance
  have htrans : ∀ {stage next : Over i₀} (t : stage ⟶ next),
      IsClosedImmersion (pullback.lift (source.map t) (projection.app stage)
        (projection.naturality t)) := by
    intro stage next t
    have square := modelTransition_isPullback D i₀ M t
    have equality : pullback.lift (source.map t) (projection.app stage)
        (projection.naturality t) = square.isoPullback.hom :=
      pullback.hom_ext ((pullback.lift_fst _ _ _).trans square.isoPullback_hom_fst.symm)
        ((pullback.lift_snd _ _ _).trans square.isoPullback_hom_snd.symm)
    rw [equality]
    infer_instance
  set sourceCone := (modelCone D i₀ M c).extend (modelLimitIso c q g sq).hom
  set targetCone := c.whisker (Over.forget i₀)
  have hslim : IsLimit sourceCone := IsLimit.extendIso _ (modelConeIsLimit D i₀ M c hc)
  have htlim : IsLimit targetCone :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc
  have hlift : htlim.lift ((Cone.postcompose projection).obj sourceCone) = g := by
    refine htlim.hom_ext fun stage => ?_
    rw [htlim.fac]
    show (modelLimitIso c q g sq).hom ≫ (modelCone D i₀ M c).π.app stage ≫
      projection.app stage = g ≫ c.π.app stage.left
    rw [(modelCone_isPullback D i₀ M c stage).w]
    exact modelLimitIso_hom_comp_fst_assoc c q g sq _
  exact AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
    source target projection sourceCone hslim targetCone htlim d (by rwa [hlift])

/-! ### The Noetherian model -/

section Model

/-- **Steps one and two of paragraph four**: a proper model of finite presentation over a stage,
together with a finitely presented module on it pulling back to the given one. The model is
produced by [Stacks, Tags 01ZM and 081F] and then replaced by its base change to a later stage
at which the module descends, which is [Stacks, Tag 01ZR] applied to the diagram of base
changes of the first model. -/
theorem exists_model_isPullback_of_isFinitePresentation [IsCofiltered I]
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)] [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}} (g : X ⟶ c.pt) [IsProper g]
    (hfp : AlgebraicGeometry.FinitePresentation g)
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ (i : I) (M : Over (D.obj i)) (_ : IsProper M.hom)
      (_ : AlgebraicGeometry.FinitePresentation M.hom) (q : X ⟶ M.left)
      (Gm : M.left.Modules) (_ : Gm.IsFinitePresentation),
      IsPullback q g M.hom (c.π.app i) ∧
        Nonempty (G ≅ (Scheme.Modules.pullback q).obj Gm) := by
  classical
  have hgOver : IsProper (Over.mk g).hom := inferInstanceAs (IsProper g)
  obtain ⟨j, Mj, hMjfp, hMjpr, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc
      (Over.mk g) hfp
  have := hMjpr
  have hsq : IsPullback (e.hom.left ≫ pullback.fst Mj.hom (c.π.app j)) g Mj.hom (c.π.app j) := by
    refine (IsPullback.of_hasPullback Mj.hom (c.π.app j)).of_iso'
      ((Over.forget _).mapIso e) (.refl _) (.refl _) (.refl _) (by simp) ?_ (by simp) (by simp)
    simpa using e.hom.w
  have htraff' : ∀ {s t : Over j} (v : s ⟶ t), IsAffineHom ((modelDiagram D j Mj).map v) :=
    fun v => MorphismProperty.of_isPullback (P := @IsAffineHom)
      (modelTransition_isPullback D j Mj v).flip inferInstance
  have hcptt : ∀ s : Over j, CompactSpace ((Over.forget j ⋙ D).obj s) :=
    fun s => inferInstanceAs (CompactSpace (D.obj s.left))
  have hqst : ∀ s : Over j, QuasiSeparatedSpace ((Over.forget j ⋙ D).obj s) :=
    fun s => inferInstanceAs (QuasiSeparatedSpace (D.obj s.left))
  have hprj : ∀ s : Over j, IsProper ((modelProjection D j Mj).app s) :=
    fun s => inferInstanceAs (IsProper (pullback.fst (D.map s.hom) Mj.hom))
  have hcpt' : ∀ s : Over j, CompactSpace ((modelDiagram D j Mj).obj s) := by
    intro s
    have := hprj s
    exact (quasiCompact_iff_compactSpace ((modelProjection D j Mj).app s)).mp inferInstance
  have hqs' : ∀ s : Over j, QuasiSeparatedSpace ((modelDiagram D j Mj).obj s) := by
    intro s
    have := hprj s
    exact quasiSeparatedSpace_of_quasiSeparated ((modelProjection D j Mj).app s)
  set sourceCone := (modelCone D j Mj c).extend
    (modelLimitIso c (e.hom.left ≫ pullback.fst Mj.hom (c.π.app j)) g hsq).hom
  have hslim : IsLimit sourceCone := IsLimit.extendIso _ (modelConeIsLimit D j Mj c hc)
  obtain ⟨stage, Gst, hGst, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      (modelDiagram D j Mj) sourceCone hslim G
  refine ⟨stage.left, Over.mk ((modelProjection D j Mj).app stage), hprj stage, ?_,
    sourceCone.π.app stage, Gst, hGst, ?_, ⟨eG⟩⟩
  · obtain ⟨_, _, _⟩ := hMjfp
    exact (⟨inferInstanceAs (LocallyOfFinitePresentation
          (pullback.fst (D.map stage.hom) Mj.hom)),
        inferInstanceAs (QuasiCompact (pullback.fst (D.map stage.hom) Mj.hom)),
        inferInstanceAs (QuasiSeparated (pullback.fst (D.map stage.hom) Mj.hom))⟩ :
      AlgebraicGeometry.FinitePresentation (pullback.fst (D.map stage.hom) Mj.hom))
  · exact isPullback_modelLimitIso_comp_modelCone_π c _ g hsq stage

/-- **Paragraph four of the proof of [Stacks, Tag 0EX4] over an affine base, without the
base-change identification.** A proper morphism `g : X ⟶ Y` of finite presentation onto an
affine base, all of whose fibres have dimension at most `d`, together with a finitely presented
`𝒪_X`-module `G`, is the base change of the same data over an **affine Noetherian** base. -/
theorem exists_noetherianModel {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    (hfp : AlgebraicGeometry.FinitePresentation g) [IsAffine Y] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞))
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ (X₀ S₀ : Scheme.{u}) (g₀ : X₀ ⟶ S₀) (_ : IsProper g₀)
      (_ : AlgebraicGeometry.FinitePresentation g₀) (_ : IsAffine S₀) (_ : IsNoetherian S₀),
      (∀ s : S₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) ∧
        ∃ (G₀ : X₀.Modules) (_ : G₀.IsFinitePresentation) (u : Y ⟶ S₀) (p : X ⟶ X₀),
          IsPullback p g g₀ u ∧ Nonempty (G ≅ (Scheme.Modules.pullback p).obj G₀) := by
  classical
  obtain ⟨J, _, _, _, DD, hpt, haff, _hft⟩ :=
    AlgebraicGeometry.exists_limitNoetherianSituation_of_isAffine Y
  subst hpt
  set D := DD.system
  set c := DD.limitCone
  have hc : IsLimit c := DD.isLimit
  have hnoeth : ∀ i : Jᵒᵖ, IsNoetherian (D.obj i) := fun i => DD.noetherian i.unop
  have htraff : ∀ {i j : Jᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t) :=
    DD.transition_affine
  have hcpt : ∀ i : Jᵒᵖ, CompactSpace (D.obj i) := fun i => have := hnoeth i; inferInstance
  have hqs : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i => have := hnoeth i; inferInstance
  obtain ⟨i, M, hMpr, hMfp, q, Gm, hGm, hsq, ⟨eG⟩⟩ :=
    exists_model_isPullback_of_isFinitePresentation (D := D) c hc g hfp G
  have := hMpr
  obtain ⟨next, hnextdim⟩ :=
    exists_forall_topologicalKrullDim_fiber_le_modelProjection D i M c hc q g hsq d hdim
  set g₀ := (modelProjection D i M).app next
  set tr : (modelDiagram D i M).obj next ⟶ M.left :=
    pullback.snd (D.map next.hom) M.hom
  set p : X ⟶ (modelDiagram D i M).obj next :=
    (modelLimitIso c q g hsq).hom ≫ (modelCone D i M c).π.app next with hp
  have hnextsq : IsPullback p g g₀ (c.π.app next.left) :=
    isPullback_modelLimitIso_comp_modelCone_π c q g hsq next
  have hptr : p ≫ tr = q := by
    have hls : (modelCone D i M c).π.app next ≫ pullback.snd (D.map next.hom) M.hom =
        pullback.snd (c.π.app i) M.hom := pullback.lift_snd _ _ _
    rw [hp, Category.assoc, hls, modelLimitIso_hom_comp_snd]
  have hprop : IsProper g₀ := inferInstanceAs (IsProper (pullback.fst (D.map next.hom) M.hom))
  refine ⟨_, D.obj next.left, g₀, hprop, ?_, haff next.left.unop, hnoeth next.left, hnextdim,
    (Scheme.Modules.pullback tr).obj Gm, ?_, c.π.app next.left, p, hnextsq, ⟨?_⟩⟩
  · exact ⟨inferInstance, inferInstance, inferInstance⟩
  · exact Stacks.Modules.isFinitePresentation_pullback tr Gm hGm
  · exact eG ≪≫ eqToIso (by rw [hptr]) ≪≫ ((Scheme.Modules.pullbackComp p tr).app Gm).symm

end Model

end Stacks.AlgebraicGeometry.NoetherianModel

end
