module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent

/-!
# A Noetherian model of a proper morphism with bounded fibre dimension, and of a module on it

This file is the third paragraph of the proof of [Stacks, Tag 0EX4]. Over an affine base `Y`, a
proper morphism `f : X ⟶ Y` of finite presentation all of whose fibres have dimension at most
`d`, together with an `𝒪_X`-module `F` of finite presentation, is the base change of the same
data over an affine **Noetherian** base.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.exists_stage_properModel`: the model over a
  stage of the canonical Noetherian presentation of the affine base, with the fibre-dimension
  bound. This is the paragraph, stated at the particular presentation it is proved at.
* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.exists_noetherianModel_of_morphism`: the same
  conclusion with the stage forgotten, as a cartesian square over an affine locally Noetherian
  base.
* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.exists_noetherianModel`: the same, carrying in
  addition a module of finite presentation on the model which pulls back to `F`.

## Implementation notes

The base presentation is **not** absolute Noetherian approximation, [Stacks, Tag 01ZA], whose
stages need not be affine. It is the elementary presentation of an affine scheme,
`AlgebraicGeometry.affineStageCone`: `Y = lim Spec ℤ[i]` over the finite subsets `i` of
`Γ(Y, ⊤)`, whose stages are affine and Noetherian, with affine transition morphisms. That is
what makes `Y₀` affine as well as locally Noetherian, which is what the finiteness theorem
[Stacks, Tag 02O6] downstream asks for.

Over that presentation the paragraph is the composite of three descent statements, each
"after increasing the index":

* [Stacks, Tag 01ZM] part (1) followed by [Stacks, Tag 01ZQ] and [Stacks, Tag 081F], packaged as
  `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`, produces a proper
  model of finite presentation over a stage;
* [Stacks, Tag 05M5], in the shape
  `AlgebraicGeometry.exists_fiberDimensionLE_baseChange_of_limitBaseChange`, moves the
  fibre-dimension bound to a later stage; replacing the model by its base change there keeps
  finite presentation and properness, and keeps the identification with `X`;
* [Stacks, Tag 01ZR] part (1), in the shape
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`,
  descends the module. It is applied not to the system of bases but to the system
  `AlgebraicGeometry.baseChangeDiagram` of base changes of the model to the later stages, whose
  limit is `X` by `AlgebraicGeometry.baseChangeConeIsLimit` and whose transition morphisms are
  affine because those of the base are; the fibre-dimension bound is then transported to the
  final stage along `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_isPullback`, which is
  [Stacks, Tag 02FY].

The order matters: the module is descended *last* among the three steps that produce an index,
because the dimension bound is only invariant under base change through Tag 02FY, whereas
properness and finite presentation are formally stable under base change. Equivalently, the
dimension step is performed before the module step and its conclusion is transported once.

Everything is stated for `IsPullback` squares rather than for isomorphisms in an overcategory.
The reason is mechanical: the source of `(affineStageCone Y).π.app j` is
`((Functor.const _).obj (affineStageCone Y).pt).obj j`, which is `Y` only up to unfolding, so an
isomorphism in `CategoryTheory.Over Y` built from it is not type-correct at `implicit`
transparency and `rw` refuses to work under it. `CategoryTheory.IsPullback.isoPullback` converts
the square back into the isomorphism where one is needed.

**No `@[stacks 0EX4]` attribute is attached.** This is one paragraph of the proof of that tag,
not the tag; nor is any input tag claimed here, each being quoted from the declaration that
carries it.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

/-- Precomposing a cartesian square with an isomorphism of its corner keeps it cartesian. This is
stated separately because at its only use the square involves legs of a cone, whose source Lean
records as `((CategoryTheory.Functor.const _).obj _).obj _`; inside a lemma with ordinary
variables every type is written out and the rewrites go through. -/
private lemma isPullback_iso_comp {C : Type*} [Category C] {W P A B Z : C}
    {t : P ⟶ A} {p : P ⟶ B} {q : A ⟶ Z} {r : B ⟶ Z} (h : IsPullback t p q r)
    (i : W ≅ P) {p' : W ⟶ B} (hp : i.hom ≫ p = p') :
    IsPullback (i.hom ≫ t) p' q r := by
  subst hp
  have := h.hasPullback
  refine IsPullback.of_iso_pullback ⟨by rw [Category.assoc, h.w, ← Category.assoc]⟩
    (i ≪≫ h.isoPullback) ?_ ?_
  · rw [Iso.trans_hom, Category.assoc, h.isoPullback_hom_fst]
  · rw [Iso.trans_hom, Category.assoc, h.isoPullback_hom_snd]

/-- The source of a morphism of finite presentation over a compact quasi-separated space is
compact and quasi-separated. -/
private lemma compactSpace_and_quasiSeparatedSpace_of_finitePresentation {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] (g : X ⟶ Y)
    (hg : AlgebraicGeometry.FinitePresentation g) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have : QuasiCompact g := hg.2.1
  have : QuasiSeparated g := hg.2.2
  exact ⟨QuasiCompact.compactSpace_of_compactSpace g, quasiSeparatedSpace_of_quasiSeparated g⟩

/-! ### The model over a stage of the Noetherian presentation of the base -/

/-- **The third paragraph of the proof of [Stacks, Tag 0EX4], at the presentation it is proved
at.** Let `f : X ⟶ Y` be proper and of finite presentation over an affine base, with every fibre
of dimension at most `d`. Then for some finite subset `j` of `Γ(Y, ⊤)` there is a scheme `Xⱼ`
over `Spec ℤ[j]`, proper and of finite presentation over it and with every fibre of dimension at
most `d`, whose base change along the projection `Y ⟶ Spec ℤ[j]` is `f`. -/
theorem exists_stage_properModel {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hfp : AlgebraicGeometry.FinitePresentation f) [IsAffine Y] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (j : (Finset Γ(Y, ⊤))ᵒᵖ)
      (Xⱼ : Over ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j)) (h : X ⟶ Xⱼ.left),
      AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧
        (∀ s : ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j),
          topologicalKrullDim (Xⱼ.hom.fiber s) ≤ (d : WithBot ℕ∞)) ∧
        IsPullback h f Xⱼ.hom ((affineStageCone Y).π.app j) := by
  -- Tag 01ZM part (1), Tag 01ZQ and Tag 081F: a proper model of finite presentation.
  obtain ⟨j₀, X₀, hfp₀, hpr₀, ⟨e₀⟩⟩ :=
    @exists_isProper_finitePresentation_model_of_isLimit _ _ _
      (specAdjoinFinsetDiagram Γ(Y, ⊤)) _ _ _
      (affineStageCone Y) (isLimit_affineStageCone Y) (Over.mk f) ‹IsProper f› hfp
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_finitePresentation X₀.hom hfp₀
  have _ : IsProper X₀.hom := hpr₀
  have _ : CompactSpace
      (Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀))).left :=
    inferInstanceAs (CompactSpace ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀))
  have _ : QuasiSeparatedSpace
      (Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀))
  have _ : LocallyOfFiniteType
      (Over.homMk X₀.hom (Category.comp_id X₀.hom) :
        X₀ ⟶ Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀))).left :=
    inferInstanceAs (LocallyOfFiniteType X₀.hom)
  -- The fibre-dimension bound at the limit, in the shape Tag 05M5 takes.
  have hlim : fiberDimensionLE d
      ((Over.pullback ((affineStageCone Y).π.app j₀)).map
        (Over.homMk X₀.hom (Category.comp_id X₀.hom) :
          X₀ ⟶ Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀)))).left :=
    (overPullback_map_terminal_iff (fiberDimensionLE d) _ X₀).mpr <|
      prop_of_overIso (fiberDimensionLE d) e₀
        ((fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le f d).mpr hdim)
  -- Tag 05M5: the bound already holds at a later stage.
  obtain ⟨j, a, hdim₁⟩ :=
    exists_fiberDimensionLE_baseChange_of_limitBaseChange (specAdjoinFinsetDiagram Γ(Y, ⊤))
      (isLimit_affineStageCone Y) j₀ X₀
      (Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j₀)))
      (Over.homMk X₀.hom (Category.comp_id X₀.hom)) d hlim
  set Xⱼ : Over ((specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j) :=
    (Over.pullback ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a)).obj X₀
  have e : Over.mk f ≅ (Over.pullback ((affineStageCone Y).π.app j)).obj Xⱼ :=
    e₀ ≪≫ overPullbackObj_shiftIso (specAdjoinFinsetDiagram Γ(Y, ⊤)) (affineStageCone Y) a X₀
  have hew : e.hom.left ≫ pullback.snd Xⱼ.hom ((affineStageCone Y).π.app j) = f := Over.w e.hom
  have hcomm : (e.hom.left ≫ pullback.fst Xⱼ.hom ((affineStageCone Y).π.app j)) ≫ Xⱼ.hom =
      f ≫ (affineStageCone Y).π.app j := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ (affineStageCone Y).π.app j) hew
  refine ⟨j, Xⱼ, e.hom.left ≫ pullback.fst Xⱼ.hom ((affineStageCone Y).π.app j),
    finitePresentation_overPullbackObj _ X₀ hfp₀, ?_, ?_,
    IsPullback.of_iso_pullback ⟨hcomm⟩ ((Over.forget Y).mapIso e) rfl hew⟩
  · change IsProper (pullback.snd X₀.hom ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a))
    infer_instance
  · exact (fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le _ d).mp
      ((overPullback_map_terminal_iff (fiberDimensionLE d) _ X₀).mp hdim₁)

/-! ### The two statements of the paragraph -/

/-- **The third paragraph of the proof of [Stacks, Tag 0EX4], without the module.** Over an
affine base, a proper morphism of finite presentation with fibres of dimension at most `d` is the
base change of a proper morphism with fibres of dimension at most `d` over an affine locally
Noetherian base. -/
theorem exists_noetherianModel_of_morphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    [IsAffine Y] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ (Y₀ X₀ : Scheme.{u}) (g : X₀ ⟶ Y₀) (u : Y ⟶ Y₀) (h : X ⟶ X₀),
      IsAffine Y₀ ∧ IsLocallyNoetherian Y₀ ∧ IsProper g ∧
        (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) ∧ IsPullback h f g u := by
  obtain ⟨j, Xⱼ, h, -, hprⱼ, hdimⱼ, hpb⟩ := exists_stage_properModel f hfp d hdim
  exact ⟨(specAdjoinFinsetDiagram Γ(Y, ⊤)).obj j, Xⱼ.left, Xⱼ.hom,
    (affineStageCone Y).π.app j, h, inferInstance, inferInstance, hprⱼ, hdimⱼ, hpb⟩

/-- **The third paragraph of the proof of [Stacks, Tag 0EX4].** Over an affine base, a proper
morphism of finite presentation with fibres of dimension at most `d`, together with a module of
finite presentation, is the base change of the same data over an affine locally Noetherian
base. -/
theorem exists_noetherianModel
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    [IsAffine Y] (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (Y₀ X₀ : Scheme.{u}) (g : X₀ ⟶ Y₀) (u : Y ⟶ Y₀) (h : X ⟶ X₀) (F₀ : X₀.Modules),
      IsAffine Y₀ ∧ IsLocallyNoetherian Y₀ ∧ IsProper g ∧
        (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) ∧
        F₀.IsFinitePresentation ∧ IsPullback h f g u ∧
        Nonempty (F ≅ (Scheme.Modules.pullback h).obj F₀) := by
  obtain ⟨j, Xⱼ, hmap, hfpⱼ, hprⱼ, hdimⱼ, hpbⱼ⟩ := exists_stage_properModel f hfp d hdim
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_finitePresentation Xⱼ.hom hfpⱼ
  have _ : IsProper Xⱼ.hom := hprⱼ
  -- `X` is the base change of `Xⱼ` to the limit, so it is the limit of the base changes of `Xⱼ`
  -- to the later stages.
  let ι : X ≅ pullback ((affineStageCone Y).π.app j) Xⱼ.hom := hpbⱼ.flip.isoPullback
  let cE : Cone (baseChangeDiagram (specAdjoinFinsetDiagram Γ(Y, ⊤)) j Xⱼ) :=
    (baseChangeCone (specAdjoinFinsetDiagram Γ(Y, ⊤)) (affineStageCone Y) j Xⱼ).extend ι.hom
  have hcE : IsLimit cE :=
    IsLimit.ofIsoLimit
      (baseChangeConeIsLimit (specAdjoinFinsetDiagram Γ(Y, ⊤)) (isLimit_affineStageCone Y) j Xⱼ)
      (Cone.extendIso
        (baseChangeCone (specAdjoinFinsetDiagram Γ(Y, ⊤)) (affineStageCone Y) j Xⱼ) ι.symm)
  have _ : ∀ {p q : Over j} (t : p ⟶ q),
      IsAffineHom ((baseChangeDiagram (specAdjoinFinsetDiagram Γ(Y, ⊤)) j Xⱼ).map t) :=
    fun t => isAffineHom_baseChangeDiagram_map _ j Xⱼ t
  have _ : ∀ p : Over j,
      CompactSpace ((baseChangeDiagram (specAdjoinFinsetDiagram Γ(Y, ⊤)) j Xⱼ).obj p) :=
    compactSpace_baseChangeDiagram_obj _ j Xⱼ
  have _ : ∀ p : Over j,
      QuasiSeparatedSpace ((baseChangeDiagram (specAdjoinFinsetDiagram Γ(Y, ⊤)) j Xⱼ).obj p) :=
    quasiSeparatedSpace_baseChangeDiagram_obj _ j Xⱼ
  -- Tag 01ZR part (1): the module comes from a stage of that system.
  obtain ⟨a, F₀, hF₀, ⟨eF⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      (baseChangeDiagram (specAdjoinFinsetDiagram Γ(Y, ⊤)) j Xⱼ) cE hcE
      (show cE.pt.Modules from F)
  have hright : IsPullback (pullback.snd ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom)
      (pullback.fst ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom) Xⱼ.hom
      ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) :=
    (IsPullback.of_hasPullback _ _).flip
  -- The leg of the cone at the chosen stage, with the source of its type written out: the source
  -- Lean records is `((Functor.const _).obj _).obj a`, which nothing may be composed into.
  let leg : pullback ((affineStageCone Y).π.app j) Xⱼ.hom ⟶
      pullback ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom :=
    (baseChangeCone (specAdjoinFinsetDiagram Γ(Y, ⊤)) (affineStageCone Y) j Xⱼ).π.app a
  have hlegfst : leg ≫ pullback.fst ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom =
      pullback.fst ((affineStageCone Y).π.app j) Xⱼ.hom ≫ (affineStageCone Y).π.app a.left :=
    baseChangeTransition_fst ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom)
      ((affineStageCone Y).π.app j) ((affineStageCone Y).π.app a.left)
      ((affineStageCone Y).w a.hom) Xⱼ
  have hlegsnd : leg ≫ pullback.snd ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom =
      pullback.snd ((affineStageCone Y).π.app j) Xⱼ.hom :=
    baseChangeTransition_snd ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom)
      ((affineStageCone Y).π.app j) ((affineStageCone Y).π.app a.left)
      ((affineStageCone Y).w a.hom) Xⱼ
  have hsq : IsPullback leg
      (pullback.fst ((affineStageCone Y).π.app j) Xⱼ.hom)
      (pullback.fst ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom)
      ((affineStageCone Y).π.app a.left) := by
    refine IsPullback.of_right ?_ hlegfst hright
    rw [hlegsnd, (affineStageCone Y).w a.hom]
    exact (IsPullback.of_hasPullback _ _).flip
  exact ⟨(specAdjoinFinsetDiagram Γ(Y, ⊤)).obj a.left,
    pullback ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom,
    pullback.fst ((specAdjoinFinsetDiagram Γ(Y, ⊤)).map a.hom) Xⱼ.hom,
    (affineStageCone Y).π.app a.left, ι.hom ≫ leg, F₀,
    inferInstance, inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hright hprⱼ,
    fun s => (topologicalKrullDim_fiber_eq_of_isPullback hright s).trans_le (hdimⱼ _), hF₀,
    isPullback_iso_comp hsq ι hpbⱼ.flip.isoPullback_hom_fst, ⟨eF⟩⟩

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
