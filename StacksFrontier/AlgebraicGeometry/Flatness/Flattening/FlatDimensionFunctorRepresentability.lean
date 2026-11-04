module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatDimensionTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.UniversallyInjectiveStage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsCoproduct
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsRepresentability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic

/-!
# Representability of the flat-dimension functor near a point

In Situation 05MT the functor `F_n` of Stacks 05MU sends a scheme `T` over `S` to a singleton
exactly when the base change `F_T` is flat over `T` in dimensions `≥ n`. Tag 05UF asserts that,
if `F/X/S` has a complete dévissage over a point `s`, `X` is of finite presentation over `S`, `F`
is of finite presentation and `F` is flat over `S` in dimensions `≥ d + 1`, then after replacing
`S` by an open neighbourhood of `s` the functor `F_d` is representable by a monomorphism
`Z_d ⟶ S` of finite presentation.

## Main definitions

* `AlgebraicGeometry.FlatDimensionSituation.openFlatDimensionFunctor`: the functor `F_n` read
  on schemes over an open subscheme of the base.
* `AlgebraicGeometry.FlatDimensionSituation.FactorizationCriterion`: the elementary form of
  the representability assertion, a morphism into the open through which exactly the flat base
  changes factor.
* `AlgebraicGeometry.IsRepresentableNear`: a condition on schemes over `S` is represented, over
  an open neighbourhood of `s` inside a prescribed open, by a monomorphism of finite
  presentation.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.representableByOfFactorizationCriterion` and
  `AlgebraicGeometry.FlatDimensionSituation.factorizationCriterion_of_representableBy`: the
  factorization criterion is an exact reformulation of representability.
* `AlgebraicGeometry.DevissageChain.isRepresentableNear`: the dévissage induction of the source.
* `AlgebraicGeometry.FlatDimensionSituation.exists_mono_finitePresentation_representableBy`:
  **Stacks 05UF**.

## Implementation notes

Restriction to an open neighbourhood is expressed by precomposition with `Over.map U.ι` rather
than by restricting the whole situation: the two give the same functor on schemes over `U`,
because the base change of `F` to a scheme over `U` depends only on its structure morphism to
`S`.

The induction runs over the chain of a complete dévissage (`AlgebraicGeometry.DevissageChain`).
Its statement keeps the base `S` and records the flatness hypothesis only over an open `V` of
`S` containing `s`, in the form `AlgebraicGeometry.IsFlatOverInDimensionsGEOn`, so that the base
may be shrunk without restricting the dévissage: the source's "replace `S` by an affine
neighbourhood of `s`" becomes "replace `V` by a smaller open containing `s`". At each stage the
module is replaced by `π_* G` on the smooth scheme `Y` of the stage
(`AlgebraicGeometry.OneStepDevissage.isFlatOverInDimensionsGEOn_baseChange_iff`), and the three
cases of the source are separated by comparing the relative dimension `d₁` of `Y` over `S` with
`d`: when `d₁ < d` every base change is flat in dimensions `≥ d`, so `F_d` is the whole base;
when `d₁ = d`, `F_d` is the finite coproduct of the strata of Stacks 05UC
(`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_mono_baseChangeFlatInDimensionsGE`);
when `d₁ > d`, Stacks 05IA shrinks the base so that `π_* G` and the cokernel of the free map of
the stage are flat at the same points after every base change
(`AlgebraicGeometry.DevissageStage.exists_basicOpen_of_lt`), and the induction hypothesis applies
to the rest of the dévissage. Finite presentation of the representing monomorphism is part of
each case, so it is produced by the induction and not assumed.

## References

* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 05MU](https://stacks.math.columbia.edu/tag/05MU)
* [Stacks Project, Tag 05HH](https://stacks.math.columbia.edu/tag/05HH)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05UE](https://stacks.math.columbia.edu/tag/05UE)
* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A condition `P` on schemes over `S` is *represented near `s` inside `V`* if there are an open
`U ⊆ V` containing `s` and a monomorphism `i : Z ⟶ U` of finite presentation through which a
scheme over `U` factors exactly when it satisfies `P`. -/
def IsRepresentableNear {S : Scheme.{u}} (P : Over S → Prop) (s : S) (V : S.Opens) : Prop :=
  ∃ U : S.Opens, U ≤ V ∧ s ∈ U ∧ ∃ (Z : Scheme.{u}) (i : Z ⟶ U.toScheme),
    Mono i ∧ FinitePresentation i ∧
      ∀ T : Over U.toScheme, P ((Over.map U.ι).obj T) ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom

namespace IsRepresentableNear

variable {S : Scheme.{u}} {P Q : Over S → Prop} {s : S} {V : S.Opens}

/-- Representability near a point transfers between two conditions which agree on the schemes
over `V`. -/
theorem congr (h : IsRepresentableNear P s V)
    (hPQ : ∀ T : Over S, (∀ t, T.hom t ∈ V) → (P T ↔ Q T)) : IsRepresentableNear Q s V := by
  obtain ⟨U, hUV, hs, Z, i, hi, hfp, hcrit⟩ := h
  exact ⟨U, hUV, hs, Z, i, hi, hfp,
    fun T ↦ (hPQ _ fun t ↦ hUV (T.hom t).2).symm.trans (hcrit T)⟩

/-- Representability near a point inside an open gives it inside every larger open. -/
theorem mono_open (h : IsRepresentableNear P s V) {V' : S.Opens} (hV : V ≤ V') :
    IsRepresentableNear P s V' := by
  obtain ⟨U, hUV, hs, Z, i, hi, hfp, hcrit⟩ := h
  exact ⟨U, hUV.trans hV, hs, Z, i, hi, hfp, hcrit⟩

end IsRepresentableNear

/-- A condition satisfied by every scheme over `V` is represented near any point of `V`, by the
identity of `V`. -/
theorem isRepresentableNear_of_forall {S : Scheme.{u}} {P : Over S → Prop} {s : S}
    {V : S.Opens} (hs : s ∈ V) (hP : ∀ T : Over S, (∀ t, T.hom t ∈ V) → P T) :
    IsRepresentableNear P s V := by
  refine ⟨V, le_rfl, hs, V.toScheme, 𝟙 _, inferInstance,
    FinitePresentation.mk inferInstance inferInstance inferInstance,
    fun T ↦ ⟨fun _ ↦ ⟨T.hom, Category.comp_id _⟩, fun _ ↦ hP _ fun t ↦ (T.hom t).2⟩⟩

/-- A condition represented over the whole base by a monomorphism of finite presentation is
represented near any point inside any open, by the restriction of that monomorphism. -/
theorem isRepresentableNear_of_global {S : Scheme.{u}} {P : Over S → Prop} {s : S}
    {V : S.Opens} (hs : s ∈ V) {Z : Scheme.{u}} (i : Z ⟶ S) [Mono i]
    (hfp : FinitePresentation i) (hP : ∀ T : Over S, P T ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom) :
    IsRepresentableNear P s V := by
  obtain ⟨_, _, _⟩ := hfp
  refine ⟨V, le_rfl, hs, pullback i V.ι, pullback.snd i V.ι, inferInstance,
    FinitePresentation.mk inferInstance inferInstance inferInstance, fun T ↦ ?_⟩
  rw [hP]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨pullback.lift g T.hom hg, pullback.lift_snd _ _ _⟩
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ pullback.fst i V.ι, ?_⟩
    show _ = T.hom ≫ V.ι
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg]

/-- The base change of the zero module is flat in all dimensions: every stalk of the pullback of
the zero module vanishes. -/
theorem baseChangeFlatInDimensionsGE_of_isZero {X S : Scheme.{u}} (f : X ⟶ S) {F : X.Modules}
    (hF : IsZero F) (n : ℕ) (T : Over S) : BaseChangeFlatInDimensionsGE f F n T := by
  intro x _ hx
  refine (hx (isFlatOverAt_of_subsingleton_stalk _ _ x ?_)).elim
  have hz := Functor.map_isZero (Scheme.Modules.pullback (pullback.fst f T.hom)) hF
  have : PreservesFiniteColimits
      (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    (Scheme.Modules.presheafStalk_preservesFiniteLimitsAndColimits x).2
  have hz' := Functor.map_isZero
    (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hz
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hz'

/-- The base change of the zero module is represented near any point of `V`, by the identity of
`V`. -/
private theorem isRepresentableNear_of_isZero {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    (hF : IsZero F) (n : ℕ) {s : S} {V : S.Opens} (hs : s ∈ V) :
    IsRepresentableNear (BaseChangeFlatInDimensionsGE f F n) s V :=
  isRepresentableNear_of_forall hs fun T _ ↦ baseChangeFlatInDimensionsGE_of_isZero _ hF n T

namespace DevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {F : X.Modules}
  [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

attribute [local instance] OneStepDevissage.quasi_coherent_G OneStepDevissage.finite_type_G
  OneStepDevissage.closed_immersion OneStepDevissage.finite OneStepDevissage.smooth

/-- The smooth scheme of a stage is of finite presentation over the base: it is smooth over it,
and both are affine. -/
theorem finitePresentation_g (stage : DevissageStage f F s) :
    FinitePresentation stage.oneStep.g := by
  have : IsAffine stage.oneStep.Y := stage.oneStep.affine_Y
  have : IsAffine S := stage.oneStep.affine_S
  exact FinitePresentation.mk inferInstance inferInstance inferInstance

/-- The cokernel of the free map of a stage is of finite presentation when `X` is of finite
presentation over `S` and `F` is of finite presentation: it is the cokernel of a map from a module
of finite type to `π_* G`, which is of finite presentation (Stacks 0H96). -/
theorem isFinitePresentation_coker (stage : DevissageStage f F s) (hf : FinitePresentation f)
    [F.IsFinitePresentation] : stage.coker.IsFinitePresentation := by
  have : LocallyOfFinitePresentation f := hf.1
  have := stage.oneStep.isFinitePresentation_pushforward
  exact Stacks.SheafOfModules.isFinitePresentation_cokernel stage.alpha

/-- **The case `d₁ < d` of Stacks 05UF.** If the fibres of the smooth scheme of a stage have
dimension less than `n`, then every base change of `π_* G` is flat in dimensions `≥ n`: its
non-flat points, like all its points, have transcendence degree less than `n` over the base. -/
theorem baseChangeFlatInDimensionsGE_of_lt (stage : DevissageStage f F s) (n : ℕ)
    (hlt : topologicalKrullDim (stage.oneStep.g.fiber s) < (n : WithBot ℕ∞)) (T : Over S) :
    BaseChangeFlatInDimensionsGE stage.oneStep.g
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) n T := by
  have hall : IsFlatOverInDimensionsGEOn stage.oneStep.g
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) n Set.univ := by
    intro y _ _
    refine toENat_trdeg_lt_of_topologicalKrullDim_fiber_lt stage.oneStep.g y n ?_
    rwa [stage.oneStep.fiber_dimension, ← stage.oneStep.fiber_dimension s]
  exact hall.of_isPullback (IsPullback.of_hasPullback stage.oneStep.g T.hom)

/-- **The case `d₁ = d` of Stacks 05UF**: Stacks 05UE together with Stacks 05UC. If the fibres
of the smooth scheme of a stage have dimension `n`, then `F_n` for `π_* G` is represented over the
whole base by a monomorphism of finite presentation, the coproduct of the strata `S_p`. -/
theorem exists_mono_of_eq (stage : DevissageStage f F s) (n : ℕ)
    (hf : FinitePresentation f) [F.IsFinitePresentation]
    (heq : topologicalKrullDim (stage.oneStep.g.fiber s) = (n : WithBot ℕ∞)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ S), Mono i ∧ FinitePresentation i ∧
      ∀ T : Over S, BaseChangeFlatInDimensionsGE stage.oneStep.g
        ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) n T ↔
          ∃ g : T.left ⟶ Z, g ≫ i = T.hom := by
  have : LocallyOfFinitePresentation f := hf.1
  have := stage.oneStep.isFinitePresentation_pushforward
  have : IsAffine S := stage.oneStep.affine_S
  have : IsAffine stage.oneStep.Y := stage.oneStep.affine_Y
  let E : FreeAtGenericPointsSituation.{u} :=
    { S := S
      X := stage.oneStep.Y
      f := stage.oneStep.g
      geometricallyIrreducibleFibers :=
        (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber stage.oneStep.g).mp
          stage.oneStep.geometrically_irreducible
      F := (Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G
      isFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _ }
  have : IsAffine E.S := stage.oneStep.affine_S
  have : QuasiCompact E.f := inferInstanceAs (QuasiCompact stage.oneStep.g)
  have : QuasiSeparated E.f := inferInstanceAs (QuasiSeparated stage.oneStep.g)
  have : E.F.IsFinitePresentation :=
    inferInstanceAs ((Scheme.Modules.pushforward stage.oneStep.π).obj
      stage.oneStep.G).IsFinitePresentation
  exact E.exists_mono_baseChangeFlatInDimensionsGE fun s' ↦
    (stage.oneStep.fiber_dimension s').trans ((stage.oneStep.fiber_dimension s).symm.trans heq)

/-- **One stage of the dévissage induction of Stacks 05UF.** Given the conclusion for the
cokernel of the free map of the stage, over every smaller open containing `s` over which the
cokernel is flat in dimensions `≥ n + 1`, the conclusion holds for `F`. -/
theorem isRepresentableNear (stage : DevissageStage f F s) (n : ℕ)
    (hf : FinitePresentation f) [F.IsFinitePresentation] {V : S.Opens} (hs : s ∈ V)
    (h : IsFlatOverInDimensionsGEOn f F (n + 1) V)
    (ih : ∀ V' : S.Opens, s ∈ V' → V' ≤ V →
      IsFlatOverInDimensionsGEOn stage.oneStep.g stage.coker (n + 1) V' →
        IsRepresentableNear (BaseChangeFlatInDimensionsGE stage.oneStep.g stage.coker n) s V') :
    IsRepresentableNear (BaseChangeFlatInDimensionsGE f F n) s V := by
  have : LocallyOfFinitePresentation f := hf.1
  set O := stage.oneStep
  set M := (Scheme.Modules.pushforward O.π).obj O.G
  have hM : IsFlatOverInDimensionsGEOn O.g M (n + 1) V :=
    (O.isFlatOverInDimensionsGEOn_iff (n + 1) V).1 h
  suffices hrep : IsRepresentableNear (BaseChangeFlatInDimensionsGE O.g M n) s V from
    hrep.congr fun T _ ↦ (O.isFlatOverInDimensionsGEOn_baseChange_iff T n Set.univ).symm
  rcases lt_trichotomy (topologicalKrullDim (O.g.fiber s)) (n : WithBot ℕ∞) with hlt | heq | hgt
  · exact isRepresentableNear_of_forall hs fun T _ ↦
      stage.baseChangeFlatInDimensionsGE_of_lt n hlt T
  · obtain ⟨Z, i, hi, hfp, hcrit⟩ := stage.exists_mono_of_eq n hf heq
    exact isRepresentableNear_of_global hs i hfp hcrit
  · obtain ⟨W, hsW, hiff, hC⟩ := stage.exists_basicOpen_of_lt n hf hs hM hgt
    refine ((ih (V ⊓ W) ⟨hs, hsW⟩ inf_le_left hC).congr fun T hT ↦ ?_).mono_open inf_le_left
    exact (hiff T fun t ↦ (hT t).2).symm

end DevissageStage

/-- **The dévissage induction of Stacks 05UF.** Let `F/X/S` have a complete dévissage over `s`
with at least one stage, let `X` be of finite presentation over `S` and `F` of finite
presentation. For every open `V` containing `s` over which `F` is flat in dimensions `≥ n + 1`,
the functor `F_n` is represented near `s` inside `V` by a monomorphism of finite presentation. -/
theorem DevissageChain.isRepresentableNear {S : Scheme.{u}} {s : S} (n : ℕ) {X : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} (c : DevissageChain s X f F hl hq ht) (hf : FinitePresentation f)
    (hF : F.IsFinitePresentation) {V : S.Opens} (hs : s ∈ V)
    (h : IsFlatOverInDimensionsGEOn f F (n + 1) V) :
    IsRepresentableNear (BaseChangeFlatInDimensionsGE f F n) s V := by
  induction c generalizing V with
  | last stage hzero =>
    exact stage.isRepresentableNear n hf hs h fun V' hs' _ _ ↦
      isRepresentableNear_of_isZero hzero n hs'
  | more stage hcq hcf hgl tail ih =>
    exact stage.isRepresentableNear n hf hs h fun V' hs' _ hC ↦
      ih stage.finitePresentation_g (stage.isFinitePresentation_coker hf) hs' hC

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u}) (U : D.S.Opens)

/-- The functor `F_n` of Stacks 05MU read on schemes over an open subscheme `U` of the base: a
scheme over `U` is sent to the value of `F_n` at that same scheme regarded over `S`. -/
abbrev openFlatDimensionFunctor : (Over U.toScheme)ᵒᵖ ⥤ Type :=
  (Over.map U.ι).op ⋙ D.flatDimensionFunctor

/-- The functor `F_n` read over an open of the base is subterminal. -/
instance subsingleton_openFlatDimensionFunctor_obj (T : (Over U.toScheme)ᵒᵖ) :
    Subsingleton ((D.openFlatDimensionFunctor U).obj T) :=
  D.flatDimensionFunctor_obj_subsingleton _

/-- A value of `F_n` over `U` is nonempty exactly when the base change of the module to that
scheme over `U`, regarded over `S`, is flat in dimensions `≥ n`. -/
theorem nonempty_openFlatDimensionFunctor_obj_iff (T : Over U.toScheme) :
    Nonempty ((D.openFlatDimensionFunctor U).obj (Opposite.op T)) ↔
      D.IsFlatInDimensionsGEAfterBaseChange ((Over.map U.ι).obj T) :=
  ⟨fun h ↦ h.some.down, fun h ↦ ⟨⟨h⟩⟩⟩

/-- The elementary form of the representability assertion of Tag 05UF: a morphism
`i : Z ⟶ U` such that a scheme over `U` factors through `i` exactly when the base change of
the module to it is flat in dimensions `≥ n`. -/
abbrev FactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ U.toScheme) : Prop :=
  ∀ T : Over U.toScheme, D.IsFlatInDimensionsGEAfterBaseChange ((Over.map U.ι).obj T) ↔
    ∃ g : T.left ⟶ Z, g ≫ i = T.hom

/-- A monomorphism satisfying the factorization criterion represents `F_n` over `U`. -/
def representableByOfFactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ U.toScheme)
    (hmono : Mono i) (hi : D.FactorizationCriterion U i) :
    (D.openFlatDimensionFunctor U).RepresentableBy (Over.mk i) :=
  FreeAtGenericPointsSituation.representableByOfSubsingleton _ (Over.mk i) hmono fun T ↦ by
    rw [D.nonempty_openFlatDimensionFunctor_obj_iff U T, hi T]
    exact ⟨fun h ↦ ⟨Over.homMk h.choose h.choose_spec⟩, fun h ↦ ⟨h.some.left, Over.w h.some⟩⟩

/-- Conversely, the structure morphism of an object representing `F_n` over `U` satisfies the
factorization criterion, so the criterion is an exact reformulation of representability. -/
theorem factorizationCriterion_of_representableBy {W : Over U.toScheme}
    (e : (D.openFlatDimensionFunctor U).RepresentableBy W) :
    D.FactorizationCriterion U W.hom := fun T ↦ by
  rw [← D.nonempty_openFlatDimensionFunctor_obj_iff U T]
  exact ⟨fun h ↦ ⟨(e.homEquiv.symm h.some : T ⟶ W).left, Over.w _⟩,
    fun h ↦ ⟨e.homEquiv (Over.homMk h.choose h.choose_spec)⟩⟩

/-- The condition defining `F_n` is the condition `AlgebraicGeometry.BaseChangeFlatInDimensionsGE`
for the family and module of the situation. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff (T : Over D.S) :
    D.IsFlatInDimensionsGEAfterBaseChange T ↔ BaseChangeFlatInDimensionsGE D.f D.F D.n T :=
  isFlatOverInDimensionsGE_iff_isFlatOverInDimensionsGEOn_univ _ _ _

/-- **Stacks Project, Tag 05UF.** In Situation 05MT, let `s` be a point of `S` and let `d = n` be
the bound of the situation. Assume that

1. there exists a complete dévissage of `F/X/S` over `s`,
2. `X` is of finite presentation over `S`,
3. `F` is an `𝒪_X`-module of finite presentation, and
4. `F` is flat over `S` in dimensions `≥ d + 1`.

Then, after replacing `S` by an open neighbourhood `U` of `s`, the functor `F_d` of Stacks 05MU
is representable by a monomorphism `Z_d ⟶ U` of finite presentation.

Hypothesis (1) is the source's own: the existence of a complete dévissage is assumed by Tag
05UF, and is produced étale locally (Tag 05HU) only in the proof of Tag 05UG. -/
@[stacks 05UF]
theorem exists_mono_finitePresentation_representableBy (s : D.S)
    (hdev : Nonempty (CompleteDevissage D.f D.F s)) (hf : FinitePresentation D.f)
    [D.F.IsFinitePresentation] (h : IsFlatOverInDimensionsGE D.f D.F (D.n + 1)) :
    ∃ U : D.S.Opens, s ∈ U ∧ ∃ Z : Over U.toScheme,
      Mono Z.hom ∧ FinitePresentation Z.hom ∧
        Nonempty ((D.openFlatDimensionFunctor U).RepresentableBy Z) := by
  have hrep : IsRepresentableNear (BaseChangeFlatInDimensionsGE D.f D.F D.n) s ⊤ := by
    obtain ⟨hdev⟩ := hdev
    cases hdev with
    | empty hzero =>
      exact isRepresentableNear_of_isZero hzero _ trivial
    | nonempty data =>
      exact data.chain.isRepresentableNear D.n hf inferInstance trivial
        (((isFlatOverInDimensionsGE_iff_isFlatOverInDimensionsGEOn_univ _ _ _).1 h).mono
          fun _ _ ↦ trivial)
  obtain ⟨U, -, hs, Z, i, hi, hfp, hcrit⟩ := hrep
  exact ⟨U, hs, Over.mk i, hi, hfp, ⟨D.representableByOfFactorizationCriterion U i hi
    fun T ↦ (D.isFlatInDimensionsGEAfterBaseChange_iff _).trans (hcrit T)⟩⟩

/-- **Stacks Project, Tag 05UF**, with the dimension bound `d` of the source independent of the
situation: the functor tested is the one attached to the situation with its bound changed to
`d`. -/
theorem exists_mono_finitePresentation_representableBy_near (s : D.S) (d : ℕ)
    (hdev : Nonempty (CompleteDevissage D.f D.F s)) (hf : FinitePresentation D.f)
    [D.F.IsFinitePresentation] (h : IsFlatOverInDimensionsGE D.f D.F (d + 1)) :
    ∃ U : D.S.Opens, s ∈ U ∧ ∃ Z : Over U.toScheme,
      Mono Z.hom ∧ FinitePresentation Z.hom ∧
        Nonempty ((({ D with n := d } :
          FlatDimensionSituation.{u}).openFlatDimensionFunctor U).RepresentableBy Z) :=
  ({ D with n := d } :
    FlatDimensionSituation.{u}).exists_mono_finitePresentation_representableBy s hdev hf h

end FlatDimensionSituation

end AlgebraicGeometry

end
