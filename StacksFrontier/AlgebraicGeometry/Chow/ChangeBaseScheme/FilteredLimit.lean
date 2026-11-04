module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FlatProjection
public import StacksCore.Tactic.StacksAttribute

/-!
# A filtered limit of base schemes for Chow homology

This file sets up the standing situation of Stacks 0FVQ: a base `S` with a dimension function
`δ`, a cofiltered inverse system `i ↦ S_i` of schemes affine over `S`, and a limit
`S' = lim S_i`, such that

* each `S_i` is locally Noetherian and universally catenary and carries the dimension function
  `δ_i` obtained by composing `S_i ⟶ S` with `δ`;
* each transition morphism `S_i ⟶ S_{i'}` is flat;
* `S' ⟶ S` is a flat base change of Chow situations with vanishing dimension shift,

together with a quasi-compact scheme `X` of finite type over `S`. Its base changes are
`X_i = X ×_S S_i` and `X' = X ×_S S'`.

The condition that the projection `S' ⟶ S_i` is itself a flat base change of Chow situations
with vanishing dimension shift is not assumed: it is proved here. The projection is flat
because the transition morphisms are affine and flat, and it preserves the dimension function
on the generic points of its fibres because the dimension functions on the stages are pulled
back from `S`. The same holds for the transition morphisms, so all three conditions of Stacks
0FVQ are available.

## Main definitions

* `Stacks.Chow.FilteredBaseChangeSystem` — the situation just described.
* `Stacks.Chow.FilteredBaseChangeSystem.stageSituation` — the Chow situation `(S_i, δ_i)`.
* `Stacks.Chow.FilteredBaseChangeSystem.stageScheme`,
  `Stacks.Chow.FilteredBaseChangeSystem.limitScheme` — the base changes `X_i` and `X'`.
* `Stacks.Chow.FilteredBaseChangeSystem.stageProjection`,
  `Stacks.Chow.FilteredBaseChangeSystem.stageTransition` — the morphisms `X' ⟶ X_i` and
  `X_i ⟶ X_j` induced by `S' ⟶ S_i` and `S_i ⟶ S_j`.
* `Stacks.Chow.FilteredBaseChangeSystem.stageToLimitBaseChange` — the flat base change of Chow
  situations from `(S_i, δ_i)` to `(S', δ')` along the projection, with dimension shift zero.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.transition_isAffineHom` — the transition morphisms are
  affine.
* `Stacks.Chow.FilteredBaseChangeSystem.flat_limitProjection` — the projections from the limit
  base to the stages are flat.

## Implementation notes

That a point of a fibre of a composite `g ∘ f` is a generic point of that fibre as soon as it is
a generic point of the corresponding fibre of `f` uses that the dimension function upstairs is
pulled back from the bottom: a strict generalization inside the fibre of the composite would
have to lie in the fibre of `f`, because the dimension function is strictly monotone under
strict generalization and is constant on the fibre of the composite.

The base changes are written throughout as the chosen fibre products `pullback X.hom g` with
structure morphism `CategoryTheory.Limits.pullback.snd`, rather than through the objects of the
over category, so that the types appearing in later constructions agree on the nose.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace Stacks.Chow

/-- **Stacks Project, Tag 0FVQ, the situation.** A cofiltered inverse system of schemes affine
over a Chow base `S`, with a chosen limit `S'`, such that every stage carries the dimension
function pulled back from `S`, every transition morphism is flat, and `S' ⟶ S` is a flat base
change of Chow situations with vanishing dimension shift; together with a quasi-compact scheme
`X` of finite type over `S`. -/
structure FilteredBaseChangeSystem (I : Type v) [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] where
  /-- The flat base change from the limit base `S'` to the base `S`. -/
  limitBaseChange : FlatBaseChangeSituation.{u}
  /-- The dimension shift between `S` and `S'` vanishes. -/
  shift_eq_zero : limitBaseChange.c = 0
  /-- The inverse system `i ↦ S_i` of base schemes. -/
  diagram : I ⥤ Scheme.{u}
  /-- A cone over the inverse system. -/
  cone : Cone diagram
  /-- The cone is a limit cone. -/
  isLimit : IsLimit cone
  /-- The vertex of the limit cone is the base `S'`. -/
  limitIdentification : cone.pt ≅ limitBaseChange.baseChange.S
  /-- The structure morphism `S_i ⟶ S`. -/
  stageToBase : ∀ i : I, diagram.obj i ⟶ limitBaseChange.base.S
  /-- The structure morphisms are compatible with the transition morphisms. -/
  stageToBase_naturality : ∀ {i j : I} (f : i ⟶ j), diagram.map f ≫ stageToBase j = stageToBase i
  /-- The structure morphism of `S'` factors through every stage. -/
  limitToBase_comm : ∀ i : I,
    cone.π.app i ≫ stageToBase i = limitIdentification.hom ≫ limitBaseChange.g
  /-- Every stage is affine over `S`. -/
  stageAffine : ∀ i : I, IsAffineHom (stageToBase i)
  /-- Every stage is locally Noetherian. -/
  stageLocallyNoetherian : ∀ i : I, IsLocallyNoetherian (diagram.obj i)
  /-- Every stage is universally catenary. -/
  stageUniversallyCatenary : ∀ i : I,
    @Scheme.IsUniversallyCatenary (diagram.obj i) (stageLocallyNoetherian i)
  /-- The dimension function `δ_i` on the stage `i`. -/
  stageDimension : ∀ i : I, DimensionFunction (diagram.obj i)
  /-- The dimension function on a stage is the one pulled back from `S`. -/
  stageDimension_eq : ∀ (i : I) (t : diagram.obj i),
    stageDimension i t = limitBaseChange.base.dimensionFunction (stageToBase i t)
  /-- Every transition morphism is flat. -/
  transitionFlat : ∀ {i j : I} (f : i ⟶ j), Flat (diagram.map f)
  /-- The quasi-compact scheme of finite type over `S`. -/
  X : Over limitBaseChange.base.S
  /-- It is quasi-compact. -/
  [compactSpaceX : CompactSpace X.left]
  /-- Its structure morphism is locally of finite type. -/
  [locallyOfFiniteTypeX : LocallyOfFiniteType X.hom]
  /-- Its structure morphism is quasi-compact, completing the finite-type hypothesis. -/
  [quasiCompactX : QuasiCompact X.hom]

attribute [instance] FilteredBaseChangeSystem.compactSpaceX
  FilteredBaseChangeSystem.locallyOfFiniteTypeX FilteredBaseChangeSystem.quasiCompactX

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-! ### The Chow situations and the base changes of `X` -/

/-- The Chow situation `(S_i, δ_i)` at a finite stage. -/
@[reducible] def stageSituation (i : I) : ChowSituation.{u} where
  S := s.diagram.obj i
  isLocallyNoetherian := s.stageLocallyNoetherian i
  isUniversallyCatenary := s.stageUniversallyCatenary i
  dimensionFunction := s.stageDimension i

/-- The base change `X_i = X ×_S S_i` of `X` to a finite stage. -/
def stageScheme (i : I) : Over (s.diagram.obj i) :=
  (Over.pullback (s.stageToBase i)).obj s.X

/-- The base change `X' = X ×_S S'` of `X` to the limit base. -/
def limitScheme : Over s.limitBaseChange.baseChange.S :=
  (Over.pullback s.limitBaseChange.g).obj s.X

/-- The underlying scheme of `X_i` is the fibre product `X ×_S S_i`. -/
@[simp]
theorem stageScheme_left (i : I) : (s.stageScheme i).left = pullback s.X.hom (s.stageToBase i) :=
  rfl

/-- The structure morphism of `X_i` is the second projection `X ×_S S_i ⟶ S_i`. -/
@[simp]
theorem stageScheme_hom (i : I) :
    (s.stageScheme i).hom = pullback.snd s.X.hom (s.stageToBase i) :=
  rfl

/-- The underlying scheme of `X'` is the fibre product `X ×_S S'`. -/
@[simp]
theorem limitScheme_left : s.limitScheme.left = pullback s.X.hom s.limitBaseChange.g := rfl

/-- The structure morphism of `X'` is the second projection `X ×_S S' ⟶ S'`. -/
@[simp]
theorem limitScheme_hom : s.limitScheme.hom = pullback.snd s.X.hom s.limitBaseChange.g := rfl

/-- The base change of `X` to a finite stage is quasi-compact, because `X` is and the projection
to `X` is a base change of an affine morphism. -/
instance stageScheme_compact (i : I) :
    CompactSpace (pullback s.X.hom (s.stageToBase i) : Scheme.{u}) := by
  have : IsAffineHom (pullback.fst s.X.hom (s.stageToBase i)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback s.X.hom (s.stageToBase i)).flip (s.stageAffine i)
  have := s.compactSpaceX
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst s.X.hom (s.stageToBase i))

/-- The base change of `X` to a finite stage is locally Noetherian. -/
instance stageScheme_locallyNoetherian (i : I) :
    IsLocallyNoetherian (pullback s.X.hom (s.stageToBase i)) := by
  let _ : IsLocallyNoetherian (s.diagram.obj i) := s.stageLocallyNoetherian i
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s.X.hom (s.stageToBase i))

/-- The base change of `X` to the limit base is locally Noetherian. -/
instance limitScheme_locallyNoetherian :
    IsLocallyNoetherian (pullback s.X.hom s.limitBaseChange.g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s.X.hom s.limitBaseChange.g)

/-- The base change of `X` to a finite stage is locally of finite type over it. -/
instance stageScheme_locallyOfFiniteType (i : I) :
    LocallyOfFiniteType (pullback.snd s.X.hom (s.stageToBase i)) :=
  inferInstance

/-- The base change of `X` to the limit base is locally of finite type over it. -/
instance limitScheme_locallyOfFiniteType :
    LocallyOfFiniteType (pullback.snd s.X.hom s.limitBaseChange.g) :=
  inferInstance

/-- The base change of `X` to a finite stage is quasi-separated. -/
instance stageScheme_quasiSeparated (i : I) :
    QuasiSeparatedSpace (pullback s.X.hom (s.stageToBase i) : Scheme.{u}) := by
  infer_instance

/-! ### The transition morphisms and the projections -/

/-- Every transition morphism of the inverse system of bases is affine, because its composite
with an affine structure morphism is affine and an affine morphism is separated. -/
theorem transition_isAffineHom {i j : I} (f : i ⟶ j) : IsAffineHom (s.diagram.map f) := by
  have hcomp : IsAffineHom (s.diagram.map f ≫ s.stageToBase j) := by
    rw [s.stageToBase_naturality f]
    exact s.stageAffine i
  let _ : IsAffineHom (s.stageToBase j) := s.stageAffine j
  let _ : IsSeparated (s.stageToBase j) := IsSeparated.of_isAffineHom (s.stageToBase j)
  exact IsAffineHom.of_comp (s.diagram.map f) (s.stageToBase j)

/-- The projection `S' ⟶ S_i` from the limit base to a stage. -/
def limitProjection (i : I) : s.limitBaseChange.baseChange.S ⟶ s.diagram.obj i :=
  s.limitIdentification.inv ≫ s.cone.π.app i

/-- The projection from the limit base to a stage, written out. -/
theorem limitProjection_def (i : I) :
    s.limitProjection i = s.limitIdentification.inv ≫ s.cone.π.app i := rfl

/-- The projection from the limit base to a stage is compatible with the structure morphisms
to `S`. -/
theorem limitProjection_comp_stageToBase (i : I) :
    s.limitProjection i ≫ s.stageToBase i = s.limitBaseChange.g := by
  rw [limitProjection, Category.assoc, s.limitToBase_comm i, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The projections from the limit base to the stages are compatible with the transition
morphisms. -/
theorem limitProjection_comp_map {i j : I} (f : i ⟶ j) :
    s.limitProjection i ≫ s.diagram.map f = s.limitProjection j := by
  rw [limitProjection, limitProjection, Category.assoc, s.cone.w f]

/-- The projection from the limit base to a stage is affine: the transition morphisms of the
inverse system are affine. -/
theorem isAffineHom_limitProjection (i : I) : IsAffineHom (s.limitProjection i) := by
  let _ {i j : I} (f : i ⟶ j) : IsAffineHom (s.diagram.map f) := s.transition_isAffineHom f
  let _ : IsAffineHom (s.cone.π.app i) :=
    AlgebraicGeometry.EventualLimit.isAffineHom_π_app s.diagram s.cone s.isLimit i
  rw [limitProjection]
  infer_instance

/-- The limit base is affine over `S`, being affine over a stage which is affine over `S`. -/
instance isAffineHom_limitBaseChange_g : IsAffineHom s.limitBaseChange.g := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  let _ : IsAffineHom (s.limitProjection i) := s.isAffineHom_limitProjection i
  let _ : IsAffineHom (s.stageToBase i) := s.stageAffine i
  rw [← s.limitProjection_comp_stageToBase i]
  infer_instance

/-- The base change of `X` to the limit base is quasi-compact, because `X` is and the projection
to `X` is a base change of an affine morphism. -/
instance limitScheme_compact :
    CompactSpace (pullback s.X.hom s.limitBaseChange.g : Scheme.{u}) := by
  have : IsAffineHom (pullback.fst s.X.hom s.limitBaseChange.g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback s.X.hom s.limitBaseChange.g).flip s.isAffineHom_limitBaseChange_g
  have := s.compactSpaceX
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst s.X.hom s.limitBaseChange.g)

/-- The projection from the limit base to a stage is flat: the transition morphisms of the
inverse system are affine and flat. -/
@[ega "IV 8.3.8" "flat clause of (ii)"]
theorem flat_limitProjection (i : I) : Flat (s.limitProjection i) := by
  let _ : Flat (s.cone.π.app i) :=
    AlgebraicGeometry.flat_π_app_of_essentiallySmall s.diagram s.cone s.isLimit
      (fun f ↦ s.transition_isAffineHom f) (fun f ↦ s.transitionFlat f) i
  rw [limitProjection]
  infer_instance

/-- The projection `X' ⟶ X_i` from the base change of `X` to the limit base to its base change
to a finite stage. -/
def stageProjection (i : I) :
    pullback s.X.hom s.limitBaseChange.g ⟶ pullback s.X.hom (s.stageToBase i) :=
  pullback.lift (pullback.fst s.X.hom s.limitBaseChange.g)
    (pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitProjection i)
    (by
      calc
        pullback.fst s.X.hom s.limitBaseChange.g ≫ s.X.hom =
            pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitBaseChange.g := pullback.condition
        _ = (pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitProjection i) ≫
              s.stageToBase i := by
          rw [Category.assoc, s.limitProjection_comp_stageToBase i])

/-- The projection `X' ⟶ X_i` commutes with the first projections to `X`. -/
@[simp]
theorem stageProjection_comp_fst (i : I) :
    s.stageProjection i ≫ pullback.fst s.X.hom (s.stageToBase i) =
      pullback.fst s.X.hom s.limitBaseChange.g :=
  pullback.lift_fst _ _ _

/-- The projection `X' ⟶ X_i` lies over the projection `S' ⟶ S_i`. -/
@[simp]
theorem stageProjection_comp_snd (i : I) :
    s.stageProjection i ≫ pullback.snd s.X.hom (s.stageToBase i) =
      pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitProjection i :=
  pullback.lift_snd _ _ _

/-- The transition morphism `X_i ⟶ X_j` between the base changes of `X` to two finite stages. -/
def stageTransition {i j : I} (f : i ⟶ j) :
    pullback s.X.hom (s.stageToBase i) ⟶ pullback s.X.hom (s.stageToBase j) :=
  pullback.lift (pullback.fst s.X.hom (s.stageToBase i))
    (pullback.snd s.X.hom (s.stageToBase i) ≫ s.diagram.map f)
    (by
      calc
        pullback.fst s.X.hom (s.stageToBase i) ≫ s.X.hom =
            pullback.snd s.X.hom (s.stageToBase i) ≫ s.stageToBase i := pullback.condition
        _ = (pullback.snd s.X.hom (s.stageToBase i) ≫ s.diagram.map f) ≫ s.stageToBase j := by
          rw [Category.assoc, s.stageToBase_naturality f])

/-- The transition morphism `X_i ⟶ X_j` commutes with the first projections to `X`. -/
@[simp]
theorem stageTransition_comp_fst {i j : I} (f : i ⟶ j) :
    s.stageTransition f ≫ pullback.fst s.X.hom (s.stageToBase j) =
      pullback.fst s.X.hom (s.stageToBase i) :=
  pullback.lift_fst _ _ _

/-- The transition morphism `X_i ⟶ X_j` lies over the transition morphism `S_i ⟶ S_j`. -/
@[simp]
theorem stageTransition_comp_snd {i j : I} (f : i ⟶ j) :
    s.stageTransition f ≫ pullback.snd s.X.hom (s.stageToBase j) =
      pullback.snd s.X.hom (s.stageToBase i) ≫ s.diagram.map f :=
  pullback.lift_snd _ _ _

/-- The projections from `X'` to the stages are compatible with the transition morphisms. -/
theorem stageProjection_comp_stageTransition {i j : I} (f : i ⟶ j) :
    s.stageProjection i ≫ s.stageTransition f = s.stageProjection j := by
  apply pullback.hom_ext
  · rw [Category.assoc, s.stageTransition_comp_fst f, s.stageProjection_comp_fst i,
      s.stageProjection_comp_fst j]
  · rw [Category.assoc, s.stageTransition_comp_snd f, ← Category.assoc,
      s.stageProjection_comp_snd i, s.stageProjection_comp_snd j, Category.assoc,
      s.limitProjection_comp_map f]

/-! ### The flat base change from a stage to the limit -/

/-- Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and let the dimension function on
`Y` be pulled back from `S`. Then a generic point of a fibre of `f` is a generic point of the
corresponding fibre of `g ∘ f`: a strict generalization inside that larger fibre would have the
same image in `S`, hence the same value of the dimension function on `Y`, which is impossible
for a strict generalization; so it lies in the fibre of `f`, where it is not strict. -/
private theorem genericPoints_fiber_comp_of_dimension_pullback
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (d : DimensionFunction Y) (δ : DimensionFunction S)
    (hd : ∀ y, d y = δ (g y)) (y : Y) (x : genericPoints (f ⁻¹' {y} : Set X)) :
    (⟨x.1.1, by simpa using congrArg g x.1.2⟩ : ((f ≫ g) ⁻¹' {g y} : Set X)) ∈
      genericPoints ((f ≫ g) ⁻¹' {g y} : Set X) := by
  let _ : QuasiSober (f ⁻¹' {y} : Set X) := (f.fiberHomeo y).symm.isOpenEmbedding.quasiSober
  let _ : QuasiSober ((f ≫ g) ⁻¹' {g y} : Set X) :=
    ((f ≫ g).fiberHomeo (g y)).symm.isOpenEmbedding.quasiSober
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz ↦ ?_
  have hzx : (z : X) ⤳ (x.1 : X) := (subtype_specializes_iff _ _).1 hz
  have hfy : f (z : X) ⤳ y := by
    simpa only [show f (x.1 : X) = y from x.1.2] using hzx.map f.continuous
  have hfz : f (z : X) = y := by
    by_contra hne
    have hlt := d.strictAnti_specializes hfy hne
    rw [hd, hd, show g (f (z : X)) = g y from z.2] at hlt
    exact lt_irrefl _ hlt
  have heq := (mem_genericPoints_iff_forall_specializes_eq x.1).1 x.2
    (⟨z.1, hfz⟩ : (f ⁻¹' {y} : Set X)) ((subtype_specializes_iff _ x.1).2 hzx)
  exact Subtype.ext (congrArg (fun t : (f ⁻¹' {y} : Set X) => (t : X)) heq)

/-- **Stacks Project, Tag 0FVQ, hypothesis (2).** The projection from the limit base to a finite
stage is a flat base change of Chow situations with vanishing dimension shift. -/
@[reducible] def stageToLimitBaseChange (i : I) : FlatBaseChangeSituation.{u} where
  base := s.stageSituation i
  baseChange := s.limitBaseChange.baseChange
  g := s.limitProjection i
  flat := s.flat_limitProjection i
  c := 0
  dimensionFunction_eq_add := by
    intro y y'
    have hyMem : (s.limitProjection i ≫ s.stageToBase i) y'.1.1 = s.stageToBase i y :=
      congrArg (s.stageToBase i) y'.1.2
    have hy : (⟨y'.1.1, hyMem⟩ :
        ((s.limitProjection i ≫ s.stageToBase i) ⁻¹' {s.stageToBase i y} : Set _)) ∈
        genericPoints ((s.limitProjection i ≫ s.stageToBase i) ⁻¹'
          {s.stageToBase i y} : Set _) :=
      genericPoints_fiber_comp_of_dimension_pullback (s.limitProjection i) (s.stageToBase i)
        (s.stageDimension i) s.limitBaseChange.base.dimensionFunction (s.stageDimension_eq i) y y'
    have hyMem' : s.limitBaseChange.g y'.1.1 = s.stageToBase i y := by
      simpa only [s.limitProjection_comp_stageToBase i] using hyMem
    have hy' : (⟨y'.1.1, hyMem'⟩ :
        (s.limitBaseChange.g ⁻¹' {s.stageToBase i y} : Set _)) ∈
        genericPoints (s.limitBaseChange.g ⁻¹' {s.stageToBase i y} : Set _) := by
      let _ : QuasiSober (s.limitBaseChange.g ⁻¹' {s.stageToBase i y} : Set _) :=
        (s.limitBaseChange.g.fiberHomeo (s.stageToBase i y)).symm.isOpenEmbedding.quasiSober
      let _ : QuasiSober ((s.limitProjection i ≫ s.stageToBase i) ⁻¹'
          {s.stageToBase i y} : Set _) :=
        ((s.limitProjection i ≫ s.stageToBase i).fiberHomeo
          (s.stageToBase i y)).symm.isOpenEmbedding.quasiSober
      refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz ↦ ?_
      have hzMem : (s.limitProjection i ≫ s.stageToBase i)
          (z : s.limitBaseChange.baseChange.S) = s.stageToBase i y := by
        rw [congrArg (fun f : s.limitBaseChange.baseChange.S ⟶ s.limitBaseChange.base.S => f z.1)
          (s.limitProjection_comp_stageToBase i)]
        exact z.2
      have hzx : (z : s.limitBaseChange.baseChange.S) ⤳
          (y'.1.1 : s.limitBaseChange.baseChange.S) :=
        (subtype_specializes_iff z ⟨y'.1.1, hyMem'⟩).1 hz
      have heq := (mem_genericPoints_iff_forall_specializes_eq _).1 hy
        (⟨z.1, hzMem⟩ : ((s.limitProjection i ≫ s.stageToBase i) ⁻¹'
          {s.stageToBase i y} : Set _))
        ((subtype_specializes_iff _ ⟨y'.1.1, hyMem⟩).2 hzx)
      exact Subtype.ext (congrArg
        (fun t : ((s.limitProjection i ≫ s.stageToBase i) ⁻¹'
          {s.stageToBase i y} : Set _) => (t : s.limitBaseChange.baseChange.S)) heq)
    have hd := s.limitBaseChange.dimensionFunction_eq_add (s.stageToBase i y) ⟨_, hy'⟩
    rw [s.shift_eq_zero, add_zero] at hd
    change s.limitBaseChange.baseChange.dimensionFunction y'.1.1 = (s.stageDimension i) y + 0
    rw [add_zero, s.stageDimension_eq i y]
    exact hd

/-- The base of the base change from a stage to the limit is the Chow situation `(S_i, δ_i)`. -/
@[simp]
theorem stageToLimitBaseChange_base (i : I) :
    (s.stageToLimitBaseChange i).base = s.stageSituation i :=
  rfl

/-- The target of the base change from a stage to the limit is the Chow situation `(S', δ')`. -/
@[simp]
theorem stageToLimitBaseChange_baseChange (i : I) :
    (s.stageToLimitBaseChange i).baseChange = s.limitBaseChange.baseChange :=
  rfl

/-- The morphism of the base change from a stage to the limit is the projection `S' ⟶ S_i`. -/
@[simp]
theorem stageToLimitBaseChange_g (i : I) :
    (s.stageToLimitBaseChange i).g = s.limitProjection i :=
  rfl

/-- The base change from a stage to the limit has dimension shift zero. -/
@[simp]
theorem stageToLimitBaseChange_c (i : I) : (s.stageToLimitBaseChange i).c = 0 := rfl

end FilteredBaseChangeSystem

end Stacks.Chow

end
