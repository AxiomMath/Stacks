module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BaseChangeComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimit
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedImmersionModel
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of integral closed subschemes in a filtered limit of base schemes

In the situation of Stacks 0FVQ, an integral closed subscheme `Z' ⊆ X'` of the base change of
`X` to the limit base descends to an integral closed subscheme `Z_i ⊆ X_i` at a finite stage,
with the same delta-dimension and with `Z'` the base change of `Z_i`.

The base changes `X_i` form a cofiltered inverse system with affine transition morphisms whose
limit is `X'`, so `Z'` descends to a closed subscheme at a finite stage; replacing it by the
scheme-theoretic image of `Z' ⟶ X_i` makes it integral without changing its base change. The
delta-dimension is unchanged because `X'` is the base change of `X_i` along the flat
dimension-preserving morphism `S' ⟶ S_i`, so Stacks 0FVH applies to the single irreducible
component of `Z'`.

## Main definitions

* `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeDiagram` — the inverse system `i ↦ X_i` of
  base changes of `X`, obtained by pulling back the inverse system of bases along `X ⟶ S`.
* `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeCone` — the cone over that system with
  vertex `X'`.

## Main results

* `Stacks.Chow.FilteredBaseChangeSystem.isPullback_stageProjection` — `X'` is the base change
  of `X_i` along the projection `S' ⟶ S_i`.
* `Stacks.Chow.FilteredBaseChangeSystem.isLimit_stageSchemeCone` — `X'` is the limit of the
  inverse system `i ↦ X_i`.
* `Stacks.Chow.FilteredBaseChangeSystem.exists_integral_closedSubscheme_model` — the descent of
  an integral closed subscheme of `X'` to a finite stage.

## Implementation notes

The inverse system of the base changes is produced by lifting the inverse system of bases into
the category of schemes over `S` and pulling back along `X ⟶ S`; pulling back preserves limits,
so the limit of the system is the fibre product of the limit base with `X`, which is identified
with `X'` by the symmetry of the fibre product and the identification of the vertex of the limit
cone with `S'`. The objects of the resulting system are the fibre products `S_i ×_S X`, so they
too are identified with the `X_i = X ×_S S_i` by the symmetry of the fibre product.

That `X'` is the base change of `X_i` along `S' ⟶ S_i` is the cancellation property of cartesian
squares applied to the composite `S' ⟶ S_i ⟶ S`.

## References

* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace Stacks.Chow

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-! ### `X'` as the base change of `X_i` -/

/-- **`X'` is the base change of `X_i` along the projection `S' ⟶ S_i`.** The composite of the
square relating `X'` and `X_i` with the square relating `X_i` and `X` is the square relating
`X'` and `X`, which is cartesian, and the second square is cartesian, so the first is. -/
theorem isPullback_stageProjection (i : I) :
    IsPullback (s.stageProjection i) (pullback.snd s.X.hom s.limitBaseChange.g)
      (pullback.snd s.X.hom (s.stageToBase i)) (s.limitProjection i) := by
  refine IsPullback.of_right ?_ (s.stageProjection_comp_snd i)
    (IsPullback.of_hasPullback s.X.hom (s.stageToBase i))
  rw [s.stageProjection_comp_fst i, s.limitProjection_comp_stageToBase i]
  exact IsPullback.of_hasPullback s.X.hom s.limitBaseChange.g

/-- The projection `X' ⟶ X_i` is affine, being a base change of the affine projection
`S' ⟶ S_i`. -/
theorem isAffineHom_stageProjection (i : I) : IsAffineHom (s.stageProjection i) := by
  have hcone : IsAffineHom (s.cone.π.app i) := by
    let _ {i j : I} (f : i ⟶ j) : IsAffineHom (s.diagram.map f) := s.transition_isAffineHom f
    exact AlgebraicGeometry.EventualLimit.isAffineHom_π_app s.diagram s.cone s.isLimit i
  have hlim : IsAffineHom (s.limitProjection i) := by
    rw [limitProjection]
    infer_instance
  exact AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
    (s.isPullback_stageProjection i).flip hlim

/-! ### The inverse system of base changes of `X` -/

/-- The structure morphisms of the stages, as a natural transformation to the constant diagram
at the base. -/
def stageBaseMap : s.diagram ⟶ (Functor.const I).obj s.limitBaseChange.base.S where
  app := s.stageToBase
  naturality _ _ f := by simpa using s.stageToBase_naturality f

/-- The inverse system of bases, read in the category of schemes over `S`. -/
def stageBaseDiagram : I ⥤ Over s.limitBaseChange.base.S :=
  Over.lift s.diagram s.stageBaseMap

/-- The limit cone of the inverse system of bases, read in the category of schemes over `S`. -/
def stageBaseCone : Cone s.stageBaseDiagram :=
  Over.liftCone s.diagram s.stageBaseMap s.cone
    (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.limitToBase_comm

/-- The cone of `Stacks.Chow.FilteredBaseChangeSystem.stageBaseCone` is a limit cone. -/
def isLimitStageBaseCone : IsLimit s.stageBaseCone := by
  have : Nonempty I := IsCofiltered.nonempty
  exact Over.isLimitLiftCone s.diagram s.stageBaseMap s.cone
    (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.limitToBase_comm s.isLimit

/-- The inverse system `i ↦ S_i ×_S X` of base changes of `X`, obtained by pulling back the
inverse system of bases along `X ⟶ S`. -/
@[ega "IV 8.8.1" "partial"]
def stageSchemeDiagram : I ⥤ Scheme.{u} :=
  s.stageBaseDiagram ⋙ Over.pullback s.X.hom ⋙ Over.forget s.X.left

/-- The transition morphisms of the inverse system of base changes of `X` are affine. -/
theorem stageSchemeTransition_isAffineHom {i j : I} (f : i ⟶ j) :
    IsAffineHom (s.stageSchemeDiagram.map f) := by
  let E := s.stageBaseDiagram ⋙ Over.pullback s.X.hom
  let _ : IsAffineHom (E.obj j).hom :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (s.stageToBase j) s.X.hom) (s.stageAffine j)
  have : IsAffineHom ((E.map f).left ≫ (E.obj j).hom) := by
    rw [(E.map f).w]
    exact AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (s.stageToBase i) s.X.hom) (s.stageAffine i)
  let _ : IsSeparated (E.obj j).hom := IsSeparated.of_isAffineHom (E.obj j).hom
  exact IsAffineHom.of_comp (E.map f).left (E.obj j).hom

/-- The image of the limit cone of bases under pulling back along `X ⟶ S`. -/
def stageSchemeConeOverX : Cone s.stageSchemeDiagram :=
  (Over.pullback s.X.hom ⋙ Over.forget s.X.left).mapCone s.stageBaseCone

/-- `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeConeOverX` is a limit cone: pulling back
along a morphism preserves limits, and so does the forgetful functor from an over category. -/
def isLimitStageSchemeConeOverX : IsLimit s.stageSchemeConeOverX :=
  isLimitOfPreserves (Over.forget s.X.left)
    (isLimitOfPreserves (Over.pullback s.X.hom) s.isLimitStageBaseCone)

/-- The vertex of `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeConeOverX` is `X'`: the
symmetry of the fibre product followed by base change along the identification of the vertex of
the limit cone with `S'`. -/
def stageLimitSchemeIso :
    s.stageSchemeConeOverX.pt ≅ pullback s.X.hom s.limitBaseChange.g :=
  pullbackSymmetry (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom ≪≫
    asIso (pullback.map s.X.hom (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom
      s.limitBaseChange.g (𝟙 _) s.limitIdentification.hom (𝟙 _)
      ((Category.comp_id s.X.hom).trans (Category.id_comp s.X.hom).symm)
      (Category.comp_id _))

/-- The inverse system `i ↦ S_i ×_S X` of base changes of `X`, with `X'` as the vertex of the
cone. -/
@[reducible] def stageSchemeCone : Cone s.stageSchemeDiagram where
  pt := pullback s.X.hom s.limitBaseChange.g
  π.app i := s.stageLimitSchemeIso.inv ≫ s.stageSchemeConeOverX.π.app i
  π.naturality _ _ f := by simp [s.stageSchemeConeOverX.w f]

/-- **`X'` is the limit of the inverse system of the `X_i`.** -/
def isLimit_stageSchemeCone : IsLimit s.stageSchemeCone :=
  s.isLimitStageSchemeConeOverX.ofIsoLimit
    (Cone.ext s.stageLimitSchemeIso (fun _ ↦ by simp [stageSchemeCone]))

/-- The object of the inverse system at a stage is the base change `X_i`, up to the symmetry of
the fibre product. -/
def stageSchemeObjectIso (i : I) :
    s.stageSchemeDiagram.obj i ≅ pullback s.X.hom (s.stageToBase i) :=
  pullbackSymmetry (s.stageToBase i) s.X.hom

/-- The inverse of `Stacks.Chow.FilteredBaseChangeSystem.stageLimitSchemeIso` followed by the
first projection is the projection `X' ⟶ S'` followed by the inverse of the limit identification.
-/
theorem stageLimitSchemeIso_inv_comp_fst :
    s.stageLimitSchemeIso.inv ≫
        pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom =
      pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitIdentification.inv := by
  let e₂ := asIso (pullback.map s.X.hom (s.limitIdentification.hom ≫ s.limitBaseChange.g)
    s.X.hom s.limitBaseChange.g (𝟙 _) s.limitIdentification.hom (𝟙 _)
    ((Category.comp_id s.X.hom).trans (Category.id_comp s.X.hom).symm) (Category.comp_id _))
  have he₂ : e₂.hom ≫ pullback.snd s.X.hom s.limitBaseChange.g =
      pullback.snd s.X.hom (s.limitIdentification.hom ≫ s.limitBaseChange.g) ≫
        s.limitIdentification.hom := pullback.lift_snd _ _ _
  show e₂.inv ≫ (pullbackSymmetry (s.limitIdentification.hom ≫ s.limitBaseChange.g)
    s.X.hom).inv ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst]
  apply (cancel_epi e₂.hom).1
  calc
    e₂.hom ≫ (e₂.inv ≫ pullback.snd _ _) = pullback.snd _ _ := by simp
    _ = (e₂.hom ≫ pullback.snd _ _) ≫ s.limitIdentification.inv := by
      rw [he₂]
      simp

/-- The inverse of `Stacks.Chow.FilteredBaseChangeSystem.stageLimitSchemeIso` followed by the
second projection is the projection `X' ⟶ X`. -/
theorem stageLimitSchemeIso_inv_comp_snd :
    s.stageLimitSchemeIso.inv ≫
        pullback.snd (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom =
      pullback.fst s.X.hom s.limitBaseChange.g := by
  let e₂ := asIso (pullback.map s.X.hom (s.limitIdentification.hom ≫ s.limitBaseChange.g)
    s.X.hom s.limitBaseChange.g (𝟙 _) s.limitIdentification.hom (𝟙 _)
    ((Category.comp_id s.X.hom).trans (Category.id_comp s.X.hom).symm) (Category.comp_id _))
  have he₂ : e₂.hom ≫ pullback.fst s.X.hom s.limitBaseChange.g =
      pullback.fst s.X.hom (s.limitIdentification.hom ≫ s.limitBaseChange.g) := by
    refine (pullback.lift_fst _ _ _).trans ?_
    simp
  show e₂.inv ≫ (pullbackSymmetry (s.limitIdentification.hom ≫ s.limitBaseChange.g)
    s.X.hom).inv ≫ pullback.snd _ _ = _
  rw [pullbackSymmetry_inv_comp_snd]
  apply (cancel_epi e₂.hom).1
  calc
    e₂.hom ≫ (e₂.inv ≫ pullback.fst _ _) = pullback.fst _ _ := by simp
    _ = e₂.hom ≫ pullback.fst _ _ := he₂.symm

/-- The leg of `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeConeOverX` at `i` followed by the
projection to `S_i` is the projection to the vertex of the limit cone followed by its leg at `i`.
-/
theorem stageSchemeConeOverX_π_comp_fst (i : I) :
    s.stageSchemeConeOverX.π.app i ≫ pullback.fst (s.stageToBase i) s.X.hom =
      pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom ≫
        s.cone.π.app i := by
  show pullback.lift
    (pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom ≫ s.cone.π.app i)
    (pullback.snd (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom) _ ≫
      pullback.fst (s.stageToBase i) s.X.hom = _
  exact pullback.lift_fst _ _ _

/-- The leg of `Stacks.Chow.FilteredBaseChangeSystem.stageSchemeConeOverX` at `i` commutes with
the projections to `X`. -/
theorem stageSchemeConeOverX_π_comp_snd (i : I) :
    s.stageSchemeConeOverX.π.app i ≫ pullback.snd (s.stageToBase i) s.X.hom =
      pullback.snd (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom := by
  show pullback.lift
    (pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom ≫ s.cone.π.app i)
    (pullback.snd (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom) _ ≫
      pullback.snd (s.stageToBase i) s.X.hom = _
  exact pullback.lift_snd _ _ _

/-- The projection `X' ⟶ X_i` is the leg of the limit cone, read through the symmetry of the
fibre product. -/
theorem stageProjection_comp_stageSchemeObjectIso_inv (i : I) :
    s.stageProjection i ≫ (s.stageSchemeObjectIso i).inv = s.stageSchemeCone.π.app i := by
  apply pullback.hom_ext
  · calc
      (s.stageProjection i ≫ (s.stageSchemeObjectIso i).inv) ≫
            pullback.fst (s.stageToBase i) s.X.hom =
          s.stageProjection i ≫ ((s.stageSchemeObjectIso i).inv ≫
            pullback.fst (s.stageToBase i) s.X.hom) := Category.assoc _ _ _
      _ = s.stageProjection i ≫ pullback.snd s.X.hom (s.stageToBase i) := by
        rw [show (s.stageSchemeObjectIso i).inv ≫ pullback.fst (s.stageToBase i) s.X.hom =
          pullback.snd s.X.hom (s.stageToBase i) from
            pullbackSymmetry_inv_comp_fst (s.stageToBase i) s.X.hom]
      _ = pullback.snd s.X.hom s.limitBaseChange.g ≫ s.limitProjection i :=
        s.stageProjection_comp_snd i
      _ = (s.stageLimitSchemeIso.inv ≫
            pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom) ≫
              s.cone.π.app i := by
        rw [s.stageLimitSchemeIso_inv_comp_fst]
        exact (Category.assoc _ _ _).symm
      _ = s.stageLimitSchemeIso.inv ≫
            (pullback.fst (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom ≫
              s.cone.π.app i) := Category.assoc _ _ _
      _ = s.stageLimitSchemeIso.inv ≫
            (s.stageSchemeConeOverX.π.app i ≫ pullback.fst (s.stageToBase i) s.X.hom) :=
        congrArg (fun m ↦ s.stageLimitSchemeIso.inv ≫ m)
          (s.stageSchemeConeOverX_π_comp_fst i).symm
      _ = s.stageSchemeCone.π.app i ≫ pullback.fst (s.stageToBase i) s.X.hom :=
        (Category.assoc _ _ _).symm
  · calc
      (s.stageProjection i ≫ (s.stageSchemeObjectIso i).inv) ≫
            pullback.snd (s.stageToBase i) s.X.hom =
          s.stageProjection i ≫ ((s.stageSchemeObjectIso i).inv ≫
            pullback.snd (s.stageToBase i) s.X.hom) := Category.assoc _ _ _
      _ = s.stageProjection i ≫ pullback.fst s.X.hom (s.stageToBase i) := by
        rw [show (s.stageSchemeObjectIso i).inv ≫ pullback.snd (s.stageToBase i) s.X.hom =
          pullback.fst s.X.hom (s.stageToBase i) from
            pullbackSymmetry_inv_comp_snd (s.stageToBase i) s.X.hom]
      _ = pullback.fst s.X.hom s.limitBaseChange.g := s.stageProjection_comp_fst i
      _ = s.stageLimitSchemeIso.inv ≫
            pullback.snd (s.limitIdentification.hom ≫ s.limitBaseChange.g) s.X.hom :=
        s.stageLimitSchemeIso_inv_comp_snd.symm
      _ = s.stageLimitSchemeIso.inv ≫
            (s.stageSchemeConeOverX.π.app i ≫ pullback.snd (s.stageToBase i) s.X.hom) :=
        congrArg (fun m ↦ s.stageLimitSchemeIso.inv ≫ m)
          (s.stageSchemeConeOverX_π_comp_snd i).symm
      _ = s.stageSchemeCone.π.app i ≫ pullback.snd (s.stageToBase i) s.X.hom :=
        (Category.assoc _ _ _).symm

/-! ### Descent of a closed subscheme -/

/-- A closed subscheme of `X'` descends to a closed subscheme of `X_i` at a finite stage. -/
theorem exists_closedImmersion_model (Z' : Over (pullback s.X.hom s.limitBaseChange.g))
    [IsClosedImmersion Z'.hom] :
    ∃ (i : I) (Zᵢ : Over (pullback s.X.hom (s.stageToBase i))), IsClosedImmersion Zᵢ.hom ∧
      Nonempty (Z' ≅ (Over.pullback (s.stageProjection i)).obj Zᵢ) := by
  let _ {i j : I} (f : i ⟶ j) : IsAffineHom (s.stageSchemeDiagram.map f) :=
    s.stageSchemeTransition_isAffineHom f
  let _ (i : I) : CompactSpace (s.stageSchemeDiagram.obj i) :=
    (Scheme.homeoOfIso (s.stageSchemeObjectIso i).symm).compactSpace
  let _ (i : I) : QuasiSeparatedSpace (s.stageSchemeDiagram.obj i) :=
    (quasiSeparatedSpace_congr (Scheme.homeoOfIso (s.stageSchemeObjectIso i))).symm.mp
      (s.stageScheme_quasiSeparated i)
  have hfp : AlgebraicGeometry.FinitePresentation Z'.hom :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i, Yᵢ, hclosed, hmodel⟩ := AlgebraicGeometry.exists_closedImmersion_model_of_isLimit
    s.stageSchemeDiagram s.stageSchemeCone s.isLimit_stageSchemeCone Z' hfp
  refine ⟨i, (Over.pullback (s.stageSchemeObjectIso i).inv).obj Yᵢ, ?_, ?_⟩
  · show IsClosedImmersion (pullback.snd Yᵢ.hom (s.stageSchemeObjectIso i).inv)
    infer_instance
  · obtain ⟨e⟩ := hmodel
    exact ⟨e.trans (s.stageProjection_comp_stageSchemeObjectIso_inv i ▸
      (Over.pullbackComp (s.stageProjection i) (s.stageSchemeObjectIso i).inv).app Yᵢ)⟩

/-- An integral closed subscheme of `X'` descends to an integral closed subscheme of `X_i` at a
finite stage: a closed model exists by
`Stacks.Chow.FilteredBaseChangeSystem.exists_closedImmersion_model`, and replacing it by the
scheme-theoretic image of `Z' ⟶ X_i` makes it integral without changing its base change. -/
theorem exists_integral_closedImmersion_model
    (Z' : Over (pullback s.X.hom s.limitBaseChange.g))
    [IsClosedImmersion Z'.hom] [IsIntegral Z'.left] :
    ∃ (i : I) (Zᵢ : Over (pullback s.X.hom (s.stageToBase i))) (_ : IsClosedImmersion Zᵢ.hom),
      IsIntegral Zᵢ.left ∧ Nonempty (Z' ≅ (Over.pullback (s.stageProjection i)).obj Zᵢ) := by
  obtain ⟨i, W, hclosed, ⟨e⟩⟩ := s.exists_closedImmersion_model Z'
  have : IsClosedImmersion W.hom := hclosed
  have := s.isAffineHom_stageProjection i
  exact ⟨i, Over.mk (Z'.hom ≫ s.stageProjection i).imageι,
    inferInstanceAs (IsClosedImmersion (Z'.hom ≫ s.stageProjection i).imageι),
    AlgebraicGeometry.isIntegral_image_of_isIntegral (Z'.hom ≫ s.stageProjection i),
    ⟨AlgebraicGeometry.baseChangeImageIso (s.stageProjection i) Z' W e⟩⟩

/-! ### The delta-dimension of the model -/

/-- The delta-dimension of an integral scheme over the base is unchanged by composing its
structure morphism with an isomorphism. -/
private theorem schemeDeltaDimension_comp_iso (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    [IsIntegral X] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (e : X ≅ Y) :
    schemeDeltaDimension C (e.hom ≫ g) = schemeDeltaDimension C g := by
  have : IsIntegral Y := IsIntegral.of_isIso e.hom
  rw [schemeDeltaDimension_eq_genericPoint, schemeDeltaDimension_eq_genericPoint]
  exact congrArg (fun d : ℤ => (d : EInt))
    ((relativeDimension_comp_closedImmersion C.dimensionFunction e.hom g (genericPoint X)).trans
      (by rw [genericPoint_eq_of_isOpenImmersion e.hom]))

/-- A closed subscheme of `X'` which is the base change of a closed subscheme `Z_i ⊆ X_i` is the
base change of `Z_i` along the projection `S' ⟶ S_i`. -/
private theorem integralModel_baseChangeIso (i : I)
    (Zᵢ : Over (pullback s.X.hom (s.stageToBase i)))
    (Z' : Over (pullback s.X.hom s.limitBaseChange.g))
    (e : Z' ≅ (Over.pullback (s.stageProjection i)).obj Zᵢ) :
    ∃ a : Z'.left ≅ pullback (Zᵢ.hom ≫ pullback.snd s.X.hom (s.stageToBase i))
        (s.limitProjection i),
      a.hom ≫ pullback.snd (Zᵢ.hom ≫ pullback.snd s.X.hom (s.stageToBase i))
          (s.limitProjection i) =
        Z'.hom ≫ pullback.snd s.X.hom s.limitBaseChange.g := by
  have heSnd : e.hom.left ≫ pullback.snd Zᵢ.hom (s.stageProjection i) = Z'.hom := e.hom.w
  have hsq1 : IsPullback (e.hom.left ≫ pullback.fst Zᵢ.hom (s.stageProjection i)) Z'.hom
      Zᵢ.hom (s.stageProjection i) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩
      ((Over.forget (pullback s.X.hom s.limitBaseChange.g)).mapIso e) rfl heSnd
    rw [Category.assoc, pullback.condition, ← Category.assoc, heSnd]
  have h := hsq1.paste_vert (s.isPullback_stageProjection i)
  exact ⟨h.isoPullback, h.isoPullback_hom_snd⟩

/-- **Stacks Project, Tag 0FVQ, descent of an integral closed subscheme.** An integral closed
subscheme of `X'` of delta-dimension `m` is the base change of an integral closed subscheme of
`X_i` of delta-dimension `m`, for some finite stage `i`. -/
theorem exists_integral_closedSubscheme_model
    (Z' : Over (pullback s.X.hom s.limitBaseChange.g))
    [IsClosedImmersion Z'.hom] [IsIntegral Z'.left] (m : ℤ)
    (hm : schemeDeltaDimension s.limitBaseChange.baseChange
      (Z'.hom ≫ pullback.snd s.X.hom s.limitBaseChange.g) = (m : EInt)) :
    ∃ (i : I) (Zᵢ : Over (pullback s.X.hom (s.stageToBase i)))
      (hclosed : IsClosedImmersion Zᵢ.hom),
      IsIntegral Zᵢ.left ∧
      @schemeDeltaDimension (s.stageSituation i) Zᵢ.left
        (Zᵢ.hom ≫ pullback.snd s.X.hom (s.stageToBase i))
        (by
          let _ : IsClosedImmersion Zᵢ.hom := hclosed
          exact AlgebraicGeometry.locallyOfFiniteType_comp Zᵢ.hom
            (pullback.snd s.X.hom (s.stageToBase i))) =
        (m : EInt) ∧
      Nonempty (Z' ≅ (Over.pullback (s.stageProjection i)).obj Zᵢ) := by
  obtain ⟨i, Zᵢ, hclosed, hintegral, hmodel⟩ := s.exists_integral_closedImmersion_model Z'
  let f : Zᵢ.left ⟶ (s.stageSituation i).S := Zᵢ.hom ≫ pullback.snd s.X.hom (s.stageToBase i)
  have hft : LocallyOfFiniteType f :=
    AlgebraicGeometry.locallyOfFiniteType_comp Zᵢ.hom (pullback.snd s.X.hom (s.stageToBase i))
  let p := s.limitProjection i
  let k : ℤ := relativeDimension (s.stageSituation i).dimensionFunction f (genericPoint Zᵢ.left)
  have hk : schemeDeltaDimension (s.stageSituation i) f = (k : EInt) :=
    schemeDeltaDimension_eq_genericPoint (s.stageSituation i) f
  obtain ⟨e⟩ := hmodel
  obtain ⟨a, ha⟩ := s.integralModel_baseChangeIso i Zᵢ Z' e
  have : IsIntegral (pullback f p : Scheme.{u}) := IsIntegral.of_isIso a.hom
  have hlft : LocallyOfFiniteType (pullback.snd f p) :=
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f p) hft
  let W : irreducibleComponents (pullback f p : Scheme.{u}) :=
    ⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩
  let _ : Subsingleton (irreducibleComponents (pullback f p : Scheme.{u})) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hdim := @deltaDimension_component_baseChange (s.stageToLimitBaseChange i) Zᵢ.left f hft
    hintegral k hk W
  have hdim₀ : deltaDimension s.limitBaseChange.baseChange (pullback.snd f p)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents
        (W : Set (pullback f p : Scheme.{u})) W.2⟩ = k := by
    change deltaDimension s.limitBaseChange.baseChange (pullback.snd f p)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents
        (W : Set (pullback f p : Scheme.{u})) W.2⟩ = k + 0 at hdim
    simpa only [add_zero] using hdim
  have hdim' : schemeDeltaDimension s.limitBaseChange.baseChange (pullback.snd f p) =
      (k : EInt) := by
    rw [schemeDeltaDimension_eq_iSup, ciSup_subsingleton W]
    exact congrArg (fun d : ℤ => (d : EInt)) hdim₀
  have hac : LocallyOfFiniteType (a.hom ≫ pullback.snd f p) :=
    @AlgebraicGeometry.locallyOfFiniteType_comp _ _ _ a.hom (pullback.snd f p) inferInstance hlft
  have htransport' : schemeDeltaDimension s.limitBaseChange.baseChange
      (Z'.hom ≫ pullback.snd s.X.hom s.limitBaseChange.g) =
      schemeDeltaDimension s.limitBaseChange.baseChange (pullback.snd f p) :=
    (schemeDeltaDimension_congr s.limitBaseChange.baseChange ha.symm).trans
      (schemeDeltaDimension_comp_iso s.limitBaseChange.baseChange (pullback.snd f p) a)
  have hmk : m = k := WithBotTop.coe_injective (hm.symm.trans (htransport'.trans hdim'))
  exact ⟨i, Zᵢ, hclosed, hintegral, by simpa only [f, hmk] using hk, ⟨e⟩⟩

end FilteredBaseChangeSystem

end Stacks.Chow

end
