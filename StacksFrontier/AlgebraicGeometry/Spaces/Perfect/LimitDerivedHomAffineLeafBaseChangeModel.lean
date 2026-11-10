module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectHomAffineLeafColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.BaseChange

/-!
# The base-changed system of Situation 09RH along an affine point, on its affine models

In Situation 09RH let `g : V ⟶ X₀` be a morphism onto the chosen stage from an algebraic space
`V` isomorphic, through `e : V ≅ h_T`, to the affine point `h_T`.  Two constructions of the base
changes `X_i ×_{X₀} V` are in use: the base-changed system
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of `g`, which is the system the leaf
of Stacks 09RI is stated on, and the base change of the situation along the affine point
`u = e⁻¹ ≫ g : h_T ⟶ X₀`, `AlgebraicGeometry.Space.DescentSituation.affinePointSituation`, whose
stages carry the chosen affine models
`AlgebraicGeometry.Space.DescentSituation.affineModelSystem` on which the colimit statement is
computed.  Both are fibre products of the same cospan, read over `V` through `e`, so they are
canonically isomorphic, and the isomorphisms are compatible with the transition morphisms, with
the projections from the limit and with the maps to `V`.

This file records those isomorphisms and assembles them into a morphism of systems over `h_T`,
from the affine models to the base-changed system read over `h_T` through `e`.  Every
isomorphism is `CategoryTheory.IsPullback.isoIsPullback` of two fibre squares, and every
compatibility follows from the uniqueness of maps into a fibre product.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.affinePointBaseChangeStageIso` and
  `affinePointBaseChangeLimitIso`: the base-changed stage `X_i ×_{X₀} h_T` and limit
  `X ×_{X₀} h_T` of the affine point are the stage `X_i ×_{X₀} V` and the vertex `X ×_{X₀} V` of
  the base-changed system.
* `AlgebraicGeometry.Space.DescentSituation.affineModelBaseChangeHom`: **the affine models map
  isomorphically onto the base-changed system**, as a morphism of systems over `h_T`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isPullback_affinePointStage_baseChange` and
  `isPullback_affinePointLimit_baseChange`: the base changes along the affine point are fibre
  products of the cospans defining the base-changed system.
* `AlgebraicGeometry.Space.DescentSituation.affinePointBaseChangeStageIso_comm` and
  `affinePointBaseChangeLimitIso_comm`: the isomorphisms commute with the transition morphisms
  and with the projections from the limit.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {V : AlgebraicSpaces B S hS} (g : V ⟶ D.stage D.base)
  {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (e : V.1 ≅ yoneda.obj T) (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hu : e.inv ≫ g.hom = u)

/-! ### The base-changed stages and limit of the affine point -/

include hu in
/-- **The base-changed stage `X_i ×_{X₀} h_T` of the affine point, read over `V` through `e`, is
a fibre product of the cospan `X_i ⟶ X₀ ⟵ V` defining the stage of the base-changed system.** -/
theorem isPullback_affinePointStage_baseChange (i : D.Stages) :
    IsPullback (affinePointStageFst hT u i) (affinePointStageSnd hT u i ≫ e.inv)
      (D.transition i.2).hom g.hom :=
  (isPullback_affinePointStage hT u i).of_iso (Iso.refl _) (Iso.refl _) e.symm
    (Iso.refl _) (by simp) (by simp)
    (by simp only [Iso.refl_hom, stagesToBase]; rfl)
    ((Category.comp_id u).trans hu.symm)

include hu in
/-- **The base-changed limit `X ×_{X₀} h_T` of the affine point, read over `V` through `e`, is a
fibre product of the cospan `X ⟶ X₀ ⟵ V` defining the vertex of the base-changed system.** -/
theorem isPullback_affinePointLimit_baseChange :
    IsPullback (affinePointLimitFst hT u) (affinePointLimitSnd hT u ≫ e.inv)
      (D.projection D.base).hom g.hom :=
  (isPullback_affinePointLimit hT u).of_iso (Iso.refl _) (Iso.refl _) e.symm
    (Iso.refl _) (by simp) (by simp)
    (by simp only [Iso.refl_hom]; rfl)
    ((Category.comp_id u).trans hu.symm)

/-- **The base-changed stage `X_i ×_{X₀} h_T` of the affine point is the stage `X_i ×_{X₀} V` of
the base-changed system.** -/
def affinePointBaseChangeStageIso (i : D.Stages) :
    (affinePointSituation D hT u).system.obj (op i) ≅ (baseChangeStage g i).1 :=
  (isPullback_affinePointStage_baseChange g hT e u hu i).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The isomorphism `affinePointBaseChangeStageIso` followed by the projection to `X_i` is the
first projection `affinePointStageFst` of `X_i ×_{X₀} h_T`. -/
@[reassoc (attr := simp)]
theorem affinePointBaseChangeStageIso_hom_toStage (i : D.Stages) :
    (affinePointBaseChangeStageIso g hT e u hu i).hom ≫ (baseChangeToStage g i).hom =
      affinePointStageFst hT u i :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `affinePointBaseChangeStageIso` followed by the projection to `V` is the
second projection `affinePointStageSnd` of `X_i ×_{X₀} h_T` composed with `e⁻¹`. -/
@[reassoc (attr := simp)]
theorem affinePointBaseChangeStageIso_hom_toBase (i : D.Stages) :
    (affinePointBaseChangeStageIso g hT e u hu i).hom ≫ (baseChangeToBase g i).hom =
      affinePointStageSnd hT u i ≫ e.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The base-changed limit `X ×_{X₀} h_T` of the affine point is the vertex `X ×_{X₀} V` of the
base-changed system.** -/
def affinePointBaseChangeLimitIso :
    (affinePointSituation D hT u).limitCone.pt ≅ (baseChangeLimit g).1 :=
  (isPullback_affinePointLimit_baseChange g hT e u hu).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- The isomorphism `affinePointBaseChangeLimitIso` followed by the projection to `X` is the
first projection `affinePointLimitFst` of `X ×_{X₀} h_T`. -/
@[reassoc (attr := simp)]
theorem affinePointBaseChangeLimitIso_hom_toLimitSpace :
    (affinePointBaseChangeLimitIso g hT e u hu).hom ≫ (baseChangeToLimitSpace g).hom =
      affinePointLimitFst hT u :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `affinePointBaseChangeLimitIso` followed by the projection to `V` is the
second projection `affinePointLimitSnd` of `X ×_{X₀} h_T` composed with `e⁻¹`. -/
@[reassoc (attr := simp)]
theorem affinePointBaseChangeLimitIso_hom_toBase :
    (affinePointBaseChangeLimitIso g hT e u hu).hom ≫ (baseChangeLimitToBase g).hom =
      affinePointLimitSnd hT u ≫ e.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- A morphism of presheaves into a base-changed stage is determined by its two projections. -/
theorem baseChangeStage_obj_hom_ext {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : D.Stages)
    {a b : W ⟶ (baseChangeStage g i).1}
    (h₁ : a ≫ (baseChangeToStage g i).hom = b ≫ (baseChangeToStage g i).hom)
    (h₂ : a ≫ (baseChangeToBase g i).hom = b ≫ (baseChangeToBase g i).hom) : a = b :=
  pullback.hom_ext h₁ h₂

/-- **The isomorphisms of the stages commute with the transition morphisms.** -/
theorem affinePointBaseChangeStageIso_comm {i j : D.Stages} (h : i ≤ j) :
    (affinePointBaseChangeStageIso g hT e u hu j).hom ≫ (baseChangeTransition g h).hom =
      (affinePointSituation D hT u).system.map (homOfLE h).op ≫
        (affinePointBaseChangeStageIso g hT e u hu i).hom := by
  refine baseChangeStage_obj_hom_ext g i ?_ ?_
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      baseChangeTransition_comp_toStage, ObjectProperty.FullSubcategory.comp_hom,
      affinePointBaseChangeStageIso_hom_toStage_assoc, Category.assoc,
      affinePointBaseChangeStageIso_hom_toStage]
    exact (affinePoint_map_comp_stageFst hT u h).symm
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      baseChangeTransition_comp_toBase, affinePointBaseChangeStageIso_hom_toBase, Category.assoc,
      affinePointBaseChangeStageIso_hom_toBase, affinePoint_map_comp_stageSnd_assoc]

/-- **The isomorphisms commute with the projections from the limit.** -/
theorem affinePointBaseChangeLimitIso_comm (j : D.Stages) :
    (affinePointBaseChangeLimitIso g hT e u hu).hom ≫ (baseChangeProjection g j).hom =
      (affinePointSituation D hT u).limitCone.π.app (op j) ≫
        (affinePointBaseChangeStageIso g hT e u hu j).hom := by
  refine baseChangeStage_obj_hom_ext g j ?_ ?_
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      baseChangeProjection_comp_toStage, ObjectProperty.FullSubcategory.comp_hom,
      affinePointBaseChangeLimitIso_hom_toLimitSpace_assoc, Category.assoc,
      affinePointBaseChangeStageIso_hom_toStage]
    exact (affinePoint_π_comp_stageFst hT u j).symm
  · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      baseChangeProjection_comp_toBase, affinePointBaseChangeLimitIso_hom_toBase, Category.assoc,
      affinePointBaseChangeStageIso_hom_toBase, ← Category.assoc, affinePoint_π_comp_stageSnd]

/-! ### The affine models as a system mapping onto the base-changed system -/

/-- The isomorphism of `V` with the affine point `h_T`, in the category of algebraic spaces. -/
abbrev baseChangeAffinePointIso :
    V ≅ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :=
  ObjectProperty.isoMk _ e

/-- The isomorphism of an affine model with the corresponding stage of the base-changed
system. -/
abbrev affineModelBaseChangeIso (i : D.Stages) :
    (⟨yoneda.obj (affineModel hT u i), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ baseChangeStage g i :=
  ObjectProperty.isoMk _
    ((affineModelIso hT u i).symm ≪≫ affinePointBaseChangeStageIso g hT e u hu i)

variable (hconv : SiteContainsBaseChangeLimits B S hS D.system)

/-- The isomorphism of the affine model of the limit with the vertex of the base-changed
system. -/
abbrev affineModelBaseChangeLimitIso :
    (⟨yoneda.obj (affineLimitModel hT u hconv), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ baseChangeLimit g :=
  ObjectProperty.isoMk _
    ((affineLimitModelIso hT u hconv).symm ≪≫ affinePointBaseChangeLimitIso g hT e u hu)

/-- **The affine models map isomorphically onto the base-changed system**, as a morphism of
systems over `h_T`: from `AlgebraicGeometry.Space.DescentSituation.affineModelSystem` to
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` read over `h_T` through `e`. -/
def affineModelBaseChangeHom :
    PullbackData.LimitSystem.Hom (affineModelSystem hT u hconv).toLimitSystem
      ((baseChangeSystem g).comp (baseChangeAffinePointIso e).hom) where
  app i := (affineModelBaseChangeIso g hT e u hu i).hom
  app_toBase i := ObjectProperty.hom_ext _ (by
    change ((affineModelIso hT u i).inv ≫
        (affinePointBaseChangeStageIso g hT e u hu i).hom) ≫
        (baseChangeToBase g i).hom ≫ e.hom =
      yoneda.map (yoneda.preimage ((affineModelIso hT u i).inv ≫
        affinePointStageSnd hT u i))
    rw [Functor.map_preimage, Category.assoc, affinePointBaseChangeStageIso_hom_toBase_assoc,
      Iso.inv_hom_id, Category.comp_id])
  app_transition {i j} h := ObjectProperty.hom_ext _ (by
    change ((affineModelIso hT u j).inv ≫
        (affinePointBaseChangeStageIso g hT e u hu j).hom) ≫ (baseChangeTransition g h).hom =
      yoneda.map (affineModelMap hT u h) ≫
        (affineModelIso hT u i).inv ≫ (affinePointBaseChangeStageIso g hT e u hu i).hom
    rw [yoneda_map_affineModelMap, Category.assoc, affinePointBaseChangeStageIso_comm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc])
  limitApp := (affineModelBaseChangeLimitIso g hT e u hu hconv).hom
  limitApp_toBase := ObjectProperty.hom_ext _ (by
    change ((affineLimitModelIso hT u hconv).inv ≫
        (affinePointBaseChangeLimitIso g hT e u hu).hom) ≫
        (baseChangeLimitToBase g).hom ≫ e.hom =
      yoneda.map (yoneda.preimage ((affineLimitModelIso hT u hconv).inv ≫
        affinePointLimitSnd hT u))
    rw [Functor.map_preimage, Category.assoc, affinePointBaseChangeLimitIso_hom_toBase_assoc,
      Iso.inv_hom_id, Category.comp_id])
  limitApp_proj j := ObjectProperty.hom_ext _ (by
    change ((affineLimitModelIso hT u hconv).inv ≫
        (affinePointBaseChangeLimitIso g hT e u hu).hom) ≫ (baseChangeProjection g j).hom =
      yoneda.map (affineLimitModelProj hT u hconv j) ≫
        (affineModelIso hT u j).inv ≫ (affinePointBaseChangeStageIso g hT e u hu j).hom
    rw [yoneda_map_affineLimitModelProj, Category.assoc, affinePointBaseChangeLimitIso_comm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc])

end DescentSituation

end AlgebraicGeometry.Space

end
