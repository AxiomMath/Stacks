module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineSystemPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectAffinePointConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackAlongIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFinitePresentationFibreProduct

/-!
# Situation 09RH as a relative situation, and its base changes along an affine point

Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated algebraic
spaces with affine transitions, a limit `X` and a chosen index `0` — is the special case of
Situation 0DKU in which the flat space of finite presentation over the chosen stage is the chosen
stage itself, with its identity morphism: the base changes are then the stages and the limit
themselves.

For an affine point `u : h_T ⟶ X₀`, the base changes `X_i ×_{X₀} h_T` and `X ×_{X₀} h_T` have
chosen affine models (`AlgebraicGeometry.Space.DescentSituation.affineModel`), which form a
directed system of affine representables over `h_T` whose rings of global functions form a
filtered colimit (Stacks 07SI). When `h_T ≅ U₀` over `X₀`, the base changes are the stages and the
limit of the situation restricted along `U₀ ⟶ X₀`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.toRelative`: Situation 09RH as Situation 0DKU with the
  identity of the chosen stage.
* `AlgebraicGeometry.Space.DescentSituation.affineModelSystem`: the affine models of the base
  changes along an affine point, as a directed system of affine representables.
* `AlgebraicGeometry.Space.DescentSituation.affinePointRestrictStageIso` and
  `AlgebraicGeometry.Space.DescentSituation.affinePointRestrictLimitIso`: the base-changed stages
  and limit are the stages and limit of the restricted relative situation.

## Main results

* `CategoryTheory.PullbackData.bijective_factorHom_of_fullyFaithful`: the map of morphism sets
  attached to a factorisation through a fully faithful inverse image is bijective.
* `AlgebraicGeometry.Space.DescentSituation.isRingColimit_affineModelSystem`: the rings of global
  functions of the affine models form a filtered colimit.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Situation 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe w u

/-- **The map of morphism sets attached to a factorisation through a fully faithful inverse image
is bijective.** -/
theorem CategoryTheory.PullbackData.bijective_factorHom_of_fullyFaithful {A : Type*}
    [Category A] {D : A → Type*} [∀ a, Category (D a)] (P : PullbackData A D) {a b c : A}
    {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) (hf : (P.pull f).FullyFaithful)
    (X Y : D c) : Function.Bijective (P.factorHom h (X := X) (Y := Y)) :=
  (((P.triangle h).app X).homCongr ((P.triangle h).app Y)).symm.bijective.comp
    (hf.map_bijective _ _)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

/-! ### Situation 09RH as Situation 0DKU -/

section Relative

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Situation 09RH as Situation 0DKU**: the inverse system, its limit and its chosen index are
those of the situation, the flat space of finite presentation over the chosen stage is that stage
with its identity morphism, and the base changes are the stages and the limit themselves. -/
def toRelative : RelativeDescentSituation B S hS hZ I where
  Y := D.system
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.algebraicSpace
  limit_isAlgebraicSpace := D.limitAlgebraicSpace
  stage_isQuasiCompact := D.quasiCompact
  stage_isQuasiSeparated := D.quasiSeparated
  transition_isAffine _ _ _ := D.transition_affine _
  i₀ := D.base
  X₀ := D.system.obj (op D.base)
  p₀ := 𝟙 _
  initial_isAlgebraicSpace := D.algebraicSpace D.base
  initial_isFlat := isFlat_id B S hS (D.algebraicSpace D.base)
  initial_isFinitePresentation := isFinitePresentation_id B S hS (D.algebraicSpace D.base)
  Xᵢ i _ := D.system.obj (op i)
  stageX_isAlgebraicSpace i _ := D.algebraicSpace i
  toX₀ _ hi := D.system.map (homOfLE hi).op
  toYᵢ _ _ := 𝟙 _
  stage_isPullback _ hi := IsPullback.id_horiz _
  fᵢⱼ _ _ _ _ hij := D.system.map (homOfLE hij).op
  fᵢⱼ_toYᵢ _ _ _ _ _ := by simp
  fᵢⱼ_toX₀ _ _ _ _ _ := by
    rw [← Functor.map_comp]
    rfl
  X := D.limitCone.pt
  X_isAlgebraicSpace := D.limitAlgebraicSpace
  toInitial := D.limitCone.π.app (op D.base)
  toLimit := 𝟙 _
  limit_isPullback := IsPullback.id_horiz _
  fᵢ i _ := D.limitCone.π.app (op i)
  fᵢ_toYᵢ _ _ := by simp
  fᵢ_toX₀ _ hi := D.limitCone.w (homOfLE hi).op

end Relative

/-! ### The affine case -/

section Affine

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {T : BigFppfOver B S hS}
  (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hconv : SiteContainsBaseChangeLimits B S hS D.system)

/-- The projection of a base-changed stage `X_i ×_{X₀} U` to the affine point `U`. -/
def affinePointStageSnd (i : D.Stages) :
    (affinePointSituation D hT u).system.obj (op i) ⟶ yoneda.obj T :=
  pullback.snd _ u

/-- The projection of the base-changed limit `X ×_{X₀} U` to the affine point `U`. -/
def affinePointLimitSnd : (affinePointSituation D hT u).limitCone.pt ⟶ yoneda.obj T :=
  pullback.snd _ u

/-- The transition maps of the base-changed stages commute with the projections to `U`. -/
@[reassoc]
theorem affinePoint_map_comp_stageSnd {i j : D.Stages} (h : i ≤ j) :
    (affinePointSituation D hT u).system.map (homOfLE h).op ≫ affinePointStageSnd hT u i =
      affinePointStageSnd hT u j :=
  baseChangeOverSystem_map_snd B S hS (stagesSystem D) (stagesToBase D) u (homOfLE h).op

/-- The projection of the base-changed limit to a base-changed stage commutes with the projections
to `U`. -/
@[reassoc]
theorem affinePoint_π_comp_stageSnd (i : D.Stages) :
    (affinePointSituation D hT u).limitCone.π.app (op i) ≫ affinePointStageSnd hT u i =
      affinePointLimitSnd hT u :=
  pullback.lift_snd _ _ _

/-- **The affine models of the base changes of Situation 09RH along an affine point**, as a
directed system of affine representables over the point. -/
def affineModelSystem : RepresentedAffineSystem T D.Stages where
  obj i := affineModel hT u i
  isAffine_obj i := inferInstance
  toBase i := yoneda.preimage ((affineModelIso hT u i).inv ≫ affinePointStageSnd hT u i)
  map h := affineModelMap hT u h
  map_toBase {i j} h := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_affineModelMap, Functor.map_preimage,
      Functor.map_preimage]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, affinePoint_map_comp_stageSnd])
  map_comp {i j k} h h' := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_affineModelMap, yoneda_map_affineModelMap,
      yoneda_map_affineModelMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]
    exact congrArg (fun m => (affineModelIso hT u k).inv ≫
      (affinePointSituation D hT u).system.map m ≫ (affineModelIso hT u i).hom)
        (Subsingleton.elim _ _))
  lim := affineLimitModel hT u hconv
  isAffine_lim := inferInstance
  limToBase := yoneda.preimage ((affineLimitModelIso hT u hconv).inv ≫ affinePointLimitSnd hT u)
  proj i := affineLimitModelProj hT u hconv i
  proj_toBase i := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_affineLimitModelProj, Functor.map_preimage,
      Functor.map_preimage]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, affinePoint_π_comp_stageSnd])
  proj_map {i j} h := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_affineLimitModelProj, yoneda_map_affineModelMap,
      yoneda_map_affineLimitModelProj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((affinePointSituation D hT u).limitCone.π.app (op j)),
      (affinePointSituation D hT u).limitCone.w (homOfLE h).op])

/-- The rings of global functions of the affine models form a filtered colimit (Stacks 07SI). -/
theorem isRingColimit_affineModelSystem : (affineModelSystem hT u hconv).IsRingColimit :=
  isStagesColimit_affineLimitModelSections hT u hconv

/-- The projection of a base-changed stage `X_i ×_{X₀} U` to the stage `X_i`. -/
def affinePointStageFst (i : D.Stages) :
    (affinePointSituation D hT u).system.obj (op i) ⟶ D.system.obj (op i.1) :=
  pullback.fst _ u

/-- The projection of the base-changed limit `X ×_{X₀} U` to the limit `X`. -/
def affinePointLimitFst : (affinePointSituation D hT u).limitCone.pt ⟶ D.limitCone.pt :=
  pullback.fst _ u

/-- A base-changed stage `X_i ×_{X₀} U` is the fibre product of `X_i ⟶ X₀` and `u`. -/
theorem isPullback_affinePointStage (i : D.Stages) :
    IsPullback (affinePointStageFst hT u i) (affinePointStageSnd hT u i)
      ((stagesToBase D).app (op i)) u :=
  IsPullback.of_hasPullback _ _

/-- The base-changed limit `X ×_{X₀} U` is the fibre product of `X ⟶ X₀` and `u`. -/
theorem isPullback_affinePointLimit :
    IsPullback (affinePointLimitFst hT u) (affinePointLimitSnd hT u)
      ((stagesCone D).π.app (op (baseStage D))) u :=
  IsPullback.of_hasPullback _ _

/-- The transition maps of the base-changed stages commute with the projections to the stages. -/
@[reassoc]
theorem affinePoint_map_comp_stageFst {i j : D.Stages} (h : i ≤ j) :
    (affinePointSituation D hT u).system.map (homOfLE h).op ≫ affinePointStageFst hT u i =
      affinePointStageFst hT u j ≫ D.system.map (homOfLE h).op :=
  baseChangeOverSystem_map_fst B S hS (stagesSystem D) (stagesToBase D) u (homOfLE h).op

/-- The projections of the base-changed limit and of the limit to the stages commute with the
projections to `X_i` and `X`. -/
@[reassoc]
theorem affinePoint_π_comp_stageFst (i : D.Stages) :
    (affinePointSituation D hT u).limitCone.π.app (op i) ≫ affinePointStageFst hT u i =
      affinePointLimitFst hT u ≫ D.limitCone.π.app (op i.1) :=
  pullback.lift_fst _ _ _

end Affine

/-! ### Transport to the restricted situation -/

section Transport

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.toRelative.X₀)
  (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)
  {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  (e : U₀ ≅ yoneda.obj T) (u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hu : e.inv ≫ g = u) (hconv : SiteContainsBaseChangeLimits B S hS D.system)

/-- A pullback square whose base-change map `u` factors as `e.inv ≫ g` is a pullback square over
`g` after composing the second projection with `e.inv`. -/
private theorem isPullback_comp_inv_of_iso {C : Type*} [Category C] {P A U U₀ X : C}
    {fst : P ⟶ A} {snd : P ⟶ U} {f : A ⟶ X} {u : U ⟶ X} {g : U₀ ⟶ X}
    (h : IsPullback fst snd f u) (e : U₀ ≅ U) (hu : e.inv ≫ g = u) :
    IsPullback fst (snd ≫ e.inv) f (g ≫ 𝟙 X) :=
  h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by change u ≫ 𝟙 _ = e.inv ≫ (g ≫ 𝟙 _); simp only [Category.comp_id]; exact hu.symm)

include hu in
/-- A base-changed stage `X_i ×_{X₀} U` of the affine point, read over `U₀` through `e`, is a
fibre product of the same cospan as the corresponding stage of the restricted situation. -/
theorem isPullback_affinePointStage_restrict (i : D.Stages) :
    IsPullback (affinePointStageFst hT u i)
      (affinePointStageSnd hT u i ≫ e.inv)
      ((D.toRelative.restrict hU₀ g hgflat hgfp).Y.map (homOfLE i.2).op)
      (D.toRelative.restrict hU₀ g hgflat hgfp).p₀ :=
  isPullback_comp_inv_of_iso (isPullback_affinePointStage hT u i) e hu

/-- The base-changed stage `X_i ×_{X₀} U` of the affine point is the corresponding stage of the
restricted relative situation. -/
def affinePointRestrictStageIso (i : D.Stages) :
    (affinePointSituation D hT u).system.obj (op i) ≅
      (D.toRelative.restrict hU₀ g hgflat hgfp).Xᵢ i.1 i.2 :=
  (isPullback_affinePointStage_restrict hU₀ g hgflat hgfp hT e u hu i).isoIsPullback _ _
    ((D.toRelative.restrict hU₀ g hgflat hgfp).stage_isPullback i.1 i.2)

/-- The identification of a base-changed stage with a restricted stage, followed by the map to
`X_i`, is the projection to `X_i`. -/
@[reassoc]
theorem affinePointRestrictStageIso_hom_toYᵢ (i : D.Stages) :
    (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom ≫
        (D.toRelative.restrict hU₀ g hgflat hgfp).toYᵢ i.1 i.2 =
      affinePointStageFst hT u i :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification of a base-changed stage with a restricted stage, followed by the map to
`U₀`, is the projection to `U` followed by `e.inv`. -/
@[reassoc]
theorem affinePointRestrictStageIso_hom_toX₀ (i : D.Stages) :
    (affinePointRestrictStageIso hU₀ g hgflat hgfp hT e u hu i).hom ≫
        (D.toRelative.restrict hU₀ g hgflat hgfp).toX₀ i.1 i.2 =
      affinePointStageSnd hT u i ≫ e.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

include hu in
/-- The base-changed limit `X ×_{X₀} U` of the affine point, read over `U₀` through `e`, is a fibre
product of the same cospan as the limit of the restricted situation. -/
theorem isPullback_affinePointLimit_restrict :
    IsPullback (affinePointLimitFst hT u) (affinePointLimitSnd hT u ≫ e.inv)
      ((D.toRelative.restrict hU₀ g hgflat hgfp).limitCone.π.app
        (op (D.toRelative.restrict hU₀ g hgflat hgfp).i₀))
      (D.toRelative.restrict hU₀ g hgflat hgfp).p₀ :=
  isPullback_comp_inv_of_iso (isPullback_affinePointLimit hT u) e hu

/-- The base-changed limit `X ×_{X₀} U` of the affine point is the limit of the restricted
relative situation. -/
def affinePointRestrictLimitIso :
    (affinePointSituation D hT u).limitCone.pt ≅
      (D.toRelative.restrict hU₀ g hgflat hgfp).X :=
  (isPullback_affinePointLimit_restrict hU₀ g hgflat hgfp hT e u hu).isoIsPullback _ _
    (D.toRelative.restrict hU₀ g hgflat hgfp).limit_isPullback

/-- The identification of the base-changed limit with the restricted limit, followed by the map to
`X`, is the projection to `X`. -/
@[reassoc]
theorem affinePointRestrictLimitIso_hom_toLimit :
    (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom ≫
        (D.toRelative.restrict hU₀ g hgflat hgfp).toLimit =
      affinePointLimitFst hT u :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification of the base-changed limit with the restricted limit, followed by the map to
`U₀`, is the projection to `U` followed by `e.inv`. -/
@[reassoc]
theorem affinePointRestrictLimitIso_hom_toInitial :
    (affinePointRestrictLimitIso hU₀ g hgflat hgfp hT e u hu).hom ≫
        (D.toRelative.restrict hU₀ g hgflat hgfp).toInitial =
      affinePointLimitSnd hT u ≫ e.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end Transport

end DescentSituation

end AlgebraicGeometry.Space

end
