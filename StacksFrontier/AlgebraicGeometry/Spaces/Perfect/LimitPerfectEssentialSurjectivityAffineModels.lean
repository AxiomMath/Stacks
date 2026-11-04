module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions

/-!
# Affine models of the base change of Situation 09RH along an affine point

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — let `u : h_U ⟶ X₀` be a point of the chosen stage with `U` an affine object of
the big fppf site. This file restricts the situation to the stages at or beyond the chosen index,
base changes it along `u`, and represents the base-changed stages `X_i ×_{X₀} U` and the
base-changed limit `X ×_{X₀} U` by affine objects of the site: a filtered diagram of affine
objects with a cocone on it, whose rings of global functions are those of the base-changed
stages and limit. These are the affine data of the induction principle of Stacks 08GP over the
quasi-compact quasi-separated objects of `(X_0)_{spaces,étale}`, in the essential surjectivity
half of Stacks 09RJ.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.stagesSituation`: Situation 09RH restricted to the
  stages at or beyond its chosen index, `AlgebraicGeometry.Space.DescentSituation.Stages`, with
  limiting cone `AlgebraicGeometry.Space.DescentSituation.isLimitStagesCone` and the transition
  morphisms `X_i ⟶ X₀` as a natural transformation,
  `AlgebraicGeometry.Space.DescentSituation.stagesToBase`.
* `AlgebraicGeometry.Space.DescentSituation.affinePointSituation`: that restricted situation base
  changed along a point `u : h_U ⟶ X₀` of the chosen stage with `U` an affine object of the site,
  with stages `X_i ×_{X₀} U` and limit `X ×_{X₀} U`.
* `AlgebraicGeometry.Space.DescentSituation.affineModel`, `affineModelLimit`, `affineModelIso` and
  `affineModelLimitIso`: chosen affine objects of the site representing the base-changed stages
  and the base-changed limit, with their chosen isomorphisms.
* `AlgebraicGeometry.Space.DescentSituation.affineModelDiagram` and
  `AlgebraicGeometry.Space.DescentSituation.affineModelCocone`: the filtered diagram of the affine
  models of the base-changed stages, and the cocone on it with vertex the affine model of the
  base-changed limit.
* `AlgebraicGeometry.Space.DescentSituation.affineModelSectionsEquiv` and
  `affineModelLimitSectionsEquiv`: the rings of global functions of the affine models, identified
  with the rings of global functions of the base-changed stages and limit.

## Main results

* `Stacks.isColimit_commRingCat_of_elementwise`: a cocone of commutative rings over a filtered
  diagram is a colimit cocone as soon as every element of the vertex comes from a stage and two
  elements of one stage with the same image agree at a later stage.
* `AlgebraicGeometry.Space.DescentSituation.isAffineSpace_affinePointSituation_system` and
  `isAffineSpace_affinePointSituation_limitCone`: every stage and the limit of the base-changed
  situation are affine algebraic spaces, the latter by Stacks 07SF, part (1).
* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_affinePointSituation`:
  Stacks 07SI for the structure sheaf on the base-changed situation — the ring of global
  functions of `X ×_{X₀} U` is the filtered colimit of those of the `X_i ×_{X₀} U`.
* `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap_representedSpaceMap`:
  naturality of the identification of the global functions of a representable algebraic space
  with those of the representing object of the site.

## Implementation notes

The index set `I : Type u` lies in the universe of the site, and the results on the limit carry
the size hypothesis `hI : #I < B.cutoff.ord.cof` of Stacks 07SF. In the big fppf sites of this
library that hypothesis cannot be dropped: the site is a full subcategory of schemes cut out by a
cardinal bound, and
`AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj` refutes the
unbounded statement. No clause of Stacks 09RJ, 09RI or 09RF is assumed.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 70.5.1 (Tag 07SF)](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Lemma 70.5.6 (Tag 07SI)](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace Stacks

/-- **A cocone of commutative rings over a filtered diagram is a colimit as soon as it is one
elementwise**: if every element of the vertex comes from a stage, and two elements of one stage
with the same image in the vertex agree at a later stage, then the cocone is a colimit cocone.

This is the categorical form of `Stacks.IsStagesColimit` for a diagram of rings.  The two
clauses are the surjectivity and separation clauses of that structure; the compatibility clause
is already carried by the cocone. -/
def isColimit_commRingCat_of_elementwise {J : Type u} [Category.{u} J] [IsFiltered J]
    (A : J ⥤ CommRingCat.{u}) [Limits.PreservesColimit A (forget CommRingCat.{u})]
    (κ : Cocone A)
    (hsurj : ∀ t : κ.pt, ∃ (j : J) (x : A.obj j), (κ.ι.app j) x = t)
    (hsep : ∀ (j : J) (x y : A.obj j), (κ.ι.app j) x = (κ.ι.app j) y →
      ∃ (k : J) (f : j ⟶ k), (A.map f) x = (A.map f) y) :
    IsColimit κ := by
  have hL : IsColimit (colimit.cocone A) := colimit.isColimit A
  have hfac : ∀ (j : J) (x : A.obj j),
      (hL.desc κ) ((colimit.cocone A).ι.app j x) = (κ.ι.app j) x := by
    intro j x
    rw [← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom (hL.fac κ j) x
  have hbij : Function.Bijective (hL.desc κ) := by
    refine ⟨fun a b hab => ?_, fun t => ?_⟩
    · obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep A hL a
      obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep A hL b
      rw [hfac, hfac] at hab
      set k := IsFiltered.max i j with hk
      set f : i ⟶ k := IsFiltered.leftToMax i j with hf
      set g : j ⟶ k := IsFiltered.rightToMax i j with hg
      have hx : (κ.ι.app k) ((A.map f) x) = (κ.ι.app i) x := by
        rw [← ConcreteCategory.comp_apply]
        exact ConcreteCategory.congr_hom (κ.w f) x
      have hy : (κ.ι.app k) ((A.map g) y) = (κ.ι.app j) y := by
        rw [← ConcreteCategory.comp_apply]
        exact ConcreteCategory.congr_hom (κ.w g) y
      obtain ⟨m, h, hm⟩ := hsep k ((A.map f) x) ((A.map g) y) (by rw [hx, hy, hab])
      refine Concrete.isColimit_rep_eq_of_exists A x y ⟨m, f ≫ h, g ≫ h, ?_⟩
      rw [A.map_comp, A.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm]
    · obtain ⟨j, x, hx⟩ := hsurj t
      exact ⟨(colimit.cocone A).ι.app j x, by rw [hfac, hx]⟩
  have : IsIso (hL.desc κ) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  exact hL.ofPointIso

end Stacks

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The inclusion of the stages at or beyond the chosen index into the index set. -/
abbrev stagesInclusion : D.Stages ⥤ I := (Subtype.mono_coe fun i => D.base ≤ i).functor

/-- The inclusion of the stages into the index set is a final functor. -/
instance stagesInclusion_final : (stagesInclusion D).Final := by
  refine (Monotone.final_functor_iff (Subtype.mono_coe fun i => D.base ≤ i)).2 fun k => ?_
  obtain ⟨m, h₀, hk⟩ := exists_ge_ge D.base k
  exact ⟨⟨m, h₀⟩, hk⟩

/-- The inverse system of Situation 09RH, restricted to the stages at or beyond the chosen
index. -/
abbrev stagesSystem : (D.Stages)ᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (stagesInclusion D).op ⋙ D.system

/-- The chosen index of Situation 09RH, read as the least of its own stages. -/
abbrev baseStage : D.Stages := ⟨D.base, le_refl D.base⟩

/-- The unique morphism of the opposite of the stages from a stage to the chosen one. -/
abbrev toBaseStage (j : (D.Stages)ᵒᵖ) : j ⟶ op (baseStage D) :=
  (homOfLE (show baseStage D ≤ j.unop from j.unop.2)).op

/-- The transition morphisms to the chosen stage, as a natural transformation from the
restricted system to the constant system at `X₀`. -/
def stagesToBase :
    stagesSystem D ⟶
      (Functor.const (D.Stages)ᵒᵖ).obj ((stagesSystem D).obj (op (baseStage D))) where
  app j := (stagesSystem D).map (toBaseStage D j)
  naturality {j k} φ := by
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
    rw [Category.comp_id, ← Functor.map_comp]
    exact congrArg (stagesSystem D).map (Subsingleton.elim _ _)

/-- The chosen limit cone of Situation 09RH, restricted to the stages. -/
abbrev stagesCone : Cone (stagesSystem D) := D.limitCone.whisker (stagesInclusion D).op

/-- The restricted cone is still limiting, the inclusion of the stages being final. -/
def isLimitStagesCone : IsLimit (stagesCone D) :=
  (Functor.Initial.isLimitWhiskerEquiv (stagesInclusion D).op D.limitCone).symm D.isLimit

/-- The projection of the restricted limit cone to a stage, followed by the transition morphism
to the chosen stage, is the projection to the chosen stage. -/
theorem stagesCone_π_comp (j : (D.Stages)ᵒᵖ) :
    (stagesCone D).π.app j ≫ (stagesToBase D).app j =
      (stagesCone D).π.app (op (baseStage D)) :=
  D.limitCone.w ((stagesInclusion D).op.map (toBaseStage D j))

/-- **Situation 09RH restricted to the stages at or beyond its chosen index.** -/
abbrev stagesSituation : DescentSituation B S hS hZ D.Stages where
  system := stagesSystem D
  algebraicSpace i := D.algebraicSpace i.1
  transition_affine _φ := D.transition_affine _
  quasiCompact i := D.quasiCompact i.1
  quasiSeparated i := D.quasiSeparated i.1
  limitCone := stagesCone D
  isLimit := isLimitStagesCone D
  limitAlgebraicSpace := D.limitAlgebraicSpace
  base := ⟨D.base, le_refl _⟩

/-! ### Base change of Situation 09RH along an affine point of the chosen stage -/

section AffinePoint

variable {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))

/-- **Situation 09RH restricted to its stages and base changed along an affine point
`u : h_U ⟶ X₀` of the chosen stage.** -/
abbrev affinePointSituation : DescentSituation B S hS hZ D.Stages :=
  (stagesSituation D).baseChangeOver B S hS hZ (D.algebraicSpace D.base)
    (D.quasiSeparated D.base) (stagesToBase D) ((stagesCone D).π.app (op (baseStage D)))
    (stagesCone_π_comp D) U hU u

/-- Every stage `X_i ×_{X₀} U` of the base-changed situation is an affine algebraic space: it
is affine over the affine space `h_U`, the transition morphism `X_i ⟶ X₀` being affine. -/
theorem isAffineSpace_affinePointSituation_system (i : D.Stages) :
    IsAffineSpace B S hS ((affinePointSituation D hU u).system.obj (op i)) :=
  IsAffineHom.isAffineSpace_source
    (IsAffineHom.of_isPullback (IsPullback.of_hasPullback _ u) (D.transition_affine _))
    (isAffineSpace_yoneda B S hS U hU)

/-- The limit `X ×_{X₀} U` of the base-changed situation is an affine algebraic space: it is
affine over the affine space `h_U`, the projection `X ⟶ X₀` being affine by Stacks 07SF. -/
theorem isAffineSpace_affinePointSituation_limitCone (hI : #I < B.cutoff.ord.cof) :
    IsAffineSpace B S hS (affinePointSituation D hU u).limitCone.pt :=
  IsAffineHom.isAffineSpace_source
    (IsAffineHom.of_isPullback (IsPullback.of_hasPullback _ u)
      (D.isAffineHom_limitCone_π hI (op D.base)))
    (isAffineSpace_yoneda B S hS U hU)

/-- **Stacks 07SI for the structure sheaf, on the base-changed situation**: the ring of global
functions of `X ×_{X₀} U` is the filtered colimit of those of the `X_i ×_{X₀} U`. -/
theorem isGlobalFunctionsColimit_affinePointSituation (hI : #I < B.cutoff.ord.cof) :
    (affinePointSituation D hU u).IsGlobalFunctionsColimit :=
  DescentSituation.isGlobalFunctionsColimit _ (lt_of_le_of_lt (mk_subtype_le _) hI)

end AffinePoint

end DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Naturality of the identification of the global functions of a representable algebraic
space with those of the representing object**, for the morphism of algebraic spaces
`AlgebraicGeometry.Space.representedSpaceMap` induced by a morphism of the site. -/
theorem globalFunctionsYonedaRingEquiv_globalFunctionsMap_representedSpaceMap
    {U' U : BigFppfOver B S hS}
    (g : U' ⟶ U) (s : globalFunctions' B S hS (yoneda.obj U)) :
    globalFunctionsYonedaRingEquiv B S hS U'
        (globalFunctionsMap B S hS (representedSpaceMap B S hS g) s) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom
        (globalFunctionsYonedaRingEquiv B S hS U s) :=
  globalFunctionsMap_val_chart B S hS (representedSpaceMap B S hS g)
    (idEtaleChart B S hS U) (idEtaleChart B S hS U') g
    ((Category.comp_id _).trans (Category.id_comp _).symm) s

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-! ### Affine models of the base-changed stages -/

section Model

variable {D : DescentSituation B S hS hZ I} {U : BigFppfOver B S hS}
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hI : #I < B.cutoff.ord.cof)

/-- A chosen affine object of the site representing the base-changed stage `X_i ×_{X₀} U`. -/
def affineModel (i : D.Stages) : BigFppfOver B S hS :=
  (isAffineSpace_affinePointSituation_system D hU u i).choose

/-- The affine model of a base-changed stage is affine. -/
instance isAffine_affineModel (i : D.Stages) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i)) :=
  (isAffineSpace_affinePointSituation_system D hU u i).choose_spec.1

/-- The chosen isomorphism of the base-changed stage with its affine model. -/
def affineModelIso (i : D.Stages) :
    (affinePointSituation D hU u).system.obj (op i) ≅ yoneda.obj (affineModel hU u i) :=
  (isAffineSpace_affinePointSituation_system D hU u i).choose_spec.2.some

/-- A chosen affine object of the site representing the base-changed limit `X ×_{X₀} U`. -/
def affineModelLimit : BigFppfOver B S hS :=
  (isAffineSpace_affinePointSituation_limitCone D hU u hI).choose

/-- The affine model of the base-changed limit is affine. -/
instance isAffine_affineModelLimit :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineModelLimit hU u hI)) :=
  (isAffineSpace_affinePointSituation_limitCone D hU u hI).choose_spec.1

/-- The chosen isomorphism of the base-changed limit with its affine model. -/
def affineModelLimitIso :
    (affinePointSituation D hU u).limitCone.pt ≅ yoneda.obj (affineModelLimit hU u hI) :=
  (isAffineSpace_affinePointSituation_limitCone D hU u hI).choose_spec.2.some

/-- The transition morphism of the affine models, read off the transition morphism of the
base-changed stages through the chosen isomorphisms. -/
def affineModelMap {i j : D.Stages} (h : i ≤ j) :
    affineModel hU u j ⟶ affineModel hU u i :=
  yoneda.preimage ((affineModelIso hU u j).inv ≫
    (affinePointSituation D hU u).system.map (homOfLE h).op ≫ (affineModelIso hU u i).hom)

/-- The image under the Yoneda embedding of the transition morphism of the affine models is the
transition morphism of the base-changed stages, conjugated by the chosen isomorphisms. -/
theorem yoneda_map_affineModelMap {i j : D.Stages} (h : i ≤ j) :
    yoneda.map (affineModelMap hU u h) = (affineModelIso hU u j).inv ≫
      (affinePointSituation D hU u).system.map (homOfLE h).op ≫ (affineModelIso hU u i).hom :=
  yoneda.map_preimage _

/-- The projection from the affine model of the base-changed limit to the affine model of a
base-changed stage, read off the projection of the limit cone. -/
def affineModelProj (i : D.Stages) : affineModelLimit hU u hI ⟶ affineModel hU u i :=
  yoneda.preimage ((affineModelLimitIso hU u hI).inv ≫
    (affinePointSituation D hU u).limitCone.π.app (op i) ≫ (affineModelIso hU u i).hom)

/-- The image under the Yoneda embedding of the projection of the affine models is the projection
of the base-changed limit cone, conjugated by the chosen isomorphisms. -/
theorem yoneda_map_affineModelProj (i : D.Stages) :
    yoneda.map (affineModelProj hU u hI i) = (affineModelLimitIso hU u hI).inv ≫
      (affinePointSituation D hU u).limitCone.π.app (op i) ≫ (affineModelIso hU u i).hom :=
  yoneda.map_preimage _

/-- **The affine models of the base-changed stages, as a filtered diagram of affine objects of
the big fppf category over `S`**, written contravariantly as the transition morphisms of the
system point from the later stage to the earlier. -/
def affineModelDiagram : D.Stages ⥤ (BigFppfOver B S hS)ᵒᵖ where
  obj i := op (affineModel hU u i)
  map {i j} h := (affineModelMap hU u (leOfHom h)).op
  map_id i := by
    refine congrArg Quiver.Hom.op (yoneda.map_injective ?_)
    rw [yoneda_map_affineModelMap, CategoryTheory.Functor.map_id,
      show (affinePointSituation D hU u).system.map (homOfLE (leOfHom (𝟙 i))).op = 𝟙 _ from by
        rw [Subsingleton.elim (homOfLE (leOfHom (𝟙 i))).op (𝟙 (op i)),
          CategoryTheory.Functor.map_id],
      Category.id_comp, Iso.inv_hom_id]
  map_comp {i j k} h h' := by
    refine congrArg Quiver.Hom.op (yoneda.map_injective ?_)
    rw [yoneda_map_affineModelMap,
      Subsingleton.elim (homOfLE (leOfHom (h ≫ h'))).op
        ((homOfLE (leOfHom h')).op ≫ (homOfLE (leOfHom h)).op),
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    simp only [Quiver.Hom.unop_op, yoneda_map_affineModelMap, Category.assoc,
      Iso.hom_inv_id_assoc]

/-- The diagram of affine models sends a stage to its affine model. -/
@[simp]
theorem affineModelDiagram_obj (i : D.Stages) :
    (affineModelDiagram hU u).obj i = op (affineModel hU u i) := rfl

/-- The diagram of affine models sends a morphism of stages to the opposite of the transition
morphism of the affine models. -/
@[simp]
theorem affineModelDiagram_map {i j : D.Stages} (h : i ⟶ j) :
    (affineModelDiagram hU u).map h = (affineModelMap hU u (leOfHom h)).op := rfl

/-- **The affine model of the base-changed limit, as the vertex of a cocone on the diagram of
the affine models of the base-changed stages.** -/
def affineModelCocone : Cocone (affineModelDiagram hU u) where
  pt := op (affineModelLimit hU u hI)
  ι :=
    { app := fun i => (affineModelProj hU u hI i).op
      naturality := fun {i j} h => by
        have key : affineModelProj hU u hI j ≫ affineModelMap hU u (leOfHom h) =
            affineModelProj hU u hI i := by
          refine yoneda.map_injective ?_
          rw [CategoryTheory.Functor.map_comp, yoneda_map_affineModelProj,
            yoneda_map_affineModelMap, yoneda_map_affineModelProj]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rw [← Category.assoc ((affinePointSituation D hU u).limitCone.π.app (op j)),
            (affinePointSituation D hU u).limitCone.w (homOfLE (leOfHom h)).op]
        exact (congrArg Quiver.Hom.op key).trans (Category.comp_id _).symm }

/-- The vertex of the cocone of affine models is the affine model of the base-changed limit. -/
@[simp]
theorem affineModelCocone_pt : (affineModelCocone hU u hI).pt = op (affineModelLimit hU u hI) :=
  rfl

/-- The leg of the cocone of affine models at a stage is the opposite of the projection of the
affine models. -/
@[simp]
theorem affineModelCocone_ι_app (i : D.Stages) :
    (affineModelCocone hU u hI).ι.app i = (affineModelProj hU u hI i).op := rfl

/-! ### The rings of global functions of the affine models -/

/-- The isomorphism of the base-changed stage with its affine model, in the category of
algebraic spaces over the base. -/
def affineModelSpaceIso (i : D.Stages) :
    (affinePointSituation D hU u).stage i ≅
      (⟨yoneda.obj (affineModel hU u i),
        isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ (affineModelIso hU u i)

/-- The isomorphism of the base-changed limit with its affine model, in the category of
algebraic spaces over the base. -/
def affineModelLimitSpaceIso :
    (affinePointSituation D hU u).limitSpace ≅
      (⟨yoneda.obj (affineModelLimit hU u hI),
        isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ (affineModelLimitIso hU u hI)

/-- The ring of global functions of a base-changed stage, identified with the ring of global
functions of its affine model. -/
def affineModelSectionsEquiv (i : D.Stages) :
    Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤) ≃+*
      globalFunctions' B S hS ((affinePointSituation D hU u).stage i).obj :=
  (globalFunctionsYonedaRingEquiv B S hS (affineModel hU u i)).symm.trans
    (globalFunctionsMapEquiv B S hS (affineModelSpaceIso hU u i))

/-- The ring of global functions of the base-changed limit, identified with the ring of global
functions of its affine model. -/
def affineModelLimitSectionsEquiv :
    Γ((BigFppfOver.toScheme B S hS).obj (affineModelLimit hU u hI), ⊤) ≃+*
      globalFunctions' B S hS (affinePointSituation D hU u).limitSpace.obj :=
  (globalFunctionsYonedaRingEquiv B S hS (affineModelLimit hU u hI)).symm.trans
    (globalFunctionsMapEquiv B S hS (affineModelLimitSpaceIso hU u hI))

end Model

end DescentSituation

end AlgebraicGeometry.Space

end
