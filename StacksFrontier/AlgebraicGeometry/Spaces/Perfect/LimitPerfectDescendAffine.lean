module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescendSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectAffinePointConvention

/-!
# The affine case of the descent of perfect objects along Situation 09RH

In Situation 09RH let `j ↦ W_j` be a directed system over an affine algebraic space `W`,
presented as the base change of the situation along `W ⟶ X₀`
(`AlgebraicGeometry.Space.DescentSituation.BaseChangeData`).  This file proves that perfect
objects descend along `j ↦ W_j` (`AlgebraicGeometry.Space.PerfectObjectsDescend`): every perfect
object of `D(𝒪_{W_∞})` is the derived pullback of a perfect object of some `D(𝒪_{W_j})`.  This is
the affine case of the induction of Stacks 08GP for the essential surjectivity half of
Stacks 09RJ.

Writing `W ≅ h_T` for an affine object `T` of the big fppf site, the system is identified, stage
by stage and at the vertex, with the base change of Situation 09RH along the affine point
`h_T ⟶ X₀` (`AlgebraicGeometry.Space.DescentSituation.affinePointSituation`), both being fibre
products of the same cospans; for that base change the statement is
`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affinePointStage`.  Descent of perfect
objects is invariant under such an identification
(`AlgebraicGeometry.Space.PerfectObjectsDescend.of_iso`).

## Main results

* `AlgebraicGeometry.Space.PerfectObjectsDescend.of_iso`.
* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.perfectObjectsDescend_of_isAffineSpace`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Descent of perfect objects is invariant under isomorphism** of the source and of the targets
compatible with the morphisms. -/
theorem PerfectObjectsDescend.of_iso {J : Type w} {X X' : AlgebraicSpaces B S hS}
    {Y Y' : J → AlgebraicSpaces B S hS} {p : ∀ j, X ⟶ Y j} {p' : ∀ j, X' ⟶ Y' j}
    (h : PerfectObjectsDescend p) (eX : X ≅ X') (eY : ∀ j, Y j ≅ Y' j)
    (he : ∀ j, p j ≫ (eY j).hom = eX.hom ≫ p' j) : PerfectObjectsDescend p' := by
  intro E' hE'
  obtain ⟨j, A, hA, ⟨α⟩⟩ := h _ (isPerfect_smallEtaleDerivedModulePullback eX.hom E' hE')
  have h₁ : p' j ≫ (eY j).inv = eX.inv ≫ p j := by
    rw [← cancel_mono (eY j).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, he, Iso.inv_hom_id_assoc]
  refine ⟨j, (smallEtaleDerivedModulePullback B S hS (eY j).inv).obj A,
    isPerfect_smallEtaleDerivedModulePullback (eY j).inv A hA, ⟨?_⟩⟩
  exact ((DerivedPullbackComposition.canonical B S hS).iso (p' j) (eY j).inv _ h₁).app A ≪≫
    ((DerivedPullbackComposition.canonical B S hS).iso eX.inv (p j) _ rfl).symm.app A ≪≫
    (smallEtaleDerivedModulePullback B S hS eX.inv).mapIso α ≪≫
    ((DerivedPullbackComposition.canonical B S hS).iso eX.inv eX.hom (𝟙 _)
      eX.inv_hom_id).app E' ≪≫
    ((DerivedPullbackComposition.canonical B S hS).idIso X').app E'

/-- A pullback square whose base map is `e.inv ≫ g` is a pullback square over `g` after composing
the second projection with `e.inv`. -/
private theorem isPullback_comp_inv_snd {C : Type*} [Category C] {P X Y Z W : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : W ⟶ Z} (e : W ≅ Y) (h : IsPullback fst snd f (e.inv ≫ g)) :
    IsPullback fst (snd ≫ e.inv) f g :=
  h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp)

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {W : AlgebraicSpaces B S hS} {y : W ⟶ D.stage D.base}
  {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}

namespace BaseChangeData

/-- **The affine case of the descent of perfect objects along Situation 09RH.**  Perfect objects
descend along a presented system over an affine algebraic space. -/
theorem perfectObjectsDescend_of_isAffineSpace (β : D.BaseChangeData y Sys)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) (hW : IsAffineSpace B S hS W.1) :
    PerfectObjectsDescend Sys.proj := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hW
  set u : yoneda.obj T ⟶ (stagesSystem D).obj (op (baseStage D)) := e.inv ≫ y.hom with hu
  have hstage : ∀ j : D.Stages, IsPullback (affinePointStageFst hT u j)
      (affinePointStageSnd hT u j ≫ e.inv) ((stagesToBase D).app (op j)) (stagePoint D y) :=
    fun j => isPullback_comp_inv_snd e (isPullback_affinePointStage hT u j)
  have hlimit : IsPullback (affinePointLimitFst hT u) (affinePointLimitSnd hT u ≫ e.inv)
      ((stagesCone D).π.app (op (baseStage D))) (stagePoint D y) :=
    isPullback_comp_inv_snd e (isPullback_affinePointLimit hT u)
  let eY : ∀ j : D.Stages, (affinePointSituation D hT u).stage j ≅ Sys.stage j := fun j =>
    ObjectProperty.isoMk _ ((hstage j).isoIsPullback _ _ (β.isPullback_stagesToBase j))
  let eX : (affinePointSituation D hT u).limitSpace ≅ Sys.limit :=
    ObjectProperty.isoMk _ (hlimit.isoIsPullback _ _ β.limit_isPullback_stagesCone)
  have hYfst : ∀ j, (eY j).hom ≫ β.fst j = ObjectProperty.homMk (affinePointStageFst hT u j) :=
    fun j => ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)
  have hYsnd : ∀ j, (eY j).hom ≫ Sys.toBase j =
      ObjectProperty.homMk (affinePointStageSnd hT u j ≫ e.inv) :=
    fun j => ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)
  have hXfst : eX.hom ≫ β.limitFst = ObjectProperty.homMk (affinePointLimitFst hT u) :=
    ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)
  have hXsnd : eX.hom ≫ Sys.limitToBase =
      ObjectProperty.homMk (affinePointLimitSnd hT u ≫ e.inv) :=
    ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)
  refine PerfectObjectsDescend.of_iso (p := fun j => (affinePointSituation D hT u).projection j)
    (fun E hE => exists_isPerfect_affinePointStage_of_siteContainsBaseChangeLimits hT u hconv E hE)
    eX eY fun j => β.stage_hom_ext j ?_ ?_
  · rw [Category.assoc, hYfst, Category.assoc, β.limitFst_proj, ← Category.assoc, hXfst]
    exact ObjectProperty.hom_ext _ (affinePoint_π_comp_stageFst hT u j)
  · rw [Category.assoc, hYsnd, Category.assoc, Sys.proj_toBase, hXsnd]
    exact ObjectProperty.hom_ext _ (affinePoint_π_comp_stageSnd_assoc hT u j e.inv)

end BaseChangeData

end DescentSituation

end AlgebraicGeometry.Space

end
