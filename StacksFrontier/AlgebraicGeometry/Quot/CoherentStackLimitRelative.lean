module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport

/-!
# `Coh_{X/Y} ⟶ Y` is limit preserving on objects, relative to `Y`

In Situation 08KB let `T = lim T_j` be a cofiltered limit of affine schemes of the big fppf site,
taken in schemes, and let `(T, g, F)` be an object of `Coh_{X/Y}` over `T` whose structure
morphism `g : T ⟶ Y` comes from a stage: `g = (T ⟶ T_i ⟶ Y)`. Then the module `F` is the inverse
image of a finitely presented module on some later stage `X_{T_j} = X ×_Y T_j`, flat over `T_j`
with support proper over `T_j`. No hypothesis is put on `Y`.

This is the essential surjectivity half of the proof of Stacks 08KD *after* its first step, which
uses that `Y` is locally of finite presentation over `S` to make the structure morphism come from a
stage: it says that the 1-morphism `Coh_{X/Y} ⟶ Y` is limit preserving on objects, which is the
form the proof of the second clause of Stacks 09TU consumes, where `Y` is an arbitrary algebraic
space.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_stage_module_of_stage`: the relative descent
  of objects of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.exists_coherentHom_stage_of_stage`: the same as a
  morphism of `Coh_{X/Y}` from the object to an object over the stage `T_j` whose structure
  morphism is `T_j ⟶ T_i ⟶ Y`. The descent of objects in the proof of Stacks 08KD,
  `AlgebraicGeometry.Space.CoherentSituation.descentObj_coherent`, is this statement after
  Stacks 05N0 has produced the stage `i`.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison)

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- **`Coh_{X/Y} ⟶ Y` is limit preserving on objects** (the relative form of the descent of
objects in the proof of Stacks 08KD). Let `T = lim T_j` be a cofiltered limit of affine schemes of
the site, taken in schemes, and let `A₀` be an object of `Coh_{X/Y}` over `T` whose structure
morphism is `T ⟶ T_i ⟶ Y` for a morphism `g : T_i ⟶ Y` from a stage, recorded by an isomorphism
`v` of `A₀.T` with the limit `T` of the test schemes above `i`. Then the module of `A₀` is the
inverse image, along `X_T ⟶ X_{T_j}`, of a finitely presented module on a later stage `X_{T_j}`
which is flat over `T_j` and has support proper over `T_j`.

The module comes from a stage by the essential surjectivity clause of Stacks 07V7 for the system of
base changes `X_{T_k}`, and its flatness and proper support descend to a later stage by Stacks 08K0
and 08K2 for that system. Nothing is asked of `Y`. -/
theorem exists_stage_module_of_stage (A₀ : CoherentObject D)
    (hA₀ : A₀.T.left = ((BigAffineFppf.inclusion B S hS).mapCone c).pt) {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (v : A₀.T ≅ (D.stageTestCone E c g).pt) (hv : v.hom.left = eqToHom hA₀) :
    ∃ (j : Over i) (Q : Modules.{u, u} B S hS (D.space ((D.stageTestSystem E g).obj j)).1
        (D.space ((D.stageTestSystem E g).obj j)).2),
      Q.IsFinitePresentationOnSite ∧ D.IsFlatWithProperSupport ((D.stageTestSystem E g).obj j) Q ∧
        Nonempty ((modulePullback B S hS
          (D.relativeMap (((D.stageTestCone E c g).extend v.hom).π.app j))).obj Q ≅ A₀.F) := by
  have hZ := B.contains_terminal
  let cT := (D.stageTestCone E c g).extend v.hom
  obtain ⟨-, -, hES⟩ := D.finitePresentationModule_isColimit_baseChange (D.stageTestSystem E g)
    cT hZ (fun e => D.isAffineHom_stageSpaceSystem_map E g e)
    (D.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
    (D.isLimit_stageSpaceCone_extend E c hc g v)
    (D.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  obtain ⟨k, Q, hQ, ⟨α⟩⟩ := hES A₀.F A₀.finitePresentation
  have hβ : (cT.π.app k).left =
      eqToHom hA₀ ≫ ((BigAffineFppf.inclusion B S hS).mapCone c).π.app k.left := by
    show v.hom.left ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app k.left) = _
    rw [hv]
    rfl
  obtain ⟨j, e, hfps⟩ :=
    D.flatProperSupportDescends E c hc A₀ hA₀ g k (cT.π.app k) hβ Q hQ α.symm
  exact ⟨j, (modulePullback B S hS (D.relativeMap ((D.stageTestSystem E g).map e))).obj Q,
    isFinitePresentationOnSite_modulePullback B S hS _ Q hQ, hfps,
    ⟨(pullbackComparison B S hS (D.relativeMap (cT.π.app j))
      (D.relativeMap ((D.stageTestSystem E g).map e)) (D.relativeMap (cT.π.app k))
      (D.relativeMap_cone_comp _ cT e) Q).symm ≪≫ α.symm⟩⟩

include hc in
/-- **`Coh_{X/Y} ⟶ Y` is limit preserving on objects, as a morphism of `Coh_{X/Y}`.** In the
situation of `AlgebraicGeometry.Space.CoherentSituation.exists_stage_module_of_stage`, every object
`A₀` of `Coh_{X/Y}` over the limit `T` whose structure morphism is `T ⟶ T_i ⟶ Y` receives a
morphism, lying over the projection `T ⟶ T_j`, to an object over a later stage `T_j` whose
structure morphism is `T_j ⟶ T_i ⟶ Y`. -/
theorem exists_coherentHom_stage_of_stage (A₀ : CoherentObject D)
    (hA₀ : A₀.T.left = ((BigAffineFppf.inclusion B S hS).mapCone c).pt) {i : I}
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶ D.Y)
    (hg : A₀.T.hom = (schemeSpaceFunctor B S hS).map
      (eqToHom hA₀ ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g) :
    ∃ (j : Over i) (xi : CoherentObject D) (hxi : xi.T = (D.stageTestSystem E g).obj j)
      (δ : CoherentHom A₀ xi),
      δ.base.left = eqToHom hA₀ ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.left) ≫
        eqToHom (congrArg CostructuredArrow.left hxi).symm := by
  let v : A₀.T ≅ (D.stageTestCone E c g).pt := CostructuredArrow.isoMk (eqToIso hA₀) (by
    show (schemeSpaceFunctor B S hS).map (eqToHom hA₀) ≫
      ((schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g) =
        A₀.T.hom
    rw [hg, Functor.map_comp, Category.assoc])
  obtain ⟨j, Q, hQ, hfps, ⟨α⟩⟩ := D.exists_stage_module_of_stage E c hc A₀ hA₀ g v rfl
  let xi : CoherentObject D :=
    { T := (D.stageTestSystem E g).obj j
      F := Q
      quasicoherent := by
        have := hQ
        infer_instance
      finitePresentation := hQ
      flat := hfps.1
      properSupport := hfps.2 }
  refine ⟨j, xi, rfl,
    { base := ((D.stageTestCone E c g).extend v.hom).π.app j
      fibre := α.hom
      isIso_fibre := inferInstance }, ?_⟩
  rfl

end AlgebraicGeometry.Space.CoherentSituation

end
