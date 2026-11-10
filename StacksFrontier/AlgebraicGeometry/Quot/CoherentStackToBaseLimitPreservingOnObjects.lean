module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitRelative
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# `Coh_{X/Y} ⟶ 𝒮_Y` is limit preserving on objects

In Situation 08KB let `f : X ⟶ Y` be a morphism of finite presentation of algebraic spaces over
`S`, and let `T = lim T_j` be a cofiltered limit of affine schemes of the big fppf site, taken in
schemes. An object `(T, g, F)` of `Coh_{X/Y}` whose structure morphism `g : T ⟶ Y` comes from a
stage, `g = (T ⟶ T_i ⟶ Y)`, is the pullback of an object over a later stage `T_j` whose
structure morphism is `T_j ⟶ T_i ⟶ Y`; no hypothesis is put on `Y`. Equivalently, the projection
`Coh_{X/Y} ⟶ 𝒮_Y`, `(T, g, F) ↦ (T, g)`, is limit preserving on objects.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_stage_module_of_structureMap_stage`: the
  relative descent of the module of an object of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.exists_coherentHom_to_stage_of_structureMap_stage`:
  the same as a morphism of `Coh_{X/Y}` to an object over the stage.
* `AlgebraicGeometry.Space.CoherentSituation.isLimitPreservingOnObjects_toBaseCFG`: the
  projection `Coh_{X/Y} ⟶ 𝒮_Y` is limit preserving on objects, at index categories in the scheme
  universe.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
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

section StageDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS) (c : Cone E)
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

/-- **`Coh_{X/Y} ⟶ Y` is limit preserving on objects.** Let `T = lim T_j` be a cofiltered limit
of affine schemes of the site, taken in schemes, and let `A₀` be an object of `Coh_{X/Y}` over `T`
whose structure morphism is `T ⟶ T_i ⟶ Y` for a morphism `g : T_i ⟶ Y` from a stage, recorded by
an isomorphism `v` of `A₀.T` with the limit `T` of the test schemes above `i`. Then the module of
`A₀` is the inverse image, along `X_T ⟶ X_{T_j}`, of a finitely presented module on a later stage
`X_{T_j}` which is flat over `T_j` and has support proper over `T_j`. Nothing is asked of `Y`. -/
alias exists_stage_module_of_structureMap_stage := exists_stage_module_of_stage

/-- **`Coh_{X/Y} ⟶ Y` is limit preserving on objects, as a morphism of `Coh_{X/Y}`.** In the
situation of
`AlgebraicGeometry.Space.CoherentSituation.exists_stage_module_of_structureMap_stage`, every object
`A₀` of `Coh_{X/Y}` over the limit `T` whose structure morphism is `T ⟶ T_i ⟶ Y` receives a
morphism, lying over the projection `T ⟶ T_j`, to an object over a later stage `T_j` whose
structure morphism is `T_j ⟶ T_i ⟶ Y`. -/
alias exists_coherentHom_to_stage_of_structureMap_stage := exists_coherentHom_stage_of_stage

end StageDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Coh_{X/Y} ⟶ 𝒮_Y` is limit preserving on objects**, for a morphism
`f : X ⟶ Y` of finite presentation of algebraic spaces over `S` and no hypothesis on `Y`. Let
`T = lim T_j` be a cofiltered limit of affine schemes of the big fppf site, taken in schemes, and
let `x = (T, g, F)` be an object of `Coh_{X/Y}` whose image `(T, g)` in `𝒮_Y` is the pullback of
an object `y = (T_i, g_i)` along the projection `T ⟶ T_i`. Then `x` is, up to isomorphism over
`T`, the pullback of an object `x'` of `Coh_{X/Y}` over a later stage `T_j`, whose image in
`𝒮_Y` is the pullback of `y` along `T_j ⟶ T_i`, compatibly with the given comparison. -/
theorem isLimitPreservingOnObjects_toBaseCFG (D : CoherentSituation B S hS) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS (coherentCFG D) (baseCFG D.Y)
      D.toBaseCFG := by
  intro I _ _ E c hc i y x γ hγ
  rcases y with ⟨⟨yl, ⟨⟨⟩⟩, g⟩, hy⟩
  rcases x with ⟨⟨⟨xl, ⟨⟨⟩⟩, xh⟩, F, hqc, hfp, hfl, hps⟩, hx⟩
  change yl = _ at hy
  change xl = _ at hx
  subst hy hx
  let incl := BigAffineFppf.inclusion B S hS
  have hγl : γ.down.left = incl.map (c.π.app i) := by
    have h := IsHomLift.fac (baseCFG D.Y).val.p (incl.map (c.π.app i)) γ
    exact h.symm
  have hg : xh = (schemeSpaceFunctor B S hS).map (eqToHom rfl ≫ incl.map (c.π.app i)) ≫ g := by
    rw [eqToHom_refl, Category.id_comp, ← hγl]
    exact (CostructuredArrow.w γ.down).symm
  obtain ⟨j, ⟨xT, xF, h₁, h₂, h₃, h₄⟩, hxi, δ, hδ⟩ :=
    D.exists_coherentHom_to_stage_of_structureMap_stage E c hc
      ⟨⟨incl.obj c.pt, ⟨⟨⟩⟩, xh⟩, F, hqc, hfp, hfl, hps⟩ rfl g hg
  change xT = _ at hxi
  subst hxi
  let γ' : (D.stageTestSystem E g).obj j ⟶ CostructuredArrow.mk g :=
    CostructuredArrow.homMk (incl.map (E.map j.hom)) rfl
  refine ⟨j.left, j.hom, ⟨⟨_, xF, h₁, h₂, h₃, h₄⟩, rfl⟩, ⟨_, rfl⟩, δ, 𝟙 _, ULift.up γ', ?_, ?_,
    inferInstance, ?_, ?_⟩
  · have : (coherentCFG D).val.p.IsHomLift (incl.map (c.π.app j.left)) δ :=
      IsHomLift.of_fac' _ _ _ rfl rfl hδ
    exact (coherentCFG D).isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  · exact IsHomLift.id rfl
  · have : (baseCFG D.Y).val.p.IsHomLift (incl.map (E.map j.hom))
        (ULift.up γ' : ULiftHom.objUp ((D.stageTestSystem E g).obj j) ⟶
          ULiftHom.objUp (CostructuredArrow.mk g)) := by
      refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
      change γ'.left = 𝟙 _ ≫ incl.map (E.map j.hom) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      rfl
    exact @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
      (baseCFG D.Y).isFiberedInGroupoids _ _ _ _ _ _ this
  · have hδ' : δ.base.left = incl.map (c.π.app j.left) := by
      refine hδ.trans ?_
      change 𝟙 _ ≫ incl.map (c.π.app j.left) ≫ 𝟙 _ = _
      rw [Category.id_comp, Category.comp_id]
    apply ULift.ext
    apply CostructuredArrow.hom_ext
    change δ.base.left ≫ incl.map (E.map j.hom) = 𝟙 (incl.obj c.pt) ≫ γ.down.left
    have key : incl.map (c.π.app j.left) ≫ incl.map (E.map j.hom) = incl.map (c.π.app i) := by
      rw [← Functor.map_comp, c.w]
    exact (congrArg (· ≫ incl.map (E.map j.hom)) hδ').trans
      (key.trans (hγl.symm.trans (Category.id_comp _).symm))

end AlgebraicGeometry.Space.CoherentSituation

end
