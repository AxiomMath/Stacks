module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# The projection `Coh_{X/B} ⟶ 𝒮_B` is limit preserving on objects

In Situation 08KB (a morphism `f : X ⟶ B` of finite presentation of algebraic spaces over `S`),
the projection `p : Coh_{X/B} ⟶ 𝒮_B` of Stacks 08LP, `(T, g, ℱ) ↦ (T, g)`, is limit preserving on
objects in the sense of Stacks 06CU. This is the relative form of Stacks 08KD: it asks for no
hypothesis on `B`, because the structure morphism to `B` of the stage is part of the data.

## Main results

* `AlgebraicGeometry.Space.isLimitPreservingOnObjects_coherentToBaseCFG`: the projection
  `Coh_{X/B} ⟶ 𝒮_B` is limit preserving on objects (relative form of Stacks 08KD).

## Implementation notes

The proof is the descent of objects in the proof of Stacks 08KD, with the structure morphism
`T_i ⟶ B` of a stage given rather than produced by Stacks 05N0: a finitely presented module on
`X_T` comes from a finitely presented module on some `X_{T_k} = X ×_B T_k` by the essential
surjectivity clause of Stacks 07V7 for the system of base changes
(`CoherentSituation.finitePresentationModule_isColimit_baseChange`), and it is flat with proper
support over a later stage by Stacks 08K0 and 08K2 for that system
(`CoherentSituation.flatProperSupportDescends`).

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 08KD, relative form** (helper, unregistered here). In Situation 08KB, the projection
`Coh_{X/B} ⟶ 𝒮_B` of Stacks 08LP, `(T, g, ℱ) ↦ (T, g)`, is limit preserving on objects
(Stacks 06CU): let `T = lim T_j` be a cofiltered limit of affine schemes of the site, taken in
schemes, and let `(T, g, ℱ)` be an object of `Coh_{X/B}` over `T` whose structure morphism
`g : T ⟶ B` factors as `T ⟶ T_i ⟶ B`. Then `ℱ` is, up to isomorphism, the pullback of an object
`(T_j, T_j ⟶ T_i ⟶ B, ℱ_j)` of `Coh_{X/B}` over a later stage, compatibly with the given
factorization. -/
theorem isLimitPreservingOnObjects_coherentToBaseCFG (D : CoherentSituation B S hS) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _ (coherentToBaseCFG D) := by
  intro I _ _ E c hc i y x γ hγ
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let incl := BigAffineFppf.inclusion B S hS
  let p := coherentSiteProjection D.categoryData
  let q := (baseBasedCategory D.Y).p
  have hp : p.IsFiberedInGroupoids := (coherentCFG D).isFiberedInGroupoids
  have hq : q.IsFiberedInGroupoids := (baseCFG D.Y).isFiberedInGroupoids
  have hZ := B.contains_terminal
  obtain ⟨y, hy⟩ := y
  obtain ⟨L, ⟨⟨⟩⟩, g⟩ := y
  change L = incl.obj (E.obj i) at hy
  subst hy
  let A₀ : CoherentObject D := x.1
  have hA₀ : A₀.T.left = (incl.mapCone c).pt := x.2
  let γ₀ : A₀.T ⟶ CostructuredArrow.mk g := γ.down
  have hγl : γ₀.left = eqToHom hA₀ ≫ incl.map (c.π.app i) := by
    have : q.IsHomLift (incl.map (c.π.app i)) γ := hγ.toIsHomLift
    have h := IsHomLift.fac' q (incl.map (c.π.app i)) γ
    change γ₀.left = eqToHom hA₀ ≫ incl.map (c.π.app i) ≫ eqToHom rfl at h
    rw [h, eqToHom_refl, Category.comp_id]
  have hg : (schemeSpaceFunctor B S hS).map (eqToHom hA₀) ≫
      ((schemeSpaceFunctor B S hS).map (incl.map (c.π.app i)) ≫ g) = A₀.T.hom := by
    have hw : (schemeSpaceFunctor B S hS).map γ₀.left ≫ g = A₀.T.hom := CostructuredArrow.w γ₀
    rwa [hγl, Functor.map_comp, Category.assoc] at hw
  let v : A₀.T ≅ (D.stageTestCone E c g).pt := CostructuredArrow.isoMk (eqToIso hA₀) hg
  let cT := (D.stageTestCone E c g).extend v.hom
  obtain ⟨-, -, hES⟩ := D.finitePresentationModule_isColimit_baseChange (D.stageTestSystem E g)
    cT hZ (fun e => D.isAffineHom_stageSpaceSystem_map E g e)
    (D.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
    (D.isLimit_stageSpaceCone_extend E c hc g v)
    (D.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  obtain ⟨k, Q, hQ, ⟨α⟩⟩ := hES A₀.F A₀.finitePresentation
  have hβ : (cT.π.app k).left = eqToHom hA₀ ≫ (incl.mapCone c).π.app k.left := rfl
  obtain ⟨j, e, hfps⟩ := D.flatProperSupportDescends E c hc A₀ hA₀ g k (cT.π.app k) hβ Q hQ
    α.symm
  have hFj := isFinitePresentationOnSite_modulePullback B S hS
    (D.relativeMap ((D.stageTestSystem E g).map e)) Q hQ
  let xi : CoherentObject D :=
    { T := (D.stageTestSystem E g).obj j
      F := (modulePullback B S hS (D.relativeMap ((D.stageTestSystem E g).map e))).obj Q
      quasicoherent := by
        have := hFj
        infer_instance
      finitePresentation := hFj
      flat := hfps.1
      properSupport := hfps.2 }
  let δ : CoherentHom A₀ xi :=
    { base := cT.π.app j
      fibre := (pullbackComparison B S hS (D.relativeMap (cT.π.app j))
          (D.relativeMap ((D.stageTestSystem E g).map e)) (D.relativeMap (cT.π.app k))
          (D.relativeMap_cone_comp _ cT e) Q).inv ≫ α.inv
      isIso_fibre := inferInstance }
  have hδ : p.IsHomLift (incl.map (c.π.app j.left)) (δ : A₀ ⟶ xi) := by
    refine IsHomLift.of_fac' p _ _ hA₀ rfl ?_
    change (cT.π.app j).left = eqToHom hA₀ ≫ incl.map (c.π.app j.left) ≫ 𝟙 _
    rw [Category.comp_id]
    rfl
  have hcart : ∀ {R T : BigFppfOver B S hS} (f : R ⟶ T) {a b : CoherentObject D} (φ : a ⟶ b),
      p.IsHomLift f φ → p.IsStronglyCartesian f φ := by
    intro R T f a b φ hφ
    have hsc := hp.isStronglyCartesian φ
    subst_hom_lift p f φ
    exact hsc
  let γ' : ULiftHom.objUp xi.T ⟶ (ULiftHom.objUp (CostructuredArrow.mk g) : BaseObjects D.Y) :=
    ULift.up (CostructuredArrow.homMk (incl.map (E.map j.hom)) rfl)
  have hγ' : q.IsStronglyCartesian (incl.map (E.map j.hom)) γ' := hq.isStronglyCartesian γ'
  have hsq : (coherentToBaseFunctor D.categoryData).map (δ : A₀ ⟶ xi) ≫ γ' =
      (coherentToBaseFunctor D.categoryData).map (𝟙 A₀) ≫ γ := by
    refine ULift.ext (CostructuredArrow.hom_ext _ _ ?_)
    change (cT.π.app j ≫ γ'.down).left =
      ((Equiv.cast (D.categoryData.hom_type A₀ A₀) (𝟙 A₀)).base ≫ γ₀).left
    rw [D.categoryData.identity A₀]
    change (eqToHom hA₀ ≫ incl.map (c.π.app j.left)) ≫ incl.map (E.map j.hom) =
      (𝟙 A₀.T ≫ γ₀).left
    rw [Category.id_comp, hγl, Category.assoc, ← Functor.map_comp, Cone.w]
  exact ⟨j.left, j.hom, ⟨xi, rfl⟩, x, δ, 𝟙 A₀, γ', hcart _ _ hδ, IsHomLift.id hA₀,
    IsIso.id _, hγ', hsq⟩

end AlgebraicGeometry.Space

end
