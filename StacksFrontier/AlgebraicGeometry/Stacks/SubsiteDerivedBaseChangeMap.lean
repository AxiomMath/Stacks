module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeMapBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteAbelianSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteRestrictedInjectiveAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The base change map for the lisse-étale and flat-fppf sites is an isomorphism

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks, let `f'` be its
restriction to the lisse-étale (respectively flat-fppf) sites of **Stacks 07AT**, and let
`g : Sh(𝒴') ⟶ Sh(𝒴_τ)`, `g' : Sh(𝒳') ⟶ Sh(𝒳_τ)` be the inclusions of the subsites, `τ` being
the étale (respectively fppf) topology. **Stacks 0GR3** asserts that the canonical base change map

`g⁻¹ Rf_* ℱ ⟶ Rf'_* (g')⁻¹ ℱ`

is an isomorphism for every abelian sheaf `ℱ` on `𝒳_τ`. This file proves it, with nothing
assumed, on the bounded below derived categories of an arbitrary model.

The canonical map is `Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus` at the
canonical map `g⁻¹f_* ⟶ f'_*(g')⁻¹` of Sites, Section 06UM: the identification of `g⁻¹ ∘ Rf_*`
with `R(g⁻¹ ∘ f_*)` for the exact `g⁻¹`, the derived map of `g⁻¹f_* ⟶ f'_*(g')⁻¹`, and the
canonical comparison `R(f'_* ∘ (g')⁻¹) ⟶ Rf'_* ∘ (g')⁻¹` of Stacks 05T2. It is invertible because

* the map `g⁻¹f_* ⟶ f'_*(g')⁻¹` is, on abelian sheaves: this is **Stacks 07AT**,
  `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianSheafBaseChange` and its flat-fppf sibling;
  and
* `(g')⁻¹` carries injective abelian sheaves on `𝒳_τ` to sheaves acyclic for `f'_*`:
  `AlgebraicGeometry.Stack.LisseEtale.isZero_rightDerived_restriction_of_injective` and its
  flat-fppf sibling, the vanishing
  `H^p((V ×_{y, 𝒴} 𝒳)', pr^{-1}I) = H^p(V ×_{y, 𝒴} 𝒳, pr^{-1}I) = 0` that the source reads off
  Stacks 075G, 0GR2 and 07AK.

The map is in fact invertible on the whole bounded below derived category, which contains the
abelian sheaves as complexes concentrated in degree zero.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isIso_baseChangeMapPlus` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_baseChangeMapPlus`: the base change map is an
  isomorphism of functors on `D⁺`.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_baseChangeMapPlus_app` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_baseChangeMapPlus_app`: **Stacks 0GR3**, the base
  change map at an abelian sheaf is an isomorphism.

## References

* [Stacks Project, Tag 0GR3](https://stacks.math.columbia.edu/tag/0GR3)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe w₁ w₂ w₃ w₄ u w

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace LisseEtale

attribute [local instance] instIsContinuousInclusion instIsCocontinuousInclusion
  instAdditiveRestriction instPreservesFiniteColimitsRestriction
  instPreservesFiniteLimitsRestriction isGrothendieckAbelian_sheaf_associatedTopology
  isGrothendieckAbelian_sheaf_inclusionTopology

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)
  [HasDerivedCategory.{w₁} (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₂} (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₃} (Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} (Sheaf (inclusionTopology.{u, w} B S hS 𝒴) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory.{w₁} (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₃} (Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1})] in
include hf in
/-- **The restriction of an injective abelian sheaf on `𝒳_étale` to the lisse-étale site is
acyclic for `f'_*`**, in the sense of the bounded below derived category. -/
theorem rightAcyclic_restriction_of_injective
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1})
    (hI : Injective I) :
    haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf))
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)).rightAcyclic
      ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).obj I) := by
  have := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  have := isContinuous_subsiteFunctor.{u, w} B S hS f hf
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf))
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
  have := (Functor.sheafAdjunctionCocontinuous (SubsitePushforward.subsiteFunctor
    f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf))
    AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (inclusionTopology.{u, w} B S hS 𝒴)).isRightAdjoint
  refine (rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa using isZero_rightDerived_restriction_of_injective f hf I n

include hf in
/-- **The base change map `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` for the lisse-étale sites is an
isomorphism** on the bounded below derived category of abelian sheaves on `𝒳_étale`. Here `f` is
a smooth 1-morphism of algebraic stacks, `f'` its restriction to the lisse-étale sites, `g` and
`g'` the inclusions of the lisse-étale sites of `𝒴` and of `𝒳`, and the map is
`Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus` at the canonical map
`g⁻¹f_* ⟶ f'_*(g')⁻¹` of Sites, Section 06UM. -/
theorem isIso_baseChangeMapPlus :
    haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
    haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf))
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    IsIso (Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus
      (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (subsiteRestriction B S hS 𝒴.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴))
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)))
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴))
      (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
        f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴))) := by
  have := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  have := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf))
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
  have := isIso_abelianSheafBaseChange B S hS f hf
  exact Stacks.Cohomology.BoundedBelowComplexes.isIso_baseChangeMapPlus _ _ _ _ _
    (rightAcyclic_restriction_of_injective B S hS f hf)

include hf in
/-- **Stacks 0GR3, the lisse-étale case.** Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic
stacks, `f'` its restriction to the lisse-étale sites (**Stacks 07AT**) and `g`, `g'` the
inclusions of the lisse-étale sites of `𝒴` and of `𝒳`. For every abelian sheaf `ℱ` on
`𝒳_étale` the canonical base change map

`g⁻¹ Rf_* ℱ ⟶ Rf'_* (g')⁻¹ ℱ`

is an isomorphism in the bounded below derived category of abelian sheaves on the lisse-étale
site of `𝒴`, for any model of the derived categories. The map is
`Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus` at the canonical map
`g⁻¹f_* ⟶ f'_*(g')⁻¹` of Sites, Section 06UM, evaluated at `ℱ` placed in degree zero. -/
@[stacks 0GR3 "the lisse-étale case: the canonical base change map g⁻¹ Rf_* ℱ ⟶ Rf'_* (g')⁻¹ ℱ \
is an isomorphism for every abelian sheaf ℱ on 𝒳_étale, in D⁺ for any model of the derived \
categories. The map is Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus (the \
identification g⁻¹ ∘ Rf_* = R(g⁻¹ ∘ f_*) for the exact g⁻¹, the derived map of the canonical map \
g⁻¹f_* ⟶ f'_*(g')⁻¹ of Sites 06UM, and the canonical comparison R(f'_* ∘ (g')⁻¹) ⟶ Rf'_* ∘ (g')⁻¹ \
of 05T2) at ℱ in degree zero. Nothing is assumed: the degree-zero isomorphism is 07AT \
(AlgebraicGeometry.Stack.LisseEtale.isIso_abelianSheafBaseChange) and the acyclicity of \
restricted injectives for f'_* is proved by descent \
(AlgebraicGeometry.Stack.LisseEtale.isZero_rightDerived_restriction_of_injective)"]
theorem isIso_baseChangeMapPlus_app
    (ℱ : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1}) :
    haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
    haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf))
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    IsIso ((Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus
      (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (subsiteRestriction B S hS 𝒴.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴))
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)))
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴))
      (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
        f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ℱ)) := by
  have := isIso_baseChangeMapPlus B S hS f hf
  infer_instance

end LisseEtale

namespace FlatFppf

attribute [local instance] instIsContinuousInclusion instIsCocontinuousInclusion
  instAdditiveRestriction instPreservesFiniteColimitsRestriction
  instPreservesFiniteLimitsRestriction

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)
  [HasDerivedCategory.{w₁} (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₂} (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₃} (Sheaf (associatedTopology B S hS 𝒴.val.val.p B.topology)
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} (Sheaf (inclusionTopology B S hS 𝒴) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory.{w₁} (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₃} (Sheaf (associatedTopology B S hS 𝒴.val.val.p B.topology)
    AddCommGrpCat.{u + 1})] in
include hf in
/-- **The restriction of an injective abelian sheaf on `𝒳_fppf` to the flat-fppf site is
acyclic for `f'_*`**, in the sense of the bounded below derived category. -/
theorem rightAcyclic_restriction_of_injective
    (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1})
    (hI : Injective I) :
    haveI := isCocontinuous_subsiteFunctor B S hS f hf
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)).rightAcyclic
      ((subsiteRestriction B S hS 𝒳.val.val.p B.topology (flatObject B S hS 𝒳.val)).obj I) := by
  have := isCocontinuous_subsiteFunctor B S hS f hf
  have := isContinuous_subsiteFunctor B S hS f hf
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf))
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
  have := (Functor.sheafAdjunctionCocontinuous (SubsitePushforward.subsiteFunctor
    f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf))
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)).isRightAdjoint
  refine (rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa using isZero_rightDerived_restriction_of_injective f hf I n

include hf in
/-- **The base change map `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` for the flat-fppf sites is an
isomorphism** on the bounded below derived category of abelian sheaves on `𝒳_fppf`. Here `f` is
a flat 1-morphism of algebraic stacks, `f'` its restriction to the flat-fppf sites, `g` and
`g'` the inclusions of the flat-fppf sites of `𝒴` and of `𝒳`, and the map is
`Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus` at the canonical map
`g⁻¹f_* ⟶ f'_*(g')⁻¹` of Sites, Section 06UM. -/
theorem isIso_baseChangeMapPlus :
    haveI := isCocontinuous_subsiteFunctor B S hS f hf
    haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    IsIso (Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus
      (subsiteRestriction B S hS 𝒳.val.val.p B.topology (flatObject B S hS 𝒳.val))
      (subsiteRestriction B S hS 𝒴.val.val.p B.topology (flatObject B S hS 𝒴.val))
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology))
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴))
      (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
        f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology)
        (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴))) := by
  have := isCocontinuous_subsiteFunctor B S hS f hf
  have := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (associatedTopology B S hS 𝒴.val.val.p B.topology)
  let := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf))
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
  have := isIso_abelianSheafBaseChange B S hS f hf
  exact Stacks.Cohomology.BoundedBelowComplexes.isIso_baseChangeMapPlus _ _ _ _ _
    (rightAcyclic_restriction_of_injective B S hS f hf)

include hf in
/-- **Stacks 0GR3, the flat-fppf case.** Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic
stacks, `f'` its restriction to the flat-fppf sites (**Stacks 07AT**) and `g`, `g'` the
inclusions of the flat-fppf sites of `𝒴` and of `𝒳`. For every abelian sheaf `ℱ` on
`𝒳_fppf` the canonical base change map

`g⁻¹ Rf_* ℱ ⟶ Rf'_* (g')⁻¹ ℱ`

is an isomorphism in the bounded below derived category of abelian sheaves on the flat-fppf
site of `𝒴`, for any model of the derived categories. The map is
`Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus` at the canonical map
`g⁻¹f_* ⟶ f'_*(g')⁻¹` of Sites, Section 06UM, evaluated at `ℱ` placed in degree zero. -/
@[stacks 0GR3 "the flat-fppf case: the canonical base change map g⁻¹ Rf_* ℱ ⟶ Rf'_* (g')⁻¹ ℱ \
is an isomorphism for every abelian sheaf ℱ on 𝒳_fppf, in D⁺ for any model of the derived \
categories. The map is Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus (the \
identification g⁻¹ ∘ Rf_* = R(g⁻¹ ∘ f_*) for the exact g⁻¹, the derived map of the canonical map \
g⁻¹f_* ⟶ f'_*(g')⁻¹ of Sites 06UM, and the canonical comparison R(f'_* ∘ (g')⁻¹) ⟶ Rf'_* ∘ (g')⁻¹ \
of 05T2) at ℱ in degree zero. Nothing is assumed: the degree-zero isomorphism is 07AT \
(AlgebraicGeometry.Stack.FlatFppf.isIso_abelianSheafBaseChange) and the acyclicity of \
restricted injectives for f'_* is proved by descent \
(AlgebraicGeometry.Stack.FlatFppf.isZero_rightDerived_restriction_of_injective)"]
theorem isIso_baseChangeMapPlus_app
    (ℱ : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1}) :
    haveI := isCocontinuous_subsiteFunctor B S hS f hf
    haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      f.hom.hom.toFunctor (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1}
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    IsIso ((Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus
      (subsiteRestriction B S hS 𝒳.val.val.p B.topology (flatObject B S hS 𝒳.val))
      (subsiteRestriction B S hS 𝒴.val.val.p B.topology (flatObject B S hS 𝒴.val))
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology))
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴))
      (SubsitePushforward.subsiteAbelianSheafBaseChange.{_, _, _, _, u + 1}
        f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology)
        (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ℱ)) := by
  have := isIso_baseChangeMapPlus B S hS f hf
  infer_instance

end FlatFppf

end AlgebraicGeometry.Stack
