module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeColimits

/-!
# Exactness and colimits for the functors `a`, `b`, `c`, `d` of Stacks 0GQS

Items (1)–(4) and (8) of Stacks 0GQS: `a`, `b`, `c` are exact, `d` is right exact, and all four
commute with colimits. The source's reasons are followed: `a` is exact and commutes with
colimits, and the inclusions `LQCoh(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 06WM),
`LQCoh^fbc(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` (Stacks 0771) and `QCoh(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` (Stacks 06WN) are
exact, respectively exact, respectively right exact, and commute with colimits. The values of
`b`, `c`, `d` lie in the full subcategory `QCoh(U_étale, 𝒪_U)`, whose inclusion is fully
faithful, so it reflects the limits and colimits that `a` produces.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_spaceRestriction`: `a` is exact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_lqcohSpaceRestriction`: `b` is exact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exactFunctor_lqcohFbcSpaceRestriction`: `c` is exact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteColimits_qcohSpaceRestriction`: `d` is
  right exact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesColimitsOfSize_spaceRestriction` and its
  three companions: `a`, `b`, `c`, `d` commute with colimits.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- **Stacks 0GQS, item (1).** The functor `a : ℱ ↦ f^*ℱ|_{U_étale}` is exact. -/
theorem exactFunctor_spaceRestriction :
    exactFunctor _ _ (spaceRestriction B S hS 𝒳 U hU f) :=
  Space.exactFunctor_etaleRestrictedModuleInverseImageFunctor (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)

/-- The inclusion `LQCoh(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` is exact (Stacks 06WM (2)). -/
theorem exactFunctor_lqcohInclusion : exactFunctor _ _ (lqcohInclusion B S hS 𝒳) :=
  let h := Stack.locallyQuasicoherentModules_abelian B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- **Stacks 0GQS, item (2).** The functor `b : LQCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` is exact: the
inclusion `LQCoh(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` is exact (Stacks 06WM) and `a` is exact. -/
theorem exactFunctor_lqcohSpaceRestriction :
    exactFunctor _ _ (lqcohSpaceRestriction B S hS 𝒳 U hU f) := by
  obtain ⟨hι₁, hι₂⟩ := exactFunctor_lqcohInclusion B S hS 𝒳
  obtain ⟨ha₁, ha₂⟩ := exactFunctor_spaceRestriction B S hS 𝒳 U hU f
  have : PreservesFiniteLimits
      (lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙ ObjectProperty.ι _) :=
    have := @comp_preservesFiniteLimits _ _ _ _ _ _ (lqcohInclusion B S hS 𝒳)
      (spaceRestriction B S hS 𝒳 U hU f) hι₁ ha₁
    preservesFiniteLimits_of_natIso (lqcohSpaceRestrictionCompι B S hS 𝒳 U hU f).symm
  have : PreservesFiniteColimits
      (lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙ ObjectProperty.ι _) :=
    have := @comp_preservesFiniteColimits _ _ _ _ _ _ (lqcohInclusion B S hS 𝒳)
      (spaceRestriction B S hS 𝒳 U hU f) hι₂ ha₂
    preservesFiniteColimits_of_natIso (lqcohSpaceRestrictionCompι B S hS 𝒳 U hU f).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (ObjectProperty.ι _),
    preservesFiniteColimits_of_reflects_of_preserves _ (ObjectProperty.ι _)⟩

/-- The inclusion `LQCoh^fbc(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` is exact: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre
subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 0771 (2)), so its inclusion there is exact, and the
inclusion of `LQCoh(𝒪_𝒳)` is fully faithful. -/
theorem exactFunctor_lqcohFbcToLqcoh : exactFunctor _ _ (lqcohFbcToLqcoh B S hS 𝒳) := by
  let := Stack.hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  let := Stack.wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have hW := Stack.isWeakSerreClass_lqcohSheafFbcEtaleModules B (associatedBigEtaleSite B) rfl S
    hS 𝒳
  have := @ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _ _ _ _ hW
  have := @ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _ _ _ _ hW
  have e : lqcohFbcToLqcoh B S hS 𝒳 ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ :=
    ObjectProperty.liftCompιIso _ _ _
  have : PreservesFiniteLimits (lqcohFbcToLqcoh B S hS 𝒳 ⋙ ObjectProperty.ι _) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (lqcohFbcToLqcoh B S hS 𝒳 ⋙ ObjectProperty.ι _) :=
    preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (ObjectProperty.ι _),
    preservesFiniteColimits_of_reflects_of_preserves _ (ObjectProperty.ι _)⟩

/-- **Stacks 0GQS, item (3).** The functor `c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` is exact:
the inclusion of `LQCoh^fbc(𝒪_𝒳)` is exact (Stacks 0771) and `b` is exact. -/
theorem exactFunctor_lqcohFbcSpaceRestriction :
    exactFunctor _ _ (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) := by
  obtain ⟨h₁, h₂⟩ := exactFunctor_lqcohFbcToLqcoh B S hS 𝒳
  obtain ⟨h₃, h₄⟩ := exactFunctor_lqcohSpaceRestriction B S hS 𝒳 U hU f
  exact ⟨@comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₃,
    @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₂ h₄⟩

/-- The inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` commutes with colimits (Stacks 06WN (1)). -/
theorem preservesColimitsOfSize_qcohToLqcoh :
    PreservesColimitsOfSize.{u, u} (qcohToLqcoh B S hS 𝒳) :=
  (FibredSite.quasicoherentModules_colimits_siteAgreement B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (associatedBigEtaleSite B) rfl).2.2.2

/-- **Stacks 0GQS, item (4), right exactness.** The functor
`d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` is right exact: the inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` is
right exact (Stacks 06WN) and `b` is exact. -/
theorem preservesFiniteColimits_qcohSpaceRestriction :
    PreservesFiniteColimits (qcohSpaceRestriction B S hS 𝒳 U hU f) := by
  have := preservesColimitsOfSize_qcohToLqcoh B S hS 𝒳
  have h₁ := PreservesColimitsOfSize.preservesFiniteColimits (qcohToLqcoh B S hS 𝒳)
  obtain ⟨-, h₂⟩ := exactFunctor_lqcohSpaceRestriction B S hS 𝒳 U hU f
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₁ h₂

/-- **Stacks 0GQS, item (8), for `a`.** The functor `a` commutes with colimits, in particular with
arbitrary direct sums: it is the restriction of modules along the continuous and cocontinuous
functor `U_étale ⥤ 𝒳`. -/
theorem preservesColimitsOfSize_spaceRestriction :
    PreservesColimitsOfSize.{u, u} (spaceRestriction B S hS 𝒳 U hU f) := by
  let := Space.etaleChartToFibred_isContinuous (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)
  let := Space.isCocontinuous_etaleChartToFibred (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom)
  let : HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (Space.SmallEtale.topology B S hS U) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Space.SmallEtale.topology B S hS U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact Stacks.SheafOfModules.pushforward_preservesColimits _ _

/-- **Stacks 0GQS, item (8), for `b`.** The functor `b` commutes with colimits: colimits in
`LQCoh(𝒪_𝒳)` are colimits in `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 06WM (1)), which `a` preserves. -/
theorem preservesColimitsOfSize_lqcohSpaceRestriction :
    PreservesColimitsOfSize.{u, u} (lqcohSpaceRestriction B S hS 𝒳 U hU f) := by
  have h₁ := (Stack.locallyQuasicoherentModules_colimits B (associatedBigEtaleSite B) rfl S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).2.2
  have h₂ := preservesColimitsOfSize_spaceRestriction B S hS 𝒳 U hU f
  have := @comp_preservesColimits _ _ _ _ _ _ (lqcohInclusion B S hS 𝒳)
    (spaceRestriction B S hS 𝒳 U hU f) h₁ h₂
  have : PreservesColimitsOfSize.{u, u}
      (lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙ ObjectProperty.ι _) :=
    preservesColimits_of_natIso (lqcohSpaceRestrictionCompι B S hS 𝒳 U hU f).symm
  exact preservesColimits_of_reflects_of_preserves _ (ObjectProperty.ι _)

/-- The inclusion `LQCoh^fbc(𝒪_𝒳) ⊆ LQCoh(𝒪_𝒳)` commutes with colimits: colimits in
`LQCoh^fbc(𝒪_𝒳)` are colimits in `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 0771 (5)). -/
theorem preservesColimitsOfSize_lqcohFbcToLqcoh :
    PreservesColimitsOfSize.{u, u} (lqcohFbcToLqcoh B S hS 𝒳) := by
  have := (Stack.lqcohSheafFbc_hasColimits_and_agree B (associatedBigEtaleSite B) rfl S hS
    𝒳).2.2.1.2
  have e : lqcohFbcToLqcoh B S hS 𝒳 ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ :=
    ObjectProperty.liftCompιIso _ _ _
  have : PreservesColimitsOfSize.{u, u} (lqcohFbcToLqcoh B S hS 𝒳 ⋙ ObjectProperty.ι _) :=
    preservesColimits_of_natIso e.symm
  exact preservesColimits_of_reflects_of_preserves _ (ObjectProperty.ι _)

/-- **Stacks 0GQS, item (8), for `c`.** The functor `c` commutes with colimits. -/
theorem preservesColimitsOfSize_lqcohFbcSpaceRestriction :
    PreservesColimitsOfSize.{u, u} (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) := by
  have h₁ := preservesColimitsOfSize_lqcohFbcToLqcoh B S hS 𝒳
  have h₂ := preservesColimitsOfSize_lqcohSpaceRestriction B S hS 𝒳 U hU f
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h₁ h₂

/-- **Stacks 0GQS, item (8), for `d`.** The functor `d` commutes with colimits. -/
theorem preservesColimitsOfSize_qcohSpaceRestriction :
    PreservesColimitsOfSize.{u, u} (qcohSpaceRestriction B S hS 𝒳 U hU f) := by
  have h₁ := preservesColimitsOfSize_qcohToLqcoh B S hS 𝒳
  have h₂ := preservesColimitsOfSize_lqcohSpaceRestriction B S hS 𝒳 U hU f
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h₁ h₂

end AlgebraicGeometry.Stack.AlgebraicStacks

end
