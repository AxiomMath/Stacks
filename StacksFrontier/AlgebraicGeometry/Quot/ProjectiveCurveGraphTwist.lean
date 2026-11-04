/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveCurveGraphHilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectivePairProductEmbedding
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor

/-!
# The twist of `ℙᴺ_T` pulled back along the graph of a relative morphism

Let `i : Z₁ ×_U Z₂ ⟶ ℙᴺ_U` be a closed immersion over `U` with `i^*𝒪(1) ≅ (pr₁^*𝒜 ⊗ pr₂^*ℬ)^{⊗ e}`
(`AlgebraicGeometry.ProjectivePairProductEmbedding.exists_isClosedImmersion_twist`). For a relative
morphism `(a, b)` over `T`, the closed immersion `j : (Z₁)_T ⟶ ℙᴺ_T` of its graph
(`AlgebraicGeometry.ProjectiveCurveGraphHilbert.graphClosedMap`) satisfies
`j^*𝒪(1) ≅ (c₁^*𝒜 ⊗ c₂^*ℬ)^{⊗ e}` with `c₁ : (Z₁)_T ⟶ Z₁` the projection and `c₂ = b`: `j`
followed by `ℙᴺ_T ⟶ ℙᴺ_U` is `(c₁, c₂) ≫ i`, the twisting sheaf of `ℙᴺ_T` is pulled back from that
of `ℙᴺ_U`, and pullback commutes with tensor products and tensor powers (Stacks 01CD).

## Main results

* `AlgebraicGeometry.ProjectiveCurveGraphTwist.graphTwistIso`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.ProjectiveCurveGraphTwist

open Space ProjectiveQuot ProjectiveCurveGraphHilbert Stacks.Ample Stacks.AmpleProjectiveImmersion
  Stacks.AmpleExternalTensor Stacks.RelativeVeryAmple

variable {B : BigFppfSite.{u}}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

variable {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} {q₁ : Z₁ ⟶ U} {q₂ : Z₂ ⟶ U}
  {N : ℕ} (i : pullback ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₁)
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₂) ⟶
      projectiveSpaceOver N ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj U))

/-- The closed immersion `i`, as a morphism of the site out of `Z₁ ×_U Z₂`. -/
def siteEmbedding : pullback q₁ q₂ ⟶ projectiveSite B N U :=
  CurveFamily.homOfScheme ((PreservesPullback.iso (𝒯) q₁ q₂).hom ≫ i)

/-- `siteEmbedding i` lies over `U`: composed with the structure map of `ℙᴺ_U` it is the
structure map of `Z₁ ×_U Z₂`. -/
theorem siteEmbedding_comp (hi : i ≫ (projectiveSpaceOver N ((𝒯).obj U) ↘ (𝒯).obj U) =
    pullback.snd ((𝒯).map q₁) ((𝒯).map q₂) ≫ (𝒯).map q₂) :
    siteEmbedding i ≫ projectiveSiteStructure B N U = pullback.snd q₁ q₂ ≫ q₂ :=
  (𝒯).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    change ((PreservesPullback.iso (𝒯) q₁ q₂).hom ≫ i) ≫
      (projectiveSpaceOver N ((𝒯).obj U) ↘ (𝒯).obj U) = _
    rw [Category.assoc, hi, ← Category.assoc, PreservesPullback.iso_hom_snd])

section Twist

variable {T : BigFppfOver B integerBase B.contains_integerBase}
  (p : RelativeMorphism B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
    (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂) (yoneda.obj T))
  (hi : i ≫ (projectiveSpaceOver N ((BigFppfOver.toScheme B integerBase
      B.contains_integerBase).obj U) ↘ (BigFppfOver.toScheme B integerBase
        B.contains_integerBase).obj U) =
    pullback.snd ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₁)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₂) ≫
      (BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₂)

/-- The pair `(c₁, b) : (Z₁)_T ⟶ Z₁ ×_U Z₂`, read on the fibre product of schemes. -/
abbrev graphSchemePair : (𝒯).obj (pullback (graphBase p) q₁) ⟶
    pullback ((𝒯).map q₁) ((𝒯).map q₂) :=
  (𝒯).map (graphPairMap p) ≫ (PreservesPullback.iso (𝒯) q₁ q₂).hom

/-- The closed immersion of the graph followed by `ℙᴺ_T ⟶ ℙᴺ_ℤ` is `(c₁, b) ≫ i` followed by
`ℙᴺ_U ⟶ ℙᴺ_ℤ`. -/
theorem graphClosedMap_comp_toIntegral :
    (𝒯).map (graphClosedMap p (siteEmbedding_comp i hi)) ≫
        projectiveSpaceOver.toIntegralAtUniverse N ((𝒯).obj T) =
      (graphSchemePair p ≫ i) ≫ projectiveSpaceOver.toIntegralAtUniverse N ((𝒯).obj U) := by
  have h := congrArg (fun k => (𝒯).map k)
    (graphClosedMap_comp_projectiveSiteMap p (siteEmbedding_comp i hi))
  simp only [Functor.map_comp] at h
  change (𝒯).map (graphClosedMap p (siteEmbedding_comp i hi)) ≫
      projectiveSpaceOverMap N ((𝒯).map (graphBase p)) =
    (𝒯).map (graphPairMap p) ≫ ((PreservesPullback.iso (𝒯) q₁ q₂).hom ≫ i) at h
  exact (congrArg ((𝒯).map (graphClosedMap p (siteEmbedding_comp i hi)) ≫ ·)
    (projectiveSpaceOverMap_snd N ((𝒯).map (graphBase p))).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
        (congrArg (· ≫ _) (Category.assoc _ _ _).symm)))

/-- The first component of `(c₁, b)` is the projection `c₁ : (Z₁)_T ⟶ Z₁`. -/
theorem graphSchemePair_fst :
    graphSchemePair p ≫ pullback.fst ((𝒯).map q₁) ((𝒯).map q₂) =
      (𝒯).map (pullback.snd (graphBase p) q₁) := by
  rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp, graphPairMap_fst]

/-- The second component of `(c₁, b)` is `b : (Z₁)_T ⟶ Z₂`. -/
theorem graphSchemePair_snd :
    graphSchemePair p ≫ pullback.snd ((𝒯).map q₁) ((𝒯).map q₂) =
      (𝒯).map (graphPairMap p ≫ pullback.snd q₁ q₂) := by
  rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp]

variable (A : ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Z₁).Modules)
  (B' : ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj Z₂).Modules)
  [IsInvertibleModule _ A] [IsInvertibleModule _ B'] (e : ℕ)
  (eL : tensorPowModule (pullback ((BigFppfOver.toScheme B integerBase
      B.contains_integerBase).map q₁) ((BigFppfOver.toScheme B integerBase
        B.contains_integerBase).map q₂))
    (externalTensor ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₁)
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map q₂) A B') (e : ℤ) ≅
    (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj U)))

/-- **`j^*𝒪(1) ≅ (c₁^*𝒜 ⊗ b^*ℬ)^{⊗ e}`** for the closed immersion `j` of the graph of `(a, b)`. -/
def graphTwistIso :
    (Scheme.Modules.pullback ((𝒯).map (graphClosedMap p (siteEmbedding_comp i hi)))).obj
        (projectiveSpaceTwistingSheaf N ((𝒯).obj T)) ≅
      tensorPowModule ((𝒯).obj (pullback (graphBase p) q₁))
        (Stacks.RelativeVeryAmple.tensorModules ((𝒯).obj (pullback (graphBase p) q₁))
          ((Scheme.Modules.pullback ((𝒯).map (pullback.snd (graphBase p) q₁))).obj A)
          ((Scheme.Modules.pullback ((𝒯).map (graphPairMap p ≫ pullback.snd q₁ q₂))).obj B'))
        (e : ℤ) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (graphClosedMap_comp_toIntegral i p hi)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (graphSchemePair p)).mapIso eL.symm ≪≫
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso
      (graphSchemePair p) _ (e : ℤ) ≪≫
    tensorPowModuleIsoOfIso _ _ _ (pullbackTensorModulesIso (graphSchemePair p) _ _ ≪≫
      tensorModulesMapIso _
        ((Scheme.Modules.pullbackComp _ _).app A ≪≫
          (Scheme.Modules.pullbackCongr (graphSchemePair_fst p)).app A)
        ((Scheme.Modules.pullbackComp _ _).app B' ≪≫
          (Scheme.Modules.pullbackCongr (graphSchemePair_snd p)).app B')) e

end Twist

end AlgebraicGeometry.ProjectiveCurveGraphTwist

end
