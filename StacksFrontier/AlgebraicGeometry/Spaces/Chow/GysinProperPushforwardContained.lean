module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardNonContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapComponent

/-!
# The second case of Stacks 0ER5: a prime cycle contained in the pulled-back divisor

In Situation 0EDT let `f : X' ⟶ X` be proper, let `(ℒ, s)` be an invertible sheaf on `X` with a
global section, `E = Z(s)` and `E' = Z(f^*s)`, and let `W' ⊆ X'` be an integral closed subspace
of δ-dimension `k + 1` contained in `E'`. Write `W ⊆ E` for the closure of the image of `W'` and
`g : W' ⟶ W` for the component morphism of Stacks 0EEG. The source's second case of the proof of
Stacks 0ER5 is the identity in `CH_k(W)`

`g_*(c₁((f^*ℒ)|_{W'}) ∩ [W']) = c₁(ℒ|_W) ∩ g_*[W']`,

the second assertion of Stacks 0EQS. Both cap products are Weil divisors of regular meromorphic
sections, `c₁((f^*ℒ)|_{W'}) ∩ [W'] = div(τ)` and `c₁(ℒ|_W) ∩ [W] = div(t)`, and
`(f^*ℒ)|_{W'} ≅ g^*(ℒ|_W)` (Stacks 03LU). So `div(τ) - div(g^*t)` is a principal divisor `P` on
`W'` (Stacks 0EPT), and

* if `dim_δ(W) = k + 1`, `g_* div(g^*t) = deg(W'/W) div(t)` (Stacks 0EQS for `g`) and `g_* P` is
  rationally equivalent to zero (Stacks 0EQC for `g`);
* if `dim_δ(W) = k`, `g_* P = 0` and `g_* div(g^*t) = 0`, and the right-hand side is zero; this is
  the case the source passes over;
* if `dim_δ(W) < k` there are no `k`-cycles on `W`.

Read on `W`, the defect of the projection formula of Stacks 0EQT at `W'` is therefore exactly
`g_* P` (`AlgebraicGeometry.Space.sectionChernDefect_eq_subspaceProperCyclePushforward`), and
`g_* P` is a principal divisor on `W` when `dim_δ(W) = k + 1` (the norm step of Stacks 0EQC,
from Stacks 0EQ4) and zero otherwise. A principal divisor on `W ⊆ E`, pushed to `X`, is
rationally equivalent to zero by the single member `W`, so inside `|W| ⊆ |E|`.

## Main results

* `AlgebraicGeometry.Space.sectionChernDefect_eq_subspaceProperCyclePushforward`
* `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub_chernPulled`
* The second case of Stacks 0ER5: given the norm step of Stacks 0EQC, every multiple of the
  defect of the projection formula at `W'` is rationally equivalent to zero inside `|W|`.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The defect at one integral closed subspace, at arbitrary regular sections -/

section SectionDefect

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (g : W.subspace.toFunctor ⟶ (chernImage D hX hY q W).subspace.toFunctor)
    (hg : g ≫ (chernImage D hX hY q W).subspace.ι = W.subspace.ι ≫ q.hom) (k : ℤ)
    (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)
    (chernX : FirstChernComponentCycleRule D sX k) (chernY : FirstChernComponentCycleRule D sY k)

include hg hqB hq in
/-- **The reading on `W'` of the defect of the projection formula, at arbitrary regular
sections.** Let `W ⊆ X` have δ-dimension `k + 1`, closure `W'` of its image and component
morphism `g : W ⟶ W'`. Let the component rule on `X` be at `W` the Weil divisor of a regular
meromorphic section `τ` of `(q^*ℒ)|_W`, and the component rule on `Y` be at `W'`, when
`dim_δ(W') = k + 1`, the Weil divisor of a regular meromorphic section `t` of `ℒ|_{W'}`. If, when
`dim_δ(W') = k + 1`, pushing the divisor of `g^*t` forward gives `deg(W/W')` times the divisor of
`t` (`hsec`, which is Stacks 0EQS for `g`), then

`g_*(c₁((q^*ℒ)|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W']) = g_*(div(τ) - div(g^*t))`

on `W'`. -/
theorem sectionChernDefect_eq_subspaceProperCyclePushforward
    (hW : deltaDimension D sX W = k + 1)
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hN : IsInvertibleModule (B := D.site)
      (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (integralClosedSubspaceRestrict D sX hX
        ((modulePullback D.site D.base D.base_mem q).obj L) W))
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1
      (integralClosedSubspaceRestrict D sX hX
        ((modulePullback D.site D.base D.base_mem q).obj L) W))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 _ τ)
    (hX' : chernX W hW = canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _ hN τ hτ hk)
    (hM : IsInvertibleModule (B := D.site)
      (⟨(chernImage D hX hY q W).subspace.toFunctor,
        (chernImage D hX hY q W).isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (chernImageModule D hX hY q L W))
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem
      (chernImage D hX hY q W).subspace.toFunctor (chernImage D hX hY q W).isClosedSubspace.1
      (chernImageModule D hX hY q L W))
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _ _ _ t)
    (hY' : ∀ (h : deltaDimension D sY (chernImage D hX hY q W) = k + 1)
      (hk' : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)),
      chernY (chernImage D hX hY q W) h = canonicalDivisorCycleAt D
        ((chernImage D hX hY q W).subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY _)
        (chernImage D hX hY q W).isIntegralSpace _ hM t ht hk')
    (hsec : ∀ (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem
        W.subspace.toFunctor W.isClosedSubspace.1 _
        (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
          (chernImageModule D hX hY q L W)
          (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t))
      (hk' : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)),
      deltaDimension D sY (chernImage D hX hY q W) = k + 1 →
      subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg k
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
            W.isIntegralSpace _
            (modulePullbackInvertible (chernComponentHom D hX hY q W g) _ hM)
            (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
              (chernImageModule D hX hY q L W)
              (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t) hσ hk) =
        properCycleDegree D sX hX sY hY q.hom W •
          canonicalDivisorCycleAt D ((chernImage D hX hY q W).subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY _) (chernImage D hX hY q W).isIntegralSpace _
            hM t ht hk')
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 _
      (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
        (chernImageModule D hX hY q L W)
        (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t)) :
    subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg k
        (chernComponentCycleOrZero D sX k chernX W) -
      properCycleDegree D sX hX sY hY q.hom W •
        chernComponentCycleOrZero D sY k chernY (chernImage D hX hY q W) =
    subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg k
      (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _ hN τ hτ hk -
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _ (modulePullbackInvertible (chernComponentHom D hX hY q W g) _ hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
            (chernImageModule D hX hY q L W)
            (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t) hσ hk) := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY (chernImage D hX hY q W)
  set σdiv := canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace _
    (modulePullbackInvertible (chernComponentHom D hX hY q W g) _ hM)
    (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
      (chernImageModule D hX hY q L W)
      (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t) hσ hk with hσdiv
  set P := canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace _ hN τ hτ hk -
    σdiv with hP
  rw [chernComponentCycleOrZero_of_deltaDimension_eq D sX k _ hW, hX',
    show canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace _ hN τ hτ hk =
      P + σdiv from (sub_add_cancel _ _).symm, map_add]
  have hle : deltaDimension D sY (chernImage D hX hY q W) ≤ k + 1 := by
    rw [← hW]
    exact IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY q.hom hqB W
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- the equal-dimensional case: Stacks 0EQS for `g`
    have hk' : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g Set.univ
        isClosed_univ = ((k + 1 : ℤ) : EInt) := by
      rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY _, heq]
    rw [chernComponentCycleOrZero_of_deltaDimension_eq D sY k _ heq, hY' heq hk', hsec hσ hk' heq,
      add_sub_cancel_right]
  rcases eq_or_lt_of_le (show deltaDimension D sY (chernImage D hX hY q W) ≤ k by omega) with
    heq | hlt'
  · -- the dimension-drop case
    have hgB : (chernComponentHom D hX hY q W g).hom ≫
        (chernImage D hX hY q W).subspace.ι ≫ sY = W.subspace.ι ≫ sX := by
      change g ≫ _ ≫ sY = _
      rw [← Category.assoc, hg, Category.assoc, hqB]
    have hσ0 := properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop
      D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g
      (chernImage D hX hY q W).isIntegralSpace (chernComponentHom D hX hY q W g) hgB
      (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 q.hom hq W
        _ g hg).2.1.2
      (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) k hk
      ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D sY hY _ hW'g).trans heq)
      _ hM _ ht hσ
    rw [chernComponentCycleOrZero_of_deltaDimension_ne D sY k _ (by omega), smul_zero,
      sub_zero]
    rw [show subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg k σdiv = 0 from hσ0,
      add_zero]
  · -- no `k`-cycles on `W'`
    rw [cycleGroup_eq_zero_of_deltaDimension_lt D sY hY _ k hlt' (_ - _)]
    exact (cycleGroup_eq_zero_of_deltaDimension_lt D sY hY _ k hlt' _).symm

include hg in
/-- The difference of the divisor of `τ` and the divisor of `g^*t`, both regular meromorphic
sections of `(q^*ℒ)|_W ≅ g^*(ℒ|_{W'})` (Stacks 03LU), is a principal divisor on `W` at the
canonical embeddings of Stacks 0ENK (Stacks 0EPT). -/
theorem isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub_chernPulled
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hN : IsInvertibleModule (B := D.site)
      (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (integralClosedSubspaceRestrict D sX hX
        ((modulePullback D.site D.base D.base_mem q).obj L) W))
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1
      (integralClosedSubspaceRestrict D sX hX
        ((modulePullback D.site D.base D.base_mem q).obj L) W))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 _ τ)
    (hM : IsInvertibleModule (B := D.site)
      (⟨(chernImage D hX hY q W).subspace.toFunctor,
        (chernImage D hX hY q W).isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (chernImageModule D hX hY q L W))
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem
      (chernImage D hX hY q W).subspace.toFunctor (chernImage D hX hY q W).isClosedSubspace.1
      (chernImageModule D hX hY q L W))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 _
      (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
        (chernImageModule D hX hY q L W)
        (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t)) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      W.isIntegralSpace k
      (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _ hN τ hτ hk -
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _ (modulePullbackInvertible (chernComponentHom D hX hY q W g) _ hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
            (chernImageModule D hX hY q L W)
            (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) t) hσ hk) := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  set φ := chernComponentModuleIso D hX hY q L W g hg with hφ
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    W.subspace.toFunctor hWg.1 φ.symm _ hσ
  rw [← canonicalDivisorCycleAt_sectionsMap_iso D (W.subspace.ι ≫ sX) hWg
    W.isIntegralSpace _ _ _ hN φ.symm _ hσ hσ' hk]
  have h := isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D (W.subspace.ι ≫ sX)
    hWg W.isIntegralSpace _ hN _ _ hτ hσ' hk 1
  rw [one_smul] at h
  exact h

end SectionDefect

/-! ### The second case -/

section SecondCase

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (hf : IsProper D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

include hL in
/-- **The source's second case of Stacks 0ER5.** Let `W' ⊆ X'` be an integral closed subspace of
δ-dimension `k + 1` contained in `E' = Z(f^*s)`, with closure `W ⊆ E` of its image and component
morphism `g : W' ⟶ W`. If, when `dim_δ(W) = k + 1`, the pushforward along `g` of a principal
divisor on `W'` is a principal divisor on `W` (`hnorm`, the norm step of Stacks 0EQC), then every
multiple of the defect of the projection formula at `W'`, for the Gysin component rules of
`(f^*ℒ, f^*s)` and of `(ℒ, s)`, is rationally equivalent to zero inside `|W|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_zsmul_properPushforwardChernDefect_sectionGysinChernRule_of_le
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hnorm : ∀ (g : W'.subspace.toFunctor ⟶ (chernImage D hp' hp f W').subspace.toFunctor)
      (hg : g ≫ (chernImage D hp' hp f W').subspace.ι = W'.subspace.ι ≫ f.hom),
      deltaDimension D p (chernImage D hp' hp f W') = k + 1 →
      ∀ c : CycleGroup D (W'.subspace.ι ≫ p') k,
        IsPrincipalDivisorCycleOfGood D (W'.subspace.ι ≫ p')
          (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace k c →
        IsPrincipalDivisorCycleOfGood D ((chernImage D hp' hp f W').subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp _) (chernImage D hp' hp f W').isIntegralSpace k
          (subspaceProperCyclePushforward D p' hp' p hp hfbase hf W' _ g hg k c))
    (hW' : deltaDimension D p' W' = k + 1)
    (hW'E' : W'.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1) (a : ℤ) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D p hp k
      (a • properPushforwardChernDefect D hp' hp hfbase hf k
        (sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)
          (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) k)
        (sectionGysinChernRule D p hp L s hL k) W')
      (subspacePointSet D.site D.base D.base_mem X
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
          (D.isDecentSpace_of_isGood p hp) f.hom W').subspace) := by
  obtain ⟨g, hg⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f.hom W'
  have hL' := isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL
  have hLm : IsInvertibleModule (B := D.site) (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      L := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hk : deltaDimensionClosed D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p' hp' W', hW']
  have hWE : (chernImage D hp' hp f W').subspace ≤ (vanishingLocus D p hp L s).1 :=
    closureImage_le_of_le D p hp f.hom _ _ _
      (pullbackVanishingLocusProjection_comm D p hp p' hp' f L s hL) W' hW'E'
  have hN :=
    isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p' hp' _ hL' W'
  have hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _ (restrictedSectionOfIntegralClosedSubspace D p' hp' _ hL' W') :=
    isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem _
      W'.isIntegralSpace _ _ hN
  have hM := isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL
    (chernImage D hp' hp f W')
  have ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _ _ _
      (restrictedSectionOfIntegralClosedSubspace D p hp L hL (chernImage D hp' hp f W')) :=
    isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem _
      (chernImage D hp' hp f W').isIntegralSpace _ _ hM
  have hσ := isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    (chernComponentHom D hp' hp f W' g)
    (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) _
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM) _ ht
  have hD := sectionChernDefect_eq_subspaceProperCyclePushforward D hp' hp f L W' g hg k hfbase hf
    (sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s) hL' k)
    (sectionGysinChernRule D p hp L s hL k) hW' hk hN
    (restrictedSectionOfIntegralClosedSubspace D p' hp' _ hL' W') hτ
    (by rw [sectionGysinChernRule, restrictedSectionChernRule_of_le D p' hp' _ _ hL' k _ hW' hW'E']
        rfl)
    hM (restrictedSectionOfIntegralClosedSubspace D p hp L hL _) ht
    (fun h hk' => by
      rw [sectionGysinChernRule, restrictedSectionChernRule_of_le D p hp L s hL k _ h hWE]
      rfl)
    (fun hσ hk' hdim => subspaceProperCyclePushforward_canonicalDivisorCycleAt_chernComponentHom D p
      hp p' hp' f hfbase hf L k W' g hg _ _ _ hσ hk hk' hW' hdim) hσ
  have hP := isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub_chernPulled D hp' hp f L W'
    g hg k hk hN _ hτ hM _ hσ
  rw [properPushforwardChernDefect_eq D hp' hp hfbase hf k _ _ W' g hg, hD]
  by_cases heq : deltaDimension D p (chernImage D hp' hp f W') = k + 1
  · rw [← map_zsmul]
    refine ⟨PUnit, fun _ => chernImage D hp' hp f W', locallyFinite_of_finite _,
      fun _ => a • subspaceProperCyclePushforward D p' hp' p hp hfbase hf W' _ g hg k _,
      fun _ => le_rfl, fun _ => heq,
      fun _ => isPrincipalDivisorCycleOfGood_zsmul D _ _ _ k (hnorm g hg heq _ hP) a,
      Subtype.ext (funext fun Z => ?_)⟩
    rw [cycleFamilySum_apply, finsum_unique]
  · have h0 : subspaceProperCyclePushforward D p' hp' p hp hfbase hf W' _ g hg k
        (canonicalDivisorCycleAt D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
          W'.isIntegralSpace _ hN _ hτ hk -
        canonicalDivisorCycleAt D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
          W'.isIntegralSpace _ (modulePullbackInvertible (chernComponentHom D hp' hp f W' g) _ hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
            (chernImageModule D hp' hp f L W')
            (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) _) hσ hk) = 0 := by
      have hle : deltaDimension D p (chernImage D hp' hp f W') ≤ k + 1 := by
        rw [← hW']
        exact IntegralClosedSubspace.deltaDimension_closureImage_le D p' p hp' hp f.hom hfbase W'
      rcases eq_or_lt_of_le (show deltaDimension D p (chernImage D hp' hp f W') ≤ k by omega) with
        heq' | hlt'
      · exact subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq D p' hp' p hp hfbase hf k
          W' g hg hW' heq' _ hP
      · exact cycleGroup_eq_zero_of_deltaDimension_lt D p hp _ k hlt' _
    rw [h0, map_zero, smul_zero]
    exact isRationallyEquivalentToZeroWithinCanonical_zero D p hp k _

end SecondCase

end AlgebraicGeometry.Space

end
