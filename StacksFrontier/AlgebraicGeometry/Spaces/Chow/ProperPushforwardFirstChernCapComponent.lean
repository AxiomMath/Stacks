module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardSectionDivisorDimensionDrop

/-!
# The defect of the projection formula at one integral closed subspace, at the canonical rules

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be proper over `B`, let `ℒ` be an
invertible `𝒪_Y`-module, and let `W ⊆ X` be an integral closed subspace of δ-dimension `k + 1`
with closure `W'` of the image of `|W|` and component morphism `g : W ⟶ W'` (Stacks 0EEG). The
component cycles of Stacks 0EQJ are the canonical ones,
`AlgebraicGeometry.Space.canonicalFirstChernRule`, at `p^*ℒ` on `X` and at `ℒ` on `Y`.

This file reduces the reading on `W'` of the defect of the projection formula of Stacks 0EQT,

`g_*(c₁((p^*ℒ)|_W) ∩ [W]) - deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`,

to the source's final step, Stacks 0EQS for `g`. The section `t_W` of `(p^*ℒ)|_W` chosen by the
canonical rule and the pullback `g^*t'` of the section `t'` chosen on `W'` for `ℒ|_{W'}` are two
regular meromorphic sections of one invertible module, `(p^*ℒ)|_W ≅ g^*(ℒ|_{W'})` (Stacks 03LU),
so their Weil divisors differ by a principal divisor `P` (Stacks 0EPT,
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_canonicalPullbackRule_sub`). Then:

* if `dim_δ(W') = k + 1`, the defect is `g_* P` once `g_* div_{g^*ℳ}(g^*t') = deg(W/W') div_ℳ(t')`
  — Stacks 0EQS for `g` — and `g_* P` is rationally equivalent to zero — Stacks 0EQC for `g`;
* if `dim_δ(W') = k`, the component cycle on `W'` is zero, `g_* P = 0` by the dimension-drop
  branch of Stacks 0EQC
  (`AlgebraicGeometry.Space.subspaceProperCyclePushforward_eq_zero_of_deltaDimension_eq`), and
  `g_* div_{g^*ℳ}(g^*t') = 0`
  (`properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop`);
  this is the case the source passes over;
* if `dim_δ(W') < k` there are no `k`-cycles on `W'`.

## Main results

* `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_canonicalPullbackRule_sub`
* `AlgebraicGeometry.Space.subspaceProperCyclePushforward_chernPulledDivisor`
* `AlgebraicGeometry.Space.properCycleDegree_eq_functionFieldDegreeAtGenericPoint`

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Component

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- The closure `W'` of the image of `|W|` along `p`, the integral closed subspace of `Y` of
Stacks 0EEG. -/
abbrev chernImage : IntegralClosedSubspace D.site D.base D.base_mem Y :=
  IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) q.hom W

variable (g : W.subspace.toFunctor ⟶ (chernImage D hX hY q W).subspace.toFunctor)
    (hg : g ≫ (chernImage D hX hY q W).subspace.ι = W.subspace.ι ≫ q.hom)

/-- The component morphism `g : W ⟶ W'` of Stacks 0EEG, as a morphism of algebraic spaces. -/
abbrev chernComponentHom :
    (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨(chernImage D hX hY q W).subspace.toFunctor,
        (chernImage D hX hY q W).isClosedSubspace.1⟩ :=
  ObjectProperty.homMk g

include hg in
/-- The component morphism carries the generic point of `W` to the generic point of `W'`. -/
theorem pointsMap_chernComponentHom_genericPoint :
    pointsMap D.site D.base D.base_mem _ g
        (genericPoint D.site D.base D.base_mem W.isClosedSubspace.1 W.isIntegralSpace) =
      genericPoint D.site D.base D.base_mem (chernImage D hX hY q W).isClosedSubspace.1
        (chernImage D hX hY q W).isIntegralSpace := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY (chernImage D hX hY q W)
  refine pointsMap_injective_of_mono D.site D.base D.base_mem (chernImage D hX hY q W).subspace.ι ?_
  rw [← pointsMap_comp_apply, hg, pointsMap_comp_apply,
    IntegralClosedSubspace.pointsMap_ι_genericPoint D W hWg.1,
    IntegralClosedSubspace.pointsMap_ι_genericPoint D (chernImage D hX hY q W) hW'g.1,
    IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem hX.1
      hY.1 _ q.hom W]

include hg in
/-- Meromorphic sections pull back along the component morphism (Stacks 0EN9, part (1)): it
carries the generic point to the generic point. -/
theorem pullbacksMeromorphicSections_chernComponentHom :
    PullbacksMeromorphicSections D.site D.base D.base_mem g :=
  pullbacksMeromorphicSections_of_genericPoint D.site D.base D.base_mem
    (Z := ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
    (Y := ⟨(chernImage D hX hY q W).subspace.toFunctor,
      (chernImage D hX hY q W).isClosedSubspace.1⟩)
    W.isIntegralSpace (chernImage D hX hY q W).isIntegralSpace g
    (pointsMap_chernComponentHom_genericPoint D hX hY q W g hg)

/-- The restriction `ℒ|_{W'}` of `ℒ` to `W'`. -/
abbrev chernImageModule :
    Modules.{u, u} D.site D.base D.base_mem (chernImage D hX hY q W).subspace.toFunctor
      (chernImage D hX hY q W).isClosedSubspace.1 :=
  integralClosedSubspaceRestrict D sY hY L (chernImage D hX hY q W)

/-- The pullback `g^*t'` along the component morphism of the section `t'` of `ℒ|_{W'}` chosen by
the canonical rule of Stacks 0EQJ on `Y`. -/
abbrev chernPulledSection :
    MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor W.isClosedSubspace.1
      ((modulePullback D.site D.base D.base_mem (chernComponentHom D hX hY q W g)).obj
        (chernImageModule D hX hY q L W)) :=
  pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hX hY q W g)
    (chernImageModule D hX hY q L W)
    (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg)
    (componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL
      (chernImage D hX hY q W))

/-- The pulled-back section `g^*t'` is regular (Stacks 0ENC, part (2)). -/
theorem isRegularMeromorphicSection_chernPulledSection :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 _ (chernPulledSection D hX hY q L hL W g hg) :=
  isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    (chernComponentHom D hX hY q W g) _ (chernImageModule D hX hY q L W)
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL (chernImage D hX hY q W)))
    _ (isRegularMeromorphicSection_componentMeromorphicSection sY hY
      (subspaceDivisorSetupOfIsGood D sY hY) L hL (chernImage D hX hY q W))

include hg in
/-- **`(p^*ℒ)|_W ≅ g^*(ℒ|_{W'})`.** Both are inverse images of `ℒ` along one morphism `W ⟶ Y`,
through the composition isomorphisms of Stacks 03LU. -/
def chernComponentModuleIso :
    integralClosedSubspaceRestrict D sX hX ((modulePullback D.site D.base D.base_mem q).obj L) W ≅
      (modulePullback D.site D.base D.base_mem (chernComponentHom D hX hY q W g)).obj
        (chernImageModule D hX hY q L W) :=
  modulePullbackCompCongrIso
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) q
    (chernComponentHom D hX hY q W g)
    (closedSubspaceHom D.site D.base D.base_mem hY.1 (chernImage D hX hY q W).subspace
      (chernImage D hX hY q W).isClosedSubspace)
    (ObjectProperty.hom_ext _ hg.symm) L

variable (k : ℤ)

include hg in
/-- **The canonical component cycle of `p^*ℒ` on `W` and the divisor of `g^*t'` differ by a
principal divisor**, and so does every integer multiple of their difference, at the canonical
embeddings of Stacks 0ENK (Stacks 0EPT): both are Weil divisors of regular meromorphic sections of
`(p^*ℒ)|_W ≅ g^*(ℒ|_{W'})`. -/
theorem isPrincipalDivisorCycleOfGood_canonicalPullbackRule_sub
    (hW : deltaDimension D sX W = k + 1)
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      W.isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
          (modulePullbackInvertible q L hL) k W hW -
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _
          (modulePullbackInvertible (chernComponentHom D hX hY q W g) _
            (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL
              (chernImage D hX hY q W)))
          (chernPulledSection D hX hY q L hL W g hg)
          (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg) hk)) := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hN := isInvertibleModule_integralClosedSubspaceRestrict D sX hX _
    (modulePullbackInvertible q L hL) W
  have hτ := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) _ (modulePullbackInvertible q L hL) W
  set φ := chernComponentModuleIso D hX hY q L W g hg with hφ
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    W.subspace.toFunctor hWg.1 φ.symm _
    (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg)
  rw [← canonicalDivisorCycleAt_sectionsMap_iso D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace _ _
    _ hN φ.symm _ (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg) hσ' hk]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D (W.subspace.ι ≫ sX)
    hWg W.isIntegralSpace _ hN _ _ hτ hσ' hk a

/-- On an integral good algebraic space the integral closed subspace attached to the generic
point is the whole space. -/
theorem integralClosedSubspaceUniv_eq_top {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (hZint : IsIntegralSpace D.site D.base D.base_mem Z) :
    integralClosedSubspaceUniv D sZ hZ hZint =
      IntegralClosedSubspace.top D.site D.base D.base_mem hZ.1 hZint := by
  refine (eq_integralClosedSubspaceOfPoint D.site D.base D.base_mem hZ.1
    (D.isDecentSpace_of_isGood sZ hZ) _ _ ?_).symm
  rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
  exact isGenericPoint_genericPoint D.site D.base D.base_mem hZ.1 hZint

/-- The integral cycle of `top` is that of `integralClosedSubspaceUniv`, at the same dimension. -/
private theorem integralCycle_top_eq_univ {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (hZint : IsIntegralSpace D.site D.base D.base_mem Z)
    {m : ℤ} (hn : deltaDimensionClosed D sZ hZ Set.univ isClosed_univ = (m : EInt))
    (htop : deltaDimension D sZ (IntegralClosedSubspace.top D.site D.base D.base_mem hZ.1 hZint) =
      m) :
    integralCycle D sZ m (IntegralClosedSubspace.top D.site D.base D.base_mem hZ.1 hZint) htop =
      integralCycle D sZ m (integralClosedSubspaceUniv D sZ hZ hZint)
        (deltaDimension_integralClosedSubspaceUniv D sZ hZ hZint hn) := by
  congr 1; exact (integralClosedSubspaceUniv_eq_top D sZ hZ hZint).symm

/-- The δ-dimension of `top` is `m` when that of the whole space is. -/
private theorem deltaDimension_top_of_deltaDimensionClosed_univ
    {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (hZint : IsIntegralSpace D.site D.base D.base_mem Z)
    {m : ℤ} (hn : deltaDimensionClosed D sZ hZ Set.univ isClosed_univ = (m : EInt)) :
    deltaDimension D sZ (IntegralClosedSubspace.top D.site D.base D.base_mem hZ.1 hZint) = m := by
  rw [← integralClosedSubspaceUniv_eq_top D sZ hZ hZint]
  exact deltaDimension_integralClosedSubspaceUniv D sZ hZ hZint hn

variable (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)

/-- The component morphism `g : W ⟶ W'` commutes with the structure morphisms to the base. -/
private theorem chernComponentHom_comp_eq (hqB : q.hom ≫ sY = sX)
    (hg : g ≫ (chernImage D hX hY q W).subspace.ι = W.subspace.ι ≫ q.hom) :
    g ≫ (chernImage D hX hY q W).subspace.ι ≫ sY = W.subspace.ι ≫ sX := by
  rw [← Category.assoc, hg, Category.assoc, hqB]

include hg hqB hq in
/-- **The degree of Stacks 0EP1 read on the component morphism.** When `dim_δ(W') = dim_δ(W)`,
the degree `deg(W/W')` of Stacks 0EP1, part (1), of the ambient morphism `p` at `W` is the degree
`[R(W) : R(W')]` of the component morphism `g : W ⟶ W'`. Both are read off pushforwards of
fundamental cycles: `p_*[W] = deg(W/W') [W']` on `Y`, and `p_*[W] = i'_* g_* [W]` by the square
of Stacks 0EP2, with `g_*[W] = [R(W) : R(W')] [W']` on `W'`. -/
theorem properCycleDegree_eq_functionFieldDegreeAtGenericPoint {m : ℤ}
    (hW : deltaDimension D sX W = m) (hW' : deltaDimension D sY (chernImage D hX hY q W) = m) :
    properCycleDegree D sX hX sY hY q.hom W =
      (functionFieldDegreeAtGenericPoint D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) ((chernImage D hX hY q W).subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY _) W.isIntegralSpace g : ℤ) := by
  classical
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY (chernImage D hX hY q W)
  have hnX : deltaDimensionClosed D (W.subspace.ι ≫ sX) hWg Set.univ isClosed_univ =
      ((m : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
  have hnY : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g Set.univ
      isClosed_univ = ((m : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY _, hW']
  have hgB := chernComponentHom_comp_eq D hX hY q W g hqB hg
  have hdom := IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base
    D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) q.hom W g hg
  have hgp := (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1
    q.hom hq W _ g hg)
  -- `g_*[W] = [R(W) : R(W')] [W']` on `W'`
  have h4 := properPushforward_integralCycle_integralClosedSubspaceUniv D (W.subspace.ι ≫ sX) hWg
    ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g W.isIntegralSpace
    (chernImage D hX hY q W).isIntegralSpace hgB hgp.2.1.2 hdom hnX hnY
  have htop := deltaDimension_top_of_deltaDimensionClosed_univ D _ hWg W.isIntegralSpace hnX
  have htop' := deltaDimension_top_of_deltaDimensionClosed_univ D _ hW'g
    (chernImage D hX hY q W).isIntegralSpace hnY
  -- `p_*[W]` read at `W'`
  have h1 : (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 m
      (integralCycle D sX m W hW)).1 (chernImage D hX hY q W) =
      properCycleDegree D sX hX sY hY q.hom W := by
    rw [properPushforward_apply, integralCycle_coe,
      finsum_eq_single _ W fun W₀ hW₀ => by rw [integralCycleCoeff_eq_zero D W hW₀, zero_mul],
      integralCycleCoeff_self, one_mul]
    unfold properCycleMult
    rw [ite_eq_left rfl]
  -- `p_*[W] = i'_* g_*[W]`
  have h2 := integralClosedSubspacePushforward_integralCycle_top D sX hX W hW htop
  have h3 := properCyclePushforward_integralClosedSubspacePushforward_closureImage D sX hX sY hY
    hqB hq W _ g hg m (integralCycle D (W.subspace.ι ≫ sX) m
      (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
        W.isIntegralSpace) htop)
  have h5 := integralClosedSubspacePushforward_integralCycle_top D sY hY
    (chernImage D hX hY q W) hW' htop'
  have hg4 : subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg m
      (integralCycle D (W.subspace.ι ≫ sX) m
        (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
          W.isIntegralSpace) htop) =
      (functionFieldDegreeAtGenericPoint D (W.subspace.ι ≫ sX) hWg
        ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g W.isIntegralSpace g : ℤ) •
        integralCycle D ((chernImage D hX hY q W).subspace.ι ≫ sY) m
          (IntegralClosedSubspace.top D.site D.base D.base_mem
            (chernImage D hX hY q W).isClosedSubspace.1
            (chernImage D hX hY q W).isIntegralSpace) htop' := by
    rw [integralCycle_top_eq_univ D _ hWg W.isIntegralSpace hnX,
      integralCycle_top_eq_univ D _ hW'g (chernImage D hX hY q W).isIntegralSpace hnY]
    exact h4
  rw [← h2, h3, hg4, map_zsmul, h5, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul,
    integralCycle_coe, integralCycleCoeff_self, mul_one] at h1
  exact h1.symm

include hg in
/-- **The pushforward along the component morphism of the divisor of the pulled-back section.**
Let `W ⊆ X` have δ-dimension `k + 1`. If, when `dim_δ(W') = k + 1`, Stacks 0EQS holds for `g`
in the form `hsec` — `g_* div_{g^*ℳ}(g^*t') = [R(W) : R(W')] div_ℳ(t')` on `W'` — then in every
case

`g_* div_{g^*ℳ}(g^*t') = deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`,

the right side being extended by zero off δ-dimension `k + 1`. When the dimension drops by one
both sides vanish
(`properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop`),
and when it drops further there are no `k`-cycles on `W'`. -/
theorem subspaceProperCyclePushforward_chernPulledDivisor
    (hW : deltaDimension D sX W = k + 1)
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hsec : ∀ hk' : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt),
      properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          ((chernImage D hX hY q W).subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY _)
          (show g ≫ (chernImage D hX hY q W).subspace.ι ≫ sY = W.subspace.ι ≫ sX by
            rw [← Category.assoc, hg, Category.assoc, hqB])
          (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 q.hom
            hq W _ g hg).2.1.2 k
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
            W.isIntegralSpace _
            (modulePullbackInvertible (chernComponentHom D hX hY q W g) _
              (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL
                (chernImage D hX hY q W)))
            (chernPulledSection D hX hY q L hL W g hg)
            (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg) hk) =
        (functionFieldDegreeAtGenericPoint D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) ((chernImage D hX hY q W).subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY _) W.isIntegralSpace g : ℤ) •
          canonicalDivisorCycleAt D ((chernImage D hX hY q W).subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY _) (chernImage D hX hY q W).isIntegralSpace
            (chernImageModule D hX hY q L W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL
              (chernImage D hX hY q W))
            (componentMeromorphicSection sY hY (subspaceDivisorSetupOfIsGood D sY hY) L hL
              (chernImage D hX hY q W))
            (isRegularMeromorphicSection_componentMeromorphicSection sY hY
              (subspaceDivisorSetupOfIsGood D sY hY) L hL (chernImage D hX hY q W)) hk') :
    subspaceProperCyclePushforward D sX hX sY hY hqB hq W _ g hg k
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace _
          (modulePullbackInvertible (chernComponentHom D hX hY q W g) _
            (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL
              (chernImage D hX hY q W)))
          (chernPulledSection D hX hY q L hL W g hg)
          (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg) hk) =
      properCycleDegree D sX hX sY hY q.hom W •
        chernComponentCycleOrZero D sY k (canonicalFirstChernRule D sY hY L hL k)
          (chernImage D hX hY q W) := by
  have hWg := isGood_integralClosedSubspace D sX hX W
  have hW'g := isGood_integralClosedSubspace D sY hY (chernImage D hX hY q W)
  have hle : deltaDimension D sY (chernImage D hX hY q W) ≤ k + 1 := by
    rw [← hW]
    exact IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY q.hom hqB W
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- the equal-dimensional case: Stacks 0EQS for `g`
    have hk' : deltaDimensionClosed D ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g Set.univ
        isClosed_univ = ((k + 1 : ℤ) : EInt) := by
      rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY _, heq]
    rw [chernComponentCycleOrZero_of_deltaDimension_eq D sY k _ heq,
      properCycleDegree_eq_functionFieldDegreeAtGenericPoint D hX hY q W g hg hqB hq hW heq]
    exact hsec hk'
  rcases eq_or_lt_of_le (show deltaDimension D sY (chernImage D hX hY q W) ≤ k by omega) with
    heq | hlt'
  · -- the dimension-drop case
    rw [chernComponentCycleOrZero_of_deltaDimension_ne D sY k _ (by omega), smul_zero]
    exact properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop
      D (W.subspace.ι ≫ sX) hWg W.isIntegralSpace ((chernImage D hX hY q W).subspace.ι ≫ sY) hW'g
      (chernImage D hX hY q W).isIntegralSpace (chernComponentHom D hX hY q W g)
      (chernComponentHom_comp_eq D hX hY q W g hqB hg)
      (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 q.hom hq W
        _ g hg).2.1.2
      (pullbacksMeromorphicSections_chernComponentHom D hX hY q W g hg) k hk
      ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D sY hY _ hW'g).trans heq)
      _ (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL (chernImage D hX hY q W))
      _ (isRegularMeromorphicSection_componentMeromorphicSection sY hY
        (subspaceDivisorSetupOfIsGood D sY hY) L hL (chernImage D hX hY q W))
      (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W g hg)
  · -- no `k`-cycles on `W'`
    exact (cycleGroup_eq_zero_of_deltaDimension_lt D sY hY _ k hlt' _).trans
      (cycleGroup_eq_zero_of_deltaDimension_lt D sY hY _ k hlt' _).symm

end Component

end AlgebraicGeometry.Space

end
