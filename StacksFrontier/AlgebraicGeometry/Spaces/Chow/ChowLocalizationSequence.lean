module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequenceRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType

/-!
# The localization sequence of Chow groups of an algebraic space

In Situation 0EDT let `X/B` be good, let `U ⊆ X` be an open subspace and let `Y ⊆ X` be a closed
subspace with `|Y| = |X| \ |U|`, with inclusions `i : Y → X` and `j : U → X`. If `α, β ∈ Z_k(X)`
have `α|_U ∼_rat β|_U` then `α ∼_rat β + i_*γ` for some `γ ∈ Z_k(Y)`; in other words,

`CH_k(Y) →[i_*] CH_k(X) →[j^*] CH_k(U) → 0`

is an exact complex of abelian groups. This file constructs the two maps of Chow groups and proves
both assertions, for every closed subspace `Y` with that point set.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupClosedPushforward`: `i_* : CH_k(Y) → CH_k(X)`.
* `AlgebraicGeometry.Space.chowGroupRestrict`: `j^* : CH_k(X) → CH_k(U)`.

## Main results

* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_cycleGroupRestrict`: restriction of cycles
  to an open subspace preserves rational equivalence.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_cycleGroupClosedPushforward`: pushforward
  of cycles from a closed subspace preserves rational equivalence.
* `AlgebraicGeometry.Space.chowGroup_localization`: the localization sequence above.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Restriction to an open subspace preserves rational equivalence -/

section Restriction

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)

include hU hj hjc in
/-- Let `j : U ⟶ X` be an open immersion over the base, let `V ⊆ U` be an integral closed subspace
and let `W' ⊆ X` be the integral closed subspace on the closure of its image, with comparison
morphism `m : V ⟶ W'`. The restriction along `m` of a principal divisor `div_{W'}(f)` on `W'` is
the principal divisor on `V` of the rational function `f` read on `V` along `m`, both principal
divisors being read at the canonical embeddings of Stacks 0ENK. -/
theorem exists_isPrincipalDivisorCycle_restrict (k : ℤ)
    (V : IntegralClosedSubspace D.site D.base D.base_mem U)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : closureSubspace D sX hX j V = W')
    (m : V.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hm : m ≫ W'.subspace.ι = V.subspace.ι ≫ j)
    (c' : CycleGroup D (W'.subspace.ι ≫ sX) k)
    (hprin : IsPrincipalDivisorCycle D (W'.subspace.ι ≫ sX) k c') :
    ∃ c : CycleGroup D (V.subspace.ι ≫ sU) k,
      IsPrincipalDivisorCycle D (V.subspace.ι ≫ sU) k c ∧
        ∀ A : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor,
          c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            W'.isClosedSubspace.1 W'.isIntegralSpace.2.1 m A) = c.1 A := by
  classical
  subst hV
  have hW'good : D.IsGood ((closureSubspace D sX hX j V).subspace.ι ≫ sX) :=
    isGood_integralClosedSubspace D sX hX (closureSubspace D sX hX j V)
  have hVgood : D.IsGood (V.subspace.ι ≫ sU) := isGood_integralClosedSubspace D sU hU V
  have hmopen : IsOpenImmersion D.site D.base D.base_mem m :=
    IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq_closureImage D.site D.base D.base_mem
      hX.1 hU.1 (D.isDecentSpace_of_isGood sX hX) hj V hm
  have hmc : m ≫ (closureSubspace D sX hX j V).subspace.ι ≫ sX = V.subspace.ι ≫ sU := by
    rw [← Category.assoc, hm, Category.assoc, hjc]
  refine ⟨cycleGroupRestrict D ((closureSubspace D sX hX j V).subspace.ι ≫ sX) hW'good
    (V.subspace.ι ≫ sU) hVgood hmopen hmc k c', ?_, fun A => rfl⟩
  obtain ⟨hWg, hWint, f, heq⟩ := hprin
  have hWd : IsDecentSpace D.site D.base D.base_mem
      (closureSubspace D sX hX j V).subspace.toFunctor :=
    hWint.isDecentSpace
  let EX := genericFractionEmbedding D.site D.base D.base_mem hWg.1 hWint.isDecentSpace hWint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
      ((closureSubspace D sX hX j V).subspace.ι ≫ sX) hWg)
  let EV := genericFractionEmbedding D.site D.base D.base_mem hVgood.1
    V.isIntegralSpace.isDecentSpace V.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (V.subspace.ι ≫ sU) hVgood)
  let := EX.nontrivial
  let := EX.isNoetherianRing
  let := EX.krullDimLE
  let := EV.nontrivial
  let := EV.isNoetherianRing
  let := EV.krullDimLE
  have hgen := pointsMap_genericPoint_of_isOpenImmersion D.site D.base D.base_mem hVgood.1
    (closureSubspace D sX hX j V).isClosedSubspace.1 V.isIntegralSpace hWint hmopen
  let fV : (rationalFunctions D.site D.base D.base_mem hVgood.1)ˣ :=
    Units.map (rationalFunctionMap D.site D.base D.base_mem hVgood.1
      (closureSubspace D sX hX j V).isClosedSubspace.1 V.isIntegralSpace hWint m hgen :
        rationalFunctions D.site D.base D.base_mem hWg.1 →*
          rationalFunctions D.site D.base D.base_mem hVgood.1) f
  have hord : ∀ Z : PrimeDivisor D.site D.base D.base_mem V.subspace.toFunctor,
      EX.ord f (Z.closureImage D.site D.base D.base_mem
          (closureSubspace D sX hX j V).isClosedSubspace.1 V.isClosedSubspace.1 hWd hmopen) =
        EV.ord fV Z := fun Z =>
    (genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion D.site D.base D.base_mem
      hVgood.1 (closureSubspace D sX hX j V).isClosedSubspace.1 V.isIntegralSpace hWint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (V.subspace.ι ≫ sU) hVgood)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
        ((closureSubspace D sX hX j V).subspace.ι ≫ sX) hWg) m
      hmopen hgen Z _ (Z.pointsMap_genericPoint_closureImage D.site D.base D.base_mem
        (closureSubspace D sX hX j V).isClosedSubspace.1 V.isClosedSubspace.1 hWd hmopen) f).symm
  refine ⟨hVgood, V.isIntegralSpace, fV, ?_⟩
  funext A
  change c'.1 _ = _
  rw [heq]
  exact principalDivisorCycleCoefficients_closureImage_of_ord_eq D
    ((closureSubspace D sX hX j V).subspace.ι ≫ sX) hWg (V.subspace.ι ≫ sU) hVgood hWd
    V.isIntegralSpace.2.1 hmopen
    EX.emb (f : rationalFunctions D.site D.base D.base_mem hWg.1)
    (fun Z => f.isUnit.map (EX.emb Z)) EV.emb
    (fV : rationalFunctions D.site D.base D.base_mem hVgood.1)
    (fun Z => fV.isUnit.map (EV.emb Z)) hord A

/-- The pushforward of a cycle from an integral closed subspace `W ⊆ X` which misses the open
subspace restricts to zero on it. -/
theorem cycleGroupRestrict_integralClosedSubspacePushforward_of_disjoint (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (hW : ∀ p ∈ subspacePointSet D.site D.base D.base_mem X W.subspace,
      p ∉ Set.range (pointsMap D.site D.base D.base_mem U j)) :
    cycleGroupRestrict D sX hX sU hU hj hjc k (integralClosedSubspacePushforward D sX hX W k c) =
      0 := by
  refine Subtype.ext (funext fun A => ?_)
  rw [cycleGroupRestrict_apply]
  change _ = (0 : IntegralClosedSubspace D.site D.base D.base_mem U → ℤ) A
  by_contra hne
  have hsub := subspacePointSet_subset_of_pushforward_ne_zero D sX hX W k c _ hne
  have := A.isIntegralSpace.2.2
  obtain ⟨p0⟩ : Nonempty (points D.site D.base D.base_mem A.subspace.toFunctor) :=
    inferInstance
  have hmem : pointsMap D.site D.base D.base_mem U j
      (pointsMap D.site D.base D.base_mem A.subspace.toFunctor A.subspace.ι p0) ∈
      subspacePointSet D.site D.base D.base_mem X
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) j A).subspace := by
    rw [IntegralClosedSubspace.subspacePointSet_closureImage]
    exact subset_closure ⟨_, ⟨p0, rfl⟩, rfl⟩
  exact hW _ (hsub hmem) ⟨_, rfl⟩

include hU hj hjc in
/-- Restriction to an open subspace preserves rational equivalence: if `α ∈ Z_k(X)` is rationally
equivalent to zero then so is `α|_U ∈ Z_k(U)`. -/
theorem isRationallyEquivalentToZero_cycleGroupRestrict (k : ℤ) {α : CycleGroup D sX k}
    (hα : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    IsRationallyEquivalentToZero.{v} D sU hU k (cycleGroupRestrict D sX hX sU hU hj hjc k α) := by
  classical
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hα
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  let P : J → Prop := fun n => ∃ A : IntegralClosedSubspace D.site D.base D.base_mem U,
    closureSubspace D sX hX j A = W n
  choose A hA using fun n : {n // P n} => n.2
  have hm' : ∀ n : {n // P n}, ∃ m : (A n).subspace.toFunctor ⟶ (W n.1).subspace.toFunctor,
      m ≫ (W n.1).subspace.ι = (A n).subspace.ι ≫ j := by
    intro n
    rw [← hA n]
    exact IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) j (A n)
  choose m hm using hm'
  choose cA hcA hcc using fun n : {n // P n} =>
    exists_isPrincipalDivisorCycle_restrict D sX hX sU hU hj hjc k (A n) (W n.1) (hA n) (m n)
      (hm n) (c n.1) (hprin n.1)
  have hsub : ∀ n : {n // P n}, subspacePointSet D.site D.base D.base_mem U (A n).subspace ⊆
      pointsMap D.site D.base D.base_mem U j ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (W n.1).subspace := by
    intro n
    rw [← hA n, IntegralClosedSubspace.preimage_subspacePointSet_closureImage D.site D.base
      D.base_mem hX.1 hU.1 (D.isDecentSpace_of_isGood sX hX) himm (A n)]
  have hAfin : LocallyFinite fun n : {n // P n} =>
      subspacePointSet D.site D.base D.base_mem U (A n).subspace :=
    ((hWfin.comp_injective Subtype.val_injective).preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem j)).subset hsub
  have hdimA : ∀ n : {n // P n}, deltaDimension D sU (A n) = k + 1 := by
    intro n
    rw [← hjc, ← IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
      (D.isDecentSpace_of_isGood sX hX) himm (A n)]
    change deltaDimension D sX (closureSubspace D sX hX j (A n)) = k + 1
    rw [hA n]
    exact hdim n.1
  refine ⟨{n // P n}, A, hAfin, cA, hdimA, hcA, ?_⟩
  refine Subtype.ext (funext fun B => ?_)
  rw [cycleGroupRestrict_apply, cycleFamilySum_apply, cycleFamilySum_apply]
  set F : J → ℤ := fun n => (integralClosedSubspacePushforward D sX hX (W n) k (c n)).1
    (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) j B) with hF
  have hterm : ∀ n : {n // P n},
      (integralClosedSubspacePushforward D sU hU (A n) k (cA n)).1 B = F n.1 := by
    intro n
    have h := congrArg (fun e : CycleGroup D sU k => e.1 B)
      (cycleGroupRestrict_integralClosedSubspacePushforward_closureImage D sX hX sU hU hj hjc
        (A n) (W n.1) (hA n).symm (hm n) k (cA n) (c n.1) (hcc n))
    simpa only [cycleGroupRestrict_apply] using h.symm
  have hzero : ∀ n, ¬ P n → F n = 0 := by
    intro n hn
    have h := cycleGroupRestrict_integralClosedSubspacePushforward_of_disjoint D sX hX sU hU hj
      hjc k (W n) (c n) (fun p hp hpj => hn (IntegralClosedSubspace.exists_closureImage_eq D
        hX.1 hU.1 (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sU hU) hj (W n)
        ⟨p, hp, hpj⟩))
    exact congrArg (fun e : CycleGroup D sU k => e.1 B) h
  rw [finsum_congr hterm, finsum_subtype_eq_finsum_cond]
  refine finsum_congr fun n => ?_
  rw [finsum_eq_if]
  split_ifs with hn
  · rfl
  · exact hzero n hn

end Restriction

/-! ### Pushforward from a closed subspace preserves rational equivalence -/

section ClosedPushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hX hY in
/-- A closed subspace of a good algebraic space over the base is good over the base. -/
theorem isGood_ι_of_isClosedSubspace : D.IsGood (Y.ι ≫ sX) :=
  isGood_closedSubspace D sX hX ⟨Y, hY⟩

include hY in
/-- The integral closed subspace of `X` on the closure of the image of an integral closed subspace
`W` of a closed subspace `Y ⊆ X` has point set the image of `|W|`. -/
theorem subspacePointSet_closureSubspace_ι
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    subspacePointSet D.site D.base D.base_mem X (closureSubspace D sX hX Y.ι W).subspace =
      pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ''
        subspacePointSet D.site D.base D.base_mem Y.toFunctor W.subspace := by
  rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  exact ((isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hY.2).isClosedMap _ (isClosed_range_pointsMap_integralClosedSubspace D.site D.base
      D.base_mem hY.1 W)).closure_eq

include hX hY in
/-- For `Y ⊆ X` a closed subspace, `W ⊆ Y` an integral closed subspace and `W' ⊆ X` an integral
closed subspace with point set the image of `|W|`, a morphism `m : W ⟶ W'` over `X` is an
isomorphism. -/
theorem isIso_of_comp_ι_eq_of_subspacePointSet
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hpts : subspacePointSet D.site D.base D.base_mem X W'.subspace =
      pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ''
        subspacePointSet D.site D.base D.base_mem Y.toFunctor W.subspace)
    (m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ Y.ι) :
    IsIso m := by
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hY.2
  have hred : HasEtaleLocalProperty D.site D.base D.base_mem W'.subspace.toFunctor
      (fun T : Scheme.{u} => IsReduced T) := W'.isIntegralSpace.1
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset D.site D.base
    D.base_mem hX.1 W'.isClosedSubspace.1 Y hY hred W'.subspace.ι).2 (by
      change subspacePointSet D.site D.base D.base_mem X W'.subspace ⊆ _
      rw [hpts]
      exact Set.image_subset_range _ _)
  obtain ⟨n, hn⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset D.site D.base
    D.base_mem hY.1 W'.isClosedSubspace.1 W.subspace W.isClosedSubspace hred g).2 (by
      rintro _ ⟨p, rfl⟩
      have hp : pointsMap D.site D.base D.base_mem W'.subspace.toFunctor W'.subspace.ι p ∈
          subspacePointSet D.site D.base D.base_mem X W'.subspace := ⟨p, rfl⟩
      rw [hpts] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      have hgp : pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
          (pointsMap D.site D.base D.base_mem W'.subspace.toFunctor g p) =
          pointsMap D.site D.base D.base_mem W'.subspace.toFunctor W'.subspace.ι p := by
        rw [← hg, pointsMap_comp]
        rfl
      rw [← hemb.injective (hqp.trans hgp.symm)]
      exact hq)
  have hmono₁ : Mono (W.subspace.ι ≫ Y.ι) := mono_comp _ _
  refine ⟨⟨n, ?_, ?_⟩⟩
  · refine (cancel_mono (W.subspace.ι ≫ Y.ι)).1 ?_
    rw [Category.id_comp, Category.assoc, ← Category.assoc n, hn, hg, hm]
  · refine (cancel_mono W'.subspace.ι).1 ?_
    rw [Category.id_comp, Category.assoc, hm, ← Category.assoc, hn, hg]

/-- For `W ⊆ Y` an integral closed subspace of a closed subspace `Y ⊆ X`, any morphism `m` from `W`
to the integral closed subspace of `X` on the closure of its image, over `X`, is an
isomorphism. -/
private theorem isIso_of_comp_ι_eq_closureSubspace_ι
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    {m : W.subspace.toFunctor ⟶ (closureSubspace D sX hX Y.ι W).subspace.toFunctor}
    (hm : m ≫ (closureSubspace D sX hX Y.ι W).subspace.ι = W.subspace.ι ≫ Y.ι) :
    IsIso m :=
  isIso_of_comp_ι_eq_of_subspacePointSet D sX hX Y hY W _
    (subspacePointSet_closureSubspace_ι D sX hX Y hY W) m hm

/-- The coefficient of a pushforward along `Y ⊆ X` vanishes at an integral closed subspace of `X`
which is not the pushforward of one of `Y`. -/
private theorem cycleClosedPushforward_apply_eq_zero_of_not_exists_pushforward
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor → ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : ¬∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T) :
    cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 β T = 0 :=
  cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 β T fun T0 hT0 => hT ⟨T0, hT0⟩

/-- For an integral closed subspace `V` of an integral closed subspace `W ⊆ Y`, the image in `X` of
the closure of the image of `V` in `W'` is the image in `X` of the image of `V` in `Y`. -/
theorem IntegralClosedSubspace.pushforward_closureImage_eq_pushforward_pushforward
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    {m : W.subspace.toFunctor ⟶ (closureSubspace D sX hX Y.ι W).subspace.toFunctor}
    (hm : m ≫ (closureSubspace D sX hX Y.ι W).subspace.ι = W.subspace.ι ≫ Y.ι)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) :
    IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
        (closureSubspace D sX hX Y.ι W).isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
        (closureSubspace D sX hX Y.ι W).isClosedSubspace.2
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
          (closureSubspace D sX hX Y.ι W).isClosedSubspace.1
          (closureSubspace D sX hX Y.ι W).isIntegralSpace.2.1 m V) =
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 W.isClosedSubspace.1
          (isDecentSpace_of_isGood D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY))
          W.isClosedSubspace.2 V) := by
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    (closureSubspace D sX hX Y.ι W).isClosedSubspace.2
  have hcomp : pointsMap D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι W).subspace.toFunctor
        (closureSubspace D sX hX Y.ι W).subspace.ι ∘
      pointsMap D.site D.base D.base_mem W.subspace.toFunctor m =
      pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ∘
        pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι := by
    rw [← pointsMap_comp, ← pointsMap_comp, hm]
  refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
    (IrreducibleCloseds.ext ?_)
  change subspacePointSet D.site D.base D.base_mem X _ =
    subspacePointSet D.site D.base D.base_mem X _
  have hcl := isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 W.isClosedSubspace.1
          (isDecentSpace_of_isGood D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY))
          W.isClosedSubspace.2 V))
  change IsClosed (subspacePointSet D.site D.base D.base_mem X _) at hcl
  rw [← hcl.closure_eq, IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_closureImage, ← hemb.closure_image_eq,
    ← Set.image_comp, hcomp, Set.image_comp, IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_pushforward]

include hY in
/-- For `W ⊆ Y` an integral closed subspace of a closed subspace, `W' ⊆ X` the integral closed
subspace on its image, and `c'` a cycle on `W'` with the coefficients of a cycle `c` on `W` along
the comparison isomorphism, pushing `c` forward to `Y` and then to `X` gives the pushforward of
`c'` to `X`. -/
theorem cycleGroupClosedPushforward_integralClosedSubspacePushforward (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    {m : W.subspace.toFunctor ⟶ (closureSubspace D sX hX Y.ι W).subspace.toFunctor}
    (hm : m ≫ (closureSubspace D sX hX Y.ι W).subspace.ι = W.subspace.ι ≫ Y.ι)
    (c : CycleGroup D (W.subspace.ι ≫ Y.ι ≫ sX) k)
    (c' : CycleGroup D ((closureSubspace D sX hX Y.ι W).subspace.ι ≫ sX) k)
    (hcc : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι W).isClosedSubspace.1
        (closureSubspace D sX hX Y.ι W).isIntegralSpace.2.1 m V) = c.1 V) :
    cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k
        (integralClosedSubspacePushforward D (Y.ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX Y hY) W k c) =
      integralClosedSubspacePushforward D sX hX (closureSubspace D sX hX Y.ι W) k c' := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have := isIso_of_comp_ι_eq_closureSubspace_ι D sX hX Y hY W hm
  have hmopen : IsOpenImmersion D.site D.base D.base_mem m :=
    isOpenImmersion_of_isIso D.site D.base D.base_mem m
  have hroute := IntegralClosedSubspace.pushforward_closureImage_eq_pushforward_pushforward D sX
    hX Y hY W hm
  have hall : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem
      (closureSubspace D sX hX Y.ι W).subspace.toFunctor, ∃ V,
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι W).isClosedSubspace.1
        (closureSubspace D sX hX Y.ι W).isIntegralSpace.2.1 m V = T := by
    intro T
    have := T.isIntegralSpace.2.2
    obtain ⟨p0⟩ : Nonempty (points D.site D.base D.base_mem T.subspace.toFunctor) :=
      inferInstance
    refine IntegralClosedSubspace.exists_closureImage_eq D
      (closureSubspace D sX hX Y.ι W).isClosedSubspace.1 W.isClosedSubspace.1
      (closureSubspace D sX hX Y.ι W).isIntegralSpace.2.1 W.isIntegralSpace.2.1 hmopen T
      ⟨_, ⟨p0, rfl⟩, ?_⟩
    refine ⟨pointsMap D.site D.base D.base_mem _ (inv m)
      (pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι p0), ?_⟩
    rw [← Function.comp_apply (f := pointsMap D.site D.base D.base_mem _ m), ← pointsMap_comp,
      IsIso.inv_hom_id, pointsMap_id]
    rfl
  refine Subtype.ext (funext fun T => ?_)
  change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (cycleClosedPushforward D hY.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood _ hYgood) W.isClosedSubspace.2 c.1) T =
    cycleClosedPushforward D hX.1 (closureSubspace D sX hX Y.ι W).isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) (closureSubspace D sX hX Y.ι W).isClosedSubspace.2 c'.1 T
  by_cases hT : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      (closureSubspace D sX hX Y.ι W).isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
      (closureSubspace D sX hX Y.ι W).isClosedSubspace.2
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι W).isClosedSubspace.1
        (closureSubspace D sX hX Y.ι W).isIntegralSpace.2.1 m V) = T
  · obtain ⟨V, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, hcc, hroute,
      cycleClosedPushforward_apply_pushforward, cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 _ _ _ c'.1 T (fun T' hT' => by
      obtain ⟨V, rfl⟩ := hall T'
      exact hT ⟨V, hT'⟩)]
    by_cases hT0 : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
    · obtain ⟨T0, rfl⟩ := hT0
      rw [cycleClosedPushforward_apply_pushforward]
      refine cycleClosedPushforward_apply_of_forall_ne D hY.1 _ _ _ c.1 T0 fun V hV => ?_
      refine hT ⟨V, ?_⟩
      rw [hroute, ← hV]
    · exact cycleClosedPushforward_apply_eq_zero_of_not_exists_pushforward D sX hX Y hY _ T hT0

include hY in
/-- Pushforward from a closed subspace preserves rational equivalence: if `β ∈ Z_k(Y)` is
rationally equivalent to zero then so is `i_*β ∈ Z_k(X)`. -/
theorem isRationallyEquivalentToZero_cycleGroupClosedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZero.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β) :
    IsRationallyEquivalentToZero.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β) := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hβ
  have himm : IsImmersion D.site D.base D.base_mem Y.ι :=
    isImmersion_of_isClosedImmersion D.site D.base D.base_mem hY.2
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hY.2
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) Y.ι (W n)
  have hmopen : ∀ n, IsOpenImmersion D.site D.base D.base_mem (m n) := fun n =>
    have := isIso_of_comp_ι_eq_closureSubspace_ι D sX hX Y hY (W n) (hm n)
    isOpenImmersion_of_isIso D.site D.base D.base_mem (m n)
  choose c' hprin' hcc using fun n =>
    exists_isPrincipalDivisorCycle_closureImage D sX hX (Y.ι ≫ sX) hYgood himm rfl k (W n) (c n)
      (m n) (hmopen n) (hdim n) (hprin n)
  have hpts := fun n => subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)
  have hW'fin : LocallyFinite fun n => subspacePointSet D.site D.base D.base_mem X
      (closureSubspace D sX hX Y.ι (W n)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend hemb (e := id)
      (fun w hw => absurd rfl (hw w)) (fun n => (hpts n).subset) hWfin
  have hdim' : ∀ n, deltaDimension D sX (closureSubspace D sX hX Y.ι (W n)) = k + 1 := by
    intro n
    rw [IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n)]
    exact hdim n
  refine ⟨J, fun n => closureSubspace D sX hX Y.ι (W n), hW'fin, c', hdim', hprin', ?_⟩
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleFamilySum_apply]
  have hterm := fun n => congrArg (fun e : CycleGroup D sX k => e.1 T)
    (cycleGroupClosedPushforward_integralClosedSubspacePushforward D sX hX Y hY k (W n) (hm n)
      (c n) (c' n) (hcc n))
  rw [← finsum_congr hterm]
  change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (cycleFamilySum D (Y.ι ≫ sX) hYgood W hWfin k c).1 T = _
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    refine finsum_congr fun n => ?_
    change _ = cycleClosedPushforward D hX.1 hY.1 _ hY.2 _ _
    rw [cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_eq_zero_of_not_exists_pushforward D sX hX Y hY _ T hT]
    exact (finsum_eq_zero_of_forall_eq_zero fun n =>
      cycleClosedPushforward_apply_eq_zero_of_not_exists_pushforward D sX hX Y hY _ T hT).symm

end ClosedPushforward

/-! ### The localization sequence -/

section Localization

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (U : Subfunctor X) (hU : IsOpenSubspace D.site D.base D.base_mem U)

include hX hU in
/-- An open subspace of a good algebraic space over the base is good over the base. -/
theorem isGood_ι_of_isOpenSubspace : D.IsGood (U.ι ≫ sX) :=
  ⟨hU.1,
    isQuasiSeparated_comp D.site D.base D.base_mem hU.1 hX.1 _ _
      (isQuasiSeparated_of_mono D.site D.base D.base_mem U.ι
        (mono_of_isOpenImmersion D.site D.base D.base_mem U.ι hU.2)) hX.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem hU.1 hX.1 D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isImmersion D.site D.base D.base_mem U.ι
        (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hU.2)) hX.2.2⟩

/-- The pushforward `i_* : CH_k(Y) → CH_k(X)` along the inclusion of a closed subspace, induced by
the pushforward of cycles. -/
def chowGroupClosedPushforward (k : ℤ) :
    chowGroup.{v} D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) k →+
      chowGroup.{v} D sX hX k :=
  QuotientAddGroup.map _ _
    (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
      (Y.ι ≫ sX) rfl k)
    (fun _ hβ => isRationallyEquivalentToZero_cycleGroupClosedPushforward.{v} D sX hX Y hY k hβ)

/-- The restriction `j^* : CH_k(X) → CH_k(U)` to an open subspace, induced by the restriction of
cycles. -/
def chowGroupRestrict (k : ℤ) :
    chowGroup.{v} D sX hX k →+
      chowGroup.{v} D (U.ι ≫ sX) (isGood_ι_of_isOpenSubspace D sX hX U hU) k :=
  QuotientAddGroup.map _ _
    (cycleGroupRestrict D sX hX (U.ι ≫ sX) (isGood_ι_of_isOpenSubspace D sX hX U hU) hU.2 rfl k)
    (fun _ hα => isRationallyEquivalentToZero_cycleGroupRestrict.{v} D sX hX (U.ι ≫ sX)
      (isGood_ι_of_isOpenSubspace D sX hX U hU) hU.2 rfl k hα)

/-- In Situation 0EDT let `X/B` be good, let `U ⊆ X` be an open subspace, let `Y ⊆ X` be a closed
subspace with `|Y| = |X| \ |U|` and let `i : Y → X`, `j : U → X` be the inclusions. Let `k ∈ ℤ`.

1. If `α, β ∈ Z_k(X)` satisfy `α|_U ∼_rat β|_U`, then `α ∼_rat β + i_*γ` for some `γ ∈ Z_k(Y)`.
2. In other words, `CH_k(Y) →[i_*] CH_k(X) →[j^*] CH_k(U) → 0` is an exact complex of abelian
   groups: the kernel of `j^*` is the image of `i_*`, and `j^*` is surjective. -/
@[stacks 0EQ7]
theorem chowGroup_localization
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem U.toFunctor U.ι))ᶜ) (k : ℤ) :
    (∀ α β : CycleGroup D sX k,
      RationallyEquivalent.{v} D (U.ι ≫ sX) (isGood_ι_of_isOpenSubspace D sX hX U hU) k
        (cycleGroupRestrict D sX hX (U.ι ≫ sX) (isGood_ι_of_isOpenSubspace D sX hX U hU) hU.2
          rfl k α)
        (cycleGroupRestrict D sX hX (U.ι ≫ sX) (isGood_ι_of_isOpenSubspace D sX hX U hU) hU.2
          rfl k β) →
      ∃ γ : CycleGroup D (Y.ι ≫ sX) k,
        RationallyEquivalent.{v} D sX hX k α
          (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
            sX hX.2.2 (Y.ι ≫ sX) rfl k γ)) ∧
      Function.Exact (chowGroupClosedPushforward.{v} D sX hX Y hY k)
        (chowGroupRestrict.{v} D sX hX U hU k) ∧
      Function.Surjective (chowGroupRestrict.{v} D sX hX U hU k) := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hUgood := isGood_ι_of_isOpenSubspace D sX hX U hU
  have hcyc : ∀ α β : CycleGroup D sX k,
      RationallyEquivalent.{v} D (U.ι ≫ sX) hUgood k
        (cycleGroupRestrict D sX hX (U.ι ≫ sX) hUgood hU.2 rfl k α)
        (cycleGroupRestrict D sX hX (U.ι ≫ sX) hUgood hU.2 rfl k β) →
      ∃ γ : CycleGroup D (Y.ι ≫ sX) k,
        RationallyEquivalent.{v} D sX hX k α
          (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
            sX hX.2.2 (Y.ι ≫ sX) rfl k γ) := fun α β h =>
    exists_rationallyEquivalent_add_cycleGroupClosedPushforward_of_restrict.{v} D sX hX
      (Y.ι ≫ sX) hYgood (U.ι ≫ sX) hUgood hY.2 rfl hU.2 rfl hcomplement k α β h
  refine ⟨hcyc, fun y => ⟨fun hy => ?_, ?_⟩, fun y => ?_⟩
  · induction y using QuotientAddGroup.induction_on with
    | H α =>
      have h0 : IsRationallyEquivalentToZero.{v} D (U.ι ≫ sX) hUgood k
          (cycleGroupRestrict D sX hX (U.ι ≫ sX) hUgood hU.2 rfl k α) :=
        (QuotientAddGroup.eq_zero_iff _).1 hy
      obtain ⟨γ, hγ⟩ := hcyc α 0 (by
        change IsRationallyEquivalentToZero.{v} D _ hUgood k (_ - _)
        rwa [map_zero, sub_zero])
      refine ⟨(γ : chowGroup.{v} D (Y.ι ≫ sX) hYgood k), ?_⟩
      change ((cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        sX hX.2.2 (Y.ι ≫ sX) rfl k γ : CycleGroup D sX k) : chowGroup.{v} D sX hX k) = α
      rw [QuotientAddGroup.eq_iff_sub_mem, ← neg_sub]
      rw [zero_add] at hγ
      exact neg_mem hγ
  · rintro ⟨z, rfl⟩
    induction z using QuotientAddGroup.induction_on with
    | H γ =>
      change ((cycleGroupRestrict D sX hX (U.ι ≫ sX) hUgood hU.2 rfl k
        (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
          sX hX.2.2 (Y.ι ≫ sX) rfl k γ) : CycleGroup D (U.ι ≫ sX) k) :
        chowGroup.{v} D (U.ι ≫ sX) hUgood k) = 0
      rw [(cycleGroupRestrict_eq_zero_iff D sX hX (Y.ι ≫ sX) hYgood (U.ι ≫ sX) hUgood hY.2 rfl
        hU.2 rfl hcomplement k _).2 ⟨γ, rfl⟩]
      rfl
  · induction y using QuotientAddGroup.induction_on with
    | H α =>
      obtain ⟨β, hβ⟩ := cycleGroupRestrict_surjective D sX hX (U.ι ≫ sX) hUgood hU.2 rfl k α
      exact ⟨(β : chowGroup.{v} D sX hX k), congrArg _ hβ⟩

end Localization

end AlgebraicGeometry.Space

end
