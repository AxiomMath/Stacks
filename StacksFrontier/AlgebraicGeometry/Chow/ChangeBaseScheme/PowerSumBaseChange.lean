module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChernCharacterCap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed

/-!
# Base change of Chow groups commutes with the power sums of a module of arbitrary rank

Let `B` be a flat base change of Chow situations `g : S' ⟶ S` ([Stacks, Tag 0FVG]), `X` locally
of finite type over `S` with base change `X' = X ×_S S'`, and `ℰ` a finite locally free
`𝒪_X`-module whose rank need not be constant, with base change `ℰ'` on `X'`. This file shows that
the base-change map `g^*` of [Stacks, Tag 0FVJ] commutes with capping with the power sums
`P_p(ℰ)` and `P_p(ℰ')` of [Stacks, Tag 0FA7]:

  `g^*(P_p(ℰ) ∩ α) = P_p(ℰ') ∩ g^*α`.

On the rank loci `X_r` of `ℰ` this is the constant-rank case
(`Stacks.Chow.TotalChowClass.baseChangeCompatible_powerSumTotal`); the base changes `X_r ×_S S'`
form a decomposition of `X'` into open and closed subschemes, the Chow groups of `X'` are the
product of theirs, and base change commutes with restriction to open subschemes
(`Stacks.Chow.baseChangeChowPullback_chowGroupRestrict`, from [Stacks, Tag 0FVK]).

## Main results

* `Stacks.Chow.baseChangeChowPullback_chowGroupRestrict` — base change commutes with restriction
  along an open immersion.
* `Stacks.Chow.TotalChowClass.baseChangeCompatible_powerSumOfFiniteLocallyFree` — the power sums
  of a module of arbitrary rank commute with base change.

## References

* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FVN](https://stacks.math.columbia.edu/tag/0FVN)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ B.base.S)
  [LocallyOfFiniteType sX]

/-! ### Base change and restriction to open subschemes -/

section OpenRestriction

variable {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]

/-- The base change of an open immersion is an open immersion. -/
instance isOpenImmersion_baseChangeMorphism : IsOpenImmersion (baseChangeMorphism B sX j) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_baseChangeMorphism B sX j) inferInstance

/-- **Base change commutes with restriction to an open subscheme, on cycles**: Stacks 0FVK for
the open immersion `j`, flat of relative dimension zero. -/
theorem cycleGroupRestrict_baseChangeCyclePullback (k : ℤ) (z : CycleGroup B.base sX k) :
    cycleGroupRestrict B.baseChange (pullback.snd sX B.g) (pullback.snd (j ≫ sX) B.g)
        (baseChangeMorphism B sX j) (baseChangeMorphism_comp_snd B sX j) (k + B.c)
        (baseChangeCyclePullback B sX k z) =
      baseChangeCyclePullback B (j ≫ sX) k (cycleGroupRestrict B.base sX (j ≫ sX) j rfl k z) := by
  have hj0 := relativeDimension_of_isOpenImmersion j
  have hb0 := relativeDimension_of_isOpenImmersion (baseChangeMorphism B sX j)
  have hcomm : pullback.fst (j ≫ sX) B.g ≫ j = baseChangeMorphism B sX j ≫ pullback.fst sX B.g :=
    (baseChangeMorphism_comp_fst B sX j).symm
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  have key := baseChangeCyclePullback_flatPullback_apply B (j ≫ sX) sX j rfl
    (baseChangeMorphism B sX j) (baseChangeMorphism_comp_snd B sX j) hcomm 0 hj0 hb0 k
    (baseChangeClosedSubschemeCycleRule_holds B)
    (flatPullbackClosedSubschemeCycleRule_holds _ _ _ _ _ _ _ _) z y
  rw [← cycleGroupRestrict_eq_flatPullback _ _ _ _ _ hb0, baseChangeCyclePullback_apply,
    ← cycleGroupRestrict_eq_flatPullback _ _ _ _ _ hj0] at key
  rw [← key, baseChangeCyclePullback_apply]
  simp only [Nat.cast_zero, add_zero]

/-- **Base change commutes with restriction to an open subscheme**, on Chow groups:
`(g^*α)|_{W ×_S S'} = g^*(α|_W)` for an open immersion `W ⟶ X`. -/
theorem baseChangeChowPullback_chowGroupRestrict (k : ℤ) (α : chowGroup B.base sX k) :
    chowGroupRestrict B.baseChange (pullback.snd sX B.g) (pullback.snd (j ≫ sX) B.g)
        (baseChangeMorphism B sX j) (baseChangeMorphism_comp_snd B sX j) (k + B.c)
        (baseChangeChowPullback B sX k α) =
      baseChangeChowPullback B (j ≫ sX) k (chowGroupRestrict B.base sX (j ≫ sX) j rfl k α) := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences B.base sX k) α
  rw [baseChangeChowPullback_mk, chowGroupRestrict_mk, chowGroupRestrict_mk,
    baseChangeChowPullback_mk, cycleGroupRestrict_baseChangeCyclePullback]

omit [LocallyOfFiniteType sX] in
/-- The image of the base change `W ×_S S' ⟶ X ×_S S'` of an open immersion `W ⟶ X` is the
inverse image of the image of `W`. -/
theorem opensRange_baseChangeMorphism :
    (baseChangeMorphism B sX j).opensRange = (pullback.fst sX B.g) ⁻¹ᵁ j.opensRange := by
  have hsq := isPullback_baseChangeMorphism B sX j
  have h : hsq.flip.isoPullback.hom ≫ pullback.fst (pullback.fst sX B.g) j =
      baseChangeMorphism B sX j :=
    IsPullback.isoPullback_hom_fst _
  rw [← Scheme.Hom.opensRange_pullbackFst]
  convert Scheme.Hom.opensRange_comp_of_isIso hsq.flip.isoPullback.hom
    (pullback.fst (pullback.fst sX B.g) j) using 2
  exact h.symm

end OpenRestriction

/-! ### Caps and restriction -/

namespace TotalChowClass

/-- **The cap product commutes with restriction to an open subscheme**:
`(c ∩ α)|_V = c|_V ∩ α|_V` for a total class `c` and an open immersion `V ⟶ Y`. -/
theorem chowGroupRestrict_capFamily {C : ChowSituation.{u}} {Y V : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sV : V ⟶ C.S} [LocallyOfFiniteType sV] (c : TotalChowClass C sY)
    (j : V ⟶ Y) [IsOpenImmersion j] (hj : j ≫ sY = sV) (k : ℤ) (p : ℕ)
    (α : chowGroup C sY k) :
    chowGroupRestrict C sY sV j hj (k - p) (c.capFamily k p α) =
      (res j hj c).capFamily k p (chowGroupRestrict C sY sV j hj k α) := by
  have h1 := chowGroupRestrict_chowCohomologyCap_restrictionOfEq C (gysinSystemOfInvertible C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) sY sY sV (p : ℤ) (𝟙 Y)
    (Category.id_comp sY) j hj (c p) k α
  rw [← res_apply_eq_chowCohomologyRestrictionOfEq, ← res_apply_eq_chowCohomologyRestrictionOfEq,
    res_id, res_congr (Category.comp_id j) _ hj] at h1
  exact h1

end TotalChowClass

/-! ### Joint injectivity of restriction to the pieces -/

/-- Two Chow classes in equal degrees are heterogeneously equal once their restrictions to the
pieces of a decomposition into open and closed subschemes are. -/
theorem heq_of_forall_chowGroupRestrict_heq {C : ChowSituation.{u}} {Y : Scheme.{u}}
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {I : Type u} {W : I → Scheme.{u}}
    (s : ∀ i, W i ⟶ C.S) [∀ i, LocallyOfFiniteType (s i)] (m : ∀ i, W i ⟶ Y)
    [∀ i, IsOpenImmersion (m i)] (hm : ∀ i, m i ≫ sY = s i)
    (hdec : IsClopenDecomposition fun i ↦ (m i).opensRange) {a b : ℤ} (hab : a = b)
    {x : chowGroup C sY a} {y : chowGroup C sY b}
    (h : ∀ i, chowGroupRestrict C sY (s i) (m i) (hm i) a x ≍
      chowGroupRestrict C sY (s i) (m i) (hm i) b y) : x ≍ y := by
  subst hab
  refine heq_of_eq ((chowGroupClopenRestrictEquiv C sY s m hm hdec a).injective
    (funext fun i => ?_))
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  exact eq_of_heq (h i)

/-! ### Power sums of modules of arbitrary rank -/

namespace TotalChowClass

variable (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
  (F' : (pullback sX B.g : Scheme.{u}).Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F']
  (eF : F' ≅ (Scheme.Modules.pullback (pullback.fst sX B.g)).obj F)

/-- The base change of `ℰ` restricted to the base change of a rank locus is the base change of
the restriction of `ℰ`. -/
def pullbackBaseChangeMorphismIso {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.pullback (baseChangeMorphism B sX j)).obj F' ≅
      (Scheme.Modules.pullback (pullback.fst (j ≫ sX) B.g)).obj
        ((Scheme.Modules.pullback j).obj F) :=
  (Scheme.Modules.pullback (baseChangeMorphism B sX j)).mapIso eF ≪≫
    (Scheme.Modules.pullbackComp (baseChangeMorphism B sX j) (pullback.fst sX B.g)).app F ≪≫
      (Scheme.Modules.pullbackCongr (baseChangeMorphism_comp_fst B sX j)).app F ≪≫
        ((Scheme.Modules.pullbackComp (pullback.fst (j ≫ sX) B.g) j).app F).symm

include eF in
/-- **The power sums of a module of arbitrary rank commute with base change**: `P_p(ℰ)` on `X`
and `P_p(ℰ')` on `X' = X ×_S S'` are compatible with base change, `ℰ'` being identified with the
base change of `ℰ`. -/
theorem baseChangeCompatible_powerSumOfFiniteLocallyFree (p : ℕ) :
    BaseChangeCompatible (powerSumOfFiniteLocallyFree B.base sX F p)
      (powerSumOfFiniteLocallyFree B.baseChange (pullback.snd sX B.g) F' p) := by
  have hU := isClopenDecomposition_rankLociFamily F
  set U := rankLociFamily F with hUdef
  let m : ∀ r, (pullback ((U r).ι ≫ sX) B.g : Scheme.{u}) ⟶ pullback sX B.g :=
    fun r => baseChangeMorphism B sX (U r).ι
  have hm : ∀ r, m r ≫ pullback.snd sX B.g = pullback.snd ((U r).ι ≫ sX) B.g :=
    fun r => baseChangeMorphism_comp_snd B sX (U r).ι
  have hdec : IsClopenDecomposition fun r ↦ (m r).opensRange := by
    have h := hU.preimage (pullback.fst sX B.g)
    convert h using 2 with r
    rw [opensRange_baseChangeMorphism, Scheme.Opens.opensRange_ι]
  refine BaseChangeCompatible.of_heq fun k q α => ?_
  refine heq_of_forall_chowGroupRestrict_heq (fun r => pullback.snd ((U r).ι ≫ sX) B.g) m hm hdec
    (by ring) fun r => ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (m r)).obj F') r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (pullbackBaseChangeMorphismIso B sX F F' eF (U r).ι).symm
      (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r.down)
  have hcr := baseChangeCompatible_powerSumTotal (B := B) (sX := (U r).ι ≫ sX)
    ((Scheme.Modules.pullback (U r).ι).obj F) r.down ((Scheme.Modules.pullback (m r)).obj F')
    (pullbackBaseChangeMorphismIso B sX F F' eF (U r).ι) p
  have hres' := res_powerSumOfFiniteLocallyFree_of_rank B.baseChange (pullback.snd sX B.g) F'
    (m r) (hm r) r.down p
  rw [baseChangeChowPullback_chowGroupRestrict B sX (U r).ι (k - q)]
  show baseChangeChowPullback B ((U r).ι ≫ sX) (k - q)
      (chowGroupRestrict B.base sX ((U r).ι ≫ sX) (U r).ι rfl (k - q)
        ((powerSumOfFiniteLocallyFree B.base sX F p).capFamily k q α)) ≍
    chowGroupRestrict B.baseChange (pullback.snd sX B.g) (pullback.snd ((U r).ι ≫ sX) B.g) (m r)
      (hm r) (k + B.c - q)
      ((powerSumOfFiniteLocallyFree B.baseChange (pullback.snd sX B.g) F' p).capFamily
        (k + B.c) q (baseChangeChowPullback B sX k α))
  rw [chowGroupRestrict_capFamily, chowGroupRestrict_capFamily, hres',
    res_powerSumOfFiniteLocallyFree_rankLocus]
  exact (hcr.heq k q _).trans (heq_of_eq (congrArg _
    (baseChangeChowPullback_chowGroupRestrict B sX (U r).ι k α).symm))

end TotalChowClass

end Stacks.Chow

end
