module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChernCharacterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothGysinRing

/-!
# Base change along a field extension carries `[X]` to `[X_{k'}]`

Let `k'/k` be an extension of fields and `X` a scheme smooth over `k`, with base change
`X' = X ×_k k'`. The base-change map `g^* : CH_n(X) ⟶ CH_n(X')` of [Stacks, Tag 0FVJ] (the
dimension shift of a field extension is zero) carries the fundamental class to the fundamental
class:

  `g^*[X]_n = [X']_n`,   and   `g^*[X] = [X']`   in `CH_*(-) ⊗ 𝐐`.

On the part `X_d` of `X` of dimension `d`, this is the cycle identity of [Stacks, Tag 0FVI] for
`n = d`, and both sides vanish for `n ≠ d`, every irreducible component of `X_d` and of its base
change having dimension `d`; the base changes of the parts form a decomposition of `X'` into open
and closed subschemes, along which base change commutes with restriction
(`Stacks.Chow.baseChangeChowPullback_chowGroupRestrict`).

## Main results

* `Stacks.Chow.baseChangeChowPullback_fundamentalChowClass` — `g^*[X]_n = [X']_n`.
* `Stacks.Chow.rationalBaseChangeChowPullback_rationalFundamentalClass` — `g^*[X] = [X']`.

## References

* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart)

universe u

namespace Stacks.Chow

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- **Base change along a field extension carries `[X]_n` to `[X']_n`**, for `X` smooth over
`k`. -/
theorem baseChangeChowPullback_fundamentalChowClass (n : ℤ) :
    baseChangeChowPullback (fieldExtensionBaseChangeSituation k k') sX n
        (fundamentalChowClass (fieldChowSituation k) sX n) =
      fundamentalChowClass (fieldChowSituation k')
        (pullback.snd sX (fieldExtensionBaseChangeSituation k k').g)
        (n + (fieldExtensionBaseChangeSituation k k').c) := by
  set B := fieldExtensionBaseChangeSituation k k' with hB
  set U : ULift.{u} ℕ → X.Opens := fun d => dimPart sX d.down with hU
  have hUdec : IsClopenDecomposition U := by
    have h := (isClopenDecomposition_dimPart sX).opensRange_ι_equiv Equiv.ulift
    convert h using 2 with d
    exact (Scheme.Opens.opensRange_ι _).symm
  let m : ∀ d, (pullback ((U d).ι ≫ sX) B.g : Scheme.{u}) ⟶ pullback sX B.g :=
    fun d => baseChangeMorphism B sX (U d).ι
  have hm : ∀ d, m d ≫ pullback.snd sX B.g = pullback.snd ((U d).ι ≫ sX) B.g :=
    fun d => baseChangeMorphism_comp_snd B sX (U d).ι
  have hdec : IsClopenDecomposition fun d ↦ (m d).opensRange := by
    have h := hUdec.preimage (pullback.fst sX B.g)
    convert h using 2 with d
    rw [opensRange_baseChangeMorphism, Scheme.Opens.opensRange_ι]
  refine eq_of_heq (heq_of_forall_chowGroupRestrict_heq (fun d => pullback.snd ((U d).ι ≫ sX) B.g)
    m hm hdec rfl fun d => heq_of_eq ?_)
  rw [baseChangeChowPullback_chowGroupRestrict B sX (U d).ι n,
    chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion,
    chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  have hd : RelativeDimension ((U d).ι ≫ sX) d.down := relativeDimension_partBase sX d.down
  have hd' : RelativeDimension (pullback.snd ((U d).ι ≫ sX) B.g) d.down :=
    relativeDimension_pullbackSnd _ hd _
  have hc : B.c = 0 := rfl
  by_cases hn : n = d.down
  · subst hn
    have hZ : schemeDeltaDimension B.base (𝟙 _ ≫ ((U d).ι ≫ sX)) ≤ ((d.down : ℤ) : EInt) := by
      have hcongr : ∀ {g h : (U d : Scheme.{u}) ⟶ B.base.S} [LocallyOfFiniteType g]
          [LocallyOfFiniteType h], g = h →
          schemeDeltaDimension B.base g = schemeDeltaDimension B.base h := by
        intro g h _ _ e
        subst e
        rfl
      rw [hcongr (Category.id_comp ((U d).ι ≫ sX))]
      exact Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _ hd
    have h0 := baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst B ((U d).ι ≫ sX)
      (𝟙 _) (d.down : ℤ) hZ
    rw [fundamentalChowClass, fundamentalChowClass, baseChangeChowPullback_mk]
    refine congrArg (QuotientAddGroup.mk' _) ?_
    rw [fundamentalCycle, h0, fundamentalCycle]
    exact cycleAssociatedToClosedSubscheme_eq_of_iso B.baseChange _ _ _
      (asIso (pullback.fst (pullback.fst ((U d).ι ≫ sX) B.g) (𝟙 _))) (Category.comp_id _) _
  · rw [fundamentalChowClass_eq_zero_of_relativeDimension k _ hd hn, map_zero,
      fundamentalChowClass_eq_zero_of_relativeDimension k' _ hd' (by rw [hc, add_zero]; exact hn)]

variable [IsNoetherian X]

/-- The base change `X ×_k k'` of a Noetherian scheme `X` smooth over `k` along the field extension
`k'/k` is Noetherian. -/
instance isNoetherian_pullback_fieldExtension :
    IsNoetherian (pullback sX (fieldExtensionBaseChangeSituation k k').g : Scheme.{u}) := by
  have : QuasiCompact sX := (quasiCompact_iff_compactSpace sX).mpr inferInstance
  exact isNoetherian_of_quasiCompact_fieldChowSituation k'
    (pullback.snd sX (fieldExtensionBaseChangeSituation k k').g)

/-- **Base change along a field extension carries `[X]` to `[X']` in `CH_*(-) ⊗ 𝐐`**, for `X`
smooth over `k` and Noetherian. -/
theorem rationalBaseChangeChowPullback_rationalFundamentalClass :
    rationalBaseChangeChowPullback (fieldExtensionBaseChangeSituation k k') sX
        (rationalFundamentalClass (fieldChowSituation k) sX) =
      rationalFundamentalClass (fieldChowSituation k')
        (pullback.snd sX (fieldExtensionBaseChangeSituation k k').g) := by
  classical
  set B := fieldExtensionBaseChangeSituation k k' with hB
  set sX' := pullback.snd sX B.g
  set D := (fundamentalClassDegrees_finite (fieldChowSituation k) sX).toFinset
  set D' := (fundamentalClassDegrees_finite (fieldChowSituation k') sX').toFinset
  have hsum : ∀ (T : Scheme.{u}) (C : ChowSituation.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
      [IsNoetherian T] (E S : Finset ℤ), (fundamentalClassDegrees_finite C sT).toFinset = E →
      E ⊆ S → rationalFundamentalClass C sT =
        ∑ n ∈ S, DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sT j) n
          ((1 : ℚ) ⊗ₜ[ℤ] fundamentalChowClass C sT n) := by
    intro T C sT _ _ E S hE hES
    rw [rationalFundamentalClass_eq, hE]
    refine Finset.sum_subset hES fun n _ hn => ?_
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sT
      fun h' => hn (hE ▸ (fundamentalClassDegrees_finite C sT).mem_toFinset.2 h'), map_zero,
      TensorProduct.tmul_zero, map_zero]
  have hfc : ∀ {a b : ℤ}, a = b → fundamentalChowClass (fieldChowSituation k') sX' a ≍
      fundamentalChowClass (fieldChowSituation k') sX' b := by
    intro a b h
    subst h
    rfl
  rw [hsum X _ sX D (D ∪ D') rfl Finset.subset_union_left,
    hsum _ _ sX' D' (D ∪ D') rfl Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [rationalBaseChangeChowPullback_of_tmul, baseChangeChowPullback_fundamentalChowClass]
  exact of_tmul_eq_of_tmul_of_heq _ sX' (by simp) _
    (hfc (by simp))

end Stacks.Chow

end
