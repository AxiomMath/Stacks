module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Compat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Injective

/-!
# The top case of Stacks 02TW for a locally projective tower

Let `π : P ⟶ X` be flat and proper, a projective tower of fibre dimension `n` locally on `X`
(`Stacks.Chow.IsLocallyProjectiveTower`), with twist `L`. Then for every class `α` on `X`,

  `π_*(c₁(L)^n ∩ π^*α) = α`,

the top case of [Stacks, Tag 02TW], and consequently the map of [Stacks, Tag 02TX] is injective.

## Main results

* `Stacks.Chow.rationalEquivalences_eq_bot_of_relativeDimension_le` — on a scheme all of whose
  points have delta-dimension at most `k`, no nonzero `k`-cycle is rationally equivalent to zero.
* `Stacks.Chow.IsLocallyProjectiveTower.bundleProjection_self` — **the top case of Stacks
  02TW.**
* `Stacks.Chow.IsLocallyProjectiveTower.bundleMap_injective` — **Stacks 02TX, injectivity.**

## Implementation notes

The source proves the top case for `α = [Z]` by computing on a dense open of `Z` and "omits the
verification that these arguments imply the result for a general cycle". The verification is
done here as follows. A representative `a` of `α` is pushed forward from the reduced closed
subscheme `T` on the union of the closures of the points of its support, which has
delta-dimension at most `k`; the operation commutes with that pushforward. On `T` there are no
rational equivalences in degree `k`, so a class is a cycle, and a cycle on `T` vanishes as soon as
its restrictions to an open cover vanish. On a member of the cover over which `π` is a projective
tower, `Stacks.Chow.IsProjectiveTower.bundleProjection_self` applies.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **No rational equivalences in the top degree.** If every point of `T` has delta-dimension at
most `k`, then `T` has no integral closed subscheme of delta-dimension `k + 1`, so the only
`k`-cycle rationally equivalent to zero is zero. -/
theorem rationalEquivalences_eq_bot_of_relativeDimension_le (C : ChowSituation.{u})
    {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ)
    (h : ∀ t : T, relativeDimension C.dimensionFunction sT t ≤ k) :
    rationalEquivalences C sT k = ⊥ := by
  refine le_antisymm (fun α hα ↦ ?_) bot_le
  obtain ⟨J, W, hW, hDim, -, g, hcoeff⟩ := hα
  have hempty : IsEmpty J := by
    refine ⟨fun j ↦ ?_⟩
    have := hW j
    have hgen := schemeDeltaDimension_eq_genericPoint C ((W j).subschemeι ≫ sT)
    rw [hDim j, relativeDimension_comp_closedImmersion] at hgen
    have hle := h ((W j).subschemeι (genericPoint (W j).subscheme))
    have hcast := WithBotTop.coe_injective hgen
    omega
  refine AddSubgroup.mem_bot.mpr (Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_))
  rw [hcoeff x]
  exact finsum_of_isEmpty _

/-- **The top case of Stacks 02TW for a locally projective tower.** For `π : P ⟶ X` flat and
proper, a projective tower of fibre dimension `n` with twist `L` locally on `X`, and every class
`α` on `X`,

  `π_*(c₁(L)^n ∩ π^*α) = α`. -/
theorem IsLocallyProjectiveTower.bundleProjection_self (C : ChowSituation.{u}) {n : ℕ}
    {P X : Scheme.{u}} {π : P ⟶ X} {L : P.Modules} (h : IsLocallyProjectiveTower n π L)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (hsP : π ≫ sX = sP)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [Flat π] [IsProper π]
    (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ) (β : chowGroup C sX k) :
    bundleProjection C sX sP π hsP n hπ (invCap C sP L) n k k (by ring) β = β := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  -- the reduced closed subscheme on the support of `a`
  have hlf := locallyFinite_closure_support a.1.locallyFiniteSupport
  set Z : Closeds X := ⟨⋃ x : Function.support a.1, closure {(x : X)},
    hlf.isClosed_iUnion fun _ ↦ isClosed_closure⟩ with hZ
  set W := Scheme.IdealSheafData.vanishingIdeal Z with hW
  have hWsupp : (W.support : Set X) = ⋃ x : Function.support a.1, closure {(x : X)} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  set V : X.Opens := ⟨(W.support : Set X)ᶜ, W.support.isClosed.isOpen_compl⟩ with hV
  have hcompl : Set.range W.subschemeι.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι, W.range_subschemeι]
    simp [hV]
  have hres : cycleGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k a = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
    rw [cycleGroupRestrict_apply]
    by_contra hne
    have hmem : V.ι.base v ∈ (W.support : Set X) := by
      rw [hWsupp]
      exact Set.mem_iUnion.2 ⟨⟨_, hne⟩, subset_closure rfl⟩
    have hv : V.ι.base v ∈ Set.range V.ι.base := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at hv
    exact hv hmem
  obtain ⟨d, hd⟩ := (cycleGroupRestrict_eq_zero_iff C sX (W.subschemeι ≫ sX) (V.ι ≫ sX)
    W.subschemeι rfl V.ι rfl hcompl k a).1 hres
  -- every point of `T` has delta-dimension at most `k`
  have hdimT : ∀ t : W.subscheme,
      relativeDimension C.dimensionFunction (W.subschemeι ≫ sX) t ≤ k := by
    intro t
    rw [relativeDimension_comp_closedImmersion]
    have hmem : W.subschemeι t ∈ (W.support : Set X) := by
      rw [← W.range_subschemeι]; exact ⟨t, rfl⟩
    rw [hWsupp] at hmem
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hmem
    exact (relativeDimension_le_of_specializes C sX (specializes_iff_mem_closure.2 hx)).trans
      (le_of_eq ((mem_cyclesOfDimension_iff_forall_point C sX k a.1).1 a.2 _ x.2))
  -- the computation on `T`
  let := locallyOfFiniteType_comapRestrict W π
  let := flat_comapRestrict W π
  let : IsProper (Stacks.Chow.comapRestrict W π) :=
    MorphismProperty.of_isPullback (isPullback_comapRestrict W π) inferInstance
  let := isInvertible_presheaf_modulePullback L (W.comap π).subschemeι
  set πT := Stacks.Chow.comapRestrict W π with hπT
  set LT := (Scheme.Modules.pullback (W.comap π).subschemeι).obj L with hLT
  set sT := W.subschemeι ≫ sX with hsT
  set sPT := (W.comap π).subschemeι ≫ sP with hsPT
  have hbaseT : πT ≫ sT = sPT := comapRestrict_comp_base C sP sX π hsP W
  have hπT : AlgebraicGeometry.RelativeDimension πT n := relativeDimension_comapRestrict W π hπ
  have hlocT : IsLocallyProjectiveTower n πT LT := h.comapRestrict W
  have hTeq : bundleProjection C sT sPT πT hbaseT n hπT (invCap C sPT LT) n k k (by ring)
      (QuotientAddGroup.mk' _ d) = QuotientAddGroup.mk' _ d := by
    rw [← sub_eq_zero]
    obtain ⟨e, he⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sT k)
      (bundleProjection C sT sPT πT hbaseT n hπT (invCap C sPT LT) n k k (by ring)
        (QuotientAddGroup.mk' _ d) - QuotientAddGroup.mk' _ d)
    rw [← he]
    suffices hez : e = 0 by rw [hez, map_zero]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun t ↦ ?_)
    by_cases hdt : relativeDimension C.dimensionFunction sT t = k
    · obtain ⟨V', htV', htower⟩ := hlocT t
      let := isInvertible_presheaf_modulePullback LT (πT ⁻¹ᵁ V').ι
      have hz : chowGroupRestrict C sT (V'.ι ≫ sT) V'.ι rfl k
          (QuotientAddGroup.mk' _ e) = 0 := by
        rw [he, map_sub, chowGroupRestrict_bundleProjection C sT sPT πT hbaseT n hπT V' LT n k k,
          htower.bundleProjection_self C (V'.ι ≫ sT) _
            (morphismRestrict_comp_base C sT sPT πT hbaseT V')
            (relativeDimension_morphismRestrict πT n hπT V') k, sub_self]
      rw [chowGroupRestrict_mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
        rationalEquivalences_eq_bot_of_relativeDimension_le C (V'.ι ≫ sT) k (fun v ↦ by
          rw [relativeDimension_comp_isOpenImmersion]; exact hdimT _)] at hz
      have h0 := congrArg (fun c : CycleGroup C (V'.ι ≫ sT) k ↦ c.1 ⟨t, htV'⟩)
        (AddSubgroup.mem_bot.1 hz)
      exact h0
    · by_contra hne
      exact hdt ((mem_cyclesOfDimension_iff_forall_point C sT k e.1).1 e.2 t hne)
  -- push the identity on `T` forward to `X`
  rw [← hd, ← properChowPushforward_mk C _ sX W.subschemeι rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k),
    ← properChowPushforward_bundleProjection_comap C sX sP π hsP n hπ W L n k k (by ring),
    hTeq]

/-- **Stacks 02TX, injectivity, for a locally projective tower.** -/
theorem IsLocallyProjectiveTower.bundleMap_injective (C : ChowSituation.{u}) {n : ℕ}
    {P X : Scheme.{u}} {π : P ⟶ X} {L : P.Modules} (h : IsLocallyProjectiveTower n π L)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (hsP : π ≫ sX = sP)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [Flat π] [IsProper π]
    (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ) :
    Function.Injective (bundleMap C sX sP π hsP n hπ (invCap C sP L) k) :=
  Stacks.Chow.bundleMap_injective C sX sP π hsP n hπ (invCap C sP L)
    (fun k α ↦ h.bundleProjection_self C sX sP hsP hπ k α) k

end Stacks.Chow

end
