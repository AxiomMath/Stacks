module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalDivisorTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalThetaPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExtendableConormalCodimensionTwo

/-!
# Tag 0FIT under (A1)–(A8), and (A9) as a consequence

This file assembles the proof of [Stacks, Tag 0FIT] under (A1)–(A8), exactly as stated, without
(A9). The source's proof cites (A9) for "`j_*(1) = γ([E])`", where `E` is the exceptional divisor
of the blowing up of `X` in the centre `Z`. Here that step comes instead from
`WeilChernData.cycleClass_exceptional_eq_pushforward_unitTw_of_lt`, which holds when `Z` has
codimension `≥ 2`. Codimension `1` is never needed, because the reduction of Tag 0FIR calls the
key case only in codimension `0` and in codimension `≥ 2`
(`WeilData.pushforward_unitTw_eq_cycleClass_of_extendable_of_ne_one`).

As a consequence, axiom (A9) follows from (A1)–(A8): for a smooth divisor `i : Y ⟶ X`,
`i_*1 = γ([Y]) = c₁^H(𝒪_X(Y))`, which is (A9) read through the trace equation of the pushforward
(`divisorTrace_of_globalSections`). Tag 0FIT is registered on
`cycleClassPushforward_of_globalSections`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.pushforward_unitTw_eq_cycleClass_of_lt_of_globalSections`:
  `i_*1 = γ([Z])` in codimension `≥ 2`, conormal class extendable.
* `Stacks.WeilCohomology.WeilChernData.pushforward_unitTw_eq_cycleClass_of_globalSections`:
  `i_*1 = γ([Z])` for every closed immersion.
* `Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_globalSections`:
  **Tag 0FIT**, `γ` commutes with pushforward.
* `Stacks.WeilCohomology.WeilChernData.divisorTrace_of_globalSections`: (A9) follows
  from (A1)–(A8).

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIP](https://stacks.math.columbia.edu/tag/0FIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero
  Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **`i_*1 = γ([Z])` in codimension `≥ 2`, through the blowing up in `Z`, under (A8).** This is
the computation of the proof of Tag 0FIT (`WeilData.pushforward_unitTw_eq_of_square`), with the
step "`j_*(1) = γ([E])` by (A9)" replaced by
`cycleClass_exceptional_eq_pushforward_unitTw_of_lt`. -/
theorem pushforward_unitTw_eq_cycleClass_of_lt_of_globalSections (hA8 : 𝔚.GlobalSections)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {m e : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X (m + 1))
    (he : e + 1 < m + 1) (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * ((m + 1 - e : ℕ) : ℤ))
        ((m + 1 - e : ℕ) : ℤ) (by omega) (by omega) (𝔚.toWeilData.unitTw Z 0 0 rfl) =
      𝔚.toWeilData.cycleClass X ((m + 1 - e : ℕ) : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left ((m + 1 - e : ℕ) : ℤ)) := by
  have := hZ.nonempty
  have he' : e < m + 1 := by omega
  have hnd := isNowhereDense_range_of_relativeDimension i hX.relativeDimension
    hZ.relativeDimension he'
  have hr := coheight_eq_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
  have hr0 : 0 < m + 1 - e := by omega
  have hE := isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension hnd
  have hX' := isNonemptyEquidimensional_blowupObj i hX hnd
  have hrel := codimensionGysin_closedSubschemeClass_heq_blowupTheta_of_codimension i hr hr0 α hα
  refine WeilData.pushforward_unitTw_eq_of_square 𝔚.perfectPairing i (exceptionalProj i)
    (exceptionalHom i) (blowupHom i) (exceptionalHom_comp_blowupHom i).symm hr0 (by omega) hZ hE
    hX hX' _ _ _ (𝔚.pushforward_pullTw_cycleClass_blowupTheta i hZ hX he' α hα) ?_
    (𝔚.cupTw_cycleClass_eq_pullTw_of_heq (blowupHom i) hr0 _ _ _ hrel) ?_
  · exact (𝔚.cycleClass_exceptional_eq_pushforward_unitTw_of_lt hA8 i hZ hX he).symm
  · exact 𝔚.toFirstChernClassData.pushforward_unitTw_blowupHom 𝔚.isCohomologicalChernCharacter
      𝔚.coproduct 𝔚.projectiveBundle 𝔚.divisor 𝔚.kunneth 𝔚.trace 𝔚.blowup hA8 i hnd hX

/-- **`i_*1 = γ([Z])` for a closed immersion of codimension `c ≠ 1` with extendable conormal
class**, under (A8). In codimension `0` the immersion is open and closed; in codimension `≥ 2`
this is `pushforward_unitTw_eq_cycleClass_of_lt_of_globalSections`. -/
theorem pushforward_unitTw_eq_cycleClass_of_conormal_of_ne_one (hA8 : 𝔚.GlobalSections)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e) (hc1 : c ≠ 1)
    (hK : ∃ β : VectorBundleKZero X.obj.left, pullbackRingHom i.hom.left β =
      classOf Z.obj.left (Stacks.Conormal.conormalSheaf i.hom.left)) :
    𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * c) c (by omega) (by omega)
        (𝔚.toWeilData.unitTw Z 0 0 rfl) =
      𝔚.toWeilData.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c) := by
  have := hZ.nonempty
  have hle := le_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · obtain rfl : c = 0 := by omega
    have := isOpenImmersion_of_coheight_eq_zero i fun z hz ↦ by
      simpa using coheight_eq_of_relativeDimension i hX.relativeDimension hZ.relativeDimension z hz
    exact 𝔚.pushforward_unitTw_eq_cycleClass_of_isOpenImmersion i hZ hX
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain rfl : c = ((m + 1 - e : ℕ) : ℤ) := by omega
    obtain ⟨β, hβ⟩ := hK
    exact 𝔚.pushforward_unitTw_eq_cycleClass_of_lt_of_globalSections hA8 i hZ hX
      (by omega) β (by rwa [VectorBundleKZero.pullback_apply_eq_pullbackRingHom])

/-- **`i_*1 = γ([Z])` for every closed immersion** `i : Z ⟶ X` of nonempty smooth projective
equidimensional schemes over `k` (the hypothesis of Lemma 0FIP), under (A1)–(A8): Lemma 0FIR
away from codimension one (`WeilData.pushforward_unitTw_eq_cycleClass_of_extendable_of_ne_one`)
applied to `pushforward_unitTw_eq_cycleClass_of_conormal_of_ne_one`, with Lemma 0FIQ
(`pushforwardCompatible_fst_grassmannian`). -/
theorem pushforward_unitTw_eq_cycleClass_of_globalSections (hA8 : 𝔚.GlobalSections)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e) :
    𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * c) c (by omega) (by omega)
        (𝔚.toWeilData.unitTw Z 0 0 rfl) =
      𝔚.toWeilData.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c) :=
  𝔚.toWeilData.pushforward_unitTw_eq_cycleClass_of_extendable_of_ne_one 𝔚.perfectPairing
    (fun X _ _ _ hln _ d' hX hP p q hq α ↦
      𝔚.pushforwardCompatible_fst_grassmannian hln X d' _ hP hX p q hq α)
    (fun i _ _ _ hZ hX c hc hc1 hK ↦
      𝔚.pushforward_unitTw_eq_cycleClass_of_conormal_of_ne_one hA8 i hZ hX c hc hc1 hK)
    i hZ hX c hc

/-- **Tag 0FIT**: for data (D0), (D1), (D2') satisfying axioms (A1)–(A8) (a `WeilChernData`,
which bundles (A1)–(A7), and (A8) `GlobalSections`), the cycle class map `γ` commutes with
pushforward: axiom (C)(b) of Section 0FHA for `WeilChernData.toWeilData`, i.e.
`γ(f_*α) = f_*γ(α)` for every morphism `f : X ⟶ Y` of nonempty equidimensional smooth projective
schemes over `k` and every `α ∈ CH^p(X)`. This is Lemma 0FIP's reduction
(`cycleClassPushforward_of_grassmannian`) applied to
`pushforward_unitTw_eq_cycleClass_of_globalSections`. The source's proof cites (A9) for
`j_*1 = γ([E])`; here that step is `cycleClass_exceptional_eq_pushforward_unitTw_of_lt`, proved
from (A1)–(A8). -/
@[stacks 0FIT "the whole lemma, under exactly (A1)-(A8): WeilChernData bundles (A1)-(A7) and the \
  only hypothesis is (A8) GlobalSections; conclusion: gamma commutes with pushforward \
  (axiom (C)(b) for toWeilData) for every morphism of nonempty equidimensional smooth \
  projective schemes; nothing assumed, (A9) is not used"]
theorem cycleClassPushforward_of_globalSections (hA8 : 𝔚.GlobalSections) :
    𝔚.toWeilData.CycleClassPushforward 𝔚.perfectPairing :=
  cycleClassPushforward_of_grassmannian
    (fun X _ _ _ hln _ d' hX hP p q hq α ↦
      𝔚.pushforwardCompatible_fst_grassmannian hln X d' _ hP hX p q hq α)
    fun i _ _ _ hZ hX c hc ↦
      𝔚.pushforward_unitTw_eq_cycleClass_of_globalSections hA8 i hZ hX c hc

/-- A linear form normalised by the diagonal class, as in (A9), is the trace map (Remark 0FIK). -/
private theorem eq_trace_of_traceContract
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) (hX : IsNonemptyEquidimensional X d)
    (lam : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔚.traceContract 𝔚.kunneth X d lam
      (𝔚.γ (prod X X) d (diagonalClass X d)) = 1) :
    lam = 𝔚.toWeilData.trace X d hX :=
  𝔚.isCohomologicalChernCharacter.trace_unique 𝔚.coproduct 𝔚.projectiveBundle 𝔚.divisor
    𝔚.kunneth 𝔚.blowup X d hX _ _ hlam
    (𝔚.isCohomologicalChernCharacter.traceContract_toWeilData_trace 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X d hX)

/-- **(A9) follows from (A1)–(A8).** For a smooth
effective Cartier divisor `i : Y ⟶ X`, `i_*1 = γ([Y]) = c₁^H(𝒪_X(Y))`
(`pushforward_unitTw_eq_cycleClass_of_globalSections`). Read through the trace equation of
the pushforward, this is `λ_Y(i^*a) = λ_X(a ∪ c₁^H(𝒪_X(Y)))`. The maps `λ_X`, `λ_Y` of (A9) are the
trace maps by the uniqueness of Remark 0FIK (`trace_unique`). -/
theorem divisorTrace_of_globalSections (hA8 : 𝔚.GlobalSections) : 𝔚.DivisorTrace := by
  intro X Y d hX hY i D hD e he lamX lamY hlamX hlamY a ha
  have := hD
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor (show X.obj.left.IdealSheafData from D) :=
    hD
  set W := 𝔚.toWeilData with hW
  -- the maps of (A9) are the trace maps (Remark 0FIK)
  obtain rfl := 𝔚.eq_trace_of_traceContract X (d + 1) hX lamX hlamX
  obtain rfl := 𝔚.eq_trace_of_traceContract Y d hY lamY hlamY
  have he' : e.hom ≫ D.subschemeι = i.hom.left := he
  have : IsClosedImmersion i.hom.left := by rw [← he']; infer_instance
  -- `i_*1 = γ([Y])`
  have key := 𝔚.pushforward_unitTw_eq_cycleClass_of_globalSections hA8 i hY hX 1
    (by push_cast; ring)
  have hcl : closedSubschemeClass X.obj.hom i.hom.left 1 =
      closedSubschemeClass X.obj.hom D.subschemeι 1 := by
    funext e'
    rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
      cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) _ i.hom.left
        D.subschemeι e he']
  have hc : (W.twCoord X (2 * 1) 1 (W.cycleClass X 1
      (closedSubschemeClass X.obj.hom i.hom.left 1))).1 =
      𝔚.κ X 1 (𝔚.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.isInvertible_divisorSheaf D))) := by
    refine (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass
      𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X 1 _).trans (congrArg (𝔚.κ X 1) ?_)
    exact (congrArg (𝔚.γ X 1) hcl).trans
      (𝔚.isCohomologicalChernCharacter.codimensionCycleClass_divisor 𝔚.coproduct
        𝔚.projectiveBundle X D)
  set b : W.Tw X (2 * (d : ℤ)) d := (W.twCoord X (2 * (d : ℤ)) d).symm ⟨a, ha⟩ with hbdef
  have hb : (W.twCoord X (2 * (d : ℤ)) d b).1 = a := by
    rw [hbdef, LinearEquiv.apply_symm_apply]
  have hpull : (W.twCoord Y (2 * (d : ℤ)) d (W.pullTw i _ _ b)).1 = 𝔚.pull i a := by
    rw [WeilData.twCoord_pullTw, WeilData.coe_pullDeg, hb]
    rfl
  have hL : 𝔚.untwistTrace Y d (W.trace Y d hY) (𝔚.pull i a) =
      W.pairingTw Y d hY (2 * (d : ℤ)) 0 (by ring) d 0 (by ring) (W.pullTw i _ _ b)
        (W.unitTw Y 0 0 rfl) := by
    rw [WeilData.pairingTw_apply, W.cupTw_eq_self_of_coe_twCoord_eq_one_right Y _ _ _ _ _ _ _ _
      (W.coe_twCoord_unitTw Y _ _ rfl), ← hpull]
    exact 𝔚.untwistTrace_twCoord Y d _ _
  have hR : 𝔚.untwistTrace X (d + 1) (W.trace X (d + 1) hX)
        (a * 𝔚.κ X 1 (𝔚.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
          (Stacks.Divisors.isInvertible_divisorSheaf D)))) =
      W.pairingTw X (d + 1) hX (2 * (d : ℤ)) (2 * 1) (by push_cast; ring) d 1
        (by push_cast; ring) b
        (W.cycleClass X 1 (closedSubschemeClass X.obj.hom i.hom.left 1)) := by
    rw [WeilData.pairingTw_apply]
    refine Eq.trans (congrArg _ ?_) (𝔚.untwistTrace_twCoord X (d + 1) _ _)
    rw [WeilData.twCoord_cupTw, WeilData.coe_cup, hb, hc]
    rfl
  rw [hL, hR, ← key]
  exact W.pushforward_trace' 𝔚.perfectPairing i hY hX 0 0 (2 * 1) 1 (by push_cast; ring)
    (by push_cast; ring) (2 * (d : ℤ)) d (by ring) (by ring) (by push_cast; ring)
    (by push_cast; ring) b (W.unitTw Y 0 0 rfl)

end Stacks.WeilCohomology.WeilChernData

end
