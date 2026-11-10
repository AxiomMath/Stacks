module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernPerfectPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionFactorSelfIntersection

/-!
# The self-intersection formula for a smooth divisor

Let data (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`),
with the data of Section 0FHA they define (`WeilChernData.toWeilData`: `γ` of Tag 0FIF and
`∫_X = λ` of (A6)), which satisfy axiom (A) by Lemma 0FIJ. Let `i : Y ⟶ X` be a closed immersion
of nonempty smooth projective schemes over `k`, equidimensional of dimensions `d` and `d + 1`.
Then for every `x ∈ H^p(Y)(q)`

  `i^*(i_*x) = i^*γ([Y]) ∪ x`   in   `H^{p+2}(Y)(q+1)`,

`i_*` being the pushforward of Section 0FHA (the contragredient of `i^*` under the pairings of
(A)) and `[Y] ∈ CH^1(X)` the class of the closed subscheme `Y`. This is one of the inputs to the
proof that Tag 0FIT holds under (A1)–(A8) without (A9).

The proof goes through the class of the diagonal. Let `γ([Δ_X]) = ∑ e_t ⊗ f_t` by (A5). By (A6)
and Lemma 0FIJ, `a = ∑ λ_X(f_t ∪ a) e_t` for every `a ∈ H^*(X)`
(`Stacks.WeilCohomology.DiagonalExpansion.sum_trace_mul_smul`), so the trace equation of `i_*`
gives

  `i^*i_*x = ∑ λ_Y(i^*f_t ∪ x) i^*e_t`,

the contraction of `(i × i)^*γ([Δ_X]) = ∑ i^*e_t ⊗ i^*f_t` against `x`. On Chow groups
`(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y])`
(`Stacks.Chow.codimensionGysin_prodHom_diagonalClass_of_divisor`, the excess intersection formula
for the diagonal of `Y` on the divisor `1 × i`), so `γ`, being compatible with Gysin maps and
multiplicative, gives `(i × i)^*γ([Δ_X]) = γ([Δ_Y]) ∪ pr₂^*c` with `c = i^*γ([Y])`. Contracting
`γ([Δ_Y]) ∪ pr₂^*c = ∑ e'_s ⊗ f'_s c` against `x` gives `∑ λ_Y(f'_s ∪ c ∪ x) e'_s = c ∪ x`, by
(A6) and Lemma 0FIJ for `Y`.

Nothing here is registered: this is a helper of Section 45.14, not a tag.

## Main results

* `Stacks.WeilCohomology.WeilChernData.pull_prodMap_untwistClass_diagonalClass_of_divisor`:
  `(i × i)^*γ([Δ_X]) = γ([Δ_Y]) ∪ pr₂^*(i^*γ([Y]))`.
* `Stacks.WeilCohomology.WeilChernData.pullTw_pushforward_divisor`: `i^*i_*x = i^*γ([Y]) ∪ x`.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FIJ](https://stacks.math.columbia.edu/tag/0FIJ)
* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow TensorProduct

universe u w

namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **`(i × i)^*γ([Δ_X]) = γ([Δ_Y]) ∪ pr₂^*(i^*γ([Y]))`** for a closed immersion `i : Y ⟶ X` of
smooth projective schemes, equidimensional of dimensions `d` and `d + 1`, in coordinates
(`FirstChernClassData.untwistClass`, `FirstChernClassData.κ`): the Chow identity
`(i × i)^![Δ_X] = [Δ_Y] · pr₂^!(i^![Y])`
(`Stacks.Chow.codimensionGysin_prodHom_diagonalClass_of_divisor`), with `γ` compatible with Gysin
maps and multiplicative. -/
theorem pull_prodMap_untwistClass_diagonalClass_of_divisor
    {Y X : (SmoothProjectiveScheme k).FullSubcategory} (i : Y ⟶ X) [IsClosedImmersion i.hom.left]
    {d : ℕ} (hY : RelativeDimension Y.obj.hom d)
    (hX : RelativeDimension X.obj.hom (d + 1)) :
    𝔚.pull (prodMap i i)
        (𝔚.untwistClass X (d + 1) (𝔚.γ (prod X X) (d + 1) (diagonalClass X (d + 1)))) =
      𝔚.untwistClass Y d (𝔚.γ (prod Y Y) d (diagonalClass Y d)) *
        𝔚.pull (snd Y Y)
          (𝔚.pull i (𝔚.κ X 1 (𝔚.γ X 1 (closedSubschemeClass X.obj.hom i.hom.left 1)))) := by
  have hCH := codimensionGysin_prodHom_diagonalClass_of_divisor Y.obj.hom X.obj.hom i.hom.left
    (Over.w i.hom) hY hX
  have hgys : codimensionGysin (prod Y Y).obj.hom (prod X X).obj.hom (Over.w (prodMap i i).hom)
      (d + 1 : ℕ) (diagonalClass X (d + 1)) =
      codimensionIntersectionProduct k (prod Y Y).obj.hom d 1 (diagonalClass Y d)
        (codimensionGysin (prod Y Y).obj.hom Y.obj.hom (Over.w (snd Y Y).hom) 1
          (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
            (closedSubschemeClass X.obj.hom i.hom.left 1))) :=
    hCH
  have hmul : 𝔚.γ (prod Y Y) (d + 1) (codimensionIntersectionProduct k (prod Y Y).obj.hom d 1
      (diagonalClass Y d) (codimensionGysin (prod Y Y).obj.hom Y.obj.hom (Over.w (snd Y Y).hom) 1
        (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
          (closedSubschemeClass X.obj.hom i.hom.left 1)))) =
      tateCup 𝔚.finrank_tate (𝔚.cup (prod Y Y)) d 1 (d + 1 : ℕ) (by push_cast; ring)
        (𝔚.γ (prod Y Y) d (diagonalClass Y d))
        (𝔚.γ (prod Y Y) 1 (codimensionGysin (prod Y Y).obj.hom Y.obj.hom (Over.w (snd Y Y).hom) 1
          (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
            (closedSubschemeClass X.obj.hom i.hom.left 1)))) :=
    𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionIntersectionProduct
      𝔚.coproduct 𝔚.projectiveBundle (prod Y Y) d 1 _ _
  have hsnd : 𝔚.γ (prod Y Y) 1 (codimensionGysin (prod Y Y).obj.hom Y.obj.hom
      (Over.w (snd Y Y).hom) 1 (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
        (closedSubschemeClass X.obj.hom i.hom.left 1))) =
      𝔚.pullTw (snd Y Y) 1 (𝔚.pullTw i 1
        (𝔚.γ X 1 (closedSubschemeClass X.obj.hom i.hom.left 1))) := by
    have h1 : 𝔚.γ (prod Y Y) 1 (codimensionGysin (prod Y Y).obj.hom Y.obj.hom
        (Over.w (snd Y Y).hom) 1 (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
          (closedSubschemeClass X.obj.hom i.hom.left 1))) =
        𝔚.pullTw (snd Y Y) 1 (𝔚.γ Y 1 (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
          (closedSubschemeClass X.obj.hom i.hom.left 1))) :=
      𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin (snd Y Y) 1 _
    have h2 : 𝔚.γ Y 1 (codimensionGysin Y.obj.hom X.obj.hom (Over.w i.hom) 1
          (closedSubschemeClass X.obj.hom i.hom.left 1)) =
        𝔚.pullTw i 1 (𝔚.γ X 1 (closedSubschemeClass X.obj.hom i.hom.left 1)) :=
      𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin i 1 _
    rw [h1, h2]
  rw [untwistClass, untwistClass, ← κ_pullTw,
    ← 𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin (prodMap i i), hgys,
    hmul, κ_tateCup, hsnd, κ_pullTw, κ_pullTw]

/-- **The self-intersection formula for a smooth divisor**, `i^*(i_*x) = i^*γ([Y]) ∪ x`. Let data
(D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), with the data
of Section 0FHA they define (`WeilChernData.toWeilData`), and let `i : Y ⟶ X` be a closed
immersion of nonempty smooth projective schemes over `k`, equidimensional of dimensions `d` and
`d + 1`. Then for `x ∈ H^p(Y)(q)`

  `i^*(i_*x) = i^*γ([Y]) ∪ x`   in   `H^{p+2}(Y)(q+1)`,

for `i_*` the pushforward of Section 0FHA formed with the perfect pairing of Lemma 0FIJ and
`[Y] ∈ CH^1(X)` the class of the closed subscheme `Y`.

Write `γ([Δ_X]) = ∑ e_t ⊗ f_t` (A5). By (A6) and Lemma 0FIJ, `i_*x = ∑ λ_X(f_t ∪ i_*x) e_t =
∑ λ_Y(i^*f_t ∪ x) e_t` (the trace equation of `i_*`), so `i^*i_*x` is the contraction of
`(i × i)^*γ([Δ_X]) = ∑ i^*e_t ⊗ i^*f_t` against `x`. By
`pull_prodMap_untwistClass_diagonalClass_of_divisor` this class is
`γ([Δ_Y]) ∪ pr₂^*c = ∑ e'_s ⊗ f'_s c`, `c = i^*γ([Y])`, by the Künneth formula (A5), and its
contraction against `x` is `∑ λ_Y(f'_s ∪ c ∪ x) e'_s = c ∪ x` by (A6) and Lemma 0FIJ for `Y`. -/
theorem pullTw_pushforward_divisor {Y X : (SmoothProjectiveScheme k).FullSubcategory} (i : Y ⟶ X)
    [IsClosedImmersion i.hom.left] {d : ℕ} (hY : IsNonemptyEquidimensional Y d)
    (hX : IsNonemptyEquidimensional X (d + 1)) (p q : ℤ) (x : 𝔚.toWeilData.Tw Y p q) :
    𝔚.toWeilData.pullTw i (p + 2 * 1) (q + 1)
        (𝔚.toWeilData.pushforward 𝔚.perfectPairing i hY hX p q (p + 2 * 1) (q + 1)
          (by push_cast; ring) (by push_cast; ring) x) =
      𝔚.toWeilData.cupTw Y (2 * 1) p (p + 2 * 1) (by ring) 1 q (q + 1) (by ring)
        (𝔚.toWeilData.pullTw i (2 * 1) 1
          (𝔚.toWeilData.cycleClass X 1 (closedSubschemeClass X.obj.hom i.hom.left 1))) x := by
  -- the diagonal data of `X` and of `Y` (A5, A6, Lemma 0FIJ)
  have hD : ∀ (Z : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
      (hZ : IsNonemptyEquidimensional Z n),
      ∃ l, DiagonalExpansion.DiagonalData (𝔚.grade Z) (𝔚.grade (prod Z Z)) (𝔚.pull (fst Z Z))
        (𝔚.pull (snd Z Z)) (2 * (n : ℤ)) (𝔚.untwistClass Z n (𝔚.γ (prod Z Z) n (diagonalClass Z n)))
        (𝔚.untwistTrace Z n (𝔚.toWeilData.trace Z n hZ)) l := fun Z n hZ ↦
    𝔚.exists_diagonalData 𝔚.kunneth Z n _
      (𝔚.untwistClass_mem_of_mem_range Z _
        (𝔚.isCohomologicalChernCharacter.codimensionCycleClass_mem 𝔚.coproduct
          𝔚.projectiveBundle _ _ _)) _
      (𝔚.isCohomologicalChernCharacter.traceContract_toWeilData_trace 𝔚.coproduct
        𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace Z n hZ)
      (𝔚.isCohomologicalChernCharacter.key_diagonalClass 𝔚.coproduct 𝔚.projectiveBundle
        𝔚.divisor 𝔚.blowup Z n hZ)
  obtain ⟨lX, hDX⟩ := hD X (d + 1) hX
  obtain ⟨lY, hDY⟩ := hD Y d hY
  -- in coordinates
  set xu : 𝔚.H Y := (𝔚.toWeilData.twCoord Y p q x).1 with hxu
  set zu : 𝔚.H X := (𝔚.toWeilData.twCoord X (p + 2 * 1) (q + 1)
    (𝔚.toWeilData.pushforward 𝔚.perfectPairing i hY hX p q (p + 2 * 1) (q + 1)
      (by push_cast; ring) (by push_cast; ring) x)).1 with hzu
  set c : 𝔚.H Y :=
    𝔚.pull i (𝔚.κ X 1 (𝔚.γ X 1 (closedSubschemeClass X.obj.hom i.hom.left 1))) with hc
  set lamY := 𝔚.untwistTrace Y d (𝔚.toWeilData.trace Y d hY) with hlamY
  have hcY : (𝔚.toWeilData.twCoord X (2 * 1) 1
      (𝔚.toWeilData.cycleClass X 1 (closedSubschemeClass X.obj.hom i.hom.left 1))).1 =
      𝔚.κ X 1 (𝔚.γ X 1 (closedSubschemeClass X.obj.hom i.hom.left 1)) :=
    𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass 𝔚.coproduct
      𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X 1 _
  -- the trace equation of `i_*` in coordinates: `λ_X(b ∪ i_*x) = λ_Y(i^*b ∪ x)` for every `b`
  have hpf : ∀ b : 𝔚.H X, 𝔚.untwistTrace X (d + 1) (𝔚.toWeilData.trace X (d + 1) hX) (b * zu) =
      lamY (𝔚.pull i b * xu) := by
    intro b
    induction b using DirectSum.Decomposition.inductionOn (𝔚.grade X) with
    | zero => simp
    | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul, map_add]
    | @homogeneous j b =>
      obtain ⟨b, hb⟩ := b
      by_cases hj : j = 2 * d - p
      · subst hj
        set b' := (𝔚.toWeilData.twCoord X (2 * d - p) (d - q)).symm ⟨b, hb⟩ with hb'
        have key := WeilData.pushforward_trace' 𝔚.perfectPairing i hY hX p q (p + 2 * 1) (q + 1)
          (by push_cast; ring) (by push_cast; ring) (2 * d - p) (d - q) (by ring) (by ring)
          (by push_cast; ring) (by push_cast; ring) b' x
        rw [WeilData.pairingTw_apply, WeilData.pairingTw_apply] at key
        have hcb : (𝔚.toWeilData.twCoord X (2 * d - p) (d - q) b').1 = b := by
          rw [hb', LinearEquiv.apply_symm_apply]
        have hX' : (𝔚.toWeilData.twCoord X (2 * ((d + 1 : ℕ) : ℤ)) (d + 1 : ℕ)
            (𝔚.toWeilData.cupTw X (2 * d - p) (p + 2 * 1) (2 * ((d + 1 : ℕ) : ℤ))
              (by push_cast; ring) (d - q) (q + 1) (d + 1 : ℕ) (by push_cast; ring) b'
              (𝔚.toWeilData.pushforward 𝔚.perfectPairing i hY hX p q (p + 2 * 1) (q + 1)
                (by push_cast; ring) (by push_cast; ring) x))).1 = b * zu := by
          rw [WeilData.twCoord_cupTw, WeilData.coe_cup, hcb]
          rfl
        have hY' : (𝔚.toWeilData.twCoord Y (2 * (d : ℤ)) d
            (𝔚.toWeilData.cupTw Y (2 * d - p) p (2 * d) (by ring) (d - q) q d (by ring)
              (𝔚.toWeilData.pullTw i (2 * d - p) (d - q) b') x)).1 = 𝔚.pull i b * xu := by
          rw [WeilData.twCoord_cupTw, WeilData.coe_cup, WeilData.twCoord_pullTw,
            WeilData.coe_pullDeg, hcb]
          rfl
        rw [← hX', ← hY']
        exact (𝔚.untwistTrace_twCoord X (d + 1) _ _).trans
          (key.symm.trans (𝔚.untwistTrace_twCoord Y d _ _).symm)
      · have hbz := SetLike.GradedMul.mul_mem hb (𝔚.toWeilData.twCoord X (p + 2 * 1) (q + 1)
          (𝔚.toWeilData.pushforward 𝔚.perfectPairing i hY hX p q (p + 2 * 1) (q + 1)
            (by push_cast; ring) (by push_cast; ring) x)).2
        have hbx := SetLike.GradedMul.mul_mem (𝔚.pull_grade i j b hb)
          (𝔚.toWeilData.twCoord Y p q x).2
        exact (𝔚.untwistTrace_eq_zero X (d + 1) _ _ (by push_cast; omega) _ hbz).trans
          (𝔚.untwistTrace_eq_zero Y d _ _ (by omega) _ hbx).symm
  apply (𝔚.toWeilData.twCoord Y (p + 2 * 1) (q + 1)).injective
  apply Subtype.ext
  rw [WeilData.twCoord_pullTw, WeilData.twCoord_cupTw, WeilData.twCoord_pullTw,
    WeilData.coe_pullDeg, WeilData.coe_cup, WeilData.coe_pullDeg, hcY]
  change 𝔚.pull i zu = c * xu
  -- `i_*x = ∑ λ_Y(i^*f_t ∪ x) e_t`, so `i^*i_*x = ∑ λ_Y(i^*f_t ∪ x) i^*e_t`
  have hpz : 𝔚.pull i zu =
      (lX.map fun t => lamY (𝔚.pull i t.2.2 * xu) • 𝔚.pull i t.2.1).sum := by
    conv_lhs => rw [← DiagonalExpansion.sum_trace_mul_smul hDX zu]
    rw [map_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_apply, map_smul]
    rw [hpf]
  -- the contraction against `x`
  set Φ : 𝔚.H Y ⊗[F] 𝔚.H Y →ₗ[F] 𝔚.H Y :=
    DiagonalExpansion.contractRight (lamY ∘ₗ LinearMap.mulRight F xu) with hΦ
  have hΦl : ∀ l : List (ℤ × 𝔚.H Y × 𝔚.H Y), Φ (DiagonalExpansion.tensorSum l) =
      (l.map fun t => lamY (t.2.2 * xu) • t.2.1).sum := by
    intro l
    rw [DiagonalExpansion.map_tensorSum]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    simp [hΦ]
  have hmapl : TensorProduct.map (𝔚.pull i).toLinearMap (𝔚.pull i).toLinearMap
      (DiagonalExpansion.tensorSum lX) =
      DiagonalExpansion.tensorSum (lX.map fun t => (t.1, 𝔚.pull i t.2.1, 𝔚.pull i t.2.2)) := by
    rw [DiagonalExpansion.map_tensorSum, DiagonalExpansion.tensorSum, List.map_map]
    rfl
  -- `(i × i)^*γ([Δ_X]) = γ([Δ_Y]) ∪ pr₂^*c` gives `∑ i^*e_t ⊗ i^*f_t = ∑ e'_s ⊗ f'_s c`
  have hT : TensorProduct.map (𝔚.pull i).toLinearMap (𝔚.pull i).toLinearMap
      (DiagonalExpansion.tensorSum lX) =
      DiagonalExpansion.tensorSum (lY.map fun t => (t.1, t.2.1, t.2.2 * c)) := by
    apply hDY.injective
    rw [DiagonalExpansion.kunneth_tensorSum_mul_right, hDY.expansion]
    have h1 := 𝔚.pull_prodMap_kunnethMap i i (DiagonalExpansion.tensorSum lX)
    have h2 : 𝔚.kunnethMap X X (DiagonalExpansion.tensorSum lX) =
        𝔚.untwistClass X (d + 1) (𝔚.γ (prod X X) (d + 1) (diagonalClass X (d + 1))) :=
      hDX.expansion
    rw [h2, 𝔚.pull_prodMap_untwistClass_diagonalClass_of_divisor i hY.relativeDimension
      hX.relativeDimension] at h1
    exact h1.symm
  calc 𝔚.pull i zu = Φ (TensorProduct.map (𝔚.pull i).toLinearMap (𝔚.pull i).toLinearMap
        (DiagonalExpansion.tensorSum lX)) := by
        rw [hmapl, hΦl, hpz, List.map_map]
        rfl
    _ = (lY.map fun t => lamY (t.2.2 * (c * xu)) • t.2.1).sum := by
        rw [hT, hΦl, List.map_map]
        refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
        simp only [Function.comp_apply, mul_assoc]
    _ = c * xu := DiagonalExpansion.sum_trace_mul_smul hDY (c * xu)

end Stacks.WeilCohomology.WeilChernData

end
