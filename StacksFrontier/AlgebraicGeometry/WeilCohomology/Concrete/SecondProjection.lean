module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationTrace

/-!
# Pushforward of an exterior product along the second projection

Let `H^*` be data (D0), (D1), (D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth
projective schemes over a field `k` (`Stacks.WeilCohomology.WeilData`), satisfying axioms (A)
and (B). Let `X` and `Y` be nonempty smooth projective schemes over `k`, equidimensional of
dimensions `d` and `e`. Stacks 0FHC says that

`pr_{2, *} : H^*(X × Y)(d + e) ⟶ H^*(Y)(e)`

sends `a ⊗ b = pr₁^*a ∪ pr₂^*b` to `(∫_X a) b`, where `∫_X`, a map on `H^{2d}(X)(d)`, is read as
zero on the other degrees.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_snd_cupTw_pullTw`: the formula
  `pr_{2, *}(pr₁^*a ∪ pr₂^*b) = (∫_X a) b` for `a ∈ H^{2d}(X)(d)`.
* `Stacks.WeilCohomology.WeilData.pushforward_snd_cupTw_pullTw_eq_zero`: the formula for `a` of
  degree other than `2d`, where `(∫_X a) b = 0`.
* `Stacks.WeilCohomology.WeilData.pushforward_snd_externalProduct`: **Stacks 0FHC**, the two
  clauses together.

## Implementation notes

The scheme `X × Y` is nonempty and equidimensional of dimension `d + e`
(`SmoothProjectiveScheme.isNonemptyEquidimensional_prod`), so `pr_{2, *}` is the pushforward
`WeilData.pushforward` of (A)(b), with source twist `d + t` and target twist `t`; the source's
`H^*(X × Y)(d + e) ⟶ H^*(Y)(e)` is the case `t = e`. The class `b` may carry any Tate twist `t`.
The proof is the source's ("this follows from (B)(a) and (B)(b)"): pairing against a test class
`c` on `Y`, the trace equation of the pushforward, graded commutativity (the sign is
`(-1)^{2d(2e - q)} = 1`), multiplicativity of pullback and axiom (B)(b) give
`∫_Y c ∪ pr_{2, *}(a ⊗ b) = ∫_X a · ∫_Y c ∪ b`, and Poincaré duality (A)(b) on `Y` concludes.
Only (A)(b) and (B)(b) are used.

## References

* [Stacks Project, Tag 0FHC](https://stacks.math.columbia.edu/tag/0FHC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- The trace on `X × Y` of `pr₂^*c ∪ (pr₁^*a ∪ pr₂^*b)` is `(-1)^{ip} ∫_X a · ∫_Y c ∪ b` for
`a` of degree `p` and `c` of degree `i`: graded commutativity, multiplicativity of pullback
and axiom (B)(b). -/
private theorem traceProj_pull_snd_mul_pull_fst_mul_pull_snd (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    {p i : ℤ} {a : W.H X} {b c : W.H Y} (ha : a ∈ W.grade X p) (hc : c ∈ W.grade Y i) :
    W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
        (W.pull (snd X Y) c * (W.pull (fst X Y) a * W.pull (snd X Y) b)) =
      ((i * p).negOnePow : ℤ) * (W.traceProj X d hX a * W.traceProj Y e hY (c * b)) := by
  rw [← mul_assoc, W.graded_comm _ i p _ _ (W.pull_grade _ i _ hc) (W.pull_grade _ p _ ha),
    smul_mul_assoc, mul_assoc, ← map_mul, map_zsmul, zsmul_eq_mul,
    traceProj_pull_fst_mul_pull_snd hK hX hY]

/-- **`pr_{2, *}(pr₁^*a ∪ pr₂^*b) = (∫_X a) b`** for `X`, `Y` nonempty equidimensional of
dimensions `d` and `e`, `a ∈ H^{2d}(X)(d)` and `b ∈ H^q(Y)(t)`, the pushforward along
`pr₂ : X × Y ⟶ Y` going from `H^{2d+q}(X × Y)(d+t)` to `H^q(Y)(t)`. Only axioms (A)(b) and
(B)(b) are used. -/
theorem pushforward_snd_cupTw_pullTw (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (q t : ℤ)
    (a : W.Tw X (2 * d) d) (b : W.Tw Y q t) :
    W.pushforward hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY (2 * d + q) (d + t) q t
        (by push_cast; ring) (by push_cast; ring)
        (W.cupTw (prod X Y) (2 * d) q _ rfl d t _ rfl (W.pullTw (fst X Y) _ _ a)
          (W.pullTw (snd X Y) _ _ b)) =
      W.trace X d hX a • b := by
  refine eq_of_pairingTw_eq hA hY (2 * e - q) q (by omega) (e - t) t (by omega) fun c ↦ ?_
  rw [← pushforward_trace' hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY
      (2 * d + q) (d + t) q t (by push_cast; ring) (by push_cast; ring) (2 * e - q) (e - t)
      (by push_cast; ring) (by push_cast; ring) (by omega) (by omega),
    map_smul, pairingTw_eq_traceProj, pairingTw_eq_traceProj, twCoord_cupTw, coe_cup,
    twCoord_pullTw, twCoord_pullTw, twCoord_pullTw, coe_pullDeg, coe_pullDeg, coe_pullDeg,
    trace_eq_traceProj, smul_eq_mul]
  rw [traceProj_pull_snd_mul_pull_fst_mul_pull_snd hK hX hY (W.twCoord X _ d a).2
    (W.twCoord Y _ _ c).2, Int.negOnePow_even _ (Int.even_mul.2 (.inr ⟨d, by ring⟩)),
    Units.val_one, Int.cast_one, one_mul]

/-- **`pr_{2, *}(pr₁^*a ∪ pr₂^*b) = 0` for `a` not of the top degree `2d`**, which is the formula
`pr_{2, *}(a ⊗ b) = (∫_X a) b` with `∫_X` read as zero outside `H^{2d}(X)`: for `X`, `Y` nonempty
equidimensional of dimensions `d` and `e`, `a ∈ H^p(X)(s)` with `p ≠ 2d` and `b ∈ H^q(Y)(t)`.
Only axioms (A)(b) and (B)(b) are used. -/
theorem pushforward_snd_cupTw_pullTw_eq_zero (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (p q s t : ℤ)
    (hp : p ≠ 2 * d) (a : W.Tw X p s) (b : W.Tw Y q t) :
    W.pushforward hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY (p + q) (s + t)
        (p + q - 2 * d) (s + t - d) (by push_cast; ring) (by push_cast; ring)
        (W.cupTw (prod X Y) p q _ rfl s t _ rfl (W.pullTw (fst X Y) _ _ a)
          (W.pullTw (snd X Y) _ _ b)) = 0 := by
  refine eq_of_pairingTw_eq hA hY (2 * e - (p + q - 2 * d)) (p + q - 2 * d) (by omega)
    (e - (s + t - d)) (s + t - d) (by omega) fun c ↦ ?_
  rw [← pushforward_trace' hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY
      (p + q) (s + t) (p + q - 2 * d) (s + t - d) (by push_cast; ring) (by push_cast; ring)
      (2 * e - (p + q - 2 * d)) (e - (s + t - d)) (by push_cast; ring) (by push_cast; ring)
      (by omega) (by omega),
    map_zero, pairingTw_eq_traceProj, twCoord_cupTw, coe_cup, twCoord_pullTw, twCoord_pullTw,
    twCoord_pullTw, coe_pullDeg, coe_pullDeg, coe_pullDeg]
  rw [traceProj_pull_snd_mul_pull_fst_mul_pull_snd hK hX hY (W.twCoord X p s a).2
    (W.twCoord Y _ _ c).2, W.traceProj_of_mem_ne X d hX (W.twCoord X p s a).2 hp, zero_mul,
    mul_zero]

/-- **Stacks Project, Tag 0FHC.** Let `H^*` be data (D0), (D1), (D3) over a field `k`
satisfying axioms (A) and (B), and let `X`, `Y` be nonempty smooth projective schemes over `k`,
equidimensional of dimensions `d` and `e`. Then `pr_{2, *} : H^*(X × Y)(d + e) ⟶ H^*(Y)(e)`
sends `a ⊗ b = pr₁^*a ∪ pr₂^*b` to `(∫_X a) b`:

* for `a ∈ H^{2d}(X)(d)` and `b ∈ H^q(Y)(t)`, `pr_{2, *}(a ⊗ b) = (∫_X a) b`;
* for `a ∈ H^p(X)(s)` with `p ≠ 2d`, where `∫_X a` is read as zero, `pr_{2, *}(a ⊗ b) = 0`.

The source's twists are `t = e`, resp. `s + t = d + e`; any twist is allowed here. Only (A)(b)
and (B)(b) are used. -/
@[stacks 0FHC "over any field k, for nonempty equidimensional (possibly disconnected) smooth \
  projective X, Y and the actual WeilData of Section 0FHA under (A)(b) and (B)(b): \
  pr_{2,*}(pr₁^*a ∪ pr₂^*b) = (∫_X a) b for a of top degree 2d, and = 0 for a of any other \
  degree, where ∫_X a is read as zero; b in any degree and Tate twist"]
theorem pushforward_snd_externalProduct (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) :
    (∀ (q t : ℤ) (a : W.Tw X (2 * d) d) (b : W.Tw Y q t),
      W.pushforward hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY (2 * d + q) (d + t)
          q t (by push_cast; ring) (by push_cast; ring)
          (W.cupTw (prod X Y) (2 * d) q _ rfl d t _ rfl (W.pullTw (fst X Y) _ _ a)
            (W.pullTw (snd X Y) _ _ b)) =
        W.trace X d hX a • b) ∧
    ∀ (p q s t : ℤ), p ≠ 2 * d → ∀ (a : W.Tw X p s) (b : W.Tw Y q t),
      W.pushforward hA (snd X Y) (isNonemptyEquidimensional_prod hX hY) hY (p + q) (s + t)
          (p + q - 2 * d) (s + t - d) (by push_cast; ring) (by push_cast; ring)
          (W.cupTw (prod X Y) p q _ rfl s t _ rfl (W.pullTw (fst X Y) _ _ a)
            (W.pullTw (snd X Y) _ _ b)) = 0 :=
  ⟨pushforward_snd_cupTw_pullTw hA hK hX hY,
    fun p q s t hp ↦ pushforward_snd_cupTw_pullTw_eq_zero hA hK hX hY p q s t hp⟩

end Stacks.WeilCohomology.WeilData

end
