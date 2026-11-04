module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass

/-!
# `i_*1` through a blowing up square

Let `(D0)`–`(D3)` be data satisfying axiom (A)(b) (`Stacks.WeilCohomology.WeilData`), and consider
a commutative square of nonempty equidimensional smooth projective schemes over `k`

```
E --j--> X'
|π       |b
v        v
Z --i--> X
```

with `dim Z = m`, `dim E = e`, `dim X = dim X' = e + 1` and `m + r = e + 1`. Given classes
`g_Z ∈ H^{2r}(X)(r)`, `g_E ∈ H^2(X')(1)` and `g_θ ∈ H^{2r-2}(X')(r-1)` with

* `π_*(j^*g_θ) = 1`, `j_*1 = g_E`, `g_θ ∪ g_E = b^*g_Z` and `b_*1 = 1`,

we have `i_*1 = g_Z`. This is the computation of the proof of [Stacks, Tag 0FIT]:

`i_*(1) = i_*π_*(j^*γ(θ)) = b_*j_*(j^*γ(θ)) = b_*(γ(θ) ∪ j_*(1)) = b_*(b^*γ([Z]))`
`= γ([Z]) ∪ b_*(1)`,

which uses only the definition of the pushforward by Poincaré duality, i.e. the projection
formula and functoriality of Stacks 0FHB. In the source `g_E = γ([E])`, `g_θ = γ(θ)` and
`g_Z = γ([Z])`, for the exceptional divisor `E` of the blowing up `b` of `X` in `Z` and the
class `θ` of Lemma 0FIH.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_of_square`: `i_*1 = g_Z`.

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- Pairing with the unit class is the trace. -/
theorem pairingTw_unitTw_right (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (x : W.Tw X (2 * d) d) :
    W.pairingTw X d hX (2 * d) 0 (by ring) d 0 (by ring) x (W.unitTw X 0 0 rfl) =
      W.trace X d hX x := by
  rw [pairingTw_apply, W.cupTw_eq_self_of_coe_twCoord_eq_one_right X _ _ _ _ _ _ _ _
    (W.coe_twCoord_unitTw X _ _ rfl)]

/-- The trace of a pullback is the pairing with the pushforward of the unit class. -/
private theorem trace_pullTw_eq_pairingTw_pushforward_unitTw (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (j' t' : ℤ)
    (hj : j' + 2 * d = 0 + 2 * e) (ht : t' + d = 0 + e) (hi' : 2 * (d : ℤ) + j' = 2 * e)
    (hs' : (d : ℤ) + t' = e) (b : W.Tw Y (2 * d) d) :
    W.trace X d hX (W.pullTw f _ _ b) = W.pairingTw Y e hY _ j' hi' _ t' hs' b
      (W.pushforward hA f hX hY 0 0 j' t' hj ht (W.unitTw X 0 0 rfl)) := by
  rw [← pairingTw_unitTw_right X d hX, pushforward_trace' hA f hX hY 0 0 j' t' hj ht _ _ _ _ _ _]

/-- **`i_*1 = g_Z` through a commutative square** `π ≫ i = j ≫ b`, given `π_*(j^*g_θ) = 1`,
`j_*1 = g_E`, `g_θ ∪ g_E = b^*g_Z` and `b_*1 = 1`: the computation of the proof of
Stacks 0FIT, from the projection formula and functoriality of the pushforward (Stacks 0FHB). -/
theorem pushforward_unitTw_eq_of_square (hA : W.PerfectPairing)
    {Z X E X' : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) (π : E ⟶ Z) (j : E ⟶ X')
    (b : X' ⟶ X) (sq : π ≫ i = j ≫ b) {m e r : ℕ} (hr0 : 0 < r) (hr : m + r = e + 1)
    (hZ : IsNonemptyEquidimensional Z m) (hE : IsNonemptyEquidimensional E e)
    (hX : IsNonemptyEquidimensional X (e + 1)) (hX' : IsNonemptyEquidimensional X' (e + 1))
    (gZ : W.Tw X (2 * (r : ℤ)) r) (gE : W.Tw X' (2 * 1) 1)
    (gθ : W.Tw X' (2 * ((r - 1 : ℕ) : ℤ)) ((r - 1 : ℕ) : ℤ))
    (hπ : W.pushforward hA π hE hZ (2 * ((r - 1 : ℕ) : ℤ)) ((r - 1 : ℕ) : ℤ) 0 0 (by omega)
      (by omega) (W.pullTw j _ _ gθ) = W.unitTw Z 0 0 rfl)
    (hj : W.pushforward hA j hE hX' 0 0 (2 * 1) 1 (by push_cast; omega) (by push_cast; omega)
      (W.unitTw E 0 0 rfl) = gE)
    (hmul : W.cupTw X' (2 * ((r - 1 : ℕ) : ℤ)) (2 * 1) (2 * (r : ℤ)) (by omega)
      ((r - 1 : ℕ) : ℤ) 1 r (by omega) gθ gE = W.pullTw b _ _ gZ)
    (hb : W.pushforward hA b hX' hX 0 0 0 0 rfl rfl (W.unitTw X' 0 0 rfl) =
      W.unitTw X 0 0 rfl) :
    W.pushforward hA i hZ hX 0 0 (2 * (r : ℤ)) r (by push_cast; omega) (by push_cast; omega)
      (W.unitTw Z 0 0 rfl) = gZ := by
  refine eq_of_pairingTw_eq hA hX (2 * (m : ℤ)) (2 * (r : ℤ)) (by push_cast; omega) m r
    (by push_cast; omega) fun c ↦ ?_
  calc _ = W.pairingTw Z m hZ (2 * (m : ℤ)) 0 (by ring) m 0 (by ring) (W.pullTw i _ _ c)
        (W.unitTw Z 0 0 rfl) :=
      (pushforward_trace' hA i hZ hX 0 0 (2 * (r : ℤ)) r _ _ (2 * (m : ℤ)) m (by ring) (by ring)
        _ _ c _).symm
    _ = W.pairingTw Z m hZ (2 * (m : ℤ)) 0 (by ring) m 0 (by ring) (W.pullTw i _ _ c)
        (W.pushforward hA π hE hZ (2 * ((r - 1 : ℕ) : ℤ)) ((r - 1 : ℕ) : ℤ) 0 0 (by omega)
          (by omega) (W.pullTw j _ _ gθ)) := by rw [hπ]
    _ = W.pairingTw E e hE (2 * (m : ℤ)) (2 * ((r - 1 : ℕ) : ℤ)) (by omega) m ((r - 1 : ℕ) : ℤ)
        (by omega) (W.pullTw π _ _ (W.pullTw i _ _ c)) (W.pullTw j _ _ gθ) :=
      (pushforward_trace' hA π hE hZ (2 * ((r - 1 : ℕ) : ℤ)) ((r - 1 : ℕ) : ℤ) 0 0 _ _
        (2 * (m : ℤ)) m _ _ _ _ _ _).symm
    _ = W.pairingTw E e hE (2 * (m : ℤ)) (2 * ((r - 1 : ℕ) : ℤ)) (by omega) m ((r - 1 : ℕ) : ℤ)
        (by omega) (W.pullTw j _ _ (W.pullTw b _ _ c)) (W.pullTw j _ _ gθ) := by
      rw [← pullTw_comp, ← pullTw_comp, sq]
    _ = W.trace E e hE (W.pullTw j _ _ (W.cupTw X' (2 * (m : ℤ)) (2 * ((r - 1 : ℕ) : ℤ)) (2 * e)
        (by omega) m ((r - 1 : ℕ) : ℤ) e (by omega) (W.pullTw b _ _ c) gθ)) := by
      rw [pairingTw_apply, pullTw_cupTw]
    _ = W.pairingTw X' (e + 1) hX' (2 * e) (2 * 1) (by push_cast; ring) e 1 (by push_cast; ring)
        (W.cupTw X' (2 * (m : ℤ)) (2 * ((r - 1 : ℕ) : ℤ)) (2 * e) (by omega) m ((r - 1 : ℕ) : ℤ) e
          (by omega) (W.pullTw b _ _ c) gθ)
        (W.pushforward hA j hE hX' 0 0 (2 * 1) 1 (by push_cast; omega) (by push_cast; omega)
          (W.unitTw E 0 0 rfl)) :=
      trace_pullTw_eq_pairingTw_pushforward_unitTw hA j hE hX' _ _ (by push_cast; omega)
        (by push_cast; omega) (by push_cast; ring) (by push_cast; ring) _
    _ = W.trace X' (e + 1) hX' (W.cupTw X' (2 * (m : ℤ)) (2 * (r : ℤ)) _ (by push_cast; omega) m r _
        (by push_cast; omega) (W.pullTw b _ _ c) (W.pullTw b _ _ gZ)) := by
      rw [hj, pairingTw_apply, ← hmul, cupTw_assoc]
    _ = W.trace X' (e + 1) hX' (W.pullTw b _ _ (W.cupTw X (2 * (m : ℤ)) (2 * (r : ℤ)) _
        (by push_cast; omega) m r _ (by push_cast; omega) c gZ)) := by
      rw [pullTw_cupTw]
    _ = W.pairingTw X (e + 1) hX _ 0 (by ring) _ 0 (by ring)
        (W.cupTw X (2 * (m : ℤ)) (2 * (r : ℤ)) _ (by push_cast; omega) m r _ (by push_cast; omega)
          c gZ)
        (W.pushforward hA b hX' hX 0 0 0 0 rfl rfl (W.unitTw X' 0 0 rfl)) :=
      trace_pullTw_eq_pairingTw_pushforward_unitTw hA b hX' hX _ _ rfl rfl (by push_cast; ring)
        (by push_cast; ring) _
    _ = _ := by rw [hb, pairingTw_unitTw_right, pairingTw_apply]

end WeilData

end Stacks.WeilCohomology

end
