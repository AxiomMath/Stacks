module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace map of a disjoint union

Let `W` be data (D0), (D1), (D2), (D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C),
and let `X`, `Y` be nonempty smooth projective schemes over `k`, both equidimensional of dimension
`d`. Stacks 0FHP: `∫_{X ⨿ Y} = ∫_X + ∫_Y`. Under the isomorphism
`(i^*, j^*) : H^{2d}(X ⨿ Y)(d) → H^{2d}(X)(d) ⊕ H^{2d}(Y)(d)` of Stacks 0FHJ, for the
coprojections `i` and `j`, the map `∫_X + ∫_Y` becomes `∫_{X ⨿ Y}`, that is,
`∫_{X ⨿ Y} = ∫_X ∘ i^* + ∫_Y ∘ j^*`.

## Main results

* `Stacks.WeilCohomology.WeilData.trace_pt_eq_add_comp_pullTw`: Stacks 0FHP for any coproduct of
  `X` and `Y` in the category of smooth projective schemes over `k`, given as a colimit cofan.
* `Stacks.WeilCohomology.WeilData.trace_coprodObj_eq_add_comp_pullTw`: the same for the disjoint
  union `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodObj X Y` of the underlying schemes.

## Implementation notes

The proof is the source's, and it is
`Stacks.WeilCohomology.WeilData.trace_eq_add` from the proof of 0FHJ. That lemma derives
`a = i_*(i^*a) + j_*(j^*a)` from `1 = γ([X ⨿ Y]) = γ([X]) + γ([Y]) = i_*1 + j_*1`, and the trace
equation defining the pushforward gives `∫_{X ⨿ Y} a ∪ i_*1 = ∫_X i^*a`. The source's `∫_{X ⨿ Y}`
presupposes that `X ⨿ Y` is nonempty and equidimensional of dimension `d`. Here that is not
assumed; it is `Stacks.WeilCohomology.SmoothProjectiveScheme.isNonemptyEquidimensional_pt`. The
scheme `X ⨿ Y` is smooth and projective over `k` (Stacks 0B46, over `Spec k` by Stacks 0B45),
which is `Stacks.WeilCohomology.SmoothProjectiveScheme.coprodObj`.

## References

* [Stacks Project, Tag 0FHP](https://stacks.math.columbia.edu/tag/0FHP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-- **Stacks Project, Tag 0FHP.** Let `X` and `Y` be nonempty smooth projective schemes over `k`,
both equidimensional of dimension `d`, and let `c` be a coproduct `X ⨿ Y` with coprojections
`i`, `j`. Given (D0)–(D3) satisfying (A), (B) and (C), `∫_{X ⨿ Y} = ∫_X + ∫_Y`, in the sense
that `∫_{X ⨿ Y} = ∫_X ∘ i^* + ∫_Y ∘ j^*` on `H^{2d}(X ⨿ Y)(d)`. -/
@[stacks 0FHP]
theorem trace_pt_eq_add_comp_pullTw (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan X Y} (hc : IsColimit c) {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y d) :
    W.trace c.pt d (isNonemptyEquidimensional_pt hc hX hY) =
      W.trace X d hX ∘ₗ W.pullTw (Y := c.pt) c.inl _ _ +
        W.trace Y d hY ∘ₗ W.pullTw (Y := c.pt) c.inr _ _ :=
  LinearMap.ext fun x =>
    trace_eq_add hA hB hC (hc.ofIsoColimit (isoBinaryCofanMk c)) hX hY
      (isNonemptyEquidimensional_pt hc hX hY) x

/-- **Stacks Project, Tag 0FHP**, for the disjoint union `X ⨿ Y` of the underlying schemes:
`∫_{X ⨿ Y} = ∫_X ∘ i^* + ∫_Y ∘ j^*` for `X`, `Y` nonempty and equidimensional of dimension
`d`. -/
theorem trace_coprodObj_eq_add_comp_pullTw (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
        {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d) :
    W.trace (coprodObj X Y) d (isNonemptyEquidimensional_coprodObj hX hY) =
      W.trace X d hX ∘ₗ W.pullTw (coprodInl X Y) _ _ +
        W.trace Y d hY ∘ₗ W.pullTw (coprodInr X Y) _ _ :=
  trace_pt_eq_add_comp_pullTw hA hB hC (isColimitCoprodCofan X Y) hX hY

end WeilData

end Stacks.WeilCohomology

end
