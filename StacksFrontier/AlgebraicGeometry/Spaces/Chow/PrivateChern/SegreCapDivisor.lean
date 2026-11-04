module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClasses

/-!
# The Segre operations along a divisor of a projective bundle

Let `(π : P ⟶ X, 𝒪_P(1))` be a projective bundle datum of fibre dimension `d + 1` and
`(π' : Q ⟶ X, 𝒪_Q(1))` one of fibre dimension `d`, related by a homomorphism
`j : CH_*(Q) ⟶ CH_*(P)` (for instance the pushforward along the inclusion of a divisor
`Q ⊆ P`) and an operation `x` on `CH_*(X)` such that

* `c₁(𝒪_P(1)) ∩ π^*α = j(π'^*α) + π^*(x α)`,
* `c₁(𝒪_P(1)) ∩ j(β) = j(c₁(𝒪_Q(1)) ∩ β)` (the projection formula),
* `π_*(j β) = π'_* β`.

Then the Segre operations `t_i ∩ α = π_*(c₁(𝒪_P(1))^{d+1+i} ∩ π^*α)` satisfy

  `t_{n+1}(P) = t_{n+1}(Q) + t_n(P) ∘ x`.

This is the computation of the proof of Stacks 0ES8, with `Q = 𝐏(ℱ) ⊆ 𝐏(ℰ) = P` the zero locus
of the section of `𝒪_P(1) ⊗ π^*ℒ^{-1}` and `x = c₁(ℒ) ∩ -`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_succ_eq_of_divisor`.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

namespace ProjectiveBundleDatum

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {d : ℕ}

/-- **The Segre operations along a divisor**: from the three relations between the operations of
a projective bundle datum `P` of fibre dimension `d + 1` and a datum `Q` of fibre dimension `d`,
`t_{n+1}(P) = t_{n+1}(Q) + t_n(P) ∘ x`. -/
theorem segreCap_succ_eq_of_divisor (P : ProjectiveBundleDatum D sX hX (d + 1))
    (Q : ProjectiveBundleDatum D sX hX d)
    (j : chowHomology.{u, v} D Q.toBase Q.isGood →+ chowHomology.{u, v} D P.toBase P.isGood)
    (x : AddMonoid.End (chowHomology.{u, v} D sX hX))
    (hstar : ∀ α, P.twistCap (P.pullbackChow α) = j (Q.pullbackChow α) + P.pullbackChow (x α))
    (hproj : ∀ β, P.twistCap (j β) = j (Q.twistCap β))
    (hpush : ∀ β, P.pushforwardChow (j β) = Q.pushforwardChow β) (n : ℕ) :
    P.segreCap (n + 1) = Q.segreCap (n + 1) + P.segreCap n * x := by
  have hpow : ∀ (k : ℕ) β, (P.twistCap ^ k) (j β) = j ((Q.twistCap ^ k) β) := by
    intro k
    induction k with
    | zero => intro β; rfl
    | succ k ih =>
      intro β
      rw [pow_succ, pow_succ]
      show (P.twistCap ^ k) (P.twistCap (j β)) = j ((Q.twistCap ^ k) (Q.twistCap β))
      rw [hproj, ih]
  refine AddMonoidHom.ext fun α => ?_
  show P.pushforwardChow ((P.twistCap ^ (d + 1 + (n + 1))) (P.pullbackChow α)) =
    Q.pushforwardChow ((Q.twistCap ^ (d + (n + 1))) (Q.pullbackChow α)) +
      P.pushforwardChow ((P.twistCap ^ (d + 1 + n)) (P.pullbackChow (x α)))
  rw [show d + 1 + (n + 1) = d + (n + 1) + 1 by omega, pow_succ]
  show P.pushforwardChow ((P.twistCap ^ (d + (n + 1))) (P.twistCap (P.pullbackChow α))) = _
  rw [hstar, map_add, map_add, hpow, hpush, show d + 1 + n = d + (n + 1) by omega]

end ProjectiveBundleDatum

end AlgebraicGeometry.Space.PrivateChern

end
