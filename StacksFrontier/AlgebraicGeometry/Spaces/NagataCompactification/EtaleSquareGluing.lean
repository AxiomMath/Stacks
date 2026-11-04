module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.HasCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Compactifying across an elementary distinguished square

Let `Y` be a quasi-compact and quasi-separated algebraic space of finite type over `Spec ℤ`, and
let `U` be an algebraic space separated and of finite type over `Y`. Let `(U₂ ⊆ U, f : U₁ ⟶ U)`
be an elementary distinguished square: `U₂` is open, `f` is étale, and `f` is an isomorphism
over the reduced complement of `U₂`. If `U₁` and `U₂` have compactifications over `Y` and the
overlap `U₁ ×_U U₂ ⟶ U` has dense image, then `U` has a compactification over `Y`.

This is the gluing step in the proof of Nagata's compactification theorem for algebraic
spaces. The theorem itself is due to Conrad, Lieblich and Olsson.

## Main definitions

* `AlgebraicGeometry.Space.Stmt0F4B`: the statement above, as a
  proposition about the big fppf site `B` over a scheme `S`.

## Implementation notes

The base is quasi-compact and quasi-separated; the source makes these standing assumptions
before it defines compactifications. Finite type over `Spec ℤ` is finite type of the
structure morphism of `Y` viewed over the integers. The density hypothesis is density of the
image, in the topological space of points of `U`, of the points of the fibre product of `f`
and the inclusion of `U₂`.

### The gluing step of the source, and its repair

The source compactifies `U₁` and `U₂` by `X₁` and `X₂`, extends `f` to a proper
`ψ₁ : V₁ ⟶ U` on an open `V₁ ⊆ X₁`, and glues `W₁ = U ⊔_{U₁} (X₁ ∖ (Z̄₁₂ ∪ T̄))` along the
étale map `f`. It then asserts that `W₁` is separated over the base. That is false in
general, for two reasons.

* The chart relation of the pushout is `Δ ⊔ O`, where `O` is the
  off-diagonal part of `U₁ ×_U U₁`. Its closure can meet the boundary. Over a field of
  characteristic `≠ 2`, take `U = 𝔸¹`, `U₂ = 𝔸¹ ∖ {0}`, `U₁ = 𝔸¹ ∖ {1, 2}` and
  `f(z) = z² - 2z`. Every choice in the source is forced (`X_i = ℙ¹`, `V_i = 𝔸¹`), and
  `O = {(a, 2 - a)}` has `(∞, ∞)` in its closure, so `W₁` is not separated.
* With `U₁ = 𝔸¹ ∖ {1, 2, 3}`, the point `3 ∈ V₁ ∖ U₁` lies over `U₂`. So
  `U₁ ⟶ U ×_B (X₁ ∖ (Z̄₁₂ ∪ T̄))` is not closed either.

The repair keeps the source's steps and modifies `X₁` three more times, each by an
admissible blowup whose centre lies in `Q = D ∖ V₁`, where `D` is the closure of `f⁻¹ Z₁`
and `∂ = X₁ ∖ V₁` is the boundary.

* First, the closures of `f⁻¹ Z₁` and `V₁ ∖ U₁` are made disjoint (Stacks 0F46).
* Second, `X₁` is blown up along `I + J ^ M`, where `I` is the ideal of `D`, `V(J) = ∂`,
  and `M` comes from the Nullstellensatz on the closure `Ō` of `O`:
  `(pᵢ^* J) ^ M ≤ p₁^* I + p₂^* I`. Afterwards no point of `Ō` has both projections in
  `Q`; over a valuation ring this is `ValuationRing.eq_top_or_eq_top_of_pow_le_sup`.
* Third, the closures of `f⁻¹ Z₁` and `∂ ∖ Q` are made disjoint (Stacks 0F46 on `X₁ ∖ Q`).

Then `N = X₁ ∖ (closure (V₁ ∖ U₁) ∪ closure (∂ ∖ Q))` contains `D` and satisfies
`N ∩ V₁ = U₁`, and `W₁ = U ⊔_{U₁} N` is separated by the corrected Stacks 0F45. The
remainder of the source's argument goes through with `N` in place of
`X₁ ∖ (Z̄₁₂ ∪ T̄)`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [B. Conrad, M. Lieblich, M. Olsson, *Nagata compactification for algebraic spaces*][CLO]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Compactifications glue across an elementary distinguished square** (Stacks 0F4B). Over a
quasi-compact, quasi-separated algebraic space `Y` of finite type over `Spec ℤ`, let `U` be
separated and of finite type over `Y` and let `(U₂ ⊆ U, f₁ : U₁ ⟶ U)` be an elementary
distinguished square such that `U₁` and `U₂` have compactifications over `Y` and
`U₁ ×_U U₂ ⟶ U` has dense image. Then `U` has a compactification over `Y`. -/
def Stmt0F4B {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (hZ : B.Contains (⊤_ Scheme.{u})) : Prop :=
  ∀ {U Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U),
    IsAlgebraicSpace B S hS Y → IsQuasiCompactSpace B S hS Y →
    IsAbsolutelyQuasiSeparated B S hS hZ Y →
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)) →
    ∀ p : U ⟶ Y, IsSeparated B S hS p → IsFiniteType B S hS p →
    ∀ (U₂ : Subfunctor U) {U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f₁ : U₁ ⟶ U),
      IsElementaryDistinguishedSquare B S hS hU U₂ f₁ →
      HasCompactification B S hS (f₁ ≫ p) → HasCompactification B S hS (U₂.ι ≫ p) →
      (letI := pointTopology B S hS U
       DenseRange (pointsMap B S hS (pullback f₁ U₂.ι) (pullback.fst f₁ U₂.ι ≫ f₁))) →
      HasCompactification B S hS p

end AlgebraicGeometry.Space

end
