module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.PushPull
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerChernCap

/-!
# The cycle computation of Voevodsky nilpotence, in the curve case

This file assembles the cycle computation in the curve case of Stacks 0FH9 (Voevodsky): with
`αₙ = ([x] - [x'])^{×n}` the smash power, `π : Xⁿ ⟶ H` finite locally free and `𝒩` invertible
on `H` with `[π^*𝒩] = m • ∑ᵢ [prᵢ^*ℒ]` in `Pic(Xⁿ)`, `m ≠ 0`,

  `c₁(𝒩)ⁿ ∩ [H]` torsion in `CH_0(H)`   implies   `αₙ` torsion in `CH_0(Xⁿ)`.

The two inputs are

* `Stacks.Chow.smashPointDifference_cycle_eq_iteratedChernCapOnChow`: `αₙ` is the iterated cap
  `c₁(pr₀^*ℒ) ∩ ⋯ ∩ c₁(pr_{n-1}^*ℒ) ∩ [Xⁿ]`, for `ℒ` with `c₁(ℒ) ∩ [X] = [x] - [x']`;
* `Stacks.Chow.isOfFinAddOrder_iteratedChernCapOnChow_fundamental_of_isOfFinAddOrder`: the
  push-pull step `π^*(c₁(𝒩)ⁿ ∩ [H]) = (mⁿ · n!) · c₁(pr₀^*ℒ) ∩ ⋯ ∩ c₁(pr_{n-1}^*ℒ) ∩ [Xⁿ]`.

In the source `H = Sⁿ(X)` is the symmetric power, `π` has degree `n!`, `m = (n-1)!` and
`𝒩 = Norm_π(pr₁^*ℒ)` with `ℒ = 𝒪_X(x - x')`; the constant the source writes `(n!)ⁿ` is in fact
`((n-1)!)ⁿ · n!`, see `StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.Hinge`.

## Main results

* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_normChern`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

attribute [local instance] SmashPowerData.finiteType

/-- **The cycle computation of Stacks 0FH9 in the curve case.** Let `k` be algebraically closed,
`X` a Noetherian variety of dimension one over `k` carrying an ample invertible module, `x`, `x'`
rational points of `X`, and `ℒ` invertible on `X` with `c₁(ℒ) ∩ [X] = [x] - [x']`. Let
`π : Xⁿ ⟶ H` be finite locally free over `k`, `H` locally of finite type over `k` with
`dim_δ H ≤ n`, and `𝒩` invertible on `H` with `[π^*𝒩] = m • ∑ᵢ [prᵢ^*ℒ]` in `Pic(Xⁿ)`, `m ≠ 0`.
If `c₁(𝒩)ⁿ ∩ [H]` is torsion in `CH_0(H)`, then the smash power `([x] - [x'])^{×n}` is torsion
in `CH_0(Xⁿ)`.

In the source, `H = Sⁿ(X)`, `π` is the canonical map of degree `n!`
(`Stacks.Hilbert.symmetricPowerMap`), `m = (n-1)!` and `𝒩 = Norm_π(pr₁^*ℒ)`, for which the Picard
relation is `Stacks.SheafOfModules.pullbackPicardClass_normInvertible_symmetricPowerMap` (stated on
`∏ᶜ fun _ : Fin n => X`, which is the fibre power here up to an isomorphism compatible with the
projections). -/
theorem isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_normChern (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    [IsVariety k f] (hdim : topologicalKrullDim X = 1) [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
    (L : X.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) f L).capOnChow (fieldChowSituation k) f 0
      (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) =
        pointDifference k f x x' hx hx')
    (n : ℕ) {H : Scheme.{u}} (sH : H ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sH]
    (hdimH : schemeDeltaDimension (fieldChowSituation k) sH ≤ ((n : ℤ) : EInt))
    (π : (smashPointDifference k f x x' hx hx' n).Y.left ⟶ H) {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d]
    (hπ : π ≫ sH = (smashPointDifference k f x x' hx hx' n).Y.hom) (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (m : ℕ) (hm : m ≠ 0)
    (hpic : Stacks.SheafOfModules.pullbackPicardClass π N hN =
      m • ∑ i, Stacks.SheafOfModules.pullbackPicardClass
        (smashProjection k f x x' hx hx' n i) L hLinv)
    (htors : IsOfFinAddOrder (iteratedChernCapOnChow (fieldChowSituation k) sH
      (List.ofFn fun _ : Fin n => invCap (fieldChowSituation k) sH N) 0
      (fundamentalChowClass (fieldChowSituation k) sH
        (0 + ((List.ofFn fun _ : Fin n => invCap (fieldChowSituation k) sH N).length : ℤ))))) :
    IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle := by
  have : LocallyOfFiniteType π :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank π d
  have : Flat π := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank π d
  rw [smashPointDifference_cycle_eq_iteratedChernCapOnChow k f x x' hx hx' hdim L hL n]
  exact isOfFinAddOrder_iteratedChernCapOnChow_fundamental_of_isOfFinAddOrder
    (fieldChowSituation k) _ sH π hπ 0
    (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) n hdimH f A hA
    hdim.le L (smashProjection k f x x' hx hx' n)
    (smashProjection_comp k f x x' hx hx' n) N m hm hpic htors

end Stacks.Chow

end
