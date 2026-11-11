module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule

/-!
# The total Chern class of a module with a filtration with invertible quotients

In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `r` with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,   `ℰ_i / ℰ_{i-1} ≅ ℒ_i`.

With `x_i = c₁(ℒ_i)` the total Chern class is `c(ℰ) = ∏_{i=1}^r (1 + x_i)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one`: the product
  formula on `CH_*(X)`, the input of Stacks 0ESA
  (`AlgebraicGeometry.Space.totalChernCapGraded_eq_prod_one_add_chernCapGraded`).

## References

* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **The total Chern class of a module with a filtration with invertible quotients, on `CH_*(X)`.**
Let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ` be a finite locally
free `𝒪_X`-module of rank `r` with a filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` such that
`ℰ_i / ℰ_{i-1} ≅ ℒ_i` (a monotone family `F` of subobjects of `ℰ` with `F 0 = ⊥`, `F r = ⊤` and
identifications `e i` of the successive quotients). With `x_i = c₁(ℒ_i)`,
`c(ℰ) = ∏_{i=1}^r (1 + x_i)` as operations on `CH_*(X) = ⨁_k CH_k(X)`.

The operations are `AlgebraicGeometry.Space.PrivateChern.chernCap`, the Segre recursion of the
proof of Stacks 0ERY, and `c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` (`totalChernCap`). This is the identity on
the test space `X` itself. Stacks 0ESA, the identity in `A^*(X)` for the classes of Stacks 0ERZ on
every good test space `X' ⟶ X`, is
`AlgebraicGeometry.Space.totalChernCapGraded_eq_prod_one_add_chernCapGraded`, which applies this
statement on `X'` to the inverse image of the filtration
(`AlgebraicGeometry.Space.exists_filtration_modulePullback`) and identifies the operations with the
cap operations of `c_j(ℰ) ∈ A^j(X)`
(`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap`). -/
theorem totalChernCap_eq_prod_one_add_chernCap_one
    {r : ℕ}
    (L : Fin r → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    totalChernCap.{u, u + 1} E r hE = (List.ofFn fun i ↦ 1 +
      chernCap.{u, u + 1} (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) 1).prod :=
  totalChernCap_eq_prod_one_add_chernCap_one_of_filtration
    (fun r T hT h₁ h₂ h₃ n ↦ chernCap_succ_eq_of_shortComplex hX r T hT h₁ h₂ h₃ n) L hL E hE F hF
    h0 hr e

end AlgebraicGeometry.Space.PrivateChern

end
