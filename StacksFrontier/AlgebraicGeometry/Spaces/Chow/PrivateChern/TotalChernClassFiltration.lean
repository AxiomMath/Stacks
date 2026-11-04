module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule

/-!
# Stacks 0ESA: the total Chern class of a module with a filtration with invertible quotients

In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `r` with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,   `ℰ_i / ℰ_{i-1} ≅ ℒ_i`.

With `x_i = c₁(ℒ_i)` the total Chern class is `c(ℰ) = ∏_{i=1}^r (1 + x_i)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one`: Stacks 0ESA.

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

/-- **Stacks 0ESA, the total Chern class of a module with a filtration with invertible
quotients.** In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules
and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` with a filtration
`0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` such that `ℰ_i / ℰ_{i-1} ≅ ℒ_i` (a monotone family `F` of subobjects
of `ℰ` with `F 0 = ⊥`, `F r = ⊤` and identifications `e i` of the successive quotients). With
`x_i = c₁(ℒ_i)`, `c(ℰ) = ∏_{i=1}^r (1 + x_i)`.

The Chern classes are those of Stacks 0ERZ, `c_n(ℰ) ∩ -` on `CH_*(X)` (`chernCap`), and
`c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` (`totalChernCap`). An identity in `A^*(X)` is an identity of the
operations on `CH_*(Y)` for every good `Y ⟶ X`; the operation of `c_n(ℰ)` on `CH_*(Y)` is
`c_n(f^*ℰ) ∩ -`, and the inverse image along `f` of the filtration is again a filtration of
`f^*ℰ` with invertible quotients `f^*ℒ_i`, so the statement for all good `X` is the statement in
`A^*(X)`. -/
@[stacks 0ESA]
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
