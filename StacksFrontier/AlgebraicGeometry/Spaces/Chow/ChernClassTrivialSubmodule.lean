module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapShortExact

/-!
# Chern classes of an extension of a finite locally free module by `𝒪_X`

In Situation 0EDT let `X/B` be good and let `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of
`𝒪_X`-modules with `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`. Then

  `c_{r+1}(ℰ) = 0`   and   `c_j(ℰ) = c_j(ℱ)` for `j = 0, …, r`.

By Stacks 0ES8 (`AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortExact`) applied
with `ℒ = 𝒪_X`, `c_{n+1}(ℰ) = c_{n+1}(ℱ) + c₁(𝒪_X) c_n(ℱ)`, and `c₁(𝒪_X) = 0` (Stacks 0EQK,
`AlgebraicGeometry.Space.PrivateChern.firstChernCapChow_tensorUnit`); so `c_n(ℰ) = c_n(ℱ)` for
every `n`, and `c_{r+1}(ℱ) = 0` because the Chern classes of `ℱ` vanish above its rank
(`AlgebraicGeometry.Space.PrivateChern.chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings`, by
the splitting principle).

## Main results

* `AlgebraicGeometry.Space.chernCap_eq_of_shortExact_tensorUnit`: the identities of Stacks 0ES7
  on `CH_*(X)`, `c_{r+1}(ℰ) ∩ - = 0` and `c_j(ℰ) ∩ - = c_j(ℱ) ∩ -` for `j = 0, …, r`; the relations
  in `A^*(X)` are `AlgebraicGeometry.Space.chernClass_eq_of_shortExact_tensorUnit`.
* `AlgebraicGeometry.Space.chernCap_tensorUnit_one`: `c₁(𝒪_X) = 0`.
* `AlgebraicGeometry.Space.chernCap_eq_chernCap_of_shortExact_tensorUnit`: `c_n(ℰ) = c_n(ℱ)` for
  every `n`.

## References

* [Stacks Project, Tag 0ES7](https://stacks.math.columbia.edu/tag/0ES7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry.Space.PrivateChern

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}

/-- **`c₁(𝒪_X) = 0`**: the first Chern class of `𝒪_X`, as a module of rank one. -/
theorem chernCap_tensorUnit_one (hX : D.IsGood sX)
    (h : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) 1) :
    chernCap.{u, u + 1} (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) 1 h 1 = 0 := by
  rw [chernCap_one_eq_firstChernCapChow _ h (isInvertibleModule_tensorUnit hX)]
  exact firstChernCapChow_tensorUnit hX _

/-- **All Chern classes of an extension by `𝒪_X` agree**: for `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0` short exact
with `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`, `c_n(ℰ) = c_n(ℱ)` for every `n`. -/
theorem chernCap_eq_chernCap_of_shortExact_tensorUnit (hX : D.IsGood sX)
    {E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : 𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1) ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (r : ℕ)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E (r + 1))
    (hF : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX F r) :
    ∀ n : ℕ, chernCap.{u, u + 1} E (r + 1) hE n = chernCap.{u, u + 1} F r hF n
  | 0 => by rw [chernCap_zero, chernCap_zero]
  | n + 1 => by
    rw [chernCap_succ_eq_of_shortExact i q hiq hC (isInvertibleModule_tensorUnit hX) r hE hF n,
      chernCap_tensorUnit_one hX, zero_mul, add_zero]

/-- **The identities of Stacks 0ES7 on `CH_*(X)`.** In Situation 0EDT let `X/B` be good and let
`ℰ`, `ℱ` be finite locally free `𝒪_X`-modules of ranks `r + 1` and `r` fitting into a short exact
sequence `0 ⟶ 𝒪_X ⟶ ℰ ⟶ ℱ ⟶ 0`. Then, as operations on `CH_*(X)`,

  `c_{r+1}(ℰ) ∩ - = 0`   and   `c_j(ℰ) ∩ - = c_j(ℱ) ∩ -` for `j = 0, …, r`,

for the operations `c_n(ℰ) ∩ -` on `CH_*(X)` (`AlgebraicGeometry.Space.PrivateChern.chernCap`)
and `𝒪_X` the unit of the tensor product of `𝒪_X`-modules
(`AlgebraicGeometry.Space.modulesTensorUnit_eq`). This is the statement on one good space; the
relations of Stacks 0ES7 in `A^*(X)`, between the bivariant classes
`AlgebraicGeometry.Space.chernClass`, are
`AlgebraicGeometry.Space.chernClass_eq_of_shortExact_tensorUnit`, which applies this on every
good test space to the inverse image of the sequence. -/
theorem chernCap_eq_of_shortExact_tensorUnit (hX : D.IsGood sX)
    {E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : 𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1) ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (r : ℕ)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E (r + 1))
    (hF : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX F r) :
    chernCap.{u, u + 1} E (r + 1) hE (r + 1) = 0 ∧
      ∀ j ≤ r, chernCap.{u, u + 1} E (r + 1) hE j = chernCap.{u, u + 1} F r hF j :=
  ⟨(chernCap_eq_chernCap_of_shortExact_tensorUnit hX i q hiq hC r hE hF (r + 1)).trans
      (chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings
        (fun hP r T hT h₁ h₂ h₃ n => chernCap_succ_eq_of_shortComplex hP r T hT h₁ h₂ h₃ n)
        (hasIntertwiningSplittings_of_flatPullbackChow
          (fun hZ hP π hπ d hflat hd M r hM hM' n α =>
            chernCap_spaceModulePullback_flatPullbackChow hZ hP π hπ d hflat hd M r hM hM' n α))
        hX F r hF (Nat.lt_succ_self r)),
    fun j _ => chernCap_eq_chernCap_of_shortExact_tensorUnit hX i q hiq hC r hE hF j⟩

end AlgebraicGeometry.Space

end
