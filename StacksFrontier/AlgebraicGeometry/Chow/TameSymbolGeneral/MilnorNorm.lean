module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Arrows
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Dvr

/-!
# The general tame symbol and the arrows of Stacks 0EAY, with the norm maps of Milnor K-theory

The constructions of `StacksDraft.AlgebraicGeometry.Chow.TameSymbolGeneral` take the norm maps
`K^M_*(L) → K^M_*(K)` as a parameter (`Stacks.Chow.MilnorKNormFamily`). This file specializes
them to the norm maps `N_{L/K}` of `Stacks.Chow.milnorKNormRing`, which preserve the degree and
satisfy the projection formula `N_{L/K}(ι z) = [L : K] z`. The result is

* for a one-dimensional Noetherian local domain `A` with fraction field `F`, the tame symbol
  `∂_A : K^M_{i+1}(F) → K^M_i(κ(A))`, `∂_A = ∑_𝔫 N_{κ(𝔫)/κ(A)} ∘ ∂_{A'_𝔫}` over the maximal ideals
  of the normalization `A'` (`Stacks.Chow.oneDimTameSymbol`), which for a discrete valuation ring
  is the tame symbol of Section 42.5 (`Stacks.Chow.oneDimTameSymbol_eq_dvrMilnorTameSymbol'`);
* for a locally Noetherian scheme `X` with a function `δ` decreasing along proper
  specializations, the arrow `⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) → ⨁_{δ(x) = j} K^M_i(κ(x))`
  (`Stacks.Chow.milnorChainBoundary`).

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Chow

/-- **The norm maps `N_{L/K}` of Milnor K-theory, as a family.** -/
def milnorKNormFamily : MilnorKNormFamily.{u} := fun K L _ _ _ _ ↦ milnorKNormRing K L

/-- The norm maps `N_{L/K} : K^M_*(L) → K^M_*(K)` send `K^M_i(L)` into `K^M_i(K)` for every `i`. -/
theorem milnorKNormFamily_preservesGrading : milnorKNormFamily.{u}.PreservesGrading :=
  fun _ _ _ _ _ _ _ _ hx ↦ milnorKNormRing_mem_milnorKGrading hx

/-- **Projection formula.** For a finite extension `L/K` and `z ∈ K^M_*(K)`, the norm of the
image of `z` in `K^M_*(L)` is `[L : K] z`. -/
theorem milnorKNormFamily_projectionFormula : milnorKNormFamily.{u}.ProjectionFormula :=
  fun _ _ _ _ _ _ z ↦ milnorKNormRing_milnorKRingMap z

/-- **The tame symbol `∂_A : K^M_{i+1}(F) → K^M_i(κ(A))` of a one-dimensional Noetherian local
domain `A` with fraction field `F`**, obtained from the tame symbols of the discrete valuation
rings `A'_𝔫` of its normalization by the norm maps `N_{κ(𝔫)/κ(A)}`. -/
@[stacks 0EAY "the extension of the tame symbol ∂_A : K^M_{i+1}(F) → K^M_i(κ) from discrete \
valuation rings to one-dimensional local domains using normalization and norm maps on K^M_i: for \
a Noetherian local domain A of dimension 1 with fraction field F, ∂_A is the sum over the maximal \
ideals 𝔫 of the normalization A' of N_{κ(𝔫)/κ} ∘ ∂_{A'_𝔫}, where A'_𝔫 is a discrete valuation \
ring with fraction field F and κ(𝔫)/κ is finite (Krull-Akizuki). This covers every Noetherian \
local domain of dimension 1, so in particular the excellent ones of the remark"]
def oneDimTameSymbol (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F] (hdim : ringKrullDim A = 1)
    (i : ℕ) : MilnorKTheory F (i + 1) →+ MilnorKTheory (ResidueField A) i :=
  (normalizationDvrFamily A F hdim).tameSymbol milnorKNormFamily_preservesGrading i

/-- **For a discrete valuation ring, `∂_A` is the tame symbol of Section 42.5.** -/
@[stacks 0EAY "the general tame symbol extends the one of a discrete valuation ring: when A is a \
discrete valuation ring, the symbol obtained by normalization and norm is the tame symbol \
∂_A : K^M_{i+1}(F) → K^M_i(κ) defined as in Section 42.5"]
theorem oneDimTameSymbol_eq_dvrMilnorTameSymbol' (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
    (i : ℕ) :
    oneDimTameSymbol A F (IsDiscreteValuationRing.ringKrullDim_eq_one A) i =
      dvrMilnorTameSymbol' A F i :=
  tameSymbol_normalizationDvrFamily_eq_dvrMilnorTameSymbol' milnorKNormFamily_projectionFormula
    milnorKNormFamily_preservesGrading _ i

/-- **The arrow `⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) → ⨁_{δ(x) = j} K^M_i(κ(x))`**, for a locally
Noetherian scheme `X` and a function `δ` strictly decreasing along proper specializations. The
coefficient at `x'` is the sum over the points `x` with `δ(x) = j + 1` specializing to `x'` of
`∂_{𝒪_{closure {x}, x'}}` applied to the class at `x`. A dimension function is strictly decreasing
along proper specializations (`DimensionFunction`, property (a)), and on a Noetherian scheme a
locally finite family is a finitely supported one
(`Stacks.Chow.mem_dimMilnorChainGroup_iff_finite`), so this is the arrow of the remark. -/
@[stacks 0EAY "the arrows of the remark's display, in every degree i: for a Noetherian scheme X \
with a dimension function δ, the map ⊕_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⊕_{δ(x) = j} K^M_i(κ(x)) \
whose coefficient at x' is the sum over the points x with δ(x) = j + 1 specializing to x' of the \
tame symbol ∂_A, A = 𝒪_{closure {x}, x'}, applied to the class at x. Proved for X locally \
Noetherian and δ strictly decreasing along proper specializations, which includes the remark's \
setting; the second arrow of the display is the same map at (i - 1, j - 1)"]
def milnorChainBoundary {X : Scheme.{u}} [IsLocallyNoetherian X] (δ : X → ℤ)
    (hδ : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ y < δ x) (i : ℕ) (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (i + 1) →+ DimMilnorChainGroup X δ j i :=
  dimMilnorChainBoundary δ hδ milnorKNormFamily_preservesGrading i j

end Stacks.Chow

end
