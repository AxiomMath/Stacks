module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.WideLayerClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.WideLayerVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldPresentation

/-!
# The homomorphism from the Chow group to the K-group of a wide dimension layer

Let `(S, δ)` be a base situation with a dimension function and `X` a quasi-compact scheme
locally of finite type over `S`. The map `Z_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` kills every
cycle rationally equivalent to zero, and therefore descends to the Chow group:

`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

## Main definitions

* `Stacks.Chow.chowToWideDimensionLayerHom`: the homomorphism
  `CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

## Main results

* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_eq_principalCycle`: on a quasi-compact
  integral scheme of delta-dimension `k + 1`, the class of the principal divisor of a unit
  rational function vanishes in the wide layer.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences_of_compactSpace`:
  the vanishing on the whole subgroup of cycles rationally equivalent to zero.
* `Stacks.Chow.chowToWideDimensionLayerHom_mk`: the value of the homomorphism on the class of a
  cycle.

## References

* [Stacks Project, Tag 02MG](https://stacks.math.columbia.edu/tag/02MG)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The integral case -/

/-- On a quasi-compact integral scheme `Y` of
delta-dimension `k + 1` over the base of a Chow situation, a `k`-cycle whose coefficient function
is the principal divisor of a unit rational function `g` has vanishing class in the wide dimension
layer `K₀(Coh_{≤k+1}(Y)/Coh_{≤k-1}(Y))`. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_eq_principalCycle (C : ChowSituation.{u})
    {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] [CompactSpace Y] [IsIntegral Y]
    [IsLocallyNoetherian Y] (k : ℤ)
    (hdim : schemeDeltaDimension C q = ((k + 1 : ℤ) : EInt)) (g : (rationalFunctions Y)ˣ)
    (b : CycleGroup C q k)
    (hb : b.1 = principalCycle Y
      ((rationalFunctionsEquivFunctionField Y).1 (g : rationalFunctions Y))) :
    cycleDimensionLayerWideHom C q k b = 0 := by
  set g' : Y.functionFieldˣ :=
    Units.map (rationalFunctionsEquivFunctionField Y).1.toMonoidHom g
  have hc : ∀ x : Y, (b : AlgebraicCycle Y ℤ) x = Y.ord (g' : Y.functionField) x := fun x ↦ by
    rw [hb]
    exact principalCycle_apply Y _ x
  have hs := isRegularMeromorphicSection_meromorphicSectionOfFunctionField Y g'
  exact cycleDimensionLayerWideHom_eq_zero_of_shortExact C q k
    (shortExact_denominatorShortComplexUnit C q _ hs hdim.le)
    (shortExact_denominatorSectionShortComplexUnit C q _ hs hdim.le)
    (Iso.refl _) (Iso.refl _) rfl rfl
    (dimensionLayerCycle_denominatorQuotientUnit_sub_eq C q hdim g' hc)

/-! ### The homomorphism from the Chow group -/

/-- On a quasi-compact scheme locally of finite type over the base
of a Chow situation, the composite `Z_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` kills every cycle
rationally equivalent to zero. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences_of_compactSpace
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    [CompactSpace X] (k : ℤ) (α : CycleGroup C sX k)
    (hα : α ∈ rationalEquivalences C sX k) :
    cycleDimensionLayerWideHom C sX k α = 0 :=
  cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences C sX k
    (fun _ q _ _ _ _ hdimY g b hb ↦
      cycleDimensionLayerWideHom_eq_zero_of_eq_principalCycle C q k hdimY g b hb) α hα

/-- For a quasi-compact scheme `X` locally of finite type over the base scheme of a Chow situation
there is a canonical homomorphism
`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` sending the class of a `k`-cycle `∑ n_Z[Z]` to the
class of `[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] − [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]` in the wide dimension layer. -/
@[stacks 0FDS "for a quasi-compact `X`; the cycle identity is formalized in the orientation \
`[𝒪_X/fI]_k − [𝒪_X/I]_k = div(f)`, correcting the sign-inverted chain of the source"]
def chowToWideDimensionLayerHom (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [CompactSpace X] (k : ℤ) :
    chowGroup C sX k →+ coherentDimensionKZero C sX (k - 1) (k + 1) :=
  chowToDimensionLayerHom C sX k
    (cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences_of_compactSpace C sX k)

/-- `Stacks.Chow.chowToWideDimensionLayerHom` sends the class of a `k`-cycle to the value of
`Stacks.Chow.cycleDimensionLayerWideHom` on that cycle. -/
theorem chowToWideDimensionLayerHom_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [CompactSpace X] (k : ℤ) (c : CycleGroup C sX k) :
    chowToWideDimensionLayerHom C sX k
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) =
      cycleDimensionLayerWideHom C sX k c :=
  chowToDimensionLayerHom_mk C sX k _ c

end Stacks.Chow

end
