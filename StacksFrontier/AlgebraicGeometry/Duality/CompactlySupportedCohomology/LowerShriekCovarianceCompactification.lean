module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroCovariance

/-!
# Covariance of compactly supported cohomology for an open, through a compactification

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`, `i : U ⟶ X` an open
immersion and `g = f ∘ i`. Choose a compactification `j : X ⟶ X̄` of `X` over `Y` with structure
morphism `f̄ : X̄ ⟶ Y` and set `j' = j ∘ i`, a compactification of `U` over `Y`. Then
`Rf_! = Rf̄_* ∘ Rj_!` and `Rg_! = Rf̄_* ∘ Rj'_!`, and the second construction of the canonical map
`Rg_!(K|_U) ⟶ Rf_! K` of [Stacks, Tag 0G56] is `Rf̄_*` applied to the map
`Rj'_!(K|_U) ⟶ Rj_! K` of [Stacks, Tag 0G4Y].

## Main definitions

* `AlgebraicGeometry.lowerShriekOpenImmersionMapOfCompactification`: [Stacks, Tag 0G56],
  construction (2).

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **[Stacks, Tag 0G56], construction (2).** Let `f : X ⟶ Y` be a morphism of `FTS_S`,
`i : U ⟶ X` an open immersion, `c` a compactification `j : X ⟶ X̄` of `X` over `Y` with structure
morphism `f̄ : X̄ ⟶ Y`, and `j' = j ∘ i` the induced compactification of `U` over `Y`. With
`Rf_! = Rf̄_* ∘ Rj_!` and `Rg_! = Rf̄_* ∘ Rj'_!` for `g = f ∘ i`, the canonical map
`Rg_!(K|_U) ⟶ Rf_! K`, functorial in `K` in `D^b_{Coh}(𝒪_X)`, is `Rf̄_*` applied to the map
`Rj'_!(K|_U) ⟶ Rj_! K` of [Stacks, Tag 0G4Y]. -/
@[stacks 0G56 "construction (2): Rf̄_* applied to the map Rj'_!(K|_U) ⟶ Rj_! K of Tag 0G4Y"]
def lowerShriekOpenImmersionMapOfCompactification (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left] :
    restrictBoundedCoherentLift i.left ⋙ lowerShriek (i ≫ f) (c.precompOpen i.left) ⟶
      lowerShriek f c :=
  haveI : IsLocallyNoetherian (Over.mk f.left).left := inferInstanceAs (IsLocallyNoetherian X.left)
  Functor.whiskerRight
    (CategoryTheory.extensionByZeroCovariance (restrictBoundedCoherentLift c.immersion)
      (restrictBoundedCoherentLift (i.left ≫ c.immersion)) (restrictBoundedCoherentLift i.left)
      (restrictBoundedCoherentLiftCompIso i.left c.immersion _ rfl).symm
      (DeligneSystem.values c.immersion).toAssignment
      (DeligneSystem.values (i.left ≫ c.immersion)).toAssignment)
    (ProSeq.map (properPushforwardBoundedCoherent c.toBase))

end AlgebraicGeometry
