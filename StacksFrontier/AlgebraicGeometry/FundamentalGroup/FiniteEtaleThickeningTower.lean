module

public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalBottomStage
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening

/-!
# The tower of finite étale covers over a tower of thickenings

By [Stacks, Tag 0BQB] base change along a thickening `j : Y ⟶ Z` is an equivalence
`FÉt_Z ⥤ FÉt_Y`, so a finite étale cover of `Y` lifts, uniquely up to isomorphism, to one of `Z`.
Iterating along a sequence of thickenings `Y 0 ⟶ Y 1 ⟶ ⋯` turns a finite étale cover of `Y 0`
into a compatible tower of finite étale covers of the `Y n`.

Applied to the infinitesimal neighbourhoods `Z_n` of a closed subscheme `Z ⊆ X` — whose
transition maps are first-order thickenings, `Stacks.Thickenings.nthOrderSucc_isThickening` —
this is the first step of the construction in the proof of [Stacks, Tag 0EK1]: a finite étale
`U_1 ⟶ Z` is lifted to finite étale `π_n : U_n ⟶ Z_n` for every `n`, each the base change of the
next.

## Main definitions

* `AlgebraicGeometry.liftFiniteEtaleAlongThickening` — the lift of a finite étale cover along a
  single thickening, with
  `AlgebraicGeometry.liftFiniteEtaleAlongThickeningIso` identifying its base change with the
  cover one started from.
* `AlgebraicGeometry.finiteEtaleTowerOfThickenings` — the tower along a sequence of thickenings,
  with `AlgebraicGeometry.finiteEtaleTowerOfThickeningsIso` for its compatibility and
  `AlgebraicGeometry.finiteEtaleTowerOfThickenings_zero` for its bottom stage.
* `AlgebraicGeometry.finiteEtaleTowerOfInfinitesimalNeighbourhoods` — the tower over the
  infinitesimal neighbourhoods of a closed subscheme.

## References

* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Lifting along a single thickening -/

variable {Y Z : Scheme.{u}} (j : Y ⟶ Z) (hj : Stacks.Thickenings.IsThickening j)

/-- **The lift of a finite étale cover along a thickening.** Base change along a thickening is an
equivalence by [Stacks, Tag 0BQB], so a cover of the thickened subscheme has a preimage. -/
public def liftFiniteEtaleAlongThickening (A : FiniteEtaleOver Y) : FiniteEtaleOver Z :=
  have := finiteEtaleBaseChange_isEquivalence_of_isThickening j hj
  (finiteEtaleBaseChange j).objPreimage A

/-- The lift of a finite étale cover along a thickening restricts to the cover one started
with. -/
public def liftFiniteEtaleAlongThickeningIso (A : FiniteEtaleOver Y) :
    (finiteEtaleBaseChange j).obj (liftFiniteEtaleAlongThickening j hj A) ≅ A :=
  have := finiteEtaleBaseChange_isEquivalence_of_isThickening j hj
  (finiteEtaleBaseChange j).objObjPreimageIso A

/-! ### The tower along a sequence of thickenings -/

variable {W : ℕ → Scheme.{u}} (k : ∀ n, W n ⟶ W (n + 1))
  (hk : ∀ n, Stacks.Thickenings.IsThickening (k n))

/-- **The tower of finite étale covers over a sequence of thickenings.** The stage `0` is the
given cover and each later stage is the lift of the previous one along the corresponding
thickening. -/
public def finiteEtaleTowerOfThickenings (A : FiniteEtaleOver (W 0)) :
    ∀ n, FiniteEtaleOver (W n)
  | 0 => A
  | n + 1 => liftFiniteEtaleAlongThickening (k n) (hk n)
      (finiteEtaleTowerOfThickenings A n)

/-- Each stage of the tower restricts to the previous one. -/
public def finiteEtaleTowerOfThickeningsIso (A : FiniteEtaleOver (W 0)) (n : ℕ) :
    (finiteEtaleBaseChange (k n)).obj (finiteEtaleTowerOfThickenings k hk A (n + 1)) ≅
      finiteEtaleTowerOfThickenings k hk A n :=
  liftFiniteEtaleAlongThickeningIso (k n) (hk n) (finiteEtaleTowerOfThickenings k hk A n)

/-- The bottom stage of the tower is the cover one started with. -/
public theorem finiteEtaleTowerOfThickenings_zero (A : FiniteEtaleOver (W 0)) :
    finiteEtaleTowerOfThickenings k hk A 0 = A :=
  rfl

/-! ### The tower over the infinitesimal neighbourhoods of a closed subscheme -/

/-- **The tower of finite étale covers over the infinitesimal neighbourhoods of a closed
subscheme.** The inclusions `Z_n ⟶ Z_{n+1}` of the infinitesimal neighbourhoods of an immersion
are first-order thickenings, so `AlgebraicGeometry.finiteEtaleTowerOfThickenings` applies; the
given cover of `Z` is transported to the bottom stage `Z_0`, which is isomorphic to `Z`. -/
public def finiteEtaleTowerOfInfinitesimalNeighbourhoods {X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (A : FiniteEtaleOver Z) (n : ℕ) :
    FiniteEtaleOver (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n) :=
  finiteEtaleTowerOfThickenings (Stacks.Thickenings.nthOrderSucc i)
    (Stacks.Thickenings.nthOrderSucc_isThickening i)
    ((finiteEtaleBaseChange (Stacks.Thickenings.nthOrderZeroIso i).inv).obj A) n

/-- Each stage of the tower over the infinitesimal neighbourhoods restricts to the previous
one. -/
public def finiteEtaleTowerOfInfinitesimalNeighbourhoodsIso {X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (A : FiniteEtaleOver Z) (n : ℕ) :
    (finiteEtaleBaseChange (Stacks.Thickenings.nthOrderSucc i n)).obj
        (finiteEtaleTowerOfInfinitesimalNeighbourhoods i A (n + 1)) ≅
      finiteEtaleTowerOfInfinitesimalNeighbourhoods i A n :=
  finiteEtaleTowerOfThickeningsIso (Stacks.Thickenings.nthOrderSucc i)
    (Stacks.Thickenings.nthOrderSucc_isThickening i)
    ((finiteEtaleBaseChange (Stacks.Thickenings.nthOrderZeroIso i).inv).obj A) n

/-- The bottom stage of the tower over the infinitesimal neighbourhoods is the given cover,
transported along the isomorphism of `Z` with its zeroth infinitesimal neighbourhood. -/
public theorem finiteEtaleTowerOfInfinitesimalNeighbourhoods_zero {X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (A : FiniteEtaleOver Z) :
    finiteEtaleTowerOfInfinitesimalNeighbourhoods i A 0 =
      (finiteEtaleBaseChange (Stacks.Thickenings.nthOrderZeroIso i).inv).obj A :=
  rfl

end AlgebraicGeometry

end
