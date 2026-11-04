module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapPropertiesAssembly

/-!
# Chern classes of the dual of a finite locally free module

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module with dual
`ℰ^∨ = ℋom(ℰ, 𝒪_X)`. Stacks 0ESD asserts `c_i(ℰ^∨) = (-1)^i c_i(ℰ)` in `A^i(X)`.

An identity between Chern classes in `A^*(X)` means (Stacks 0ES3) the equality of the operations
`c_i(f^*ℰ^∨) ∩ -` and `(-1)^i c_i(f^*ℰ) ∩ -` on `CH_*(Y)` for every morphism `f : Y ⟶ X` of good
algebraic spaces over `B`. When the rank of `ℰ` is not constant its Chern classes are defined
(Stacks 0ES2) through the decomposition `Y = ∐_r Y_r` by the rank of `f^*ℰ`, acting on each factor
`CH_*(Y_r)` by the Chern classes of the module `f^*ℰ|_{Y_r}` of constant rank `r`; so the identity
is the one for every `f : Y ⟶ X` along which `f^*ℰ` has constant rank, which is what is stated.
The Chern classes are those of Stacks 0ERZ, `AlgebraicGeometry.Space.PrivateChern.chernCap`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_moduleDual`: Stacks 0ESD.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ESD: the Chern classes of the dual.** Let `X/B` be good and `ℰ` a finite locally
free `𝒪_X`-module with dual `ℰ^∨ = ℋom(ℰ, 𝒪_X)`. Then `c_i(ℰ^∨) = (-1)^i c_i(ℰ)` in `A^i(X)`: for
every morphism `f : Y ⟶ X` of good algebraic spaces over `B` along which `f^*ℰ` has rank `r`,
`c_i(f^*ℰ^∨) ∩ - = (-1)^i c_i(f^*ℰ) ∩ -` on `CH_*(Y)`. -/
@[stacks 0ESD]
theorem chernCap_moduleDual (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) {Y : D.Ambient} (f : Y ⟶ X)
    (hY : D.IsGood (f ≫ sX)) (r : ℕ)
    (hr : IsFiniteLocallyFreeOfRank D (f ≫ sX) hY ((spaceModulePullback D hX.1 hY.1 f).obj E) r)
    (i : ℕ) :
    chernCap.{u, u + 1} (hX := hY)
        ((spaceModulePullback D hX.1 hY.1 f).obj ((ihom E).obj (𝟙_ _))) r
        (isFiniteLocallyFreeOfRank_modulePullback_dual
          (ObjectProperty.homMk f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
            ⟨X, hX.1⟩) E hE hr) i =
      (-1 : ℤ) ^ i •
        chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 f).obj E) r hr i :=
  chernCap_dual_of_chernCapProperties (hX := hX) (chernCapProperties D)
    (hasIntertwiningSplittings_of_flatPullbackChow
      (fun hZ hP π hπ d hflat hd M r hM hM' n α =>
        chernCap_spaceModulePullback_flatPullbackChow hZ hP π hπ d hflat hd M r hM hM' n α))
    E hE f hY r hr i

end AlgebraicGeometry.Space.PrivateChern

end
