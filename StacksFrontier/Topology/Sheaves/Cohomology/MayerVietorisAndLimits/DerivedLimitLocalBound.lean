module

public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.DerivedLimitStalkInjectivity
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.MayerVietorisCanonical

/-!
# Convergence of the truncation tower from a bound on a fundamental system

Let `(X, 𝒪_X)` be a ringed space and `E` an object of `D(𝒪_X)`. If every point `x` carries an
integer `dₓ ≥ 0` and a fundamental system `𝔘ₓ` of open neighbourhoods on whose members
`Hᵖ(U, Hᵠ(E))` vanishes whenever `p > dₓ` and `q < 0`, then the canonical map from `E` to a
derived limit of its tower of truncations `τ_{≥ -n} E` is an isomorphism.

## Main results

* `Stacks.Cohomology.DerivedLimitStalk.isIso_to_isDerivedLimit_truncGETower_of_local_bound`:
  under such a local bound, `E` is the derived limit of its truncation tower.

## Implementation notes

Tag 0D62 is stated with two instance hypotheses that the source does not have: that the functor
whose right derived functor assembles the sections over all opens is derivable, and that the
truncation tower has a product in `D(𝒪_X)`. Neither is needed here, both being theorems for
sheaves of modules on a ringed space. The first is
`Stacks.Cohomology.MayerVietoris.hasPointwiseRightDerivedFunctor_of_homotopyCategory`, which
holds for every functor out of the homotopy category because `SheafOfModules O` is Grothendieck
abelian and therefore has K-injective resolutions (Tag 079P); the second is
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, which gets
countable products in `D(𝒪_X)` from those same resolutions rather than from the exactness of
products assumed in Tag 07KC, which sheaves of modules do not satisfy. They are supplied below
as file-local instances, so the statement carries exactly the hypotheses of the source.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
* [Stacks Project, Tag 0D63](https://stacks.math.columbia.edu/tag/0D63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.CohomologyPresheaf

universe wX wP u

namespace Stacks.Cohomology.DerivedLimitStalk

/-- The functor whose right derived functor assembles the sections over all opens has a right
derived functor. -/
local instance hasRightDerivedFunctor_homotopySectionsPresheaf {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)] :
    (homotopySectionsPresheaf O).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  have := Stacks.Cohomology.MayerVietoris.hasPointwiseRightDerivedFunctor_of_homotopyCategory
    O (homotopySectionsPresheaf O)
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- The derived category of sheaves of modules on a ringed space has countable products. -/
local instance hasProductsOfShape_nat_derivedCategory {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)] :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{u} O)) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{wX, u, u, u, u} O

/-- Let `E` be an object of the derived category of sheaves of `𝒪_X`-modules on a ringed space, and
suppose every point `x` carries an integer `dₓ ≥ 0` and a fundamental system `𝔘ₓ` of open
neighbourhoods on whose members `Hᵖ(U, Hᵠ(E))` vanishes whenever `p > dₓ` and `q < 0`. Then the
canonical map from `E` to a derived limit of its tower of truncations `τ_{≥ -n} E` from below is an
isomorphism. -/
@[stacks 0D63]
public theorem isIso_to_isDerivedLimit_truncGETower_of_local_bound {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hvanishing : ∀ x : X, ∃ (d : ℕ) (𝔘 : Set (Opens X)),
      (nhds x).HasBasis (fun U : Opens X ↦ U ∈ 𝔘) (fun U ↦ (U : Set X)) ∧
        ∀ U ∈ 𝔘, ∀ (p : ℕ) (q : ℤ), (d : ℤ) < (p : ℤ) → q < 0 →
          IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
            (cohomologyPresheaf O
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
                ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj E))
              (p : ℤ))))
    (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (hc : ∀ n : ℕ, c ≫ pr ≫ Pi.π
      (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  refine isIso_to_isDerivedLimit_truncGETower_of_local_vanishing.{wX, wP, u} O E ?_ L c pr hL hc
  intro x
  obtain ⟨d, 𝔘, hbasis, hvan⟩ := hvanishing x
  refine ⟨fun m ↦ (d : ℤ) + max 0 m, 𝔘, hbasis, ?_⟩
  intro U hU p m hm
  replace hm : (d : ℤ) + max 0 m < (p : ℤ) := hm
  have hm₀ : (0 : ℤ) ≤ max 0 m := le_max_left _ _
  have hm₁ : m ≤ max 0 m := le_max_right _ _
  exact hvan U hU p (m - (p : ℤ)) (by omega) (by omega)

end Stacks.Cohomology.DerivedLimitStalk

end
