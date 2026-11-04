module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.PowerSummands
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The Leray--Hirsch morphism of a projective bundle

Let `g : X ⟶ S` be a morphism of schemes, `ℰ` a quasi-coherent `𝒪_X`-module and
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle (`Stacks.RelativeProj.projectiveBundle`), with
tautological invertible module `𝒪_P(1)` (`Stacks.RelativeProj.tautologicalDatumTwist`). This file
names the objects of Proposition 0FMT and Remark 0FUN:

* `c₁^{dR}(𝒪_P(1)) ∈ H^2_{dR}(P/S)`, the de Rham first Chern class of `𝒪_P(1)` relative to `S`;
* the morphism `ξ̃ : ⨁_{0 ≤ t < r} Ω^•_{X/S}[-2t] ⟶ Rp_*Ω^•_{P/S}` of Proposition 0FMR for the
  classes `c₁^{dR}(𝒪_P(1))^t`.

The computations of Remark 0FUN hold for any class and are in
`StacksFrontier/AlgebraicGeometry/DeRham/LerayHirsch/PowerSummands.lean`.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.projectiveBundleChernClass`: `c₁^{dR}(𝒪_P(1))`.
* `AlgebraicGeometry.DeRhamLerayHirsch.projectiveBundleLerayHirschMorphism`: `ξ̃`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules) [E.IsQuasicoherent]

/-- **The de Rham first Chern class `c₁^{dR}(𝒪_P(1)) ∈ H^2_{dR}(P/S)`** of the tautological
invertible module of the projective bundle `p : P = 𝐏(ℰ) ⟶ X`, relative to `S` through
`p ≫ g`. -/
abbrev projectiveBundleChernClass :
    SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))
      (SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))) ((2 : ℕ) : ℤ) :=
  SheafOfModules.deRhamCohomologyFirstChernClass (X := (projectiveBundle X E).toRingedSpace)
    (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (projectiveBundleToBase X E ≫ g)))
    (tautologicalDatumTwist E)
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ (tautologicalDatumTwist E)
      (isInvertible_tautologicalDatumTwist E))

/-- **The morphism `ξ̃ : ⨁_{0 ≤ t < r} Ω^•_{X/S}[-2t] ⟶ Rp_*Ω^•_{P/S}`** of Proposition 0FMR for
the projective bundle `p : P = 𝐏(ℰ) ⟶ X` and the classes `c₁^{dR}(𝒪_P(1))^t`, `0 ≤ t < r`. -/
abbrev projectiveBundleLerayHirschMorphism (r : ℕ) :
    (⨁ fun t : Fin r => (deRhamObject g)⟦-((2 * (t : ℕ) : ℕ) : ℤ)⟧) ⟶
      (relativeDirectImage (projectiveBundleToBase X E) g).obj
        (deRhamObject (projectiveBundleToBase X E ≫ g)) :=
  lerayHirschPowerMorphism (projectiveBundleToBase X E) g 2 (projectiveBundleChernClass g E) r

end AlgebraicGeometry.DeRhamLerayHirsch

end
