module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimits

/-!
# Convergence of the truncation tower on an algebraic space, with no hypothesis

Let `S` be a scheme of a big fppf site, let `X` be an algebraic space over `S` and let `E` be an
object of `D_QCoh(𝒪_X)`.  [Stacks, Tag 08F6] asserts that the canonical map from `E` to a derived
limit of the tower `n ↦ τ_{≥ -n} E` of canonical truncations from below is an isomorphism.

`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` proves this with the source's two
citations carried as named hypotheses.  **Both are now theorems**, so this file states the tag
with no hypothesis beyond the membership of `E` in `D_QCoh(𝒪_X)`:

* `hcover`, that the affine étale charts cover the small étale site, is
  `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`;
* `h03DW`, that a quasi-coherent module has no higher cohomology on an affine étale chart, is
  `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_unconditional`:
  **[Stacks, Tag 08F6]**, with both of the source's citations discharged.

## Implementation notes

The module universe is `u`, the universe of the structure rings.  That is where the two
discharged inputs live: `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`
rests on Descent, Proposition [Stacks, Tag 03DX] (2) for the small étale site of an algebraic
space, which this library has for `AlgebraicGeometry.Space.Modules.{u, u}`.  The conditional form
is stated at a free module universe `m` and is not superseded: this file instantiates it at
`m = u` and discharges the two hypotheses there.

Enough injectives of the `𝒪_X`-modules, which the conditional form takes as an instance
argument, is `AlgebraicGeometry.Space.enoughInjectives_modules` at this module universe.

## References

* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks Project, Tag 08F6, with no hypothesis.**  Let `S` be a scheme, let `X` be an
algebraic space over `S` and let `E` be an object of `D_QCoh(𝒪_X)`.  Then the canonical map from
`E` to a derived limit `L` of the tower `n ↦ τ_{≥ -n} E` of canonical truncations from below is
an isomorphism.

This is `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` with its two named
hypotheses discharged: `hcover` by
`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart` and `h03DW` by
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`.  As there, the derived
limit is presented by its structural morphism `p` to the product of the tower together with the
distinguished triangle `hL` characterising it, and the map `c` out of `E` is the canonical one
because its composites with the product projections are required to be the truncation maps. -/
@[stacks 08F6 "the source's statement, with both of its citations discharged: the affine étale \
charts cover the small étale site (04JS, at the index universe HasEnoughObjects asks for) and a \
quasi-coherent module has no higher cohomology on an affine étale chart (the étale-site analogue \
of 01XB that the source cites 03DW for).  The module universe is the universe of the structure \
rings"]
theorem isIso_of_isDerivedLimit_truncGETower_unconditional
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) q).obj E).IsQuasicoherentOnSite)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩]
    (L : DerivedCategory (Modules.{u, u} B S hS F hF))
    (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
          (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower
            (Modules.{u, u} B S hS F hF) E).map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (Modules.{u, u} B S hS F hF) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  let := enoughInjectives_modules B S hS F hF
  exact isIso_of_isDerivedLimit_truncGETower B S hS F hF E hE
    (hasEnoughObjects_isAffineChart B S hS F)
    (fun U hU M hM r hr ↦
      isZero_rightDerived_evaluation_of_isAffineChart B S hS F hF M hM U hU r hr)
    L c p δ hL hc

end AlgebraicGeometry.Space

end
