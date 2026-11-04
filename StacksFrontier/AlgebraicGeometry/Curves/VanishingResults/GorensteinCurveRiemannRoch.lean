module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDualityZero
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Curves.LocallyFreeDualizingDuality
import StacksCore.Tactic.StacksAttribute

/-!
# Riemann--Roch on a proper Gorenstein curve

Let `X` be a proper scheme over a field `k` which is Gorenstein and equidimensional of dimension
one, and let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of [Stacks, Tag 0BS2]. This
file proves clauses (2) and (3) of [Stacks, Tag 0BS6]; clause (1) is
`Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein`: **clause (2)**,
  `deg(ω_X) = -2 χ(X, 𝒪_X)`.
* `eulerCharacteristic_eq_curveDegree_sub_half_of_isGorenstein`: the Riemann--Roch formula
  `χ(X, ℰ) = deg(ℰ) - ½ rank(ℰ) deg(ω_X)`.
* `finrank_derivedCohomologyOverField_eq_one_sub_dualTensorDualizingSheafOverField`: the duality
  of dimensions `dim_k H^i(X, ℰ) = dim_k H^{1-i}(X, ℰ^∨ ⊗ ω_X)` for all `i ∈ ℤ`, on a
  Cohen--Macaulay curve.
* `eulerCharacteristic_eq_and_finrank_cohomology_eq_of_isGorenstein`: **clause (3)**, the two
  together.

## The argument

The degree of [Stacks, Tag 0AYR] at a finite locally free `ℰ` of constant rank `r` is
`deg(ℰ) = χ(X, ℰ) - r χ(X, 𝒪_X)` (`AlgebraicGeometry.curveDegree`), which is equation
[Stacks, Tag 0BRZ] in the spelling of this development. At `ℰ = ω_X`, which has rank one by
clause (1), and with [Stacks, Tag 0BS5] `χ(X, 𝒪_X) = -χ(X, ω_X)` this gives clause (2); putting
clause (2) back into the definition of `deg(ℰ)` gives the Riemann--Roch formula.

The duality of dimensions is read in hypercohomology `H^i(X, ℰ[0])`, which is indexed by `ℤ`
as the tag's `i ∈ ℤ` is; for `i ≥ 0` it is sheaf cohomology
(`Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField`).
As in the source it is a consequence of the duality of [Stacks, Tag 0BS4] on a Cohen--Macaulay
curve, `Hom_k(H^{-j}(X, ℰ), k) = H^{1+j}(X, ℰ^∨ ⊗ ω_X)`
(`Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv`), read at `j = -i`:
a vector space and its dual have the same `Module.finrank`. A Gorenstein scheme is
Cohen--Macaulay ([Stacks, Tag 0C00]).

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-! ### Clause (2) -/

/-- **[Stacks, Tag 0BS6], clause (2).** Let `X` be a proper scheme over a field `k` which is
Gorenstein and equidimensional of dimension one, and `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the
dualizing sheaf of [Stacks, Tag 0BS2], which is invertible by clause (1). Then

  `deg(ω_X) = -2 χ(X, 𝒪_X)`,

with `deg` the degree of [Stacks, Tag 0AYR] (`AlgebraicGeometry.curveDegree`, at rank one).
The proof is the source's: `deg(ω_X) = χ(X, ω_X) - χ(X, 𝒪_X)` and
`χ(X, 𝒪_X) = -χ(X, ω_X)` by [Stacks, Tag 0BS5]. -/
@[stacks 0BS6 "(2)"]
public theorem curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein
    (hG : IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (Stacks.Ample.unitModule X).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    letI := (Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein f hG hequi
      hdim).2
    curveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) 1 =
      -2 * eulerCharacteristic k f (Stacks.Ample.unitModule X) := by
  have h := eulerCharacteristic_unit_eq_neg_eulerCharacteristic_dualizingSheafOverField f
    (isCohenMacaulay_of_isGorenstein X) hequi hdim
  simp only [eulerCharacteristic] at h
  simp only [curveDegree, eulerCharacteristic, Nat.cast_one, one_mul]
  show _ - _ = -2 * _
  linarith

/-! ### The Riemann--Roch formula of clause (3) -/

/-- **The Riemann--Roch formula of [Stacks, Tag 0BS6], clause (3).** On a proper Gorenstein
`k`-scheme `X` equidimensional of dimension one, for `ℰ` finite locally free of constant rank
`r`,

  `χ(X, ℰ) = deg(ℰ) - ½ r deg(ω_X)`,

an identity of rational numbers. It is the definition `deg(ℰ) = χ(X, ℰ) - r χ(X, 𝒪_X)` of
[Stacks, Tag 0AYR] together with clause (2). -/
public theorem eulerCharacteristic_eq_curveDegree_sub_half_of_isGorenstein
    (hG : IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI : E.IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E r
    letI := (Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein f hG hequi
      hdim).2
    (eulerCharacteristic k f E : ℚ) =
      (curveDegree k f hdim.le E r : ℚ) -
        1 / 2 * (r : ℚ) *
          (curveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) 1 : ℚ) := by
  have h2 := curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein f hG hequi hdim
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E r
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (Stacks.Ample.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hE : curveDegree k f hdim.le E r =
      eulerCharacteristic k f E - (r : ℤ) * eulerCharacteristic k f (Stacks.Ample.unitModule X) :=
    rfl
  rw [hE, h2]
  push_cast
  ring

/-! ### The duality of dimensions of clause (3) -/

/-- **The duality of dimensions of [Stacks, Tag 0BS6], clause (3).** On a proper `k`-scheme `X`
which is Cohen--Macaulay and equidimensional of dimension one, for `ℰ` finite locally free,

  `dim_k H^i(X, ℰ) = dim_k H^{1-i}(X, ℰ^∨ ⊗ ω_X)` for all `i ∈ ℤ`,

with `H^i(X, -)` the hypercohomology of a module placed in degree zero, which is sheaf
cohomology for `i ≥ 0`. As in the source this is a consequence of the
duality of [Stacks, Tag 0BS4],
`Hom_k(H^{-j}(X, ℰ), k) = H^{1+j}(X, ℰ^∨ ⊗ ω_X)`
(`Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv`), at `j = -i`, a vector
space and its dual having the same `Module.finrank`. -/
public theorem finrank_derivedCohomologyOverField_eq_one_sub_dualTensorDualizingSheafOverField
    (hcm : IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (i : ℤ) :
    Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj E) i) =
      Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (dualTensorDualizingSheafOverField f E)) (1 - i)) := by
  have e := Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv
    (hE := by exact ‹SheafOfModules.IsFiniteLocallyFree.{u, u, u} E›) E f hcm hequi hdim (-i)
  rw [neg_neg, ← sub_eq_add_neg] at e
  exact Subspace.dual_finrank_eq.symm.trans e.finrank_eq

/-! ### Clause (3) -/

/-- **[Stacks, Tag 0BS6], clause (3).** Let `X` be a proper scheme over a field `k` which is
Gorenstein and equidimensional of dimension one, `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing
sheaf of [Stacks, Tag 0BS2] (invertible by clause (1)), and `ℰ` a finite locally free
`𝒪_X`-module of constant rank `r`. Then

  `χ(X, ℰ) = deg(ℰ) - ½ rank(ℰ) deg(ω_X)`

with `deg` the degree of [Stacks, Tag 0AYR], and

  `dim_k H^i(X, ℰ) = dim_k H^{1-i}(X, ℰ^∨ ⊗_{𝒪_X} ω_X)` for all `i ∈ ℤ`,

with `H^i(X, -)` the hypercohomology of a module placed in degree zero, which is sheaf cohomology
for `i ≥ 0`. -/
@[stacks 0BS6 "(3)"]
public theorem eulerCharacteristic_eq_and_finrank_cohomology_eq_of_isGorenstein
    (hG : IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI : E.IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E r
    letI := (Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein f hG hequi
      hdim).2
    (eulerCharacteristic k f E : ℚ) =
        (curveDegree k f hdim.le E r : ℚ) -
          1 / 2 * (r : ℚ) *
            (curveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) 1 : ℚ) ∧
      ∀ i : ℤ, Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
          ((DerivedCategory.singleFunctor X.Modules 0).obj E) i) =
        Module.finrank k (Stacks.Duality.derivedCohomologyOverField f
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (dualTensorDualizingSheafOverField f E)) (1 - i)) := by
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  exact ⟨eulerCharacteristic_eq_curveDegree_sub_half_of_isGorenstein f hG hequi hdim E r,
    finrank_derivedCohomologyOverField_eq_one_sub_dualTensorDualizingSheafOverField f
      (isCohenMacaulay_of_isGorenstein X) hequi hdim E⟩

end AlgebraicGeometry

end
