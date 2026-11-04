module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowersPerfect

/-!
# Numerical invariants along the products of integer tensor powers (Situation 0DNC for `ℤ^{⊕ r}`)

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation and let
`E_1, …, E_r` be perfect objects of `D(𝒪_X)`.  Stacks 0DNE considers the index set
`I = ℤ^{⊕ r}` and the map

`I ⟶ D(𝒪_X)`,  `(n_1, …, n_r) ↦ E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`,

where `⊗` is the derived tensor product and a negative power is a power of the dual
`E^∨ = R𝓗om(E, 𝒪_X)`.  Every value of this map is perfect, so together with a map
`P : ℤ^{⊕ r} ⟶ ℤ` it is an instance of the standing data of Situation 0DNC, and the substack
`Coh^P_{X/B} ⊆ Coh_{X/B}` of Stacks 0DNE is the substack of Situation 0DNC for these data: an
object `(T, 𝓕)` lies in it when

`χ(X_t, (E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_t ⊗^𝐋 𝓕_t) = P(n_1, …, n_r)`

for every `n ∈ ℤ^{⊕ r}` and every `t ∈ T`.  This file constructs those standing data.

The declarations listed below live in the `AlgebraicGeometry.Space.NumericalSituation` namespace.

## Main definitions

* `ofDerivedTensorPowerProducts`: the standing data of Situation 0DNC with index set `ℤ^{⊕ r}`,
  the family `n ↦ E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` and the prescribed invariants `P`.

## Main results

* `hasNumericalInvariants_ofDerivedTensorPowerProducts_iff`: an object `(T, 𝓕)` of `Coh_{X/B}`
  lies in `Coh^P_{X/B}` for these data exactly when `χ_n(t) = P(n)` for every `n ∈ ℤ^{⊕ r}` and
  every point `t` of `T`, where `χ_n` is the derived-fibre Euler characteristic of
  `Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)`.

## Implementation notes

The group `ℤ^{⊕ r}` is `Fin r → ℤ`.  The objects `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` are
`AlgebraicGeometry.Space.derivedTensorPowerProduct`, and their perfectness is
`AlgebraicGeometry.Space.isPerfect_derivedTensorPowerProduct`.  The module universe of the data is
the universe of the schemes, which is the universe at which the derived tensor product, the
derived dual and the numerical invariants of Situation 0DNC are formed.  The derived categories
are those of the standard model, the model at which the standing data of Situation 0DNC are
stated.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

/-- **The standing data of Situation 0DNC for Stacks 0DNE.**  Over a separated morphism `f` of
finite presentation, the index set `ℤ^{⊕ r}`, the family of perfect objects
`n ↦ E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` of `D(𝒪_X)` attached to perfect objects `E_1, …, E_r`, and
the prescribed invariants `P : ℤ^{⊕ r} ⟶ ℤ`. -/
def ofDerivedTensorPowerProducts (hf : IsSeparated B S hS D.f.hom) {r : ℕ}
    (E : Fin r → DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2))
    (hE : ∀ j, (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
    (P : (Fin r → ℤ) → ℤ) : NumericalSituation.{u, 0, u} B S hS D where
  separated := hf
  I := Fin r → ℤ
  E := derivedTensorPowerProduct B S hS D.X.1 D.X.2 E
  perfect := isPerfect_derivedTensorPowerProduct E hE
  P := P

variable (hf : IsSeparated B S hS D.f.hom) {r : ℕ}
    (E : Fin r → DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2))
    (hE : ∀ j, (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
    (P : (Fin r → ℤ) → ℤ)

/-- The index set of the data of Stacks 0DNE is `ℤ^{⊕ r}`. -/
@[simp]
theorem ofDerivedTensorPowerProducts_I : (ofDerivedTensorPowerProducts hf E hE P).I = (Fin r → ℤ) :=
  rfl

/-- The perfect object attached to `n ∈ ℤ^{⊕ r}` is `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`. -/
@[simp]
theorem ofDerivedTensorPowerProducts_E (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf E hE P).E n =
      derivedTensorPowerProduct B S hS D.X.1 D.X.2 E n :=
  rfl

/-- The prescribed invariant attached to `n ∈ ℤ^{⊕ r}` is `P n`. -/
@[simp]
theorem ofDerivedTensorPowerProducts_P (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf E hE P).P n = P n :=
  rfl

/-- **The objects of `Coh^P_{X/B}` for the data of Stacks 0DNE.**  An object `(T, 𝓕)` of
`Coh_{X/B}` lies in `Coh^P_{X/B}` exactly when, for every `n ∈ ℤ^{⊕ r}` and every point `t` of
`T`, the derived-fibre Euler characteristic at `t` of
`Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)` is `P n`. -/
theorem hasNumericalInvariants_ofDerivedTensorPowerProducts_iff (A : CoherentObject D) :
    (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants A ↔
      ∀ (n : Fin r → ℤ) (t : points B S hS (testSpace A).1),
        derivedFibreEuler (testSpace A)
          ((ofDerivedTensorPowerProducts hf E hE P).numericalDirectImage A n) t = P n :=
  Iff.rfl

end NumericalSituation

end AlgebraicGeometry.Space

end
