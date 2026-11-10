module

public import StacksFrontier.RingTheory.DeRham.MapExteriorPowerNaturality
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso

/-!
# The Poincaré lemma for an algebra isomorphic to a polynomial algebra

Let `R → A` be a ring map with `A` a `ℚ`-algebra and let `B` be an `A`-algebra isomorphic, as an
`A`-algebra, to the polynomial ring `A[X]`. This file proves that the restriction of forms
`Ω^•_{A/R} ⟶ Ω^•_{B/R}` is a quasi-isomorphism. For `B = A[X]` itself this is
`PolynomialDeRham.quasiIso_incl`; the point here is that the statement only depends on `B` up to
isomorphism of `A`-algebras, which is the form in which the functions on the total space of a
trivialized line bundle over an affine open arise.

## Main results

* `KaehlerDifferential.deRhamComplexMap_comp`: the de Rham complex is functorial along a tower
  `A → B → C` of `R`-algebras.
* `KaehlerDifferential.deRhamComplexMap_self`: the map induced by the identity of `A` is the
  identity.
* `KaehlerDifferential.mapExteriorPower_smul_ιMulti_D`: restriction of forms on the generators
  `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)`.
* `KaehlerDifferential.isIso_deRhamComplexMap_of_algEquiv`: an isomorphism of `R`-algebras
  induces an isomorphism of de Rham complexes.
* `PolynomialDeRham.quasiIso_deRhamComplexMap_of_algEquiv`: **the Poincaré lemma for an algebra
  isomorphic to `A[X]`.**

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace KaehlerDifferential

section Functoriality

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The identity of `A` induces the identity on `p`-forms. -/
theorem mapExteriorPower_self (p : ℕ) : mapExteriorPower R A A p = LinearMap.id := by
  have hmap : (map R R A A).restrictScalars A = LinearMap.id :=
    LinearMap.ext_on (span_range_derivation R A) (by rintro _ ⟨a, rfl⟩; simp)
  refine LinearMap.ext_on (exteriorPower.ιMulti_span A p (Ω[A⁄R])) ?_
  rintro _ ⟨v, rfl⟩
  rw [mapExteriorPower_ιMulti, LinearMap.id_apply]
  congr 1
  funext i
  exact LinearMap.congr_fun hmap (v i)

/-- **The identity of `A` induces the identity of `Ω^•_{A/R}`.** -/
theorem deRhamComplexMap_self : deRhamComplexMap R A A = 𝟙 (deRhamComplex R A) := by
  ext p x
  exact LinearMap.congr_fun (mapExteriorPower_self R A p) x

variable (B C : Type u) [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra A B]
  [Algebra A C] [Algebra B C] [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C]
  [IsScalarTower A B C]

/-- **The de Rham complex is functorial along a tower `A → B → C` of `R`-algebras.** -/
theorem deRhamComplexMap_comp :
    deRhamComplexMap R A B ≫ deRhamComplexMap R B C = deRhamComplexMap R A C := by
  ext p x
  exact LinearMap.congr_fun (mapExteriorPower_comp R A B C p) x

/-- **Restriction of forms on a generator**: along `A → B` the form `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)` goes
to `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)` with every `aᵢ` read in `B`. -/
theorem mapExteriorPower_smul_ιMulti_D (B : Type u) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (n : ℕ) (b : Fin (n + 1) → A) :
    mapExteriorPower R A B n (b 0 • exteriorPower.ιMulti A n fun i ↦ D R A (b i.succ)) =
      algebraMap A B (b 0) •
        exteriorPower.ιMulti B n fun i ↦ D R B (algebraMap A B (b i.succ)) := by
  rw [LinearMap.map_smul, mapExteriorPower_ιMulti, algebraMap_smul]
  simp only [map_D]

end Functoriality

/-- **An isomorphism of `R`-algebras induces an isomorphism of de Rham complexes**: for an
`R`-algebra `B` and an `A`-algebra structure on it isomorphic to `A` through `e`, the
restriction `Ω^•_{A/R} ⟶ Ω^•_{B/R}` is invertible. -/
theorem isIso_deRhamComplexMap_of_algEquiv (R : Type u) {A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (e : A ≃ₐ[R] B) (he : algebraMap A B = e.toRingHom) :
    IsIso (deRhamComplexMap R A B) := by
  let : Algebra B A := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq fun r ↦ (e.symm.commutes r).symm
  have : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change a = e.symm (algebraMap A B a)
    rw [he]
    exact (e.symm_apply_apply a).symm
  have : IsScalarTower B A B := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change b = algebraMap A B (e.symm b)
    rw [he]
    exact (e.apply_symm_apply b).symm
  refine ⟨deRhamComplexMap R B A, ?_, ?_⟩ <;>
    rw [deRhamComplexMap_comp, deRhamComplexMap_self]

end KaehlerDifferential

namespace PolynomialDeRham

open KaehlerDifferential

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Algebra ℚ A]

/-- **The Poincaré lemma for an algebra isomorphic to a polynomial algebra.** If `A` is a
`ℚ`-algebra over `R` and `B` is an `A`-algebra isomorphic to `A[X]` as an `A`-algebra, then
`Ω^•_{A/R} ⟶ Ω^•_{B/R}` is a quasi-isomorphism of complexes of `R`-modules: it is the inclusion
`Ω^•_{A/R} ⟶ Ω^•_{A[X]/R}` of `PolynomialDeRham.quasiIso_incl` followed by the isomorphism of
de Rham complexes that `A[X] ≅ B` induces. -/
theorem quasiIso_deRhamComplexMap_of_algEquiv (e : A[X] ≃ₐ[A] B) :
    QuasiIso (deRhamComplexMap R A B) := by
  let : Algebra A[X] B := e.toRingHom.toAlgebra
  have : IsScalarTower A A[X] B := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have : IsScalarTower R A[X] B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R A A[X]]
    exact (e.commutes _).symm
  let e' : A[X] ≃ₐ[R] B :=
    { e.toRingEquiv with
      commutes' := fun r ↦ by
        change e (algebraMap R A[X] r) = algebraMap R B r
        rw [IsScalarTower.algebraMap_apply R A A[X], e.commutes,
          ← IsScalarTower.algebraMap_apply] }
  have := isIso_deRhamComplexMap_of_algEquiv R e' rfl
  rw [← deRhamComplexMap_comp R A A[X] B]
  change QuasiIso (incl R A ≫ deRhamComplexMap R A[X] B)
  infer_instance

end PolynomialDeRham

end
