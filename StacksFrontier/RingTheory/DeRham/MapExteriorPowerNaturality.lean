module

public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# Restriction of differential forms is natural in the target ring

Let `R → A` be a ring map.  Restriction of differential forms along a map of `R`-algebras
`A → B`,

`⋀^p Ω[A⁄R] → ⋀^p_B Ω[B⁄R]`,

is `KaehlerDifferential.mapExteriorPower`.  This file records its naturality in the target
ring: a tower `A → B → C` of `R`-algebras factors the restriction to `C` through the
restriction to `B`, so the kernel of the former contains the kernel of the latter; and two
targets that are isomorphic as `A`-algebras therefore have *equal* kernels, as submodules of
`⋀^p Ω[A⁄R]` and not merely isomorphic ones.

The equality of kernels is what identifies the two readings of the term `Ω^•_{Y/S}` of the
residue sequence of [Stacks, Tag 0FMW] at a point of the divisor.  At a point `y` of an
effective Cartier divisor `Y ⊆ X` with local equation `t`, the affine statement is written over
the target `𝒪_{X, y} ⧸ (t)` — that is the ring whose kernel of restriction
`Stacks.LogPoles.ker_mapExteriorPower_quotient_succ` computes — while the stalk of the de Rham
complex of `Y` is written over the target `𝒪_{Y, y}`.  The ring isomorphism between the two is
`AlgebraicGeometry.Scheme.Hom.quotientSpanGermEquivStalk`, and
`KaehlerDifferential.ker_mapExteriorPower_eq_of_algEquiv` is what transports the kernel along
it.

## Main results

* `KaehlerDifferential.map_map`: the functoriality of Kähler differentials composes along a
  tower `A → B → C` of `R`-algebras.
* `KaehlerDifferential.mapExteriorPower_comp`: **restriction of forms is functorial in the
  target ring**, that is restriction to `C` is restriction to `B` followed by restriction
  from `B` to `C`.
* `KaehlerDifferential.ker_mapExteriorPower_le` and
  `KaehlerDifferential.ker_mapExteriorPower_le_of_algHom`: the kernel of restriction grows with
  the target, along a tower and along an arbitrary map of `A`-algebras respectively.
* `KaehlerDifferential.ker_mapExteriorPower_eq_of_algEquiv`: **two `A`-algebra targets that are
  isomorphic have the same kernel of restriction.**

## Implementation notes

`KaehlerDifferential.ker_mapExteriorPower_le_of_algHom` names no algebra of `C` over `B` in its
statement: that algebra is read off the given map of `A`-algebras inside the proof, where
`IsScalarTower.of_algebraMap_eq` supplies the two towers it needs.  This is what lets the
isomorphism version be applied in both directions, with the two algebras coming from the
isomorphism and from its inverse, neither of which can be a binder of the statement.

`KaehlerDifferential.map_map` has a `private` sibling in
`StacksFrontier/FieldTheory/KaehlerDifferential/Separable.lean` (line 67), stated for three fields
`k ⊆ A ⊆ B` over the base `ℤ`; being `private` it is unavailable here, and it is the special
case of the statement below.  The one here is in no universe or field restriction, so it
subsumes that one, which is left where it is: the exterior-power statements of this file need
all four rings in one universe, while the sibling's three fields need not be, so the two sit in
different sections rather than in different files.

No surjectivity, finiteness or regularity is used anywhere in this file, and the degree `p` is
arbitrary.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose quotient term is
  the consumer of the naturality proved here
-/

@[expose] public noncomputable section

universe u

namespace KaehlerDifferential

section Differentials

variable (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A B C]

/-- **The functoriality of Kähler differentials composes along a tower.** For a tower
`A → B → C` of `R`-algebras, the map `Ω[A⁄R] → Ω[C⁄R]` is the map `Ω[A⁄R] → Ω[B⁄R]` followed by
the map `Ω[B⁄R] → Ω[C⁄R]`.  Both sides are determined by their values on the image of `D`,
where the identity is the compatibility `algebraMap B C ∘ algebraMap A B = algebraMap A C` of
the tower. -/
theorem map_map (x : Ω[A⁄R]) : map R R B C (map R R A B x) = map R R A C x := by
  have key : (map R R B C).restrictScalars A ∘ₗ map R R A B = map R R A C := by
    refine LinearMap.ext_on (span_range_derivation R A) ?_
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D]
    rw [IsScalarTower.algebraMap_apply A B C]
  exact LinearMap.congr_fun key x

end Differentials

section Tower

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A B C]

/-- **Restriction of differential forms is functorial in the target ring.** For a tower
`A → B → C` of `R`-algebras, restriction of `p`-forms from `A` to `C` is restriction from `A`
to `B` followed by restriction from `B` to `C`. -/
theorem mapExteriorPower_comp (p : ℕ) :
    (mapExteriorPower R B C p).restrictScalars A ∘ₗ mapExteriorPower R A B p =
      mapExteriorPower R A C p := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span A p (Ω[A⁄R])) ?_
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    mapExteriorPower_ιMulti]
  exact congrArg (fun w ↦ exteriorPower.ιMulti C p w) (funext fun i ↦ map_map R A B C (v i))

/-- **The kernel of restriction grows with the target along a tower.** A `p`-form on `Spec A`
restricting to zero on `Spec B` restricts to zero on `Spec C` for any `B`-algebra `C`. -/
theorem ker_mapExteriorPower_le (p : ℕ) :
    LinearMap.ker (mapExteriorPower R A B p) ≤ LinearMap.ker (mapExteriorPower R A C p) := by
  intro x hx
  rw [LinearMap.mem_ker, ← LinearMap.congr_fun (mapExteriorPower_comp R A B C p) x,
    LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

end Tower

section AlgHom

variable (R A : Type u) {B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [Algebra A C]
  [IsScalarTower R A B] [IsScalarTower R A C]

/-- **Naturality of the restriction of differential forms in the target ring.** A map of
`A`-algebras `B → C` enlarges the kernel of restriction: a `p`-form on `Spec A` restricting to
zero on `Spec B` restricts to zero on `Spec C`.  No algebra structure on `C` over `B` is named
in the statement; it is the one carried by the given map. -/
theorem ker_mapExteriorPower_le_of_algHom (f : B →ₐ[A] C) (p : ℕ) :
    LinearMap.ker (mapExteriorPower R A B p) ≤ LinearMap.ker (mapExteriorPower R A C p) := by
  let _ : Algebra B C := f.toRingHom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A C r, IsScalarTower.algebraMap_apply R A B r]
    exact (f.commutes _).symm
  exact ker_mapExteriorPower_le R A B C p

/-- **Isomorphic targets have the same kernel of restriction.** If two `A`-algebras `B` and `C`
are isomorphic as `A`-algebras, then a `p`-form on `Spec A` restricts to zero on `Spec B`
exactly when it restricts to zero on `Spec C`, as an equality of submodules of `⋀^p Ω[A⁄R]`.

This is the naturality in the target ring that identifies the quotient term of the residue
sequence of [Stacks, Tag 0FMW] written over `A ⧸ (t)` with the same term written over a ring
only isomorphic to `A ⧸ (t)`, such as the local ring of the divisor at a point. -/
theorem ker_mapExteriorPower_eq_of_algEquiv (e : B ≃ₐ[A] C) (p : ℕ) :
    LinearMap.ker (mapExteriorPower R A B p) = LinearMap.ker (mapExteriorPower R A C p) :=
  le_antisymm (ker_mapExteriorPower_le_of_algHom R A e.toAlgHom p)
    (ker_mapExteriorPower_le_of_algHom R A e.symm.toAlgHom p)

end AlgHom

end KaehlerDifferential

end
