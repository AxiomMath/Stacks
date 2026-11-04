module

public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.Cotangent.EtaleVanishingUnconditional
public import StacksFrontier.Cotangent.LocalizationSquareQuasiIso
public import StacksFrontier.Homology.ExtendScalars.FlatHomologyAdjoint

/-!
# The cohomology of the cotangent complex under an étale map of algebras

Let `A → A'`, `B → B'` be a commutative square of ring maps. Its functoriality map of Tag 08PN,
read through extension of scalars along `B → B'`, is the `B'`-linear map
`B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` (`CommAlgCat.squareCotangentExtendScalarsMap`). This file proves
that it is a quasi-isomorphism as soon as `L_{B'/B} = 0` and `L_{A'/A} = 0`, in particular when
`B → B'` is étale and `A → A'` is bijective, and deduces the statement on cohomology modules that
the étale localization of the cotangent complex rests on:

`B' ⊗_B H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`,  `b' ⊗ m ↦ b' · m`,

is bijective when moreover `B → B'` is flat. This is how `H^i(L_{X/A})` is seen to be
quasi-coherent: on affine étale charts `U = Spec B' ⟶ W = Spec B` of an `A`-scheme, the cohomology
of the cotangent complex of `B'` is that of `B` tensored up to `B'`.

## Main definitions

* `CommAlgCat.squareHomologyMap`: the `B`-linear map `H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})` of the
  square.
* `CommAlgCat.squareHomologyExtendScalarsMap`: its `B'`-linear adjoint
  `B' ⊗_B H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`.

## Main results

* `CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_isZero`: the adjoint functoriality map
  is a quasi-isomorphism when `L_{B'/B} = 0` and `L_{A'/A} = 0`.
* `CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_etale`: the same for `B → B'` étale and
  `A → A'` bijective.
* `CommAlgCat.isIso_squareHomologyExtendScalarsMap`: for `B → B'` flat, the adjoint map on
  cohomology is an isomorphism whenever the adjoint map of complexes is a quasi-isomorphism; this
  is `ModuleCat.isIso_homologyExtendScalarsAdjoint` of
  `StacksFrontier/Homology/ExtendScalars/FlatHomologyAdjoint.lean`.
* `CommAlgCat.isIso_squareHomologyExtendScalarsMap_of_etale`: the case of `B → B'` étale and
  `A → A'` bijective.
* `CommAlgCat.squareHomologyExtendScalarsMap_tmul`: it sends `b' ⊗ m` to `b' · m`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ChangeOfRings

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable {A A' : Type u} [CommRing A] [CommRing A'] {B : CommAlgCat.{u} A}
  {B' : CommAlgCat.{u} A'}

/-- **The adjoint functoriality map of a square with vanishing relative cotangent complexes is a
quasi-isomorphism.** In the commutative square `A → A'`, `B → B'`, if `L_{B'/B} = 0` and
`L_{A'/A} = 0`, then `B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` is a quasi-isomorphism: it factors as the first
morphism `B' ⊗_B L_{B/A} ⟶ L_{B'/A}` of the fundamental triangle of `A → B → B'`, whose third
vertex `L_{B'/B}` vanishes, followed by the change of base ring `L_{B'/A} ⟶ L_{B'/A'}` along a map
with vanishing cotangent complex. -/
theorem quasiIso_squareCotangentExtendScalarsMap_of_isZero
    (sq : AlgebraSquare.{u, u, u} A A' B B')
    (hB : letI : Algebra (B : Type u) (B' : Type u) := sq.map.toAlgebra
      IsZero (cotangentComplexDerived.{u, u} (B : Type u)
        (CommAlgCat.of (B : Type u) (B' : Type u))))
    (hA : letI : Algebra A A' := sq.base.toAlgebra
      IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A A'))) :
    QuasiIso (squareCotangentExtendScalarsMap sq) := by
  let iAA' : Algebra A A' := sq.base.toAlgebra
  let iBB' : Algebra B B' := sq.map.toAlgebra
  let iAB' : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq fun a => (sq.map_algebraMap a).symm
  let b : (B : Type u) →ₐ[A] (B' : Type u) := IsScalarTower.toAlgHom A B B'
  have hE : QuasiIso (cotangentExtendScalarsComplexMap (A := A) (A' := A)
      (B := CommAlgCat.of A B) (B' := CommAlgCat.of A B') b) := by
    have h₁ : IsIso (fundamentalMor₁.{u} A (B : Type u) (B' : Type u)) :=
      (Triangle.isZero₃_iff_isIso₁ _
        (productFundamentalTriangle_distinguished A (B : Type u) (B' : Type u))).1 hB
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) (B' : Type u)).hom _ _ h₁
  have hR := quasiIso_cotangentComplexBaseRingMap_of_isZero A A' (B' : Type u) hA
  have heq : squareCotangentExtendScalarsMap sq =
      cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
          (B' := CommAlgCat.of A B') b ≫
        cotangentComplexBaseRingMap A A' (B' : Type u) := by
    rw [cotangentExtendScalarsComplexMap_eq_counit]
    exact squareCotangentComplexMap_comp_counit
      (algebraSquareOfAlgHom (A := A) (A' := A) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of A B') b) (displaySquare₂ A A' (B' : Type u))
  rw [heq]
  exact quasiIso_comp _ _ (hφ := hE) (hφ' := hR)

/-- **The adjoint functoriality map of a square with étale right side and bijective base is a
quasi-isomorphism.** For `B → B'` étale, `L_{B'/B} = 0` (Tag 08R2, item (5)); for `A → A'`
bijective, `L_{A'/A} = 0`. -/
theorem quasiIso_squareCotangentExtendScalarsMap_of_etale
    (sq : AlgebraSquare.{u, u, u} A A' B B') (hB : sq.map.Etale)
    (hA : Function.Bijective sq.base) :
    QuasiIso (squareCotangentExtendScalarsMap sq) := by
  refine quasiIso_squareCotangentExtendScalarsMap_of_isZero sq ?_ ?_
  · let : Algebra (B : Type u) (B' : Type u) := sq.map.toAlgebra
    have : Algebra.Etale (B : Type u) (B' : Type u) := hB
    exact isZero_cotangentComplexDerived_of_etale_unconditional (B : Type u) (B' : Type u)
  · let : Algebra A A' := sq.base.toAlgebra
    exact isZero_cotangentComplexDerived_of_bijective A A' hA

/-! ### Cohomology -/

variable (sq : AlgebraSquare.{u, u, u} A A' B B') (i : ℤ)

/-- **The map of a square on cohomology**, `H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`, as a `B`-linear map:
the cohomology of `CommAlgCat.squareCotangentComplexMap`, followed by the identification of the
cohomology of the restriction of scalars of `L_{B'/A'}` with the restriction of scalars of its
cohomology. -/
abbrev squareHomologyMap :
    (cotangentComplex.{u, u} A B).homology i ⟶
      (ModuleCat.restrictScalars sq.map).obj ((cotangentComplex.{u, u} A' B').homology i) :=
  ModuleCat.homologyRestrictScalarsMap sq.map (squareCotangentComplexMap.{u, u, u} sq) i

/-- **The `B'`-linear adjoint of the map of a square on cohomology**,
`B' ⊗_B H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`, `b' ⊗ m ↦ b' · m`. -/
abbrev squareHomologyExtendScalarsMap :
    (ModuleCat.extendScalars sq.map).obj ((cotangentComplex.{u, u} A B).homology i) ⟶
      (cotangentComplex.{u, u} A' B').homology i :=
  ModuleCat.homologyExtendScalarsAdjoint sq.map (squareCotangentComplexMap.{u, u, u} sq) i

/-- The adjoint map on cohomology sends `b' ⊗ m` to `b' · m`. -/
theorem squareHomologyExtendScalarsMap_tmul (b' : (B' : Type u))
    (m : (cotangentComplex.{u, u} A B).homology i) :
    squareHomologyExtendScalarsMap sq i (b' ⊗ₜ[B, sq.map] m) =
      b' • (squareHomologyMap sq i m : ToType ((cotangentComplex.{u, u} A' B').homology i)) :=
  ModuleCat.homologyExtendScalarsAdjoint_tmul sq.map _ i b' m

/-- **Flat base change of the cohomology of the cotangent complex.** For a commutative square
`A → A'`, `B → B'` with `B → B'` flat, if the adjoint functoriality map
`B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` is a quasi-isomorphism, then
`B' ⊗_B H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`, `b' ⊗ m ↦ b' · m`, is an isomorphism. -/
theorem isIso_squareHomologyExtendScalarsMap (hflat : sq.map.Flat)
    (hq : QuasiIso (squareCotangentExtendScalarsMap sq)) :
    IsIso (squareHomologyExtendScalarsMap sq i) :=
  ModuleCat.isIso_homologyExtendScalarsAdjoint sq.map _ i hflat hq

/-- **Étale base change of the cohomology of the cotangent complex.** For a commutative square
`A → A'`, `B → B'` with `A → A'` bijective and `B → B'` étale, the map
`B' ⊗_B H^i(L_{B/A}) ⟶ H^i(L_{B'/A'})`, `b' ⊗ m ↦ b' · m`, is an isomorphism. -/
theorem isIso_squareHomologyExtendScalarsMap_of_etale (hB : sq.map.Etale)
    (hA : Function.Bijective sq.base) :
    IsIso (squareHomologyExtendScalarsMap sq i) := by
  let : Algebra (B : Type u) (B' : Type u) := sq.map.toAlgebra
  have : Algebra.Etale (B : Type u) (B' : Type u) := hB
  have hflat : sq.map.Flat := (inferInstance : Module.Flat (B : Type u) (B' : Type u))
  exact isIso_squareHomologyExtendScalarsMap sq i hflat
    (quasiIso_squareCotangentExtendScalarsMap_of_etale sq hB hA)

end CommAlgCat

end
