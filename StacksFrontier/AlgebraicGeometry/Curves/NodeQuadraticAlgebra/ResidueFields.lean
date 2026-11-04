module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.MaximalIdeals
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SeparableTower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The residue fields of the normalization of a node are separable

Let `A` be a nodal Nagata local algebra over a field `k` and let
`A' = integralClosure A (FractionRing A)` be its normalization. Then the residue field of `A'` at
every maximal ideal is separable over `k`.

The route is again the closed fibre. A maximal ideal `m` of `A'` contains `𝔪_A A'`
(`Stacks.Curves.map_maximalIdeal_le_of_isMaximal`), so `A' ⧸ m` is a quotient of the quadratic
algebra `Stacks.Curves.quadraticAlgebra A = A' ⧸ 𝔪_A A'`, which is a separable algebra over the
residue field `κ` of `A` (Stacks Tag 0CBT); a quotient of a separable algebra is separable
(`Stacks.Curves.isSeparable_quotient`), so `A' ⧸ m` is a separable algebraic extension of `κ`.
Nodality gives separability of `κ/k`, and
`Algebra.IsSeparableExtension.trans_of_isSeparable` composes the two steps of the tower
`k ⊆ κ ⊆ A' ⧸ m`.

What remains is the identification of `Ideal.ResidueField m`, which Mathlib defines through
`Localization.AtPrime m`, with `A' ⧸ m`. For a *maximal* ideal that is immediate from the instance
`IsFractionRing (R ⧸ m) (Ideal.ResidueField m)`: a field is its own field of fractions, so the
comparison map is bijective (`Stacks.Curves.residueFieldAlgEquivQuotient`).

## Main definitions

* `Stacks.Curves.residueFieldAlgEquivQuotient` — for a maximal ideal `m` of `R`, the quotient
  `R ⧸ m` is the residue field of `m`, as an algebra over any base of `R`.

## Main results

* `Stacks.Curves.isSeparableExtension_residueField_integralClosure_fractionRing` — the residue
  field at every maximal ideal of the normalization of a nodal Nagata local algebra is separable
  over the ground field.

## Implementation notes

Two things are forced by instance resolution rather than by the mathematics.

`Ideal.Quotient.field` is introduced with `let` rather than `have`, because a field structure is
data: a `have` makes it opaque and the `nonZeroDivisors` of the quotient then elaborates against
a different multiplicative structure than the localization statements expect.

The tower step is stated at an abstract ideal of an abstract algebra
(`Stacks.Curves.isSeparableExtension_of_quotient_algEquiv`) and only then instantiated. Applied
directly to the concrete ideal, synthesis of `IsScalarTower k κ (T ⧸ I)` exhausts the default
budget, because the ideal's term carries the whole description of the normalization; at an
abstract ideal the same synthesis is immediate. The instance itself is present:
`Stacks.Curves.instIsScalarTowerResidueFieldQuadraticAlgebra` for the algebra, and
`Ideal.Quotient.isScalarTower` for its quotients.

No `@[stacks]` tag is carried here.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### The residue field of a maximal ideal is the quotient -/

/-- **The comparison map `R ⧸ m → κ(m)` is bijective for a maximal ideal `m`.** Mathlib's
`Ideal.ResidueField m` is a field of fractions of `R ⧸ m`, and a field is its own field of
fractions. -/
public theorem bijective_algebraMap_residueField_of_isMaximal {R : Type u} [CommRing R]
    (m : Ideal R) [m.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ m) m.ResidueField) := by
  let fld : Field (R ⧸ m) := Ideal.Quotient.field m
  exact (IsFractionRing.self_iff_bijective m.ResidueField).mp
    (IsLocalization.self fun _ hx => isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero hx))

/-- **For a maximal ideal `m` of an algebra `R` over `k`, the residue field of `m` is `R ⧸ m`**,
as a `k`-algebra. -/
public def residueFieldAlgEquivQuotient (k : Type u) {R : Type v} [CommRing k] [CommRing R]
    [Algebra k R] (m : Ideal R) [m.IsMaximal] : (R ⧸ m) ≃ₐ[k] m.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (R ⧸ m) m.ResidueField)
    (bijective_algebraMap_residueField_of_isMaximal m)

/-! ### Separability of a field identified with a separable quotient -/

/-- **A field isomorphic to a quotient of a separable `κ`-algebra, with `κ/k` separable, is
separable over `k`.** The two steps of the tower `k ⊆ κ ⊆ T ⧸ I` are composed by
`Algebra.IsSeparableExtension.trans_of_isSeparable`, and the result transported along the
isomorphism. The quotient being a field is an argument, since it is not an instance, and is
supplied as `IsField` so that the field structure built from it is the quotient's own. -/
public theorem isSeparableExtension_of_quotient_ringEquiv {k κ T L : Type*} [Field k] [Field κ]
    [CommRing T] [Field L] [Algebra k κ] [Algebra κ T] [Algebra k T] [IsScalarTower k κ T]
    [Algebra k L] [Algebra.IsSeparableExtension k κ] (I : Ideal T)
    (hfld : IsField (T ⧸ I)) (hsep : Algebra.IsSeparable κ (T ⧸ I)) (e : (T ⧸ I) ≃+* L)
    (he : ∀ c : k, e (algebraMap k (T ⧸ I) c) = algebraMap k L c) :
    Algebra.IsSeparableExtension k L := by
  let fld : Field (T ⧸ I) := hfld.toField
  have htower : Algebra.IsSeparableExtension k (T ⧸ I) :=
    Algebra.IsSeparableExtension.trans_of_isSeparable k κ (T ⧸ I)
  exact Algebra.IsSeparableExtension.of_algEquiv { __ := e, commutes' := he }

/-! ### Separability of the residue fields of the normalization -/

/-- **The residue field at every maximal ideal of the normalization of a nodal Nagata local
algebra is separable over the ground field.** -/
@[stacks 0C4A "residue field extensions"]
public theorem isSeparableExtension_residueField_integralClosure_fractionRing
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hA : IsNagataRing A) (hNodal : IsNodalAlgebra k A)
    (m : MaximalSpectrum ↥(integralClosure A (FractionRing A))) :
    Algebra.IsSeparableExtension k m.asIdeal.ResidueField := by
  have : IsNoetherianRing A := hA.isNoetherianRing
  have hm : m.asIdeal.IsMaximal := m.isMaximal
  have hsepκ : Algebra.IsSeparableExtension k (ResidueField A) := hNodal.1
  have hsep : Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) :=
    isSeparable_quadraticAlgebra_of_isNodalAlgebra k A hNodal
  -- the third isomorphism theorem identifies `(A' ⧸ 𝔪_A A') ⧸ m̄` with `A' ⧸ m`
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ k
    (A := ↥(integralClosure A (FractionRing A)))
    (I := (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))))
    (J := m.asIdeal) (map_maximalIdeal_le_of_isMaximal m.asIdeal)
  let fld : Field (↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  let etot := e.trans (residueFieldAlgEquivQuotient k m.asIdeal)
  exact isSeparableExtension_of_quotient_ringEquiv (κ := ResidueField A) _
    (e.toRingEquiv.toMulEquiv.isField (Field.toIsField _))
    (isSeparable_quotient (ResidueField A) _) etot.toRingEquiv etot.commutes

end Stacks.Curves

end
