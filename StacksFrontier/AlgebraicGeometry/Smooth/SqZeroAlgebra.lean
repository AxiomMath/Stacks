module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trivial square-zero extension of a commutative ring

For a commutative ring `R` and an `R`-module `M`, Mathlib's `TrivSqZeroExt R M` is the ring
`R ⋉ M` with `M` squaring to zero. This file collects the three pieces of that construction which
are needed before any geometry: the action of the opposite ring that `TrivSqZeroExt.commRing`
asks for, the presentation of a Leibniz map as a ring homomorphism into `R ⋉ M`, and the
functoriality of `R ⋉ M` in the pair `(R, M)`.

## Main definitions

* `Stacks.Smooth.moduleMulOpposite`: a module over a commutative ring is a module over the
  opposite ring. `TrivSqZeroExt.commRing` asks for this and it is not an instance for a
  commutative ring, so it is supplied here and enabled locally where it is needed.
* `Stacks.Smooth.sqZeroRingHom`: a map satisfying the Leibniz rule relative to a ring
  homomorphism, presented as a ring homomorphism into a trivial square-zero extension.
* `Stacks.Smooth.sqZeroMap`: the functoriality of the trivial square-zero extension.

## Implementation notes

These declarations were part of
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentSquareZero` and are in a module of their own
because two developments need them and neither may import the other: the square-zero extension
of the structure sheaf of a scheme, in that file, and the square-zero extension of an arbitrary
sheaf of commutative rings on a topological space, in
`StacksFrontier.Topology.Sheaves.Modules.SquareZeroExtension`. With the algebra here, the second can
be the general construction and the first its specialization, which is the layering the sheaf
file asked for.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
-/

@[expose] public section

universe u

namespace Stacks.Smooth

/-- A module over a commutative ring is a module over the opposite ring, through the
identification of the ring with its opposite. This is the instance that the trivial square-zero
extension of a commutative ring by a module asks for; it is local to this file. -/
@[instance_reducible]
noncomputable def moduleMulOpposite (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingEquiv.toOpposite R).symm : Rᵐᵒᵖ →+* R)

attribute [local instance] moduleMulOpposite

/-- The action of the opposite ring on a module over a commutative ring, through
`Stacks.Smooth.moduleMulOpposite`, is the original action. -/
instance isCentralScalarMulOpposite (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] : IsCentralScalar R M :=
  ⟨fun _ _ ↦ rfl⟩

/-- A map satisfying the Leibniz rule relative to a ring homomorphism kills the unit. -/
theorem apply_one_eq_zero_of_leibniz {A R M : Type u} [CommRing A] [CommRing R] [AddCommGroup M]
    [Module R M] (φ : A →+* R) (D : A →+ M)
    (hD : ∀ x y : A, D (x * y) = φ x • D y + φ y • D x) : D 1 = 0 := by
  have h := hD 1 1
  rw [one_mul, φ.map_one, one_smul] at h
  exact (add_left_cancel (a := D 1) ((add_zero (D 1)).trans h)).symm

/-- **A derivation presented as a ring homomorphism into a square-zero extension.** For a ring
homomorphism `φ : A → R` and an additive map `D : A → M` satisfying the Leibniz rule relative to
`φ`, the map `x ↦ (φ x, D x)` is a ring homomorphism into the trivial square-zero extension of
`R` by `M`. -/
def sqZeroRingHom {A R M : Type u} [CommRing A] [CommRing R] [AddCommGroup M] [Module R M]
    (φ : A →+* R) (D : A →+ M) (hD : ∀ x y : A, D (x * y) = φ x • D y + φ y • D x) :
    A →+* TrivSqZeroExt R M where
  toFun x := TrivSqZeroExt.inl (φ x) + TrivSqZeroExt.inr (D x)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [apply_one_eq_zero_of_leibniz φ D hD]
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [hD x y, add_comm]
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The first component of `Stacks.Smooth.sqZeroRingHom`. -/
@[simp]
theorem sqZeroRingHom_fst {A R M : Type u} [CommRing A] [CommRing R] [AddCommGroup M]
    [Module R M] (φ : A →+* R) (D : A →+ M)
    (hD : ∀ x y : A, D (x * y) = φ x • D y + φ y • D x) (x : A) :
    (sqZeroRingHom φ D hD x).fst = φ x := by
  simp [sqZeroRingHom]

/-- The second component of `Stacks.Smooth.sqZeroRingHom`. -/
@[simp]
theorem sqZeroRingHom_snd {A R M : Type u} [CommRing A] [CommRing R] [AddCommGroup M]
    [Module R M] (φ : A →+* R) (D : A →+ M)
    (hD : ∀ x y : A, D (x * y) = φ x • D y + φ y • D x) (x : A) :
    (sqZeroRingHom φ D hD x).snd = D x := by
  simp [sqZeroRingHom]

/-- The first component of a section of a square-zero extension written in terms of the two
inclusions. -/
theorem fst_inl_add_inr {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (r : R)
    (m : M) : (TrivSqZeroExt.inl r + TrivSqZeroExt.inr m : TrivSqZeroExt R M).fst = r := by
  simp

/-- The second component of a section of a square-zero extension written in terms of the two
inclusions. -/
theorem snd_inl_add_inr {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (r : R)
    (m : M) : (TrivSqZeroExt.inl r + TrivSqZeroExt.inr m : TrivSqZeroExt R M).snd = m := by
  simp

/-- **Functoriality of the trivial square-zero extension.** A ring homomorphism together with a
semilinear additive map of the modules induces a ring homomorphism of the square-zero
extensions. -/
@[ega "0 18.2.9"]
def sqZeroMap {R R' M M' : Type u} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R' M'] (φ : R →+* R') (ψ : M →+ M')
    (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m) :
    TrivSqZeroExt R M →+* TrivSqZeroExt R' M' where
  toFun x := TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (ψ x.snd)
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' x y := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp [hψ]
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The first component of `Stacks.Smooth.sqZeroMap`. -/
@[simp]
theorem sqZeroMap_fst {R R' M M' : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] (φ : R →+* R') (ψ : M →+ M')
    (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m) (x : TrivSqZeroExt R M) :
    (sqZeroMap φ ψ hψ x).fst = φ x.fst := by
  simp [sqZeroMap]

/-- The second component of `Stacks.Smooth.sqZeroMap`. -/
@[simp]
theorem sqZeroMap_snd {R R' M M' : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] (φ : R →+* R') (ψ : M →+ M')
    (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m) (x : TrivSqZeroExt R M) :
    (sqZeroMap φ ψ hψ x).snd = ψ x.snd := by
  simp [sqZeroMap]

end Stacks.Smooth

end
