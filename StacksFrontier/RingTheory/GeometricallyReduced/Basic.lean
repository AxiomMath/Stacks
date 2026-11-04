module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Polynomial.Nilpotent
public import Mathlib.RingTheory.PolynomialAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometrically reduced algebras: localizations and polynomial rings
-/

/-!
# Geometrically reduced algebras: localizations and polynomial rings

Throughout, `k` is a field and all rings are commutative with unit; a ring is *reduced* if
its only nilpotent element is `0`. A `k`-algebra `S` is *geometrically reduced over `k`* if
`K ⊗[k] S` is reduced for every field extension `K/k`, where a field extension means a field
`K` together with a ring homomorphism `k → K` (automatically injective, `k` being a field)
and `K ⊗[k] S` carries the `K`-algebra structure coming from its first factor.

Two permanence properties are proved here. If `R` is geometrically reduced over `k`, then so
is every localization `S⁻¹R` of `R` at a multiplicative subset `S ⊆ R`, and so is the
polynomial ring `R[x]` in one variable; in both cases the `k`-algebra structure is the one
induced from `R` along the canonical map out of `R`.

Both arguments run over a fixed field extension `K/k` and reduce to a statement about the
reduced ring `K ⊗[k] R`: localization commutes with base change, so `K ⊗[k] S⁻¹R` is a
localization of `K ⊗[k] R` and a localization of a reduced ring is reduced; and
`K ⊗[k] R[x] ≃+* (K ⊗[k] R)[x]`, a polynomial ring over a reduced ring.

## Conventions

Geometric reducedness quantifies over field extensions `K` lying in a fixed universe `w`.
The statements below preserve that universe, so each result holds for field extensions in
every universe.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- `S` is *geometrically reduced over the field `k`* if for every field extension
`K/k`, the `K`-algebra `K ⊗[k] S` is reduced.

We quantify over field extensions `K` lying in a fixed (universe-polymorphic)
universe `w`; the statements below preserve this universe, so the result holds for
field extensions in every universe. -/
@[ega "IV 4.6.17" "special case", ega "IV 4.6.2", ega "IV 6.7.6", sga "1 X 1.1" "special case"]
def GeometricallyReduced (k : Type u) [Field k] (S : Type v) [CommRing S]
    [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K], IsReduced (K ⊗[k] S)

/-- Reducedness transfers backward along a ring isomorphism: if there is a ring
isomorphism `e : A ≃+* B` with `B` reduced, then `A` is reduced.

If `x : A` is nilpotent, say `x ^ n = 0`, then `e x` is nilpotent in `B`, since
`(e x) ^ n = e (x ^ n) = e 0 = 0`; hence `e x = 0` as `B` is reduced, and `x = 0` as `e`
is injective. -/
theorem isReduced_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : IsReduced B) : IsReduced A := by
  constructor
  intro x hx
  exact e.injective (by simpa using (hx.map e.toRingHom).eq_zero)

/-- The polynomial ring over a reduced commutative ring is reduced.

A polynomial `p` is nilpotent iff each of its coefficients is nilpotent
(`Polynomial.isNilpotent_iff`); if `B` is reduced each such coefficient is `0`, so
`p = 0`. -/
theorem isReduced_polynomial (B : Type*) [CommRing B] [IsReduced B] :
    IsReduced (Polynomial B) := by
  constructor
  intro p hp
  rw [Polynomial.isNilpotent_iff] at hp
  ext n
  simpa using (hp n).eq_zero

/-- A localization of a reduced commutative ring is reduced.

If `A` is reduced, `M : Submonoid A`, and `B` is a localization of `A` at `M`,
then `B` is reduced.

Let `b : B` with `b ^ n = 0` and write `b = mk' a s` with `a : A` and `s ∈ M`. Then
`b ^ n = mk' (a ^ n) (s ^ n) = 0`, and `mk' x t = 0` iff `u * x = 0` for some `u ∈ M`, so
`u * a ^ n = 0` for some `u ∈ M`. Hence `(u * a) ^ n = u ^ n * a ^ n = u ^ (n-1) * (u * a ^ n)
= 0`, so `u * a = 0` as `A` is reduced, and therefore
`mk' a s = mk' (u * a) (u * s) = mk' 0 (u * s) = 0`, i.e. `b = 0`. -/
@[ega "0 1.2.8", ega "IV 10.10.4" "special case"]
theorem isReduced_localization (A : Type*) [CommRing A] [IsReduced A]
    (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] :
    IsReduced B := by
  rw [isReduced_iff]
  rintro b ⟨n, hn⟩
  obtain ⟨⟨a, s⟩, hb⟩ := IsLocalization.mk'_surjective M b
  simp only at hb
  subst hb
  rw [← IsLocalization.mk'_pow] at hn
  rw [IsLocalization.mk'_eq_zero_iff] at hn
  obtain ⟨u, hu⟩ := hn
  -- hu : ↑u * a ^ n = 0
  have huan : (↑u : A) * a = 0 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simp only [pow_zero, mul_one] at hu
      -- hu : ↑u = 0
      rw [hu, zero_mul]
    · have hnil : (↑u * a) ^ n = 0 := by
        rw [mul_pow]
        have hsplit : (↑u : A) ^ n = ↑u ^ (n - 1) * ↑u := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hsplit, mul_assoc, hu, mul_zero]
      exact IsReduced.eq_zero (↑u * a) ⟨n, hnil⟩
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨u, huan⟩

open Polynomial in
/-- For a `k`-algebra `R` and a `k`-algebra `K`, the tensor product
`K ⊗[k] R[X]` is ring-isomorphic to `(K ⊗[k] R)[X]`.

Since `R[X] ≅ R ⊗[k] k[X]` (`polyEquivTensor'`), we get
`K ⊗[k] R[X] ≅ K ⊗[k] (R ⊗[k] k[X]) ≅ (K ⊗[k] R) ⊗[k] k[X] ≅ (K ⊗[k] R)[X]`, the middle
isomorphism being associativity of the tensor product and the last being `polyEquivTensor'`
again, over the base ring `K ⊗[k] R`. -/
noncomputable def tensorPolyRingEquiv (k R K : Type*) [CommRing k] [CommRing R]
    [CommRing K] [Algebra k R] [Algebra k K] :
    K ⊗[k] R[X] ≃+* (K ⊗[k] R)[X] :=
  let e1 : K ⊗[k] R[X] ≃ₐ[k] K ⊗[k] (R ⊗[k] k[X]) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((polyEquivTensor' k R).restrictScalars k)
  let e2 : K ⊗[k] (R ⊗[k] k[X]) ≃ₐ[k] (K ⊗[k] R) ⊗[k] k[X] :=
    (Algebra.TensorProduct.assoc k k k K R k[X]).symm
  let e3 : (K ⊗[k] R) ⊗[k] k[X] ≃ₐ[K ⊗[k] R] (K ⊗[k] R)[X] :=
    (polyEquivTensor' k (K ⊗[k] R)).symm
  (e1.trans e2).toRingEquiv.trans e3.toRingEquiv

/-- For a localization `A` of `R` at `M` and a field extension `K/k`, the base
change `K ⊗[k] A` is reduced whenever `K ⊗[k] R` is reduced.

This is the heart of the localization statement. View `K ⊗[k] R` as an `R`-algebra via its
right tensor factor (`Algebra.TensorProduct.rightAlgebra`). Then `IsLocalization.tensor`
says `(K ⊗[k] R) ⊗[R] A` is a localization of `K ⊗[k] R` at
`Algebra.algebraMapSubmonoid (K ⊗[k] R) M`, so it is reduced whenever `K ⊗[k] R` is.
Cancelling the base change gives a ring isomorphism `(K ⊗[k] R) ⊗[R] A ≃+* K ⊗[k] A`,
along which reducedness transfers back to `K ⊗[k] A`. -/
theorem isReduced_tensor_localization
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (M : Submonoid R) (A : Type v) [CommRing A] [Algebra R A] [IsLocalization M A]
    [Algebra k A] [IsScalarTower k R A]
    (K : Type w) [Field K] [Algebra k K] [IsReduced (K ⊗[k] R)] :
    IsReduced (K ⊗[k] A) := by
  let : Algebra R (K ⊗[k] R) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (K ⊗[k] R) M) ((K ⊗[k] R) ⊗[R] A) :=
    IsLocalization.tensor (R := R) (S := K ⊗[k] R) A M
  have : IsReduced ((K ⊗[k] R) ⊗[R] A) :=
    isReduced_localization (K ⊗[k] R) (Algebra.algebraMapSubmonoid (K ⊗[k] R) M)
      ((K ⊗[k] R) ⊗[R] A)
  exact isReduced_of_ringEquiv
    (Algebra.IsPushout.cancelBaseChangeAlg k K R (K ⊗[k] R) A).symm.toRingEquiv inferInstance

/-- For a field extension `K/k`, if `K ⊗[k] R` is reduced then `K ⊗[k] R[X]` is
reduced.

`(K ⊗[k] R)[X]` is a polynomial ring over the reduced ring `K ⊗[k] R`, hence reduced, and
the ring isomorphism `tensorPolyRingEquiv k R K : K ⊗[k] R[X] ≃+* (K ⊗[k] R)[X]` transfers
reducedness back. -/
theorem isReduced_tensor_polynomial
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (K : Type w) [Field K] [Algebra k K] [IsReduced (K ⊗[k] R)] :
    IsReduced (K ⊗[k] Polynomial R) :=
  isReduced_of_ringEquiv (tensorPolyRingEquiv k R K) (isReduced_polynomial _)

/-- If `R` is geometrically reduced over the field `k` and `A` is a localization of `R` at a
multiplicative subset `M ⊆ R`, carrying the induced `k`-algebra structure, then `A` is
geometrically reduced over `k`.

Fix a field extension `K/k`; then `K ⊗[k] R` is reduced. The key base-change fact is that
`K ⊗[k] A` is isomorphic to a localization of `K ⊗[k] R`: viewing `K ⊗[k] R` as an
`R`-algebra, `(K ⊗[k] R) ⊗[R] A` is a localization of `K ⊗[k] R` at the image submonoid
`Algebra.algebraMapSubmonoid (K ⊗[k] R) M`, and cancelling the base change gives a
`K`-algebra isomorphism `(K ⊗[k] R) ⊗[R] A ≃ₐ[K] K ⊗[k] A`. A localization of a reduced ring
is reduced, so `(K ⊗[k] R) ⊗[R] A` is reduced and reducedness transfers back to `K ⊗[k] A`
along that isomorphism. As `K/k` was arbitrary, `A` is geometrically reduced over `k`. -/
@[stacks 04KN "(1)", ega "IV 7.3.9" "(ii)"]
theorem geometricallyReduced_localization
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (M : Submonoid R) (A : Type v) [CommRing A] [Algebra R A] [IsLocalization M A]
    [Algebra k A] [IsScalarTower k R A]
    (hR : GeometricallyReduced.{u, v, w} k R) :
    GeometricallyReduced.{u, v, w} k A := by
  intro K _ _
  -- `K ⊗[k] R` is reduced (from `hR`).
  have hKR : IsReduced (K ⊗[k] R) := hR K
  -- It remains to show `IsReduced (K ⊗[k] A)`, which has two ingredients:
  --
  --  (1) a ring isomorphism `K ⊗[k] A ≃+* (K ⊗[k] R) ⊗[R] A`, together with the
  --      fact that `(K ⊗[k] R) ⊗[R] A` is a localization of `K ⊗[k] R` at
  --      `Algebra.algebraMapSubmonoid (K ⊗[k] R) M` (viewing `K ⊗[k] R` as an
  --      `R`-algebra via its right factor);
  --  (2) a localization of a reduced ring is reduced, giving
  --      `IsReduced ((K ⊗[k] R) ⊗[R] A)` from `hKR`.
  --
  -- Transferring reducedness backward along the isomorphism of (1) concludes; the
  -- whole argument for the fixed `K` is `isReduced_tensor_localization`.
  exact isReduced_tensor_localization k R M A K

/-- If `R` is geometrically reduced over the field `k`, then so is the polynomial ring `R[x]`
in one variable.

Fix a field extension `K/k`. Then `K ⊗[k] R` is reduced, hence so is the polynomial ring
`(K ⊗[k] R)[X]`, and transferring reducedness backward along the ring isomorphism
`K ⊗[k] R[X] ≃+* (K ⊗[k] R)[X]` shows `K ⊗[k] R[X]` is reduced. As `K/k` was arbitrary,
`R[X]` is geometrically reduced. -/
@[stacks 04KN "(2)",
  ega "IV 4.6.21" "4.6.21(ii), special case",
  ega "IV 4.6.5" "(ii), special case"]
theorem geometricallyReduced_polynomial
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (hR : GeometricallyReduced.{u, v, w} k R) :
    GeometricallyReduced.{u, v, w} k (Polynomial R) := by
  intro K _ _
  -- `K ⊗[k] R` is reduced; delegate the transfer to `isReduced_tensor_polynomial`.
  have : IsReduced (K ⊗[k] R) := hR K
  exact isReduced_tensor_polynomial k R K

end
