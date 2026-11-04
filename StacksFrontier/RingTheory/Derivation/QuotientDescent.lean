module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Derivation.Localization
public import StacksFrontier.RingTheory.Derivation.Regularity

/-!
# Derivations on quotients and on fibres

A derivation `D : R → R` over a base ring `A` which maps an ideal `J` of `R` into itself induces
a derivation of `R ⧸ J`.  The elements `x` of an ideal `I` with `D x ∈ I` always form an ideal,
by the Leibniz rule, and for an ideal extended from the base this subideal is everything: an
`A`-derivation kills `algebraMap A R a`, hence preserves `p R` for every ideal `p` of `A`.

Combining this with the extension of a derivation to a localization gives, for a prime `q` of `R`
and an ideal `p` of `A`, a derivation of the fibre ring `R_q ⧸ p R_q`, computed on the class of
the image of an element of `R` by applying `D` first.

The file closes with the form of Stacks 0GEE used at such a fibre: if the quotient `R ⧸ J` is a
regular local ring and a family `y₁, …, y_m` of elements of `R` has a Jacobian determinant
`det (D i (y j))` which becomes a unit in `R ⧸ J`, then the classes of the `y j` form a regular
sequence in `R ⧸ J`.

## Main definitions

* `Derivation.quotientOfMapsTo`: the induced derivation of `R ⧸ J`.
* `Derivation.stableSubideal`: the subideal of elements preserved by a derivation.
* `Derivation.atPrimeQuotient`: the induced derivation of `R_q ⧸ p R_q`.

## Main results

* `Derivation.map_mem_map_algebraMap`: a derivation over `A` preserves `p R`.
* `isRegular_ofList_quotient_of_isUnit_det_derivation`: Stacks 0GEE read on a quotient.

## References

* [Stacks Project, Tag 0GEE](https://stacks.math.columbia.edu/tag/0GEE)
-/

@[expose] public noncomputable section

universe u v

namespace Derivation

/-- The `A`-linear map on `R ⧸ J` induced by an `A`-derivation of `R` mapping `J` into itself. -/
public def quotientLinearMapOfMapsTo {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] (D : Derivation A R R) (J : Ideal R) (hD : ∀ x ∈ J, D x ∈ J) :
    (R ⧸ J) →ₗ[A] (R ⧸ J) :=
  Submodule.liftQ (J.restrictScalars A)
    ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ D.toLinearMap)
    fun x hx => by simpa [Ideal.Quotient.eq_zero_iff_mem] using hD x hx

/-- The induced linear map sends the class of `x` to the class of `D x`. -/
public theorem quotientLinearMapOfMapsTo_mk {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] (D : Derivation A R R) (J : Ideal R) (hD : ∀ x ∈ J, D x ∈ J) (x : R) :
    quotientLinearMapOfMapsTo D J hD (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (D x) :=
  rfl

/-- An `A`-derivation of `R` mapping an ideal `J` into itself descends to an `A`-derivation of
the quotient ring `R ⧸ J`. -/
public def quotientOfMapsTo {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (D : Derivation A R R) (J : Ideal R) (hD : ∀ x ∈ J, D x ∈ J) :
    Derivation A (R ⧸ J) (R ⧸ J) :=
  Derivation.mk' (quotientLinearMapOfMapsTo D J hD) fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [smul_eq_mul, smul_eq_mul, ← map_mul, quotientLinearMapOfMapsTo_mk,
      quotientLinearMapOfMapsTo_mk, quotientLinearMapOfMapsTo_mk, ← map_mul, ← map_mul,
      ← map_add, D.leibniz, smul_eq_mul, smul_eq_mul]

/-- The descended derivation sends the class of `x` to the class of `D x`. -/
public theorem quotientOfMapsTo_mk {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] (D : Derivation A R R) (J : Ideal R) (hD : ∀ x ∈ J, D x ∈ J) (x : R) :
    quotientOfMapsTo D J hD (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (D x) :=
  rfl

/-- The elements of an ideal `I` whose image under a derivation again lies in `I`.  The Leibniz
rule makes this set an ideal. -/
public def stableSubideal {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (D : Derivation A R R) (I : Ideal R) : Ideal R where
  carrier := {y | y ∈ I ∧ D y ∈ I}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by simpa using add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c x hx := by
    refine ⟨I.smul_mem c hx.1, ?_⟩
    rw [smul_eq_mul, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (I.mul_mem_left _ hx.2) (Ideal.mul_mem_right _ _ hx.1)

/-- A derivation over the base ring preserves the extension of every ideal of the base. -/
public theorem map_mem_map_algebraMap {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] (D : Derivation A R R) (p : Ideal A) {x : R}
    (hx : x ∈ p.map (algebraMap A R)) : D x ∈ p.map (algebraMap A R) := by
  have key : p.map (algebraMap A R) ≤ stableSubideal D (p.map (algebraMap A R)) :=
    Ideal.map_le_iff_le_comap.2 fun a ha => ⟨Ideal.mem_map_of_mem _ ha, by simp⟩
  exact (key hx).2

/-- An `A`-derivation of `R`, localized at a prime `q` of `R` and then reduced modulo the
extension of an ideal `p` of `A`, as a derivation of the fibre ring `R_q ⧸ p R_q`. -/
public def atPrimeQuotient {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (D : Derivation A R R) (q : Ideal R) [q.IsPrime] (p : Ideal A) :
    Derivation A
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) :=
  quotientOfMapsTo (D.localization q.primeCompl (Localization.AtPrime q))
    (p.map (algebraMap A (Localization.AtPrime q)))
    fun _ hx => map_mem_map_algebraMap _ p hx

/-- The fibre derivation computes on the class of the image of an element of `R`. -/
public theorem atPrimeQuotient_mk_algebraMap {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] (D : Derivation A R R) (q : Ideal R) [q.IsPrime] (p : Ideal A) (x : R) :
    atPrimeQuotient D q p
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime q) x)) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime q) (D x)) := by
  rw [atPrimeQuotient, quotientOfMapsTo_mk, Derivation.localization_algebraMap]

end Derivation

/-- **Stacks 0GEE on a quotient.**  Let `J` be an ideal of `R` whose quotient `R ⧸ J` is a regular
local ring, let `D₁, …, D_m` be `A`-derivations of `R` mapping `J` into itself and let
`y₁, …, y_m` be elements of `R` whose classes lie in the maximal ideal of `R ⧸ J`.  If the
determinant of `(D i (y j))` becomes a unit in `R ⧸ J`, then the classes of `y₁, …, y_m` form a
regular sequence in `R ⧸ J`. -/
public theorem isRegular_ofList_quotient_of_isUnit_det_derivation {A X : Type*} [CommRing A]
    [CommRing X] [Algebra A X] (J : Ideal X) [IsRegularLocalRing (X ⧸ J)] {m : ℕ}
    (DA : Fin m → Derivation A X X) (hstab : ∀ i, ∀ x ∈ J, DA i x ∈ J) (y : Fin m → X)
    (hy : ∀ j, (Ideal.Quotient.mk J) (y j) ∈ IsLocalRing.maximalIdeal (X ⧸ J))
    (hdet : IsUnit ((Ideal.Quotient.mk J) (Matrix.det fun i j => DA i (y j)))) :
    RingTheory.Sequence.IsRegular (X ⧸ J)
      (List.ofFn fun j => (Ideal.Quotient.mk J) (y j)) := by
  refine (isRegularLocalRing_quotient_span_range_and_isRegular_of_isUnit_det_derivation
    (fun j => Ideal.Quotient.mk J (y j)) hy
    (fun i => Derivation.quotientOfMapsTo ((DA i).restrictScalars ℤ) J
      fun x hx => by simpa using hstab i x hx) ?_).2
  rwa [RingHom.map_det (Ideal.Quotient.mk J) (fun i j => DA i (y j))] at hdet

end
