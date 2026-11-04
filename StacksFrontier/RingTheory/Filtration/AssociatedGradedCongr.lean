module

public import StacksFrontier.RingTheory.Filtration.AssociatedGradedAlgebra
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading

/-!
# The structure map of the associated graded ring, and its transport along a ring isomorphism

For an ideal `I` of a commutative ring `A` the associated graded ring
`Gr_I(A) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹` is `AssociatedGraded.gradedRing I`. Two things about it are
supplied here.

**Its structure map.** The class in degree zero of an element of `A`, placed in the degree-zero
summand, is a ring homomorphism `A ⟶ Gr_I(A)` with kernel exactly `I`
(`AssociatedGraded.gradeZeroRingHom`, `AssociatedGraded.ker_gradeZeroRingHom`). So `Gr_I(A)` is
an `A ⧸ I`-algebra, unconditionally, and that is the algebra structure over which the degree-zero
part of a graded `Gr_I(A)`-algebra is read.

**Its transport.** A ring isomorphism `f : A ≃+* B` carrying `I` to `I'` induces a ring
isomorphism `Gr_I(A) ≃+* Gr_{I'}(B)`, degreewise
`AssociatedGraded.pieceEquivOfRingEquiv`. This is the associated-graded analogue of
`Stacks.Blowup.reesAlgebraCongr`, and it is what moves `Gr_I(A)` for an ideal of `A` to the
associated graded ring of the ideal `I` generates in a ring presented as isomorphic to `A` — for
instance `Γ(Spec A, ⊤)`.

## Main definitions

* `AssociatedGraded.gradeZeroRingHom`: the ring map `A ⟶ Gr_I(A)`, `a ↦ [a]₀`.
* `AssociatedGraded.algebraQuotient`: the resulting `A ⧸ I`-algebra structure on `Gr_I(A)`.
* `AssociatedGraded.congrRingHom` and `AssociatedGraded.congrRingEquiv`: the transport along a
  ring isomorphism carrying one ideal to the other.

## Main results

* `AssociatedGraded.ker_gradeZeroRingHom`: the kernel of `A ⟶ Gr_I(A)` is `I`.
* `AssociatedGraded.bijective_congrRingHom`: the transport is bijective.
* `AssociatedGraded.congrRingEquiv_gradeZeroRingHom`: the transport carries the structure map of
  `Gr_I(A)` to that of `Gr_{I'}(B)`, so it is an isomorphism over the identification `A ≃+* B`
  and not merely an abstract one.

## Implementation notes

Multiplicativity of the transport is proved on the source, by `DirectSum.toSemiring`: a family of
additive maps out of the homogeneous summands carrying the graded unit to the unit and the graded
product of two homogeneous elements to the product is a ring homomorphism out of the external
direct sum. The graded multiplication of `fun n => AssociatedGraded.piece I n` is
`AssociatedGraded.homogeneousSMul` and the lemmas available for
`AssociatedGraded.pieceEquivOfRingEquiv` are stated for the internal multiplication
`AssociatedGraded.homogeneousMul` of the associated graded algebra of `A` as an `A`-algebra; the
two agree by `AssociatedGraded.homogeneousMul_eq_homogeneousSMul`, which is the only place the
distinction is crossed.

Bijectivity is proved by exhibiting the inverse degreewise, as an additive map, and never by `rw`
under `DirectSum.of`.

`AssociatedGraded.algebraQuotient` is an `instance`: it depends on nothing but `I`, so instance
search can find it, which is what lets a consumer of a graded `A ⧸ I`-algebra write
`algebraMap (A ⧸ I) (Gr_I(A))`.

## References

* [Stacks Project, Section 15.4](https://stacks.math.columbia.edu/tag/07VD)
-/

@[expose] public noncomputable section

open scoped DirectSum

universe u

namespace AssociatedGraded

variable {A B : Type u} [CommRing A] [CommRing B]

/-! ### The structure map `A ⟶ Gr_I(A)` -/

/-- **The structure map of the associated graded ring**: the class in degree zero of an element of
`A`, placed in the degree-zero summand of `Gr_I(A)`. It is `AssociatedGraded.gradeZeroHom`
followed by the inclusion of the degree-zero part, written out so that no `GradedRing` instance
is needed to state it. -/
def gradeZeroRingHom (I : Ideal A) : A →+* gradedRing I where
  toFun a := DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a)
  map_one' := rfl
  map_mul' a b := by
    rw [of_mul_of I (gradeZeroMk I a) (gradeZeroMk I b), gradeZeroMk_mul]
  map_zero' := by
    rw [show gradeZeroMk I (0 : A) = 0 from rfl, map_zero]
  map_add' a b := by
    rw [show gradeZeroMk I (a + b) = gradeZeroMk I a + gradeZeroMk I b from rfl, map_add]

/-- The structure map `A ⟶ Gr_I(A)` sends `a` to its degree-zero class in the degree-zero
summand. -/
theorem gradeZeroRingHom_apply (I : Ideal A) (a : A) :
    gradeZeroRingHom I a = DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a) :=
  rfl

/-- **The kernel of the structure map `A ⟶ Gr_I(A)` is `I`.** The degree-zero class of `a`
vanishes exactly when `a ∈ I` (`AssociatedGraded.gradeZeroMk_eq_zero_iff`), and the inclusion of
a summand of a direct sum is injective. -/
theorem ker_gradeZeroRingHom (I : Ideal A) : RingHom.ker (gradeZeroRingHom I) = I := by
  refine Ideal.ext fun a => ?_
  rw [RingHom.mem_ker, ← gradeZeroMk_eq_zero_iff I a, gradeZeroRingHom_apply]
  constructor
  · intro h
    have h0 := congrArg (fun z : gradedRing I => z 0) h
    simpa using h0
  · intro h
    rw [h, map_zero]

/-- **`Gr_I(A)` is an `A ⧸ I`-algebra**: the structure map `A ⟶ Gr_I(A)` kills `I`, by
`AssociatedGraded.ker_gradeZeroRingHom`, so it factors through the quotient. -/
instance algebraQuotient (I : Ideal A) : Algebra (A ⧸ I) (gradedRing I) :=
  (Ideal.Quotient.lift I (gradeZeroRingHom I) fun a ha => by
    rw [← RingHom.mem_ker, ker_gradeZeroRingHom I]
    exact ha).toAlgebra

/-- The `A ⧸ I`-algebra structure of `Gr_I(A)` on the class of an element of `A` is the structure
map of `Gr_I(A)`. -/
theorem algebraMap_quotient_mk (I : Ideal A) (a : A) :
    algebraMap (A ⧸ I) (gradedRing I) (Ideal.Quotient.mk I a) = gradeZeroRingHom I a :=
  rfl

/-! ### Transport along a ring isomorphism -/

section Congr

variable (f : A ≃+* B) {I : Ideal A} {I' : Ideal B} (hI : I.map (f : A →+* B) = I')

/-- The degree-`n` component of the transport, placed in the degree-`n` summand of
`Gr_{I'}(B)`. -/
def congrIncl (n : ℕ) : piece (M := A) I n →+ gradedRing I' :=
  (DirectSum.of (fun m => piece (M := B) I' m) n).comp
    (pieceEquivOfRingEquiv f hI n).toAddMonoidHom

/-- The degree-`n` component of the transport sends `x` to the image of `x` under
`AssociatedGraded.pieceEquivOfRingEquiv` in the degree-`n` summand of `Gr_{I'}(B)`. -/
theorem congrIncl_apply (n : ℕ) (x : piece (M := A) I n) :
    congrIncl f hI n x =
      DirectSum.of (fun m => piece (M := B) I' m) n (pieceEquivOfRingEquiv f hI n x) :=
  rfl

/-- The transport carries the graded unit to the unit: the degree-zero class of `1` goes to the
degree-zero class of `f 1 = 1`. -/
theorem congrIncl_one :
    congrIncl f hI 0 (GradedMonoid.GOne.one : piece (M := A) I 0) = 1 := by
  rw [congrIncl_apply,
    show (GradedMonoid.GOne.one : piece (M := A) I 0) = homogeneousOne (M := A) I from rfl,
    pieceEquivOfRingEquiv_homogeneousOne f hI]
  rfl

/-- The transport is multiplicative on homogeneous elements: it is
`AssociatedGraded.pieceEquivOfRingEquiv_homogeneousMul`, read through
`AssociatedGraded.homogeneousMul_eq_homogeneousSMul`. -/
theorem congrIncl_mul (n m : ℕ) (a : piece (M := A) I n) (b : piece (M := A) I m) :
    congrIncl f hI (n + m) (homogeneousSMul I a b) =
      congrIncl f hI n a * congrIncl f hI m b :=
  (congrArg (DirectSum.of (fun k => piece (M := B) I' k) (n + m))
      (pieceEquivOfRingEquiv_homogeneousMul f hI n m a b)).trans
    (of_mul_of I' (pieceEquivOfRingEquiv f hI n a) (pieceEquivOfRingEquiv f hI m b)).symm

/-- **The transport of `Gr_I(A)` along a ring isomorphism carrying `I` to `I'`**, as a ring
homomorphism. -/
def congrRingHom : gradedRing I →+* gradedRing I' :=
  DirectSum.toSemiring (congrIncl f hI) (congrIncl_one f hI)
    fun {_ _} a b => congrIncl_mul f hI _ _ a b

/-- On the degree-`n` summand, the transport is its degree-`n` component
`AssociatedGraded.congrIncl`. -/
theorem congrRingHom_of (n : ℕ) (x : piece (M := A) I n) :
    congrRingHom f hI (DirectSum.of (fun m => piece (M := A) I m) n x) =
      congrIncl f hI n x :=
  DirectSum.toSemiring_of (congrIncl f hI) _ _ n x

/-- The inverse of the transport, degree by degree. -/
def congrInv : gradedRing I' →+ gradedRing I :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m => piece (M := A) I m) n).comp
      (pieceEquivOfRingEquiv f hI n).symm.toAddMonoidHom

/-- On the degree-`n` summand of `Gr_{I'}(B)`, the inverse of the transport is the inverse of
`AssociatedGraded.pieceEquivOfRingEquiv` followed by the inclusion of the degree-`n` summand. -/
theorem congrInv_of (n : ℕ) (y : piece (M := B) I' n) :
    congrInv f hI (DirectSum.of (fun m => piece (M := B) I' m) n y) =
      DirectSum.of (fun m => piece (M := A) I m) n ((pieceEquivOfRingEquiv f hI n).symm y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The transport is bijective**, its inverse being the transport along the inverse
isomorphism. -/
theorem bijective_congrRingHom : Function.Bijective (congrRingHom f hI) := by
  refine Function.bijective_iff_has_inverse.2 ⟨congrInv f hI, fun z => ?_, fun z => ?_⟩ <;>
    induction z using DirectSum.induction_on <;>
    simp_all [congrRingHom_of, congrIncl_apply, congrInv_of]

/-- **A ring isomorphism carrying `I` to `I'` identifies `Gr_I(A)` with `Gr_{I'}(B)`.** This is
the associated-graded analogue of `Stacks.Blowup.reesAlgebraCongr`. -/
def congrRingEquiv : gradedRing I ≃+* gradedRing I' :=
  RingEquiv.ofBijective (congrRingHom f hI) (bijective_congrRingHom f hI)

/-- **The transport carries the structure map of `Gr_I(A)` to that of `Gr_{I'}(B)`**, over the
identification `f` of the two base rings. -/
theorem congrRingEquiv_gradeZeroRingHom (a : A) :
    congrRingEquiv f hI (gradeZeroRingHom I a) = gradeZeroRingHom I' (f a) := by
  show congrRingHom f hI (gradeZeroRingHom I a) = _
  rw [gradeZeroRingHom_apply, congrRingHom_of, congrIncl_apply]
  rfl

end Congr

end AssociatedGraded

end
