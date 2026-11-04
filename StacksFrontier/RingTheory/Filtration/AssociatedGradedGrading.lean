module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# The internal grading of the associated graded ring, and its degree-zero part

`AssociatedGraded.gradedRing I` is the associated graded ring `Gr_I(A) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹` of an
ideal `I` of a commutative ring `A`, built as an *external* direct sum carrying a
`DirectSum.GCommRing` structure. Every statement about a graded ring that mentions homogeneous
ideals — `Ideal.IsHomogeneous`, `HomogeneousIdeal.irrelevant`, `ProjectiveSpectrum`, and so
`AlgebraicGeometry.Proj` — is instead stated for Mathlib's *internal* picture `GradedRing 𝒜`,
for a family `𝒜` of additive subgroups decomposing the ring.

This file supplies the internal grading, as the images of the structure maps
(`Stacks.ExternalGrading.summand`), and identifies its degree-zero part: the canonical ring map
`A → (Gr_I(A))₀` is surjective with kernel `I`, so `(Gr_I(A))₀ = A/I`. It also records when
`Gr_I(A)` is the zero ring, which is exactly when `I = A`.

The degree-zero identification is what makes the structure morphism
`AlgebraicGeometry.Proj.toSpecZero` of `Proj (Gr_I(A))` a morphism to `Spec(A/I)`, which is the
form in which it appears in [Stacks, Tag 0GA6].

## Main definitions

* `AssociatedGraded.grading`: the internal grading of `Gr_I(A)`, as a family
  `ℕ → AddSubgroup (Gr_I(A))`. The `GradedRing` instance for it is
  `Stacks.ExternalGrading.gradedRing`.
* `AssociatedGraded.gradingEquivPiece`: the degree-`n` piece of that grading is `Iⁿ/Iⁿ⁺¹`.
* `AssociatedGraded.gradeZeroMk`: the class in degree `0` of an element of `A`.
* `AssociatedGraded.gradeZeroHom`: the canonical ring map `A → (Gr_I(A))₀`.
* `AssociatedGraded.gradeZeroEquiv`: the resulting ring isomorphism `A/I ≅ (Gr_I(A))₀`.

## Main results

* `AssociatedGraded.ker_gradeZeroHom`: the kernel of `A → (Gr_I(A))₀` is `I`.
* `AssociatedGraded.subsingleton_gradedRing_iff`: `Gr_I(A)` is the zero ring iff `I = A`.

## Implementation notes

`grading` is an `abbrev` rather than a `def` so that instance search unfolds it and finds
`Stacks.ExternalGrading.gradedRing`; with a `def` the `GradedRing` instance has to be supplied as
a term at every use.

`instAddSubgroupClassGradedRing` repeats Mathlib's `AddSubgroup.instAddSubgroupClass` at this one
ring, at raised priority. It is not redundant: once the ambient import set is large, instance
search no longer finds `AddSubgroupClass (AddSubgroup (Gr_I(A))) (Gr_I(A))` on its own, while
`AddSubmonoidClass` is still found — so `GradedRing (grading I)` and `Proj (grading I)` elaborate
but `SetLike.GradeZero.instCommRing`, `integerGrading` and the twisting sheaves do not. Supplying
it here makes the degree-zero ring structure, and everything downstream of it, available to any
module importing this one.

## References

* [Stacks Project, Section 51.22 (0GA6)](https://stacks.math.columbia.edu/tag/0GA6) — where
  `Gr_I(A)` is formed and its `Proj` is taken over `Spec` of its degree-zero part.
* [Stacks Project, Section 15.4 (07VD)](https://stacks.math.columbia.edu/tag/07VD) — the
  associated graded ring itself.
-/

@[expose] public noncomputable section

namespace AssociatedGraded

open DirectSum

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The internal grading of the associated graded ring `Gr_I(A) = ⨁_{n ≥ 0} Iⁿ/Iⁿ⁺¹`**: the
degree-`n` piece is the image of the `n`-th structure map of the direct sum. The `GradedRing`
instance is `Stacks.ExternalGrading.gradedRing`, which applies because
`AssociatedGraded.gradedCommRing` makes the family of pieces a `DirectSum.GCommRing`. -/
abbrev grading : ℕ → AddSubgroup (gradedRing I) :=
  Stacks.ExternalGrading.summand (fun n => piece (M := A) I n)

/-- `AddSubgroup (Gr_I(A))` is a class of additive subgroups of `Gr_I(A)`. See the implementation
notes: this is Mathlib's instance, restated at raised priority because instance search stops
finding it once the ambient import set is large. -/
instance (priority := 10000) instAddSubgroupClassGradedRing :
    AddSubgroupClass (AddSubgroup (gradedRing I)) (gradedRing I) :=
  AddSubgroup.instAddSubgroupClass

/-- **The degree-`n` piece of the grading is `Iⁿ/Iⁿ⁺¹`.** -/
def gradingEquivPiece (n : ℕ) : piece (M := A) I n ≃+ grading I n :=
  Stacks.ExternalGrading.summandEquiv (fun k => piece (M := A) I k) n

/-- The image of an element of `Iⁿ/Iⁿ⁺¹` under the `n`-th structure map lies in the degree-`n`
piece of the grading. -/
theorem of_mem_grading {n : ℕ} (a : piece (M := A) I n) :
    DirectSum.of (fun k => piece (M := A) I k) n a ∈ grading I n :=
  Stacks.ExternalGrading.of_mem_summand n a

/-- An element lies in the first power of `I` exactly when it lies in `I`. -/
theorem mem_power_one_iff {a : A} : a ∈ power (M := A) I 1 ↔ a ∈ I := by
  rw [ring_power_eq, pow_one]

/-- The class in degree `0` of an element of `A`. Every element of `A` lies in `I⁰ = A`, so this
is defined without hypothesis. -/
def gradeZeroMk (a : A) : piece (M := A) I 0 := mk I 0 ⟨a, by simp [power]⟩

/-- The class of `a` in degree `0` vanishes exactly when `a ∈ I`. -/
theorem gradeZeroMk_eq_zero_iff (a : A) : gradeZeroMk I a = 0 ↔ a ∈ I := by
  rw [gradeZeroMk, mk, Submodule.Quotient.mk_eq_zero]
  simp

/-- Every element of `I⁰/I¹` is the degree-`0` class of an element of `A`. -/
theorem gradeZeroMk_surjective : Function.Surjective (gradeZeroMk I) := by
  intro c
  induction c using Quotient.inductionOn with
  | _ a => exact ⟨(a : A), rfl⟩

/-- The product of two degree-`0` classes is the degree-`0` class of the product. -/
theorem gradeZeroMk_mul (a b : A) :
    homogeneousSMul I (gradeZeroMk I a) (gradeZeroMk I b) = gradeZeroMk I (a * b) := rfl

/-- **The canonical ring map `A → (Gr_I(A))₀`**, sending `a` to the class of `a` in degree `0`,
placed in the degree-zero summand. The ring structure on the target is
`SetLike.GradeZero.instCommRing` for `AssociatedGraded.grading`. -/
def gradeZeroHom : A →+* grading I 0 where
  toFun a := ⟨DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a),
    of_mem_grading I _⟩
  map_one' := rfl
  map_mul' a b := Subtype.ext (by
    change DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I (a * b)) =
      DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a) *
        DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I b)
    rw [of_mul_of, gradeZeroMk_mul])
  map_zero' := Subtype.ext (by
    change DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I 0) = 0
    rw [show gradeZeroMk I (0 : A) = 0 from rfl, map_zero])
  map_add' a b := Subtype.ext (by
    change DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I (a + b)) =
      DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a) +
        DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I b)
    rw [show gradeZeroMk I (a + b) = gradeZeroMk I a + gradeZeroMk I b from rfl, map_add])

/-- The image of `a` under `gradeZeroHom` is the degree-`0` class of `a`, placed in the
degree-zero summand. -/
theorem coe_gradeZeroHom (a : A) :
    ((gradeZeroHom I a : grading I 0) : gradedRing I) =
      DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a) := rfl

/-- The canonical ring map `A → (Gr_I(A))₀` is surjective. -/
theorem gradeZeroHom_surjective : Function.Surjective (gradeZeroHom I) := by
  rintro ⟨x, c, rfl⟩
  obtain ⟨a, rfl⟩ := gradeZeroMk_surjective I c
  exact ⟨a, rfl⟩

/-- An element of `A` maps to zero in `(Gr_I(A))₀` exactly when it lies in `I`. -/
theorem gradeZeroHom_eq_zero_iff (a : A) : gradeZeroHom I a = 0 ↔ a ∈ I := by
  rw [← gradeZeroMk_eq_zero_iff I a, Subtype.ext_iff, coe_gradeZeroHom]
  constructor
  · intro h
    have h0 := congrArg (fun z : gradedRing I => z 0) h
    simpa using h0
  · intro h; rw [h]; exact Subtype.ext_iff.mp (map_zero (gradeZeroHom I))

/-- **The kernel of `A → (Gr_I(A))₀` is `I`.** -/
theorem ker_gradeZeroHom : RingHom.ker (gradeZeroHom I) = I :=
  Ideal.ext fun a => gradeZeroHom_eq_zero_iff I a

/-- **The degree-zero part of `Gr_I(A)` is `A/I`.** -/
def gradeZeroEquiv : (A ⧸ I) ≃+* grading I 0 :=
  (Ideal.quotEquivOfEq (ker_gradeZeroHom I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (gradeZeroHom_surjective I))

/-- If `I = A`, every piece `Iⁿ/Iⁿ⁺¹` is zero. -/
theorem subsingleton_piece_of_eq_top (h : I = ⊤) (n : ℕ) :
    ∀ z : piece (M := A) I n, z = 0 := by
  intro z
  induction z using Quotient.inductionOn with
  | _ x =>
    rw [show (Quotient.mk _ x : piece (M := A) I n) = mk I n x from rfl, mk,
      Submodule.Quotient.mk_eq_zero]
    simp [h, ring_power_eq, Ideal.top_pow]

/-- **`Gr_I(A)` is the zero ring exactly when `I = A`.** This is the degenerate case with which
[Stacks, Tag 0GA6] qualifies its two invariants, and with which the proof of
[Stacks, Tag 0GA7] opens. -/
theorem subsingleton_gradedRing_iff : Subsingleton (gradedRing I) ↔ I = ⊤ :=
  ⟨fun h => Submodule.eq_top_iff'.mpr fun a =>
      (gradeZeroHom_eq_zero_iff I a).mp (Subtype.ext (h.elim _ _)),
    fun h => ⟨fun x y => DFinsupp.ext fun n => by
      rw [subsingleton_piece_of_eq_top I h n (x n), subsingleton_piece_of_eq_top I h n (y n)]⟩⟩

/-- If `I = A`, the degree-zero part of `Gr_I(A)` is the zero ring. -/
theorem subsingleton_gradeZero_of_eq_top (h : I = ⊤) : Subsingleton (grading I 0) :=
  have h' := (subsingleton_gradedRing_iff I).mpr h
  ⟨fun _ _ => Subtype.ext (h'.elim _ _)⟩

end AssociatedGraded

end
