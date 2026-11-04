module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange

/-!
# Descent of membership in a submodule along a faithfully flat family

Let `A` be a faithfully flat `R`-algebra, `M` an `R`-module and `P ⊆ M` a submodule.  An element
`x : M` lies in `P` as soon as `1 ⊗ x` lies in the base change `P.baseChange A`, and the same
holds for a *finite family* of `R`-algebras whose product is faithfully flat, testing one element
`1 ⊗ x` in each member of the family.

Only one half of faithfully flat descent is used, and the easy one: the base change of `P` is
contained in the kernel of the base change of the quotient map `M ⟶ M ⧸ P`, which needs no
flatness at all.  Faithful flatness enters only through
`Module.FaithfullyFlat.one_tmul_eq_zero_iff`, applied to the quotient.

## Main results

* `Module.faithfullyFlat_pi_of_ringHom_pi`: a product of `R`-algebras is faithfully flat as soon
  as the product of their structure maps is a faithfully flat ring map.
* `Submodule.mem_of_one_tmul_mem_baseChange`: **membership in a submodule descends along a
  faithfully flat algebra.**
* `Submodule.mem_of_forall_one_tmul_mem_baseChange`: **membership in a submodule descends along a
  finite family of algebras whose product is faithfully flat.**

## Implementation notes

The family statement is reduced to the single-algebra one for the product `∀ i, A i` by writing
`1 = ∑ i, Pi.single i 1` and pushing each summand forward along `Pi.single i`, read as an
`R`-linear map `A i →ₗ[R] ∀ j, A j`.  No compatibility of the tensor product with finite products
is needed: all that is used is that the unit of the product ring is a finite sum of the images of
the units of its factors.

The push-forward step is an induction over the range description of
`Submodule.baseChange` — `ArtinReesBaseChange.range_subtype_baseChange` — and *not* over the
spanning description `Submodule.baseChange_eq_span`: the latter spans over `A`, and `Pi.single i`
is linear only over `R`, so the scalar step of the span induction has no proof.

`Pi.single i` is packaged as a linear map by hand rather than taken as `LinearMap.single`: the
latter has `Pi.module` on its target, while the module structure in scope on a product of
`R`-algebras comes from `Pi.algebra`, and instance search is syntactic.  The two share their
`SMul`, which is why the proof of linearity is `Pi.smul_apply` and a case split.

The hypothesis of the family statement is spelled with `RingHom.FaithfullyFlat` of
`RingHom.pi`, which is the form in which faithful flatness of a finite flat covering family of an
affine scheme is available; `Module.faithfullyFlat_pi_of_ringHom_pi` converts it, the structure
map of `Pi.algebra` being `RingHom.pi` of the structure maps.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- A product of `R`-algebras is faithfully flat as an `R`-module as soon as the product of their
structure maps is a faithfully flat ring map.

The structure map of `Pi.algebra` is `RingHom.pi` of the structure maps, so the two statements
differ only in the spelling of the `Algebra` instance. -/
theorem Module.faithfullyFlat_pi_of_ringHom_pi {R : Type u} [CommRing R] {ι : Type v}
    {A : ι → Type w} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (h : (RingHom.pi (fun i => algebraMap R (A i))).FaithfullyFlat) :
    Module.FaithfullyFlat R (∀ i, A i) :=
  RingHom.faithfullyFlat_algebraMap_iff.1 h

namespace ArtinReesBaseChange

/-- The inclusion of one factor of a product of `R`-algebras, as an `R`-linear map.

This is `Pi.single` with its `R`-linearity recorded for the module structure which `Pi.algebra`
puts on the product, the one in scope wherever the product is read as an `R`-algebra. -/
def piSingleLinearMap (R : Type u) [CommRing R] {ι : Type v} [DecidableEq ι] (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] (i : ι) : A i →ₗ[R] (∀ j, A j) where
  toFun := Pi.single i
  map_add' a b := Pi.single_add i a b
  map_smul' r a := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, Pi.smul_apply, RingHom.id_apply]
    · simp only [Pi.single_eq_of_ne hj, Pi.smul_apply, RingHom.id_apply, smul_zero]

/-- `piSingleLinearMap R A i` sends `a : A i` to `Pi.single i a`. -/
@[simp]
theorem piSingleLinearMap_apply (R : Type u) [CommRing R] {ι : Type v} [DecidableEq ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] (i : ι) (a : A i) :
    piSingleLinearMap R A i a = Pi.single i a := rfl

end ArtinReesBaseChange

namespace Submodule

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The base change of a submodule is carried into the base change of the same submodule by any
`R`-linear map of the coefficient algebras.**

The map need not be a map of algebras; only `R`-linearity is used, through the description of the
base change as the range of the base change of the inclusion of the submodule. -/
theorem rTensor_mem_baseChange {A A' : Type*} [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (P : Submodule R M) (τ : A →ₗ[R] A') {z : A ⊗[R] M}
    (hz : z ∈ P.baseChange A) : LinearMap.rTensor M τ z ∈ P.baseChange A' := by
  rw [← ArtinReesBaseChange.range_subtype_baseChange] at hz
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero =>
      simpa only [map_zero] using zero_mem (P.baseChange A')
  | tmul a p =>
      rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ p.2
  | add y y' hy hy' =>
      rw [map_add, map_add]
      exact add_mem hy hy'

/-- The base change of a submodule is annihilated by the base change of the quotient map.

No flatness is involved: the base change of `P` is spanned by the elements `1 ⊗ p` with `p ∈ P`,
and each of those is sent to `1 ⊗ 0`. -/
theorem baseChange_le_ker_baseChange_mkQ (A : Type*) [CommRing A] [Algebra R A]
    (P : Submodule R M) :
    P.baseChange A ≤ LinearMap.ker (LinearMap.baseChange A P.mkQ) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  intro z hz
  simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hp0 : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).2 hp
  simp only [SetLike.mem_coe, LinearMap.mem_ker, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul, hp0, TensorProduct.tmul_zero]

/-- The image of `x` in `M ⧸ P` dies in `A ⊗ (M ⧸ P)` as soon as `1 ⊗ x` lies in the base change
of `P`. -/
theorem one_tmul_mkQ_eq_zero_of_one_tmul_mem_baseChange {A : Type*} [CommRing A] [Algebra R A]
    (P : Submodule R M) {x : M} (hx : (1 : A) ⊗ₜ[R] x ∈ P.baseChange A) :
    (1 : A) ⊗ₜ[R] (P.mkQ x) = 0 := by
  have h := baseChange_le_ker_baseChange_mkQ A P hx
  rwa [LinearMap.mem_ker, LinearMap.baseChange_tmul] at h

/-- **Membership in a submodule descends along a faithfully flat algebra.**  If `1 ⊗ x` lies in
the base change of `P` to a faithfully flat `R`-algebra `A`, then `x` lies in `P`. -/
theorem mem_of_one_tmul_mem_baseChange {A : Type*} [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] (P : Submodule R M) {x : M}
    (hx : (1 : A) ⊗ₜ[R] x ∈ P.baseChange A) : x ∈ P :=
  (Submodule.Quotient.mk_eq_zero P).1
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff R (M ⧸ P) (P.mkQ x)).1
      (one_tmul_mkQ_eq_zero_of_one_tmul_mem_baseChange P hx))

/-- **Membership in a submodule descends along a finite family of algebras whose product is
faithfully flat.**  If `1 ⊗ x` lies in the base change of `P` to each `A i`, then `x` lies in
`P`.

The unit of the product ring is the finite sum of the images of the units of the factors, and
each summand of `1 ⊗ x` is the image of `(1 : A i) ⊗ x` along `Pi.single i`. -/
theorem mem_of_forall_one_tmul_mem_baseChange {ι : Type v} [Finite ι] {A : ι → Type w}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (hff : (RingHom.pi (fun i => algebraMap R (A i))).FaithfullyFlat)
    (P : Submodule R M) {x : M}
    (h : ∀ i, (1 : A i) ⊗ₜ[R] x ∈ P.baseChange (A i)) : x ∈ P := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have _ : Module.FaithfullyFlat R (∀ i, A i) := Module.faithfullyFlat_pi_of_ringHom_pi hff
  refine mem_of_one_tmul_mem_baseChange (A := ∀ i, A i) P ?_
  have h1 : ∑ i : ι, Pi.single i (1 : A i) = (1 : ∀ i, A i) :=
    Finset.univ_sum_single (1 : ∀ i, A i)
  rw [← h1, TensorProduct.sum_tmul]
  refine sum_mem fun i _ => ?_
  have hi := rTensor_mem_baseChange P (ArtinReesBaseChange.piSingleLinearMap R A i) (h i)
  rwa [LinearMap.rTensor_tmul, ArtinReesBaseChange.piSingleLinearMap_apply] at hi

end Submodule

end
