module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Descent of an element along a finite faithfully flat family of algebras

Let `R → A` be a faithfully flat ring map and `N` an `R`-module.  An element `x` of `A ⊗[R] N`
comes from `N` exactly when it is a *cocycle*: its two images in `A ⊗[R] (A ⊗[R] N)` agree.  This
file proves that, the version for a finite family `A i` whose product is faithfully flat over
`R`, and the reformulation in which the two images are taken in a third algebra `P i j` playing
the role of a tensor product `A i ⊗[R] A j`.  The last form is the one a cover produces: the
double overlaps come with their own rings of functions, identified with the tensor product only
through a comparison isomorphism.

This is the element-level content of descent of modules along a faithfully flat ring map,
Stacks 023M, in the form used to verify the sheaf axiom for a cartesian presheaf of modules.

## Main results

* `Module.Descent.exists_tmul_one_eq_of_cocycle`: **a cocycle in `A ⊗[R] N` comes from `N`.**
* `Module.Descent.exists_forall_tmul_one_eq_of_cocycle`: the same for a finite family of
  algebras whose product is faithfully flat.
* `Module.Descent.tmul_one_eq_lTensor_mk_of_pushout`: an agreement of two images in a ring `P`
  identified with `A ⊗[R] B` is a cocycle condition.
* `Module.Descent.existsUnique_forall_tmul_one_eq`: **the descent statement for a finite family**
  — a family of sections agreeing on the double overlaps comes from a unique element of `N`.

## Implementation notes

Faithful flatness enters only through `Module.FaithfullyFlat.tensorProduct_mk_injective`, applied
once to the quotient of `A ⊗[R] N` by the image of `N` and once for the uniqueness clause.  The
passage from one algebra to a finite family is the comparison `TensorProduct.piLeft`, so the
index type must be finite but nothing else about it is used.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Module.Descent

/-- **A cocycle in `A ⊗[R] N` comes from `N`.**  If the two images of `x` in `A ⊗[R] (A ⊗[R] N)`
agree then `x = 1 ⊗ₜ n` for some `n : N`. -/
theorem exists_tmul_one_eq_of_cocycle
    (R : Type u) (A : Type v) (N : Type w)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]
    [Module.FaithfullyFlat R A]
    (x : A ⊗[R] N)
    (hx : (1 : A) ⊗ₜ[R] x =
      (LinearMap.lTensor A (TensorProduct.mk R A N 1)) x) :
    ∃ n : N, (1 : A) ⊗ₜ[R] n = x := by
  let i : N →ₗ[R] A ⊗[R] N := TensorProduct.mk R A N 1
  let P := LinearMap.range i
  let q := P.mkQ
  have hz : q.comp i = 0 := by
    ext n
    exact (Submodule.Quotient.mk_eq_zero P).mpr ⟨n, rfl⟩
  have hqx : (1 : A) ⊗ₜ[R] q x = 0 := by
    simpa only [LinearMap.lTensor_tmul, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, hz, LinearMap.lTensor_zero, LinearMap.zero_apply]
      using (show (1 : A) ⊗ₜ[R] q x = (LinearMap.lTensor A q) ((LinearMap.lTensor A i) x) from
        congrArg (LinearMap.lTensor A q) hx)
  exact (Submodule.Quotient.mk_eq_zero P).mp
    ((Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := A) (M := _))
      (by simpa using hqx) : q x = 0)

/-- A cocycle for a finite family of algebras whose product is faithfully flat comes from `N`:
if the two images of `x i` and `x j` in `A i ⊗[R] (A j ⊗[R] N)` agree for all `i, j`, then all
the `x i` are the images of one element of `N`. -/
theorem exists_forall_tmul_one_eq_of_cocycle
    (R : Type u) (I : Type v) (A : I → Type w) (N : Type*)
    [CommRing R] [Finite I] [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)] [AddCommGroup N] [Module R N]
    [Module.FaithfullyFlat R (∀ i, A i)]
    (x : ∀ i, A i ⊗[R] N)
    (hx : ∀ i j, (1 : A i) ⊗ₜ[R] x j =
      LinearMap.lTensor (A i) (TensorProduct.mk R (A j) N 1) (x i)) :
    ∃ n : N, ∀ i, (1 : A i) ⊗ₜ[R] n = x i := by
  classical
  let _ := Fintype.ofFinite I
  let B := ∀ i, A i
  let e := TensorProduct.piLeft R N A
  let z : B ⊗[R] N := e.symm x
  have ez : e z = x := e.apply_symm_apply x
  have hz : (1 : B) ⊗ₜ[R] z =
      LinearMap.lTensor B (TensorProduct.mk R B N 1) z := by
    apply (TensorProduct.piLeft R (B ⊗[R] N) A).injective
    funext i
    apply (TensorProduct.congr (LinearEquiv.refl R (A i)) e).injective
    apply (TensorProduct.piRight R R (A i) (fun j => A j ⊗[R] N)).injective
    funext j
    have lhs :
        TensorProduct.piRight R R (A i) (fun j => A j ⊗[R] N)
          ((TensorProduct.congr (LinearEquiv.refl R (A i)) e)
            (TensorProduct.piLeft R (B ⊗[R] N) A ((1 : B) ⊗ₜ[R] z) i)) j =
          (1 : A i) ⊗ₜ[R] x j := by
      simp [TensorProduct.piLeft, TensorProduct.piRight, ez, B]
    rw [lhs, hx]
    have rhs (t : B ⊗[R] N) :
        TensorProduct.piRight R R (A i) (fun j => A j ⊗[R] N)
          ((TensorProduct.congr (LinearEquiv.refl R (A i)) e)
            (TensorProduct.piLeft R (B ⊗[R] N) A
              (LinearMap.lTensor B (TensorProduct.mk R B N 1) t) i)) j =
          LinearMap.lTensor (A i) (TensorProduct.mk R (A j) N 1) (e t i) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => simp [TensorProduct.piLeft, TensorProduct.piRight, e, B]
      | add t t' ht ht' => simp_all
    rw [rhs, ez]
  obtain ⟨n, hn⟩ := exists_tmul_one_eq_of_cocycle R B N z hz
  refine ⟨n, fun i => ?_⟩
  simpa [e, TensorProduct.piLeft, TensorProduct.piRight, B] using
    (congrArg (fun y => e y i) hn).trans (congrFun ez i)

/-- An agreement of the two images of `x : A ⊗[R] N` and `y : B ⊗[R] N` in `P ⊗[R] N`, for a ring
`P` `R`-linearly identified with `A ⊗[R] B` compatibly with the two algebra maps, is exactly the
cocycle condition relating `x` and `y`. -/
theorem tmul_one_eq_lTensor_mk_of_pushout
    (R A B P N : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R P]
    [AddCommGroup N] [Module R N]
    (eP : A ⊗[R] B ≃ₗ[R] P) (l : A →ₐ[R] P) (r : B →ₐ[R] P)
    (heP : ∀ a b, eP (a ⊗ₜ[R] b) = l a * r b)
    (x : A ⊗[R] N) (y : B ⊗[R] N)
    (h : TensorProduct.map l.toLinearMap LinearMap.id x =
      TensorProduct.map r.toLinearMap LinearMap.id y) :
    (1 : A) ⊗ₜ[R] y = LinearMap.lTensor A (TensorProduct.mk R B N 1) x := by
  let e := (TensorProduct.assoc R A B N).symm.trans
    (TensorProduct.congr eP (LinearEquiv.refl R N))
  apply e.injective
  have hy : e.toLinearMap ∘ₗ TensorProduct.mk R A (B ⊗[R] N) 1 =
      TensorProduct.map r.toLinearMap LinearMap.id :=
    TensorProduct.ext' fun b n => by simp [e, heP]
  have hx : e.toLinearMap ∘ₗ LinearMap.lTensor A (TensorProduct.mk R B N 1) =
      TensorProduct.map l.toLinearMap LinearMap.id :=
    TensorProduct.ext' fun a n => by simp [e, heP]
  exact (LinearMap.congr_fun hy y).trans (h.symm.trans (LinearMap.congr_fun hx x).symm)

/-- **Descent of an element along a finite faithfully flat family.**  A family of elements
`x i : A i ⊗[R] N` whose images agree in the rings `P i j` of the double overlaps comes from a
unique element of `N`. -/
theorem existsUnique_forall_tmul_one_eq
    (R : Type u) (I : Type v) (A : I → Type w) (N : Type*)
    [CommRing R] [Finite I] [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)] [AddCommGroup N] [Module R N]
    [Module.FaithfullyFlat R (∀ i, A i)]
    (P : I → I → Type*) [∀ i j, CommRing (P i j)]
    [∀ i j, Algebra R (P i j)]
    (eP : ∀ i j, A i ⊗[R] A j ≃ₗ[R] P i j)
    (l : ∀ i j, A i →ₐ[R] P i j) (r : ∀ i j, A j →ₐ[R] P i j)
    (heP : ∀ i j a b, eP i j (a ⊗ₜ[R] b) = l i j a * r i j b)
    (x : ∀ i, A i ⊗[R] N)
    (hx : ∀ i j,
      TensorProduct.map (l i j).toLinearMap LinearMap.id (x i) =
      TensorProduct.map (r i j).toLinearMap LinearMap.id (x j)) :
    ∃! n : N, ∀ i, (1 : A i) ⊗ₜ[R] n = x i := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨n, hn⟩ := exists_forall_tmul_one_eq_of_cocycle R I A N x
    (fun i j => tmul_one_eq_lTensor_mk_of_pushout R (A i) (A j) (P i j) N
      (eP i j) (l i j) (r i j) (heP i j) _ _ (hx i j))
  refine ⟨n, hn, fun n' hn' => ?_⟩
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := ∀ i, A i) N
  apply (TensorProduct.piLeft R N A).injective
  funext i
  simpa [TensorProduct.piLeft, TensorProduct.piRight] using (hn' i).trans (hn i).symm

end Module.Descent

end
