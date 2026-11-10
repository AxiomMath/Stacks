module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Quotients of finite products of rings

Let `A i` be finitely many commutative rings. This file records that an ideal of the product
`∀ i, A i` is the product of its coordinate images, so that a quotient of the product is the
product of the quotients of the factors, and that a finite product of étale algebras is étale.

## Main results

* `Ideal.map_ringHomPi`: the extension of an ideal along `R →+* ∀ i, A i` is the product of
  its extensions along the factors.
* `Ideal.quotientPiRingEquiv`: a quotient of a product by a product of ideals is the product
  of the quotients. (No finiteness is needed here.)
* `Ideal.quotientPiEvalRingEquiv`: a quotient of a finite product by any ideal is the product
  of the quotients of the factors by the coordinate images of that ideal.
* `RingHom.Etale.pi`: a finite product of étale ring maps is étale.
-/

@[expose] public section

namespace Ideal

variable {ι : Type*} {R : Type*} [CommRing R] {A : ι → Type*} [∀ i, CommRing (A i)]

/-- The extension of an ideal along the map into a finite product is the product of its
extensions along the factors. -/
public theorem map_ringHomPi [Finite ι] (f : ∀ i, R →+* A i) (I : Ideal R) :
    I.map (RingHom.pi f) = Ideal.pi fun i ↦ I.map (f i) := by
  apply (Ideal.piOrderIso (R := A)).injective
  funext i
  change Ideal.map (Pi.evalRingHom A i) (Ideal.map (RingHom.pi f) I) =
    Ideal.map (Pi.evalRingHom A i) (Ideal.pi fun j ↦ I.map (f j))
  rw [Ideal.map_map, Ideal.map_evalRingHom_pi]
  congr 1

/-- The quotient of a product of rings by a product of ideals is the product of the
quotients. -/
public noncomputable def quotientPiRingEquiv (I : ∀ i, Ideal (A i)) :
    ((∀ i, A i) ⧸ Ideal.pi I) ≃+* ∀ i, A i ⧸ I i := by
  refine RingEquiv.ofBijective
    (Ideal.Quotient.lift (Ideal.pi I)
      (RingHom.pi fun i ↦ (Ideal.Quotient.mk (I i)).comp (Pi.evalRingHom A i))
      (fun a ha ↦ ?_)) ⟨?_, ?_⟩
  · ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (ha i)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.Quotient.eq_zero_iff_mem.mpr fun i ↦ ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx i)
  · intro z
    choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (z i)
    exact ⟨Ideal.Quotient.mk (Ideal.pi I) a, funext ha⟩

/-- `Ideal.quotientPiRingEquiv` sends the class of `a` to the family of the classes of its
coordinates. -/
@[simp]
public theorem quotientPiRingEquiv_mk (I : ∀ i, Ideal (A i)) (a : ∀ i, A i) :
    quotientPiRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) a) =
      fun i ↦ Ideal.Quotient.mk (I i) (a i) := rfl

/-- Every ideal of a finite product of rings is the product of its coordinate images. -/
public theorem pi_map_evalRingHom [Finite ι] (K : Ideal (∀ i, A i)) :
    Ideal.pi (fun i ↦ K.map (Pi.evalRingHom A i)) = K :=
  Ideal.piOrderIso.symm_apply_apply K

/-- The quotient of a finite product of rings by any ideal is the product of the quotients by
the coordinate images of that ideal. -/
public noncomputable def quotientPiEvalRingEquiv [Finite ι] (K : Ideal (∀ i, A i)) :
    ((∀ i, A i) ⧸ K) ≃+* ∀ i, A i ⧸ K.map (Pi.evalRingHom A i) :=
  (Ideal.quotEquivOfEq (pi_map_evalRingHom K).symm).trans (Ideal.quotientPiRingEquiv _)

/-- `Ideal.quotientPiEvalRingEquiv` sends the class of `a` to the family of the classes of its
coordinates. -/
@[simp]
public theorem quotientPiEvalRingEquiv_mk [Finite ι] (K : Ideal (∀ i, A i)) (a : ∀ i, A i) :
    quotientPiEvalRingEquiv K (Ideal.Quotient.mk K a) =
      fun i ↦ Ideal.Quotient.mk (K.map (Pi.evalRingHom A i)) (a i) := rfl

/-- The `i`-th coordinate of `Ideal.quotientPiEvalRingEquiv` is the quotient map induced by the
`i`-th projection. -/
public theorem evalRingHom_comp_quotientPiEvalRingEquiv [Finite ι] (K : Ideal (∀ i, A i))
    (i : ι) :
    (Pi.evalRingHom (fun j ↦ A j ⧸ K.map (Pi.evalRingHom A j)) i).comp
        (quotientPiEvalRingEquiv K).toRingHom =
      Ideal.quotientMap (K.map (Pi.evalRingHom A i)) (Pi.evalRingHom A i)
        Ideal.le_comap_map := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end Ideal

namespace RingHom

/-- A finite product of étale algebras is étale. -/
public theorem Etale.pi {ι : Type*} [_root_.Finite ι] {R : Type*} [CommRing R] {A : ι → Type*}
    [∀ i, CommRing (A i)] (f : ∀ i, R →+* A i) (hf : ∀ i, (f i).Etale) :
    (RingHom.pi f).Etale := by
  let (i : ι) : Algebra R (A i) := (f i).toAlgebra
  let (i : ι) : Algebra.Etale R (A i) := hf i
  change @Algebra.Etale R (∀ i, A i) _ _ (RingHom.pi f).toAlgebra
  have halg : (RingHom.pi f).toAlgebra = Pi.algebra ι A := by
    apply Algebra.algebra_ext
    intro r
    rfl
  rw [halg]
  infer_instance

end RingHom
