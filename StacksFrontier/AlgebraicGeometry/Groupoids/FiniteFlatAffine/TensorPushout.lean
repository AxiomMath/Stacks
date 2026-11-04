module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Flat.Rank
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# Changing the two factors of a tensor product is a pushout square

For `R`-algebra maps `s : A → B` and `p : D → E`, the square of tensor products

```
A ⊗[R] D ⟶ B ⊗[R] D
    ↓           ↓
A ⊗[R] E ⟶ B ⊗[R] E
```

is cocartesian: changing the two factors separately commutes, and either change is the base
change of the other. Consequently the scalar determinant of a finite projective algebra and
its stalk rank are both computed from the corresponding data on the left-hand column.

## Main results

* `Algebra.TensorProduct.isPushout_map`: the displayed square is a pushout of commutative
  rings.
* `ProjectiveDeterminant.finite_and_projective_of_isPushout`: around a pushout square of
  commutative rings the right-hand algebra stays finite projective.
* `ProjectiveDeterminant.map_det_lmul_of_isPushout`: its scalar determinants are the images of
  those on the left.
* `ProjectiveDeterminant.rankAtStalk_of_isPushout`: its stalk ranks are those on the left.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Algebra.TensorProduct

variable {R A B D E : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D] [CommRing E]
variable [Algebra R A] [Algebra R B] [Algebra R D] [Algebra R E]

/-- Changing the right factor and then the left factor changes both at once. -/
theorem map_id_comp_map (s : A →ₐ[R] B) (p : D →ₐ[R] E) :
    (map s (AlgHom.id R E)).comp (map (AlgHom.id R A) p) = map s p := by
  ext <;> simp

/-- Changing the left factor and then the right factor changes both at once. -/
theorem map_comp_map_id (s : A →ₐ[R] B) (p : D →ₐ[R] E) :
    (map (AlgHom.id R B) p).comp (map s (AlgHom.id R D)) = map s p := by
  ext <;> simp

/-- Changing the left and the right factor of a tensor product commute. -/
theorem map_id_comp_map_eq_map_comp_map_id (s : A →ₐ[R] B) (p : D →ₐ[R] E) :
    (map s (AlgHom.id R E)).comp (map (AlgHom.id R A) p) =
      (map (AlgHom.id R B) p).comp (map s (AlgHom.id R D)) :=
  (map_id_comp_map s p).trans (map_comp_map_id s p).symm

/-- Changing both factors of a tensor product is a map of algebras over any ring acting on the
left factor compatibly with the left component. -/
private theorem isScalarTower_map (S : Type u) [CommRing S] [Algebra R S] [Algebra S A]
    [Algebra S B] [SMulCommClass R S A] [SMulCommClass R S B] (s : A →ₐ[R] B) (p : D →ₐ[R] E)
    (hs : ∀ x : S, s (algebraMap S A x) = algebraMap S B x) :
    let _ : Algebra S (A ⊗[R] D) := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra S (B ⊗[R] E) := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra (A ⊗[R] D) (B ⊗[R] E) := (map s p).toRingHom.toAlgebra
    IsScalarTower S (A ⊗[R] D) (B ⊗[R] E) := by
  let _ : Algebra S (A ⊗[R] D) := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra S (B ⊗[R] E) := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra (A ⊗[R] D) (B ⊗[R] E) := (map s p).toRingHom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x ↦ ?_)
  show (algebraMap S B x) ⊗ₜ[R] (1 : E) = map s p ((algebraMap S A x) ⊗ₜ[R] (1 : D))
  rw [map_tmul, map_one, hs]

/-- Changing the two factors of a tensor product separately is a cocartesian square of
commutative rings. -/
theorem isPushout_map (s : A →ₐ[R] B) (p : D →ₐ[R] E) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom (map s (AlgHom.id R D)).toRingHom)
      (CommRingCat.ofHom (map (AlgHom.id R A) p).toRingHom)
      (CommRingCat.ofHom (map (AlgHom.id R B) p).toRingHom)
      (CommRingCat.ofHom (map s (AlgHom.id R E)).toRingHom) := by
  let _ : Algebra A B := s.toRingHom.toAlgebra
  have hs : ∀ a, s a = algebraMap A B a := fun _ ↦ rfl
  let _ : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r ↦ (s.commutes r).symm)
  let _ : Algebra A (A ⊗[R] D) := leftAlgebra (R := R) (S := A) (A := A) (B := D)
  let _ : Algebra A (B ⊗[R] D) := leftAlgebra (R := R) (S := A) (A := B) (B := D)
  let _ : Algebra A (A ⊗[R] E) := leftAlgebra (R := R) (S := A) (A := A) (B := E)
  let _ : Algebra A (B ⊗[R] E) := leftAlgebra (R := R) (S := A) (A := B) (B := E)
  let _ : Algebra B (B ⊗[R] D) := leftAlgebra (R := R) (S := B) (A := B) (B := D)
  let _ : Algebra B (B ⊗[R] E) := leftAlgebra (R := R) (S := B) (A := B) (B := E)
  let _ : Algebra (A ⊗[R] D) (B ⊗[R] D) := (map s (AlgHom.id R D)).toRingHom.toAlgebra
  let _ : Algebra (A ⊗[R] E) (B ⊗[R] E) := (map s (AlgHom.id R E)).toRingHom.toAlgebra
  let _ : Algebra (A ⊗[R] D) (A ⊗[R] E) := (map (AlgHom.id R A) p).toRingHom.toAlgebra
  let _ : Algebra (B ⊗[R] D) (B ⊗[R] E) := (map (AlgHom.id R B) p).toRingHom.toAlgebra
  let _ : Algebra (A ⊗[R] D) (B ⊗[R] E) := (map s p).toRingHom.toAlgebra
  let _ : IsScalarTower A (A ⊗[R] D) (B ⊗[R] D) :=
    isScalarTower_map A s (AlgHom.id R D) (fun a ↦ by simpa using hs a)
  let _ : IsScalarTower A (A ⊗[R] E) (B ⊗[R] E) :=
    isScalarTower_map A s (AlgHom.id R E) (fun a ↦ by simpa using hs a)
  let _ : IsScalarTower A (A ⊗[R] D) (A ⊗[R] E) :=
    isScalarTower_map A (AlgHom.id R A) p (fun _ ↦ rfl)
  let _ : IsScalarTower A (B ⊗[R] D) (B ⊗[R] E) :=
    isScalarTower_map A (AlgHom.id R B) p (fun _ ↦ rfl)
  let _ : IsScalarTower A (A ⊗[R] D) (B ⊗[R] E) :=
    isScalarTower_map A s p (fun a ↦ by simpa using hs a)
  let _ : IsScalarTower B (B ⊗[R] D) (B ⊗[R] E) :=
    isScalarTower_map B (AlgHom.id R B) p (fun _ ↦ rfl)
  let _ : IsScalarTower A B (B ⊗[R] D) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A B (B ⊗[R] E) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (A ⊗[R] D) (A ⊗[R] E) (B ⊗[R] E) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x ↦
      congrArg (fun k : (A ⊗[R] D) →ₐ[R] B ⊗[R] E ↦ k x) (map_id_comp_map s p).symm)
  let _ : IsScalarTower (A ⊗[R] D) (B ⊗[R] D) (B ⊗[R] E) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x ↦
      congrArg (fun k : (A ⊗[R] D) →ₐ[R] B ⊗[R] E ↦ k x) (map_comp_map_id s p).symm)
  have hD : Algebra.IsPushout A B (A ⊗[R] D) (B ⊗[R] D) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R D A B
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have hE : Algebra.IsPushout A B (A ⊗[R] E) (B ⊗[R] E) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R E A B
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  let _ : Algebra.IsPushout (A ⊗[R] D) (B ⊗[R] D) (A ⊗[R] E) (B ⊗[R] E) :=
    (hD.symm.comp_iff.mp hE.symm).symm
  exact CommRingCat.isPushout_of_isPushout (A ⊗[R] D) (B ⊗[R] D) (A ⊗[R] E) (B ⊗[R] E)

end Algebra.TensorProduct

namespace ProjectiveDeterminant

section Pushout

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Module.Finite A B] [Module.Projective A B]

/-- Around a cocartesian square of commutative rings, a finite projective algebra stays finite
and projective. -/
theorem finite_and_projective_of_isPushout (a : A →+* A') (b : B →+* B')
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom a)
      (CommRingCat.ofHom b) (CommRingCat.ofHom (algebraMap A' B'))) :
    Module.Finite A' B' ∧ Module.Projective A' B' := by
  let _ := a.toAlgebra
  let _ := b.toAlgebra
  let _ := (b.comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let _ : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.mp h
  let _ : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  exact ⟨Module.Finite.equiv (Algebra.IsPushout.equiv A A' B B').toLinearEquiv,
    Module.Projective.of_equiv (Algebra.IsPushout.equiv A A' B B').toLinearEquiv⟩

/-- Around a cocartesian square of commutative rings, the scalar determinant of multiplication
by an element upstairs is the image of the scalar determinant downstairs. -/
theorem map_det_lmul_of_isPushout [Module.Finite A' B'] [Module.Projective A' B']
    (a : A →+* A') (b : B →+* B')
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom a)
      (CommRingCat.ofHom b) (CommRingCat.ofHom (algebraMap A' B'))) (x : B) :
    a (ProjectiveDeterminant.det (Algebra.lmul A B x)) =
      ProjectiveDeterminant.det (Algebra.lmul A' B' (b x)) := by
  let _ := a.toAlgebra
  let _ := b.toAlgebra
  let _ := (b.comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let _ : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.mp h
  let _ : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  have hmap : (Algebra.IsPushout.equiv A A' B B').toLinearMap.comp
      ((Algebra.lmul A' (A' ⊗[A] B) (1 ⊗ₜ[A] x)).comp
        (Algebra.IsPushout.equiv A A' B B').symm.toLinearMap) =
      Algebra.lmul A' B' (b x) := by
    ext y
    have hb : algebraMap B B' x = b x := rfl
    simp [Algebra.IsPushout.equiv_tmul, hb]
  calc
    a (ProjectiveDeterminant.det (Algebra.lmul A B x)) =
        ProjectiveDeterminant.det ((Algebra.lmul A B x).baseChange A') :=
      ProjectiveDeterminant.det_baseChange _
    _ = ProjectiveDeterminant.det (Algebra.lmul A' (A' ⊗[A] B) (1 ⊗ₜ[A] x)) := by
      rw [Algebra.baseChange_lmul]
    _ = ProjectiveDeterminant.det (Algebra.lmul A' B' (b x)) := by
      rw [← hmap]
      exact (ProjectiveDeterminant.det_conj (Algebra.IsPushout.equiv A A' B B').toLinearEquiv
        _).symm

/-- Around a cocartesian square of commutative rings, the stalk ranks upstairs are the stalk
ranks downstairs. -/
theorem rankAtStalk_of_isPushout (a : A →+* A') (b : B →+* B')
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom a)
      (CommRingCat.ofHom b) (CommRingCat.ofHom (algebraMap A' B')))
    (q : PrimeSpectrum A') :
    Module.rankAtStalk B' q = Module.rankAtStalk B (q.comap a) := by
  let _ := a.toAlgebra
  let _ := b.toAlgebra
  let _ := (b.comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let _ : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout A B A' B' q

end Pushout

end ProjectiveDeterminant

end
