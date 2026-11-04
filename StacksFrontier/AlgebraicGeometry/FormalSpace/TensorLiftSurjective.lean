module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Surjectivity of the tensor comparison map of a pair of morphisms of schemes

A pair of morphisms of schemes `p : P ⟶ U` and `q : P ⟶ V` induces a ring map from the tensor
product over `ℤ` of the coordinate rings of `U` and `V` to that of `P`. This file records
conditions under which that map is surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.tensor_lift_surjective_of_comp`: surjectivity survives
  composing the second morphism with a morphism surjective on global sections.
* `AlgebraicGeometry.FormalSpace.tensor_lift_surjective_of_isPullback_comp`: for a fibre
  product of affine schemes over an affine base, followed on the second factor by a morphism
  surjective on global sections, the map is surjective.
* `AlgebraicGeometry.FormalSpace.tensor_lift_surjective_comp`: surjectivity survives
  precomposing both morphisms with a morphism surjective on global sections.
* `AlgebraicGeometry.FormalSpace.tensor_lift_surjective_congr`: surjectivity depends on the
  two morphisms only through their values.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The map from the tensor product over `ℤ` of the coordinate rings of two schemes to that of
a third stays surjective when the second of the two morphisms is replaced by its composite
with a morphism surjective on global sections. -/
lemma tensor_lift_surjective_of_comp {U V Q P : Scheme.{u}} (p : P ⟶ U) (r : P ⟶ Q) (s : Q ⟶ V)
    (hs : Function.Surjective s.appTop.hom)
    (h : Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      r.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      (r ≫ s).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  have hfac : Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
        (r ≫ s).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _) =
      (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom r.appTop.hom.toIntAlgHom
          (fun _ _ ↦ Commute.all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id ℤ Γ(U, ⊤)) s.appTop.hom.toIntAlgHom) :=
    Algebra.TensorProduct.ext' fun _ _ ↦ by simp; rfl
  rw [hfac, AlgHom.coe_comp]
  exact h.comp (Algebra.TensorProduct.map_surjective (f := AlgHom.id ℤ Γ(U, ⊤))
    (g := s.appTop.hom.toIntAlgHom) (fun x ↦ ⟨x, rfl⟩) hs)

/-- For a fibre product `P = U ×_Z V` of affine schemes over an affine base, followed on the
second factor by a morphism `s : V ⟶ W` surjective on global sections, the canonical map from
the tensor product over `ℤ` of the coordinate rings of `U` and `W` to the coordinate ring of
`P` is surjective. -/
lemma tensor_lift_surjective_of_isPullback_comp {U V W Z P : Scheme.{u}} [IsAffine U]
    [IsAffine V] [IsAffine Z] {p : P ⟶ U} {q : P ⟶ V} {a : U ⟶ Z} {b : V ⟶ Z}
    (sq : IsPullback p q a b) (s : V ⟶ W) (hs : Function.Surjective s.appTop.hom) :
    Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      (q ≫ s).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  refine tensor_lift_surjective_of_comp p q s hs ?_
  have _ : IsAffine P := IsAffine.of_isPullback sq
  let base := Γ(Z, ⊤)
  let left := Γ(U, ⊤)
  let right := Γ(V, ⊤)
  let result := Γ(P, ⊤)
  let _ : Algebra base left := a.appTop.hom.toAlgebra
  let _ : Algebra base right := b.appTop.hom.toAlgebra
  let _ : Algebra base result := (p.appTop.hom.comp a.appTop.hom).toAlgebra
  let _ : Algebra left result := p.appTop.hom.toAlgebra
  let _ : Algebra right result := q.appTop.hom.toAlgebra
  let _ : IsScalarTower base left result := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower base right result :=
    .of_algebraMap_eq fun x ↦ congrArg (fun φ ↦ φ.appTop.hom x) sq.w
  let _ : Algebra.IsPushout base left right result :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback sq)
  have heq : Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom q.appTop.hom.toIntAlgHom
      (fun _ _ ↦ Commute.all _ _) =
      ((Algebra.IsPushout.equiv base left right result).toAlgHom.restrictScalars ℤ).comp
        (Algebra.TensorProduct.mapOfCompatibleSMul base ℤ ℤ left right) := by
    apply Algebra.TensorProduct.ext'
    intro first second
    show _ = (Algebra.IsPushout.equiv base left right result) (first ⊗ₜ[base] second)
    rw [Algebra.IsPushout.equiv_tmul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [heq]
  exact (Algebra.IsPushout.equiv base left right result).surjective.comp
    (Algebra.TensorProduct.mapOfCompatibleSMul_surjective base ℤ ℤ left right)

/-- The map from the tensor product over `ℤ` of the coordinate rings of two schemes to that of
a third stays surjective when both morphisms are precomposed with a morphism `l` surjective on
global sections. -/
lemma tensor_lift_surjective_comp {U V P W : Scheme.{u}} (l : W ⟶ P) (p : P ⟶ U) (q : P ⟶ V)
    (hl : Function.Surjective l.appTop.hom)
    (h : Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      q.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Surjective (Algebra.TensorProduct.lift (l ≫ p).appTop.hom.toIntAlgHom
      (l ≫ q).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  have hfac : Algebra.TensorProduct.lift (l ≫ p).appTop.hom.toIntAlgHom
        (l ≫ q).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _) =
      l.appTop.hom.toIntAlgHom.comp
        (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom q.appTop.hom.toIntAlgHom
          (fun _ _ ↦ Commute.all _ _)) :=
    Algebra.TensorProduct.ext' fun _ _ ↦ by simp; rfl
  rw [hfac, AlgHom.coe_comp]
  exact hl.comp h

/-- Surjectivity of the map from the tensor product over `ℤ` of the coordinate rings of two
schemes depends on the pair of morphisms only through their values, the commutation proof the
map carries being irrelevant. -/
lemma tensor_lift_surjective_congr {U V P : Scheme.{u}} {p p' : P ⟶ U} {q q' : P ⟶ V}
    (hp : p = p') (hq : q = q')
    (h : Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      q.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Surjective (Algebra.TensorProduct.lift p'.appTop.hom.toIntAlgHom
      q'.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  subst hp hq
  exact h

end AlgebraicGeometry.FormalSpace

end
