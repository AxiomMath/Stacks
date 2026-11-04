module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transports for composing base changes

This file collects four facts about base change of algebras.

## Main definitions

* `Algebra.TensorProduct.cancelBaseChangeTower`: for a tower `K → F → E` and a `K`-algebra `A`,
  the `E`-algebra equivalence `(A ⊗[K] F) ⊗[F] E ≃ₐ[E] A ⊗[K] E`.
* `AdjoinRoot.ridAlgEquiv`: the `T`-algebra equivalence between `AdjoinRoot` of `p` with
  coefficients moved to `T ⊗[R] R` and `AdjoinRoot (p.map (algebraMap R T))`.
* `AdjoinRoot.baseChangeAlgEquiv`: the `T`-algebra equivalence
  `T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (p.map (algebraMap R T))`.

## Main results

* `AdjoinRoot.baseChangeAlgEquiv_tmul_root`, `AdjoinRoot.baseChangeAlgEquiv_tmul_of`: the values
  of `AdjoinRoot.baseChangeAlgEquiv` on `1 ⊗ₜ root p` and on `1 ⊗ₜ of p r`.
* `IsFractionRing.of_ringEquiv_ringEquiv`: if `K` is a fraction field of `S`, then `L` is a
  fraction field of `R` for ring isomorphisms `R ≃+* S` and `K ≃+* L` compatible with
  `algebraMap R L`.
* `isLocalHom_algebraMap_of_isIntegral`: the structure map of an integral extension of local
  rings is a local homomorphism.

## Implementation notes

`Algebra.TensorProduct.cancelBaseChangeTower` is linear over `E` rather than over `A`, since
`Algebra A ((A ⊗[K] F) ⊗[F] E)` is not an instance: `Algebra S (X ⊗[R] Y)` requires
`IsScalarTower R S X`.
-/

@[expose] public section

open scoped TensorProduct

open Polynomial

namespace Algebra.TensorProduct

/-- For a tower `K → F → E` and a `K`-algebra `A`, the `E`-algebra equivalence
`(A ⊗[K] F) ⊗[F] E ≃ₐ[E] A ⊗[K] E`, where `A ⊗[K] F` is an `F`-algebra and both sides are
`E`-algebras through their right factors. -/
noncomputable def cancelBaseChangeTower (K F E A : Type*) [CommRing K] [CommRing F] [CommRing E]
    [CommRing A] [Algebra K F] [Algebra K A] [Algebra F E] [Algebra K E] [IsScalarTower K F E] :
    letI : Algebra F (A ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra E ((A ⊗[K] F) ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra E (A ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
    ((A ⊗[K] F) ⊗[F] E) ≃ₐ[E] (A ⊗[K] E) :=
  letI : Algebra F (A ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra E ((A ⊗[K] F) ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra E (A ⊗[K] E) := Algebra.TensorProduct.rightAlgebra
  (Algebra.TensorProduct.commRight F E (A ⊗[K] F)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
      (Algebra.TensorProduct.commRight K F A).symm).trans
        ((Algebra.TensorProduct.cancelBaseChange K F E E A).trans
          (Algebra.TensorProduct.commRight K E A)))

end Algebra.TensorProduct

namespace AdjoinRoot

/-- Mapping `p : R[X]` to `(T ⊗[R] R)[X]` along `Algebra.TensorProduct.includeRight` and then
to `T[X]` along `Algebra.TensorProduct.rid R T T` gives `p.map (algebraMap R T)`. -/
theorem map_includeRight_map_rid (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (p : R[X]) :
    (p.map (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := R)).toRingHom).map
      ((Algebra.TensorProduct.rid R T T).toRingEquiv : (T ⊗[R] R) →+* T)
      = p.map (algebraMap R T) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp [Algebra.smul_def]

/-- The `T`-algebra equivalence between `AdjoinRoot` of `p` with coefficients mapped to
`T ⊗[R] R` and `AdjoinRoot (p.map (algebraMap R T))`, induced by `Algebra.TensorProduct.rid`. -/
noncomputable def ridAlgEquiv (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (p : R[X]) :
    AdjoinRoot (p.map (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := R)).toRingHom)
      ≃ₐ[T] AdjoinRoot (p.map (algebraMap R T)) :=
  AlgEquiv.ofRingEquiv (f := AdjoinRoot.mapRingEquiv
    (Algebra.TensorProduct.rid R T T).toRingEquiv _ _
    (map_includeRight_map_rid R T p ▸ Associated.refl _)) (fun x => by
      rw [AdjoinRoot.algebraMap_eq', AdjoinRoot.algebraMap_eq', RingHom.comp_apply,
        RingHom.comp_apply, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of]
      simp)

/-- `AdjoinRoot.ridAlgEquiv` acts as `AdjoinRoot.map` along `Algebra.TensorProduct.rid`. -/
theorem ridAlgEquiv_apply (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (p : R[X]) (x) :
    ridAlgEquiv R T p x = AdjoinRoot.map
      ((Algebra.TensorProduct.rid R T T).toRingEquiv : (T ⊗[R] R) →+* T) _ _
      (map_includeRight_map_rid R T p ▸ dvd_refl _) x := rfl

/-- **Adjoining a root commutes with base change**:
`T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (p.map (algebraMap R T))`. -/
noncomputable def baseChangeAlgEquiv (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    (p : R[X]) :
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (p.map (algebraMap R T)) :=
  (AdjoinRoot.tensorAlgEquiv p _ rfl).trans (ridAlgEquiv R T p)

/-- Base change sends the root to the root. -/
@[simp] theorem baseChangeAlgEquiv_tmul_root (R T : Type*) [CommRing R] [CommRing T]
    [Algebra R T] (p : R[X]) :
    baseChangeAlgEquiv R T p (1 ⊗ₜ AdjoinRoot.root p)
      = AdjoinRoot.root (p.map (algebraMap R T)) := by
  rw [baseChangeAlgEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    ridAlgEquiv_apply, AdjoinRoot.map_root]

/-- Base change acts on the coefficients through `algebraMap R T`. -/
@[simp] theorem baseChangeAlgEquiv_tmul_of (R T : Type*) [CommRing R] [CommRing T]
    [Algebra R T] (p : R[X]) (r : R) :
    baseChangeAlgEquiv R T p (1 ⊗ₜ AdjoinRoot.of p r)
      = AdjoinRoot.of (p.map (algebraMap R T)) (algebraMap R T r) := by
  rw [baseChangeAlgEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
    ridAlgEquiv_apply, AdjoinRoot.map_of]
  simp [Algebra.smul_def]

end AdjoinRoot

/-- If `K` is a fraction field of `S`, and `e : R ≃+* S` and `f : K ≃+* L` are ring isomorphisms
compatible with `algebraMap R L`, then `L` is a fraction field of `R`. -/
theorem IsFractionRing.of_ringEquiv_ringEquiv {R S K L : Type*}
    [CommRing R] [CommRing S] [CommRing K] [CommRing L]
    [Algebra S K] [IsFractionRing S K] [Algebra R L]
    (e : R ≃+* S) (f : K ≃+* L)
    (h : ∀ x : R, algebraMap R L x = f (algebraMap S K (e x))) :
    IsFractionRing R L := by
  let : Algebra S L := ((f : K →+* L).comp (algebraMap S K)).toAlgebra
  have : IsFractionRing S L :=
    IsFractionRing.of_algEquiv (AlgEquiv.ofRingEquiv (f := f) fun _ => rfl)
  exact IsFractionRing.of_ringEquiv_left e h

/-- If `B` is a local ring integral over a local ring `A`, then `algebraMap A B` is a local
homomorphism. -/
@[ega "II 6.4.5.1" "special case"]
theorem isLocalHom_algebraMap_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    IsLocalHom (algebraMap A B) := by
  have hcomap : (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
      = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal B))
  refine ⟨fun a ha => IsLocalRing.notMem_maximalIdeal.mp ?_⟩
  rw [← hcomap]
  exact fun hmem => IsLocalRing.notMem_maximalIdeal.mpr ha (Ideal.mem_comap.mp hmem)

end
