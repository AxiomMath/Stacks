module

public import StacksFrontier.RingTheory.FormsTrace.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsIndependence
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# Transport of trace maps on forms along isomorphisms of rings

Condition (1) of Stacks, Lemma 0FLB is a statement about a finite projective ring map `A → B`
and the modules of absolute differential forms of `A` and `B`; it is invariant under
isomorphisms of ring maps. This file proves that invariance: given ring isomorphisms
`A ≅ A'` and `B ≅ B'` compatible with `A → B` and `A' → B'`, maps `Θ'^p` satisfying condition
(1) for `A' → B'` give maps satisfying it for `A → B`, by conjugating with the induced
isomorphisms of forms.

## Main results

* `Stacks.FormsTrace.formsMap_self`: the pull-back of forms along the identity is the identity.
* `Stacks.FormsTrace.trace_ringEquiv`: the trace is invariant under isomorphisms.
* `Stacks.FormsTrace.exists_isFormsTrace_of_ringEquiv`: condition (1) transports.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Stacks.Discriminant (finiteProjectiveTrace)

universe u

namespace Stacks.FormsTrace

section Identity

variable (R : Type u) [CommRing R]

/-- The pull-back of forms along the identity is the identity. -/
theorem formsMap_self (p : ℕ) (ω : ⋀[R]^p Ω[R⁄ℤ]) : formsMap R R p ω = ω :=
  ExteriorAlgebra.powMapₛₗ_eq_self p _ (fun _ => rfl) (Stacks.DeRham.kaehlerMapₛₗ_self R) ω

end Identity

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B']

/-- **The trace is invariant under isomorphisms of finite projective ring maps**: for ring
isomorphisms `eA : A ≅ A'`, `eB : B ≅ B'` compatible with the algebra maps,
`Trace_{B'/A'}(eB b) = eA (Trace_{B/A}(b))`. -/
theorem trace_ringEquiv (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    [Module.Finite A B] [Module.Projective A B] [Module.Finite A' B'] [Module.Projective A' B']
    (b : B) : trace A' B' (eB b) = eA (trace A B b) := by
  let : Algebra A B' := ((algebraMap A' B').comp eA.toRingHom).toAlgebra
  let e : B ≃ₗ[A] B' :=
    { eB.toAddEquiv with
      map_smul' := fun a x => by
        change eB (a • x) = (algebraMap A' B' (eA a)) * eB x
        rw [Algebra.smul_def, map_mul, h] }
  have : Module.Finite A B' := Module.Finite.equiv e
  have : Module.Projective A B' := Module.Projective.of_equiv e
  have h1 : finiteProjectiveTrace A B' (e.conj (Algebra.lmul A B b)) =
      finiteProjectiveTrace A B (Algebra.lmul A B b) :=
    Stacks.Discriminant.finiteProjectiveTrace_conj_linearEquiv e _
  have h2 := Stacks.Discriminant.finiteProjectiveTrace_congr_ringEquiv (C := B') eA
    (fun _ => rfl) (e.conj (Algebra.lmul A B b))
    (Algebra.lmul A' B' (eB b)) (fun x => by
      change eB (b * eB.symm x) = eB b * x
      rw [map_mul, RingEquiv.apply_symm_apply])
  change finiteProjectiveTrace A' B' (Algebra.lmul A' B' (eB b)) =
    eA (finiteProjectiveTrace A B (Algebra.lmul A B b))
  rw [← h2, h1]

/-- **`IsFormsTrace` transports along isomorphisms of ring maps.** Let
`eA : A ≅ A'` and `eB : B ≅ B'` be ring isomorphisms compatible with finite projective ring maps
`A → B` and `A' → B'`. If some maps `Θ'^p : Ω^p_{B'} → Ω^p_{A'}` satisfy condition (1) for
`A' → B'`, then the conjugates `Θ^p = eA^{-1} ∘ Θ'^p ∘ eB` satisfy it for `A → B`. -/
theorem exists_isFormsTrace_of_ringEquiv (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    [Module.Finite A B] [Module.Projective A B] [Module.Finite A' B'] [Module.Projective A' B']
    (H : ∃ Θ' : ∀ p : ℕ, ⋀[B']^p Ω[B'⁄ℤ] →ₗ[A'] ⋀[A']^p Ω[A'⁄ℤ], IsFormsTrace A' B' Θ') :
    ∃ Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ], IsFormsTrace A B Θ := by
  obtain ⟨Θ', hΘ'⟩ := H
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let : Algebra A' A := eA.symm.toRingHom.toAlgebra
  let : Algebra B B' := eB.toRingHom.toAlgebra
  let : Algebra A B' := ((algebraMap A' B').comp eA.toRingHom).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a => (h a).symm
  have : IsScalarTower A A' A :=
    IsScalarTower.of_algebraMap_eq fun a => (eA.symm_apply_apply a).symm
  have hB (p : ℕ) (a : A) (x : ⋀[B]^p Ω[B⁄ℤ]) :
      formsMap B B' p (a • x) = eA a • formsMap B B' p x := by
    rw [← algebraMap_smul B a x, map_smulₛₗ]
    change eB (algebraMap A B a) • _ = _
    rw [h, algebraMap_smul]
  have hA (p : ℕ) (a' : A') (y : ⋀[A']^p Ω[A'⁄ℤ]) :
      formsMap A' A p (a' • y) = eA.symm a' • formsMap A' A p y :=
    map_smulₛₗ _ a' y
  refine ⟨fun p =>
    { toFun := fun x => formsMap A' A p (Θ' p (formsMap B B' p x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a x => by
        change formsMap A' A p (Θ' p (formsMap B B' p (a • x))) =
          a • formsMap A' A p (Θ' p (formsMap B B' p x))
        rw [hB, map_smul, hA, RingEquiv.symm_apply_apply] }, ?_⟩
  intro p b ω
  change formsMap A' A p (Θ' p (formsMap B B' p (b • formsMap A B p ω))) = _
  rw [map_smulₛₗ, formsMap_formsMap (A := A) (B := B) (C := B'),
    ← formsMap_formsMap (A := A) (B := A') (C := B')]
  change formsMap A' A p (Θ' p (eB b • formsMap A' B' p (formsMap A A' p ω))) = _
  rw [hΘ', hA, formsMap_formsMap (A := A) (B := A') (C := A), formsMap_self,
    trace_ringEquiv eA eB h, RingEquiv.symm_apply_apply]

end Stacks.FormsTrace

end
