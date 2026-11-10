module

public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.DifferentIdeal
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProjectiveTraceContraction
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Transport of the Dedekind setup along ring isomorphisms

Let `A → B` and `A' → B'` be ring maps and `eA : A ≃ A'`, `eB : B ≃ B'` ring isomorphisms
compatible with them. The hypotheses of the Dedekind different transfer from `A → B` to
`A' → B'`, and the induced isomorphism of generic fibres `B ⊗[A] Q(A) ≃ B' ⊗[A'] Q(A')`
identifies the traces, the complementary modules and the Dedekind differents. In particular `1`
lies in one complementary module exactly when it lies in the other, and the Dedekind different
ideal of `B'` is the image of the one of `B`.

## Main definitions

* `Stacks.Discriminant.DedekindDifferentSetup.genericFiberEquiv`: the isomorphism of generic
  fibres `b ⊗ k ↦ eB b ⊗ eK k`.
* `Stacks.Discriminant.DedekindDifferentSetup.ofRingEquiv`: the transported setup.

## Main results

* `Stacks.Discriminant.DedekindDifferentSetup.trace_ofRingEquiv`: compatibility of the traces.
* `Stacks.Discriminant.DedekindDifferentSetup.one_mem_complementaryModule_ofRingEquiv_iff`.
* `Stacks.Discriminant.DedekindDifferentSetup.dedekindDifferentIdeal_ofRingEquiv`.

## Implementation notes

The ring isomorphisms may live in different universes, so the étaleness of the generic fibre is
transported through `Algebra.Etale.of_equiv` and `Algebra.Etale.comp` rather than through
`RingHom.Etale.respectsIso`, which is stated within one universe.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u₁ v₁ u₂ v₂

variable {A : Type u₁} {B : Type v₁} {A' : Type u₂} {B' : Type v₂}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra A B] [Algebra A' B']

namespace DedekindDifferentSetup

/-- The ring map of generic fibres `B ⊗[A] Q(A) → B' ⊗[A'] Q(A')` induced by compatible ring
isomorphisms `A ≃ A'` and `B ≃ B'`. -/
def genericFiberHom (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    B ⊗[A] FractionRing A →+* B' ⊗[A'] FractionRing A' :=
  letI : Algebra A (B' ⊗[A'] FractionRing A') :=
    ((algebraMap A' (B' ⊗[A'] FractionRing A')).comp eA.toRingHom).toAlgebra
  (Algebra.TensorProduct.lift (R := A) (S := A)
    { toRingHom := (algebraMap B' (B' ⊗[A'] FractionRing A')).comp eB.toRingHom
      commutes' := fun a => by
        change algebraMap B' (B' ⊗[A'] FractionRing A') (eB (algebraMap A B a)) =
          algebraMap A' (B' ⊗[A'] FractionRing A') (eA a)
        rw [← h, ← IsScalarTower.algebraMap_apply] }
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp
        (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A').toRingHom
      commutes' := fun a => by
        change Algebra.TensorProduct.includeRight
          (IsFractionRing.ringEquivOfRingEquiv eA (algebraMap A (FractionRing A) a)) =
            algebraMap A' (B' ⊗[A'] FractionRing A') (eA a)
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, AlgHom.commutes] }
    fun _ _ => Commute.all _ _).toRingHom

/-- The ring map of generic fibres on pure tensors. -/
theorem genericFiberHom_tmul (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (b : B) (k : FractionRing A) :
    genericFiberHom eA eB h (b ⊗ₜ k) =
      eB b ⊗ₜ (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A') k := by
  change (algebraMap B' (B' ⊗[A'] FractionRing A') (eB b)) *
      Algebra.TensorProduct.includeRight (IsFractionRing.ringEquivOfRingEquiv eA k) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The compatibility of the inverse isomorphisms with the structure maps. -/
theorem algebraMap_symm_eq (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (a' : A') :
    algebraMap A B (eA.symm a') = eB.symm (algebraMap A' B' a') := by
  apply eB.injective
  rw [RingEquiv.apply_symm_apply, ← h, RingEquiv.apply_symm_apply]

/-- The isomorphism of fraction rings induced by `eA.symm` inverts the one induced by `eA`. -/
theorem fractionRingEquiv_symm_apply_apply (eA : A ≃+* A') (k : FractionRing A) :
    (IsFractionRing.ringEquivOfRingEquiv eA.symm : FractionRing A' ≃+* FractionRing A)
      ((IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A') k) = k :=
  (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A').symm_apply_apply k

/-- The ring isomorphism of generic fibres `B ⊗[A] Q(A) ≃ B' ⊗[A'] Q(A')` induced by compatible
ring isomorphisms `A ≃ A'` and `B ≃ B'`; it sends `b ⊗ k` to `eB b ⊗ eK k`. -/
def genericFiberEquiv (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    B ⊗[A] FractionRing A ≃+* B' ⊗[A'] FractionRing A' :=
  RingEquiv.ofRingHom (genericFiberHom eA eB h)
    (genericFiberHom eA.symm eB.symm (algebraMap_symm_eq eA eB h))
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul b k =>
        rw [RingHom.comp_apply, genericFiberHom_tmul, genericFiberHom_tmul,
          RingEquiv.apply_symm_apply, RingHom.id_apply]
        congr 1
        exact fractionRingEquiv_symm_apply_apply eA.symm k
      | add x y hx hy =>
        rw [RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢
        rw [map_add, map_add, hx, hy])
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul b k =>
        rw [RingHom.comp_apply, genericFiberHom_tmul, genericFiberHom_tmul,
          RingEquiv.symm_apply_apply, RingHom.id_apply]
        congr 1
        exact fractionRingEquiv_symm_apply_apply eA k
      | add x y hx hy =>
        rw [RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢
        rw [map_add, map_add, hx, hy])

/-- The isomorphism of generic fibres on pure tensors. -/
theorem genericFiberEquiv_tmul (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (b : B) (k : FractionRing A) :
    genericFiberEquiv eA eB h (b ⊗ₜ k) =
      eB b ⊗ₜ (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A') k :=
  genericFiberHom_tmul eA eB h b k

/-- The isomorphism of generic fibres is compatible with the maps from `B` and `B'`. -/
theorem genericFiberEquiv_algebraMap (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (b : B) :
    genericFiberEquiv eA eB h (algebraMap B (B ⊗[A] FractionRing A) b) =
      algebraMap B' (B' ⊗[A'] FractionRing A') (eB b) := by
  change genericFiberEquiv eA eB h (b ⊗ₜ 1) = eB b ⊗ₜ 1
  rw [genericFiberEquiv_tmul, map_one]

/-- The isomorphism of generic fibres is compatible with the maps from the total quotient
rings. -/
theorem genericFiberEquiv_includeRight (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (k : FractionRing A) :
    genericFiberEquiv eA eB h (1 ⊗ₜ k) =
      1 ⊗ₜ (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A') k := by
  rw [genericFiberEquiv_tmul, map_one]

/-- The algebra map of the generic fibre over the total quotient ring is carried by the
isomorphism of generic fibres to the one of the other generic fibre. -/
theorem genericFiberEquiv_comp_algebraMap (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (FractionRing A') (B' ⊗[A'] FractionRing A') :=
      Algebra.TensorProduct.rightAlgebra
    (genericFiberEquiv eA eB h).toRingHom.comp (algebraMap (FractionRing A) _) =
      (algebraMap (FractionRing A') (B' ⊗[A'] FractionRing A')).comp
        (IsFractionRing.ringEquivOfRingEquiv eA :
          FractionRing A ≃+* FractionRing A').toRingHom :=
  RingHom.ext (genericFiberEquiv_includeRight eA eB h)

/-- **Transport of the Dedekind setup** along compatible ring isomorphisms `A ≃ A'` and
`B ≃ B'`. -/
theorem ofRingEquiv (setup : DedekindDifferentSetup A B) (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    DedekindDifferentSetup A' B' := by
  let := setup.isNoetherianRing
  let := setup.finite
  let := setup.etaleGenericFiber
  let : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (FractionRing A') (B' ⊗[A'] FractionRing A') :=
    Algebra.TensorProduct.rightAlgebra
  have hF : Module.Finite A' B' :=
    Module.Finite.of_surjective (σ := eA.toRingHom) (M := B)
      { toFun := eB
        map_add' := map_add eB
        map_smul' := fun a b => by
          change eB (a • b) = eA a • eB b
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, h] } eB.surjective
  have hE : Algebra.Etale (FractionRing A') (B' ⊗[A'] FractionRing A') := by
    let eK : FractionRing A ≃+* FractionRing A' := IsFractionRing.ringEquivOfRingEquiv eA
    let : Algebra (FractionRing A) (B' ⊗[A'] FractionRing A') :=
      ((algebraMap (FractionRing A') (B' ⊗[A'] FractionRing A')).comp eK.toRingHom).toAlgebra
    let : Algebra (FractionRing A') (FractionRing A) := eK.symm.toRingHom.toAlgebra
    have : Algebra.Etale (FractionRing A') (FractionRing A) :=
      RingHom.Etale.of_bijective eK.symm.bijective
    have : IsScalarTower (FractionRing A') (FractionRing A) (B' ⊗[A'] FractionRing A') :=
      IsScalarTower.of_algebraMap_eq fun k => by
        change _ = algebraMap (FractionRing A') (B' ⊗[A'] FractionRing A') (eK (eK.symm k))
        rw [RingEquiv.apply_symm_apply]
    let eL : (B ⊗[A] FractionRing A) ≃ₐ[FractionRing A] (B' ⊗[A'] FractionRing A') :=
      { genericFiberEquiv eA eB h with
        commutes' := fun k => genericFiberEquiv_includeRight eA eB h k }
    have : Algebra.Etale (FractionRing A) (B' ⊗[A'] FractionRing A') := Algebra.Etale.of_equiv eL
    exact Algebra.Etale.comp (FractionRing A') (FractionRing A) (B' ⊗[A'] FractionRing A')
  exact
    { isNoetherianRing := isNoetherianRing_of_ringEquiv A eA
      finite := hF
      maps_nonZeroDivisors := fun a' ha' => by
        have ha : eA.symm a' ∈ nonZeroDivisors A := by
          rw [← MulEquivClass.map_nonZeroDivisors eA.symm]
          exact Submonoid.mem_map_of_mem _ ha'
        have hb := setup.maps_nonZeroDivisors _ ha
        rw [algebraMap_symm_eq eA eB h, ← MulEquivClass.map_nonZeroDivisors eB.symm] at hb
        obtain ⟨y, hy, hyy⟩ := hb
        rwa [eB.symm.injective hyy] at hy
      etaleGenericFiber := hE }

/-- The generic-fibre trace of the Dedekind setup is the finite-projective trace of
multiplication. -/
theorem trace_eq_finiteProjectiveTrace (setup : DedekindDifferentSetup A B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    ∀ [Module.Finite (FractionRing A) (B ⊗[A] FractionRing A)]
      [Module.Projective (FractionRing A) (B ⊗[A] FractionRing A)] (x : B ⊗[A] FractionRing A),
      setup.trace x = finiteProjectiveTrace (FractionRing A) (B ⊗[A] FractionRing A)
        (Algebra.lmul (FractionRing A) (B ⊗[A] FractionRing A) x) := by
  let : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
  intro _ _ x
  rw [finiteProjectiveTrace_eq_contract]
  rfl

/-- The generic fibre of the Dedekind setup is finite projective over the total quotient
ring. -/
theorem finite_projective_genericFiber (setup : DedekindDifferentSetup A B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    Module.Finite (FractionRing A) (B ⊗[A] FractionRing A) ∧
      Module.Projective (FractionRing A) (B ⊗[A] FractionRing A) := by
  let := setup.finite
  let : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
  let := setup.etaleGenericFiber
  let K := FractionRing A
  let L := B ⊗[A] FractionRing A
  let : Module.Finite K (K ⊗[A] B) := Module.Finite.base_change A K B
  let e : (K ⊗[A] B) ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  have : Module.Flat K L := Algebra.Smooth.flat K L
  have : Module.FinitePresentation K L :=
    Module.FinitePresentation.of_finite_of_finitePresentation K L
  exact ⟨‹Module.Finite K L›, Module.Flat.projective_of_finitePresentation⟩

/-- The isomorphism of generic fibres carries the trace of the Dedekind setup to the trace of
the transported setup. -/
theorem trace_ofRingEquiv (setup : DedekindDifferentSetup A B) (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (x : B ⊗[A] FractionRing A) :
    (setup.ofRingEquiv eA eB h).trace (genericFiberEquiv eA eB h x) =
      (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A')
        (setup.trace x) := by
  let : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (FractionRing A') (B' ⊗[A'] FractionRing A') :=
    Algebra.TensorProduct.rightAlgebra
  let eK : FractionRing A ≃+* FractionRing A' := IsFractionRing.ringEquivOfRingEquiv eA
  let eL := genericFiberEquiv eA eB h
  obtain ⟨_, _⟩ := setup.finite_projective_genericFiber
  obtain ⟨_, _⟩ := (setup.ofRingEquiv eA eB h).finite_projective_genericFiber
  let : Algebra (FractionRing A) (B' ⊗[A'] FractionRing A') :=
    ((algebraMap (FractionRing A') (B' ⊗[A'] FractionRing A')).comp eK.toRingHom).toAlgebra
  let eLK : (B ⊗[A] FractionRing A) ≃ₐ[FractionRing A] (B' ⊗[A'] FractionRing A') :=
    { eL with commutes' := fun k => genericFiberEquiv_includeRight eA eB h k }
  have : Module.Finite (FractionRing A) (B' ⊗[A'] FractionRing A') :=
    Module.Finite.equiv eLK.toLinearEquiv
  have : Module.Projective (FractionRing A) (B' ⊗[A'] FractionRing A') :=
    Module.Projective.of_equiv eLK.toLinearEquiv
  rw [trace_eq_finiteProjectiveTrace, trace_eq_finiteProjectiveTrace,
    ← finiteProjectiveTrace_conj_linearEquiv eLK.toLinearEquiv]
  refine (finiteProjectiveTrace_congr_ringEquiv (C := B' ⊗[A'] FractionRing A') eK
    (fun _ => rfl) _ _ fun c => ?_).symm
  change eL (x * eL.symm c) = eL x * c
  rw [map_mul, RingEquiv.apply_symm_apply]

/-- An element of the fraction ring of `A` comes from `A` exactly when its image under the
induced isomorphism of fraction rings comes from `A'`. -/
theorem fractionRingEquiv_mem_range_iff (eA : A ≃+* A') (k : FractionRing A) :
    (IsFractionRing.ringEquivOfRingEquiv eA : FractionRing A ≃+* FractionRing A') k ∈
        Set.range (algebraMap A' (FractionRing A')) ↔
      k ∈ Set.range (algebraMap A (FractionRing A)) := by
  constructor
  · rintro ⟨a', ha'⟩
    refine ⟨eA.symm a', ?_⟩
    rw [← fractionRingEquiv_symm_apply_apply eA k, ← ha',
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  · rintro ⟨a, rfl⟩
    exact ⟨eA a, (IsFractionRing.ringEquivOfRingEquiv_algebraMap eA a).symm⟩

/-- The isomorphism of generic fibres identifies the complementary modules. -/
theorem genericFiberEquiv_mem_complementaryModule_ofRingEquiv_iff
    (setup : DedekindDifferentSetup A B) (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (x : B ⊗[A] FractionRing A) :
    genericFiberEquiv eA eB h x ∈ (setup.ofRingEquiv eA eB h).complementaryModule ↔
      x ∈ setup.complementaryModule := by
  rw [mem_complementaryModule, mem_complementaryModule, ← eB.forall_congr_right]
  refine forall_congr' fun b => ?_
  rw [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ← genericFiberEquiv_algebraMap eA eB h,
    ← map_mul, trace_ofRingEquiv, fractionRingEquiv_mem_range_iff]

/-- One lies in the complementary module of the transported setup exactly when it lies in the
complementary module of the original one. -/
theorem one_mem_complementaryModule_ofRingEquiv_iff (setup : DedekindDifferentSetup A B)
    (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    (1 : B' ⊗[A'] FractionRing A') ∈ (setup.ofRingEquiv eA eB h).complementaryModule ↔
      (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule := by
  rw [← genericFiberEquiv_mem_complementaryModule_ofRingEquiv_iff setup eA eB h, map_one]

/-- The isomorphism of generic fibres identifies the Dedekind differents. -/
theorem genericFiberEquiv_mem_dedekindDifferent_ofRingEquiv_iff
    (setup : DedekindDifferentSetup A B) (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) (x : B ⊗[A] FractionRing A) :
    genericFiberEquiv eA eB h x ∈ (setup.ofRingEquiv eA eB h).dedekindDifferent ↔
      x ∈ setup.dedekindDifferent := by
  rw [mem_dedekindDifferent, mem_dedekindDifferent,
    ← (genericFiberEquiv eA eB h).forall_congr_right]
  refine forall_congr' fun y => ?_
  rw [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    genericFiberEquiv_mem_complementaryModule_ofRingEquiv_iff, ← map_mul]
  refine imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨b', hb'⟩
    refine ⟨eB.symm b', (genericFiberEquiv eA eB h).injective ?_⟩
    rw [genericFiberEquiv_algebraMap eA eB h, RingEquiv.apply_symm_apply, hb']
  · rintro ⟨b, hb⟩
    exact ⟨eB b, by rw [← genericFiberEquiv_algebraMap eA eB h, hb]⟩

/-- The Dedekind different ideal of the transported setup is the image of the original one. -/
theorem dedekindDifferentIdeal_ofRingEquiv (setup : DedekindDifferentSetup A B)
    (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ a, algebraMap A' B' (eA a) = eB (algebraMap A B a)) :
    dedekindDifferentIdeal (setup.ofRingEquiv eA eB h) =
      (dedekindDifferentIdeal setup).map eB := by
  ext b'
  rw [show (dedekindDifferentIdeal setup).map eB =
      (dedekindDifferentIdeal setup).map (eB : B →+* B') from rfl,
    Ideal.map_comap_of_equiv, Ideal.mem_comap]
  change algebraMap B' (B' ⊗[A'] FractionRing A') b' ∈
      (setup.ofRingEquiv eA eB h).dedekindDifferent ↔
    algebraMap B (B ⊗[A] FractionRing A) (eB.symm b') ∈ setup.dedekindDifferent
  rw [← genericFiberEquiv_mem_dedekindDifferent_ofRingEquiv_iff setup eA eB h,
    genericFiberEquiv_algebraMap, RingEquiv.apply_symm_apply]

end DedekindDifferentSetup

end Stacks.Discriminant

end
