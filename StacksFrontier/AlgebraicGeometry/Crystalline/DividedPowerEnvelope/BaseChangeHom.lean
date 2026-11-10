module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.FlatAlgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.PolynomialModel

/-!
# The base change map of a divided power envelope along a change of divided power base

Let `φ : (A, I, γ) → (A₁, I₁, γ₁)` be a homomorphism of divided power rings, let `A → B` be a
ring map and `J ⊆ B` an ideal containing `I B`, and let `J₁ ⊆ A₁ ⊗_A B` be an ideal containing
`I₁ (A₁ ⊗_A B)` and the image of `J`. The universal property of the envelope `D = D_{B,γ}(J)`
gives a divided power morphism `ψ : D → D₁ = D_{A₁ ⊗_A B, γ₁}(J₁)` over `φ`, hence the canonical
ring map `A₁ ⊗_A D → D₁`, `a ⊗ d ↦ a ψ(d)`. This file defines it and proves:

* it is compatible with maps of envelopes along `B → B'`
  (`Crystalline.envelopeBaseChangeHom_comp_tensorEnvelopeMap`);
* its bijectivity passes along a flat `B → B'` with `J' = J B'`
  (`Crystalline.bijective_envelopeBaseChangeHom_of_flat`), the envelopes of `J B'` being
  `D ⊗_B B'` by Stacks 07HD;
* it is bijective for the envelope `A⟨x⟩` of the variables of a polynomial algebra
  (`Crystalline.bijective_envelopeBaseChangeHom_model`).

## Main definitions

* `Crystalline.envelopeBaseChangeHom` — the canonical map `A₁ ⊗_A D_{B,γ}(J) → D_{B₁,γ₁}(J₁)`.

## Implementation notes

The base `A → A₁` is an instance `[Algebra A A₁]` together with the divided power morphism `φ`
and the equation `φ.toRingHom = algebraMap A A₁`, so that `A₁ ⊗[A] B` is formed with the instance.
The `A`-algebra structure of an envelope is the one given by its structure map.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

open DividedPowers

section Def

variable {A A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁)
  {B : Type u} [CommRing B] [Algebra A B]
  {J : Ideal B} {hJ : A.ideal.map (algebraMap A B) ≤ J}
  {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
  (hJJ₁ : J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
  (D : DividedPowerEnvelope A (algebraMap A B) J hJ)
  (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁)

include hφ in
/-- The square `A → B → A₁ ⊗_A B`, `A → A₁ → A₁ ⊗_A B` commutes. -/
theorem includeRight_comp_algebraMap_eq :
    (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom.comp (algebraMap A B) =
      (algebraMap A₁ (A₁ ⊗[A] B)).comp φ.toRingHom := by
  rw [hφ]
  ext a
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

include hφ hJJ₁ in
/-- The divided power morphism `D → D₁` over `φ` induced by `B → A₁ ⊗_A B`. -/
noncomputable def envelopeBaseChangePairMap :
    DividedPowers.DPMorphism D.object.dividedPowers D₁.object.dividedPowers :=
  (envelopePairMap D D₁ φ (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom
    hJJ₁ (includeRight_comp_algebraMap_eq (B := B) φ hφ)).1

include hφ hJJ₁ in
/-- The morphism `D → D₁` restricts to `b ↦ 1 ⊗ b` on the image of `B`. -/
theorem envelopeBaseChangePairMap_algebraMap (b : B) :
    (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom (D.algebraMap.toRingHom b) =
      D₁.algebraMap.toRingHom (1 ⊗ₜ[A] b) :=
  envelopePairMap_algebraMap D D₁ _ _ hJJ₁ _ b

include hφ hJJ₁ in
/-- The morphism `D → D₁` lies over `A → A₁`. -/
theorem envelopeBaseChangePairMap_structureMap (z : A) :
    (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom (D.structureMap.toRingHom z) =
      D₁.structureMap.toRingHom (algebraMap A A₁ z) := by
  rw [← hφ]
  exact envelopePairMap_structureMap D D₁ _ _ hJJ₁ _ z

include hφ hJJ₁ in
/-- **The canonical map `A₁ ⊗_A D_{B,γ}(J) → D_{A₁ ⊗_A B, γ₁}(J₁)`**, `a ⊗ d ↦ a · ψ(d)`, where
`ψ` is the divided power morphism of envelopes over `φ`. -/
noncomputable def envelopeBaseChangeHom :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    A₁ ⊗[A] D.object →+* D₁.object :=
  letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  letI : Algebra A₁ D₁.object := D₁.structureMap.toRingHom.toAlgebra
  letI : Algebra A D₁.object := (D₁.structureMap.toRingHom.comp (algebraMap A A₁)).toAlgebra
  haveI : IsScalarTower A A₁ D₁.object := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.lift (Algebra.ofId A₁ D₁.object)
    ({ (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom with
        commutes' := fun z => envelopeBaseChangePairMap_structureMap φ hφ hJJ₁ D D₁ z } :
      D.object →ₐ[A] D₁.object)
    (fun _ _ => Commute.all _ _)).toRingHom

include hφ hJJ₁ in
/-- The base change map on a pure tensor. -/
theorem envelopeBaseChangeHom_tmul (a : A₁) (d : D.object) :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (a ⊗ₜ[A] d) =
      D₁.structureMap.toRingHom a * (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom d :=
  rfl

end Def

section Functoriality

variable {A A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁)
  {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B B']
  [IsScalarTower A B B']
  {J : Ideal B} {hJ : A.ideal.map (algebraMap A B) ≤ J}
  {J' : Ideal B'} {hJ' : A.ideal.map (algebraMap A B') ≤ J'}
  {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
  {J₁' : Ideal (A₁ ⊗[A] B')} {hJ₁' : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B')) ≤ J₁'}
  (hJJ' : J.map (algebraMap B B') ≤ J')
  (hJJ₁ : J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
  (hJ'J₁' : J'.map (Algebra.TensorProduct.includeRight : B' →ₐ[A] A₁ ⊗[A] B').toRingHom ≤ J₁')
  (hJ₁J₁' : J₁.map (Algebra.TensorProduct.map (AlgHom.id A₁ A₁)
    (IsScalarTower.toAlgHom A B B')).toRingHom ≤ J₁')
  (D : DividedPowerEnvelope A (algebraMap A B) J hJ)
  (D' : DividedPowerEnvelope A (algebraMap A B') J' hJ')
  (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁)
  (D₁' : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B')) J₁' hJ₁')

/-- The map `A₁ ⊗_A B → A₁ ⊗_A B'`. -/
noncomputable abbrev tensorAlgebraMap : A₁ ⊗[A] B →ₐ[A₁] A₁ ⊗[A] B' :=
  Algebra.TensorProduct.map (AlgHom.id A₁ A₁) (IsScalarTower.toAlgHom A B B')

/-- The map `A₁ ⊗_A B → A₁ ⊗_A B'` is an `A₁`-algebra map. -/
theorem tensorAlgebraMap_comp_algebraMap :
    (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom.comp
      (algebraMap A₁ (A₁ ⊗[A] B)) = algebraMap A₁ (A₁ ⊗[A] B') := by
  ext a
  exact (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).commutes a

/-- The divided power morphism `D → D'` along `B → B'`. -/
noncomputable def envelopeMapOfAlgebra :
    DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers :=
  envelopeAlgebraMapHom D D' (IsScalarTower.algebraMap_eq A B B') hJJ'

/-- The divided power morphism `D₁ → D₁'` along `A₁ ⊗_A B → A₁ ⊗_A B'`. -/
noncomputable def envelopeMapOfTensor :
    DividedPowers.DPMorphism D₁.object.dividedPowers D₁'.object.dividedPowers :=
  (envelopePairMap D₁ D₁' (DividedPowers.DPMorphism.id A₁.dividedPowers)
    (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom hJ₁J₁'
    (by rw [tensorAlgebraMap_comp_algebraMap]; rfl)).1

/-- The map `A₁ ⊗_A D → A₁ ⊗_A D'`. -/
noncomputable def tensorEnvelopeMap :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    letI : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
    A₁ ⊗[A] D.object →ₐ[A₁] A₁ ⊗[A] D'.object :=
  letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  letI : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
  Algebra.TensorProduct.map (AlgHom.id A₁ A₁)
    { (envelopeMapOfAlgebra hJJ' D D').toRingHom with
      commutes' := fun z => envelopeAlgebraMapHom_structureMap D D' _ hJJ' z }

/-- The map `A₁ ⊗_A D → A₁ ⊗_A D'` on a pure tensor. -/
theorem tensorEnvelopeMap_tmul (a : A₁) (d : D.object) :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    letI : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
    tensorEnvelopeMap hJJ' D D' (a ⊗ₜ[A] d) =
      a ⊗ₜ[A] (envelopeMapOfAlgebra hJJ' D D').toRingHom d :=
  rfl

include hφ in
/-- **The base change maps commute with the maps of envelopes along `B → B'`.** -/
theorem envelopeBaseChangeHom_comp_tensorEnvelopeMap :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    ∀ z : A₁ ⊗[A] D.object,
      envelopeBaseChangeHom φ hφ hJ'J₁' D' D₁' (tensorEnvelopeMap hJJ' D D' z) =
        (envelopeMapOfTensor hJ₁J₁' D₁ D₁').toRingHom
          (envelopeBaseChangeHom φ hφ hJJ₁ D D₁ z) := by
  let : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  let : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
  have hψ : (envelopeBaseChangePairMap φ hφ hJ'J₁' D' D₁').comp
      (envelopeMapOfAlgebra hJJ' D D') =
      (envelopeMapOfTensor hJ₁J₁' D₁ D₁').comp (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁) := by
    refine envelopeHom_ext D D₁'.object _ _ ?_ ?_
    · apply DividedPowers.DPMorphism.ext
      funext z
      change (envelopeBaseChangePairMap φ hφ hJ'J₁' D' D₁').toRingHom
          ((envelopeMapOfAlgebra hJJ' D D').toRingHom (D.structureMap.toRingHom z)) =
        (envelopeMapOfTensor hJ₁J₁' D₁ D₁').toRingHom
          ((envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom (D.structureMap.toRingHom z))
      rw [envelopeMapOfAlgebra, envelopeAlgebraMapHom_structureMap,
        envelopeBaseChangePairMap_structureMap, envelopeBaseChangePairMap_structureMap,
        envelopeMapOfTensor, envelopePairMap_structureMap]
      rfl
    · ext b
      change (envelopeBaseChangePairMap φ hφ hJ'J₁' D' D₁').toRingHom
          ((envelopeMapOfAlgebra hJJ' D D').toRingHom (D.algebraMap.toRingHom b)) =
        (envelopeMapOfTensor hJ₁J₁' D₁ D₁').toRingHom
          ((envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom (D.algebraMap.toRingHom b))
      rw [envelopeMapOfAlgebra, envelopeAlgebraMapHom_algebraMap,
        envelopeBaseChangePairMap_algebraMap, envelopeBaseChangePairMap_algebraMap,
        envelopeMapOfTensor, envelopePairMap_algebraMap]
      simp
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a d =>
    rw [tensorEnvelopeMap_tmul, envelopeBaseChangeHom_tmul, envelopeBaseChangeHom_tmul,
      map_mul]
    congr 1
    · rw [envelopeMapOfTensor, envelopePairMap_structureMap]
      rfl
    · exact congrArg (fun q => q.toRingHom d) hψ
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsScalarTower A B B'] in
/-- The base change map sends `a ⊗ b` (with `b` read in the envelope) to `a ⊗ b` read in the
envelope of `J₁`. -/
theorem envelopeBaseChangeHom_tmul_algebraMap (a : A₁) (b : B) :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (a ⊗ₜ[A] D.algebraMap.toRingHom b) =
      D₁.algebraMap.toRingHom (a ⊗ₜ[A] b) := by
  rw [envelopeBaseChangeHom_tmul, envelopeBaseChangePairMap_algebraMap]
  have h : D₁.structureMap.toRingHom a = D₁.algebraMap.toRingHom (a ⊗ₜ[A] 1) := by
    rw [← D₁.algebraMap_comp]
    rfl
  rw [h, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

include hφ in
/-- **Base change of envelopes along a flat `B → B'`**: if the base change map of the envelope
of `J ⊆ B` is bijective then so is that of the envelope of `J B' ⊆ B'`. -/
theorem bijective_envelopeBaseChangeHom_of_flat [Module.Flat B B']
    (hJ'eq : J' = J.map (algebraMap B B'))
    (hJ₁'eq : J₁' = J₁.map (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom)
    (h : Function.Bijective (envelopeBaseChangeHom φ hφ hJJ₁ D D₁)) :
    Function.Bijective (envelopeBaseChangeHom φ hφ hJ'J₁' D' D₁') := by
  let : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  let : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
  set Φ := envelopeBaseChangeHom φ hφ hJJ₁ D D₁ with hΦ
  set Φ' := envelopeBaseChangeHom φ hφ hJ'J₁' D' D₁' with hΦ'
  set κ := envelopeMapOfAlgebra hJ'eq.ge D D' with hκ
  set κ₁ := envelopeMapOfTensor hJ₁'eq.ge D₁ D₁' with hκ₁
  set T := A₁ ⊗[A] D'.object
  -- the two flat base changes
  obtain ⟨e, he⟩ := exists_envelope_tensor_equiv_of_flat D D' (IsScalarTower.algebraMap_eq A B B')
    hJ'eq
  let : Algebra (A₁ ⊗[A] B) (A₁ ⊗[A] B') :=
    (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom.toAlgebra
  have hflat : Module.Flat (A₁ ⊗[A] B) (A₁ ⊗[A] B') :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id A₁ A₁) (g := IsScalarTower.toAlgHom A B B')
      (RingHom.Flat.of_bijective Function.bijective_id)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  obtain ⟨e₁, he₁⟩ := exists_envelope_tensor_equiv_of_flat D₁ D₁'
    (tensorAlgebraMap_comp_algebraMap (A₁ := A₁) (B := B) (B' := B')).symm hJ₁'eq
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let : Algebra (A₁ ⊗[A] B) D₁.object := D₁.algebraMap.toRingHom.toAlgebra
  change ∀ x y, e₁ (x ⊗ₜ y) = κ₁.toRingHom x * D₁'.algebraMap.toRingHom y at he₁
  change ∀ x y, e (x ⊗ₜ y) = κ.toRingHom x * D'.algebraMap.toRingHom y at he
  let Φe := RingEquiv.ofBijective Φ h
  -- the inverse
  let Dalg' : B' →ₐ[A] D'.object :=
    { D'.algebraMap.toRingHom with
      commutes' := fun a => by
        change D'.algebraMap.toRingHom (algebraMap A B' a) = D'.structureMap.toRingHom a
        rw [← D'.algebraMap_comp]
        rfl }
  let u₂ : A₁ ⊗[A] B' →ₐ[A₁] T := Algebra.TensorProduct.map (AlgHom.id A₁ A₁) Dalg'
  let u₁ : D₁.object →+* T := (tensorEnvelopeMap hJ'eq.ge D D').toRingHom.comp Φe.symm.toRingHom
  have hΦalg (z : A₁ ⊗[A] B) :
      Φ (Algebra.TensorProduct.map (AlgHom.id A₁ A₁)
        ({ D.algebraMap.toRingHom with
          commutes' := fun a => by
            change D.algebraMap.toRingHom (algebraMap A B a) = D.structureMap.toRingHom a
            rw [← D.algebraMap_comp]
            rfl } : B →ₐ[A] D.object) z) = D₁.algebraMap.toRingHom z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => exact envelopeBaseChangeHom_tmul_algebraMap φ hφ hJJ₁ D D₁ a b
    | add x y hx hy => simp only [map_add, hx, hy]
  have hκalg (b : B) : κ.toRingHom (D.algebraMap.toRingHom b) =
      D'.algebraMap.toRingHom (algebraMap B B' b) :=
    envelopeAlgebraMapHom_algebraMap D D' _ _ b
  have hu (z : A₁ ⊗[A] B) : u₁ (D₁.algebraMap.toRingHom z) =
      u₂ (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B') z) := by
    rw [← hΦalg]
    change tensorEnvelopeMap hJ'eq.ge D D' (Φe.symm (Φe _)) = _
    rw [RingEquiv.symm_apply_apply]
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change tensorEnvelopeMap hJ'eq.ge D D' (a ⊗ₜ[A] D.algebraMap.toRingHom b) =
        a ⊗ₜ[A] D'.algebraMap.toRingHom (algebraMap B B' b)
      rw [tensorEnvelopeMap_tmul]
      exact congrArg (a ⊗ₜ[A] ·) (hκalg b)
    | add x y hx hy => simp only [map_add, hx, hy]
  let : Algebra (A₁ ⊗[A] B) T :=
    (u₂.toRingHom.comp (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom).toAlgebra
  let v₁ : D₁.object →ₐ[A₁ ⊗[A] B] T :=
    { u₁ with commutes' := fun z => hu z }
  let v₂ : A₁ ⊗[A] B' →ₐ[A₁ ⊗[A] B] T :=
    { u₂.toRingHom with commutes' := fun z => rfl }
  let Ψ₀ : D₁.object ⊗[A₁ ⊗[A] B] (A₁ ⊗[A] B') →ₐ[A₁ ⊗[A] B] T :=
    Algebra.TensorProduct.lift v₁ v₂ (fun _ _ => Commute.all _ _)
  let Ψ : D₁'.object →+* T := Ψ₀.toRingHom.comp e₁.symm.toRingHom
  have hΨe (x : D₁.object) (y : A₁ ⊗[A] B') : Ψ (e₁ (x ⊗ₜ y)) = u₁ x * u₂ y := by
    change Ψ₀ (e₁.symm (e₁ _)) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  have hΦ'u₂ (y : A₁ ⊗[A] B') : Φ' (u₂ y) = D₁'.algebraMap.toRingHom y := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => exact envelopeBaseChangeHom_tmul_algebraMap φ hφ hJ'J₁' D' D₁' a b
    | add x y hx hy => simp only [map_add, hx, hy]
  have hΦ'u₁ (x : D₁.object) : Φ' (u₁ x) = κ₁.toRingHom x := by
    change Φ' (tensorEnvelopeMap hJ'eq.ge D D' (Φe.symm x)) = _
    rw [hΦ', envelopeBaseChangeHom_comp_tensorEnvelopeMap φ hφ hJ'eq.ge hJJ₁ hJ'J₁' hJ₁'eq.ge
      D D' D₁ D₁']
    change κ₁.toRingHom (Φe (Φe.symm x)) = _
    rw [RingEquiv.apply_symm_apply]
  have hleft (z : D₁'.object) : Φ' (Ψ z) = z := by
    obtain ⟨w, rfl⟩ := e₁.surjective z
    induction w using TensorProduct.inductionOn with
    | tmul x y => rw [hΨe, map_mul, hΦ'u₁, hΦ'u₂, he₁]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hright (z : T) : Ψ (Φ' z) = z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a d =>
      have hsplit : a ⊗ₜ[A] d = (a ⊗ₜ[A] (1 : D'.object)) * ((1 : A₁) ⊗ₜ[A] d) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit, map_mul, map_mul]
      congr 1
      · have h1 : Φ' (a ⊗ₜ[A] (1 : D'.object)) = e₁ (1 ⊗ₜ (a ⊗ₜ[A] 1)) := by
          rw [he₁, map_one, one_mul, hΦ', envelopeBaseChangeHom_tmul, map_one, mul_one,
            ← D₁'.algebraMap_comp]
          rfl
        rw [h1, hΨe, map_one, one_mul]
        change a ⊗ₜ[A] Dalg' 1 = _
        rw [map_one]
      · clear hsplit
        obtain ⟨w, rfl⟩ := e.surjective d
        induction w using TensorProduct.inductionOn with
        | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, map_add, hx, hy]
        | tmul x b' =>
          rw [he]
          have hsp : (1 : A₁) ⊗ₜ[A] (κ.toRingHom x * D'.algebraMap.toRingHom b') =
              ((1 : A₁) ⊗ₜ[A] κ.toRingHom x) * ((1 : A₁) ⊗ₜ[A] D'.algebraMap.toRingHom b') := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          rw [hsp, map_mul, map_mul]
          congr 1
          · have h2 : (1 : A₁) ⊗ₜ[A] κ.toRingHom x =
                tensorEnvelopeMap hJ'eq.ge D D' ((1 : A₁) ⊗ₜ[A] x) := rfl
            have h4 : κ₁.toRingHom (Φ ((1 : A₁) ⊗ₜ[A] x)) = e₁ (Φ ((1 : A₁) ⊗ₜ[A] x) ⊗ₜ 1) := by
              rw [he₁, map_one, mul_one]
            rw [h2, hΦ', envelopeBaseChangeHom_comp_tensorEnvelopeMap φ hφ hJ'eq.ge hJJ₁ hJ'J₁'
              hJ₁'eq.ge D D' D₁ D₁', ← hΦ, h4, hΨe, map_one, mul_one]
            change tensorEnvelopeMap hJ'eq.ge D D' (Φe.symm (Φe ((1 : A₁) ⊗ₜ[A] x))) = _
            rw [RingEquiv.symm_apply_apply]
          · have h3 : Φ' ((1 : A₁) ⊗ₜ[A] D'.algebraMap.toRingHom b') =
                e₁ (1 ⊗ₜ ((1 : A₁) ⊗ₜ[A] b')) := by
              rw [he₁, map_one, one_mul, hΦ']
              exact envelopeBaseChangeHom_tmul_algebraMap φ hφ hJ'J₁' D' D₁' 1 b'
            rw [h3, hΨe, map_one, one_mul]
            rfl
  exact ⟨Function.LeftInverse.injective hright, Function.RightInverse.surjective hleft⟩

end Functoriality

section Model

variable {A A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁) (W : Type u)

/-- The polynomial algebra is the polynomial algebra on its variables. -/
theorem bijective_aeval_X :
    Function.Bijective (MvPolynomial.aeval MvPolynomial.X :
      MvPolynomial W A →ₐ[A] MvPolynomial W A) := by
  rw [MvPolynomial.aeval_X_left]
  exact Function.bijective_id

/-- `A₁ ⊗_A A[x_w]` is the polynomial algebra over `A₁` on the elements `1 ⊗ x_w`. -/
theorem bijective_aeval_one_tmul_X :
    Function.Bijective (MvPolynomial.aeval (fun w => (1 : A₁) ⊗ₜ[A] MvPolynomial.X w) :
      MvPolynomial W A₁ →ₐ[A₁] A₁ ⊗[A] MvPolynomial W A) := by
  have : (MvPolynomial.aeval (fun w => (1 : A₁) ⊗ₜ[A] MvPolynomial.X w) :
      MvPolynomial W A₁ →ₐ[A₁] A₁ ⊗[A] MvPolynomial W A) =
      (MvPolynomial.algebraTensorAlgEquiv A A₁).symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro w
    simp [MvPolynomial.algebraTensorAlgEquiv_symm_X]
  rw [this]
  exact (MvPolynomial.algebraTensorAlgEquiv A A₁).symm.bijective

include hφ in
/-- The extension of `I A[x] + (x)` to `A₁ ⊗_A A[x]` lies in `I₁ (A₁ ⊗_A A[x]) + (1 ⊗ x)`. -/
theorem map_polynomialModelIdeal_X_le :
    (polynomialModelIdeal A (MvPolynomial.X : W → MvPolynomial W A)).map
        (Algebra.TensorProduct.includeRight : MvPolynomial W A →ₐ[A]
          A₁ ⊗[A] MvPolynomial W A).toRingHom ≤
      polynomialModelIdeal A₁ (fun w => (1 : A₁) ⊗ₜ[A] MvPolynomial.X w) := by
  rw [polynomialModelIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span]
  apply sup_le
  · rw [includeRight_comp_algebraMap_eq φ hφ, ← Ideal.map_map]
    exact le_sup_of_le_left (Ideal.map_mono φ.ideal_comp)
  · refine le_sup_of_le_right (Ideal.span_le.mpr ?_)
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨w, rfl⟩

/-- The model envelope of the variables of `A[x_w]`. -/
noncomputable abbrev polynomialModelEnvelopeX :=
  polynomialModelEnvelope A (MvPolynomial.X : W → MvPolynomial W A) (bijective_aeval_X W)

/-- The model envelope of the variables of `A₁ ⊗_A A[x_w]`. -/
noncomputable abbrev polynomialModelEnvelopeTensorX :=
  polynomialModelEnvelope A₁ (fun w => (1 : A₁) ⊗ₜ[A] MvPolynomial.X w)
    (bijective_aeval_one_tmul_X (A := A) W)

/-- The morphism `A⟨x⟩ → A₁⟨x⟩` of model envelopes sends variables to variables. -/
theorem envelopeBaseChangePairMap_model_variable (w : W) :
    (envelopeBaseChangePairMap φ hφ (map_polynomialModelIdeal_X_le φ hφ W)
      (polynomialModelEnvelopeX W) (polynomialModelEnvelopeTensorX (A₁ := A₁) W)).toRingHom
        (dividedPowerPolynomialVariable A w) = dividedPowerPolynomialVariable A₁ w := by
  have h1 : (polynomialModelEnvelopeX (A := A) W).algebraMap.toRingHom (MvPolynomial.X w) =
      dividedPowerPolynomialVariable A w :=
    polynomialModelMap_apply_x A _ _ w
  rw [← h1, envelopeBaseChangePairMap_algebraMap]
  exact polynomialModelMap_apply_x A₁ _ _ w

/-- The morphism `A⟨x⟩ → A₁⟨x⟩` of model envelopes sends divided power monomials to divided
power monomials. -/
theorem envelopeBaseChangePairMap_model_monomial (n : W →₀ ℕ) :
    (envelopeBaseChangePairMap φ hφ (map_polynomialModelIdeal_X_le φ hφ W)
      (polynomialModelEnvelopeX W) (polynomialModelEnvelopeTensorX (A₁ := A₁) W)).toRingHom
        (dividedPowerPolynomialMonomial A n) = dividedPowerPolynomialMonomial A₁ n := by
  set ψ := envelopeBaseChangePairMap φ hφ (map_polynomialModelIdeal_X_le φ hφ W)
      (polynomialModelEnvelopeX W) (polynomialModelEnvelopeTensorX (A₁ := A₁) W)
  simp only [dividedPowerPolynomialMonomial, Finsupp.prod]
  refine (map_prod ψ.toRingHom (fun w => (DividedPowerAlgebra.dp A (n w) (Finsupp.single w 1) :
    (polynomialModelEnvelopeX (A := A) W).object)) n.support).trans
    (Finset.prod_congr rfl fun w _ => ?_)
  have hv := variable_mem_polynomialIdeal A w
  have h := ψ.dpow_comp (n := n w) _ hv
  rw [envelopeBaseChangePairMap_model_variable] at h
  change (setIndexedDividedPowerPolynomialDividedPowers A₁ W).dpow (n w)
        (dividedPowerPolynomialVariable A₁ w) = ψ.toRingHom
      ((setIndexedDividedPowerPolynomialDividedPowers A W).dpow (n w)
        (dividedPowerPolynomialVariable A w)) at h
  rw [setIndexedDividedPowerPolynomialDividedPowers_dpow_variable,
    setIndexedDividedPowerPolynomialDividedPowers_dpow_variable] at h
  exact h.symm

/-- **The divided power polynomial algebra commutes with base change**: the base change map
`A₁ ⊗_A A⟨x⟩ → A₁⟨x⟩` of the envelopes of the variables is bijective, since it carries the
base change of the monomial basis to the monomial basis. -/
theorem bijective_envelopeBaseChangeHom_model :
    Function.Bijective (envelopeBaseChangeHom φ hφ (map_polynomialModelIdeal_X_le φ hφ W)
      (polynomialModelEnvelopeX W) (polynomialModelEnvelopeTensorX (A₁ := A₁) W)) := by
  classical
  set E := polynomialModelEnvelopeX (A := A) W
  set E₁ := polynomialModelEnvelopeTensorX (A₁ := A₁) (A := A) W
  set Φ := envelopeBaseChangeHom φ hφ (map_polynomialModelIdeal_X_le φ hφ W) E E₁
  let inst : Algebra A E.object := E.structureMap.toRingHom.toAlgebra
  let b₀ := DividedPowers.dividedPowerPolynomialMonomialBasis A W
  let e : DividedPowerAlgebra A (W →₀ A) ≃ₗ[A] E.object :=
    { toFun := fun z => z
      invFun := fun z => z
      map_add' := fun _ _ => rfl
      map_smul' := fun c z => Algebra.smul_def c z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b := b₀.map e
  let b₁ := DividedPowers.dividedPowerPolynomialMonomialBasis A₁ W
  let Φl : A₁ ⊗[A] E.object →ₗ[A₁] DividedPowerAlgebra A₁ (W →₀ A₁) :=
    { toFun := Φ
      map_add' := map_add Φ
      map_smul' := fun a z => by
        have h1 : Φ (a • z) = Φ (a ⊗ₜ[A] (1 : E.object)) * Φ z := by
          rw [← map_mul]
          congr 1
          rw [Algebra.smul_def]
          rfl
        have h2 : Φ (a ⊗ₜ[A] (1 : E.object)) =
            algebraMap A₁ (DividedPowerAlgebra A₁ (W →₀ A₁)) a :=
          (envelopeBaseChangeHom_tmul φ hφ _ E E₁ a 1).trans (by rw [map_one, mul_one]; rfl)
        exact h1.trans ((congrArg (· * Φ z) h2).trans
          (Algebra.smul_def (A := DividedPowerAlgebra A₁ (W →₀ A₁)) a (Φ z)).symm) }
  have hΦl : Φl = ((b.baseChange A₁).equiv b₁ (Equiv.refl _)).toLinearMap := by
    apply (b.baseChange A₁).ext
    intro n
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.baseChange_apply,
      Equiv.refl_apply, DividedPowers.dividedPowerPolynomialMonomialBasis_apply]
    refine (envelopeBaseChangeHom_tmul φ hφ _ E E₁ 1 (b n)).trans ?_
    rw [map_one, one_mul, show b n = dividedPowerPolynomialMonomial A n from
      DividedPowers.dividedPowerPolynomialMonomialBasis_apply A n]
    exact envelopeBaseChangePairMap_model_monomial φ hφ W n
  change Function.Bijective Φl
  rw [hΦl]
  exact ((b.baseChange A₁).equiv b₁ (Equiv.refl _)).bijective

end Model

end Crystalline
