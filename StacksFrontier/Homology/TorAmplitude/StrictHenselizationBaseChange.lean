module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.TorAmplitudeHenselization
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange

/-!
# Tor amplitude over a local ring and over its strict henselization, after a faithfully flat
base change

Let `A → B` be a ring map with `A` local, let `B → B'` be faithfully flat, and let `R'` be a
henselization of `A` with some separably closed residue field extension, mapping to `B'`
compatibly with `A → B → B'`.  For a complex `P` of `B`-modules, `P` has Tor amplitude in
`[a, b]` over `A` if and only if `P ⊗_B B'` has Tor amplitude in `[a, b]` over `R'`.  This is
the algebra in the proof of Stacks 0DK7: Stacks 0DJF for `B → B'`, then Stacks 0DK0 for
`A → R'`.
-/

@[expose] public section

open CategoryTheory IsLocalRing StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.TorAmplitude

variable {A B B' R' : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [CommRing B']
  [CommRing R'] {κ : Type v} [Field κ] [Algebra (ResidueField A) κ]
  [IsSepClosure (ResidueField A) κ]

/-- **Tor amplitude over a local ring and over a strict henselization of it, after a faithfully
flat base change.**  If `R'` is the strict henselization of `A` in a henselization tower, and
`γ : R' → B'` restricts along `A → R'` to `A → B → B'` with `B → B'` faithfully flat, then a
complex `P` of `B`-modules has Tor amplitude in `[a, b]` over `A` exactly when `P ⊗_B B'` has
Tor amplitude in `[a, b]` over `R'`. -/
theorem hasTorAmplitudeCanonical_restrictScalars_iff_extendScalars_of_henselizationTower
    (H : HenselizationTower A κ) (e : H.strictHenselization ≃+* R')
    (α : A →+* B) (β : B →+* B') (hβ : β.FaithfullyFlat) (γ : R' →+* B')
    (hcomm : γ.comp (e.toRingHom.comp (algebraMap A H.strictHenselization)) = β.comp α)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonical A (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) a b ↔
      HasTorAmplitudeCanonical R' (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
        a b := by
  let : Algebra A B := α.toAlgebra
  let : Algebra B B' := β.toAlgebra
  let : Algebra A B' := (β.comp α).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat B B' := hβ
  -- Stacks 0DJF for `B → B'`, read at the canonical derived tensor product over `A`.
  have h1 := FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars A B B' P a b
  open AlgebraicGeometry.AffineRelativeTorAmplitude in
  rw [← hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF,
    ← hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF] at h1
  refine h1.trans ?_
  let N := ((ModuleCat.restrictScalars γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  let Msh := ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N
  show HasTorAmplitudeCanonical A (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (β.comp α)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) a b ↔ _
  rw [← hcomm]
  show HasTorAmplitudeCanonical A (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap A H.strictHenselization)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Msh)) a b ↔ _
  -- Stacks 0DK0, conditions (1) and (3), for the strict henselization in the tower.
  have h2 := (torAmplitude_tfae_henselization.{u, u, u, v, u, u, u, u}
    (R := A) (Rh := H.henselization) (Rsh := H.strictHenselization) (K := κ) Msh a b).out 1 3
  rw [hasTorAmplitudeCanonical_iff_lift, h2, ← hasTorAmplitudeCanonical_iff_lift]
  open AlgebraicGeometry.AffineRelativeTorAmplitude in
  exact hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff e N a b

end StacksDraft.TorAmplitude

end
