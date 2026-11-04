module

public import StacksFrontier.Homology.Tor.ChangeOfRingsSystem
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism

/-!
# Tor along isomorphisms of algebras

Let `R' → A'`, `R' → B'` and `R → A`, `R → B` be algebras, and let `ρ : R' ≃ R`, `α : A' ≃ A`,
`β : B' ≃ B` be ring isomorphisms compatible with the structure maps. The canonical
change-of-rings maps of `TorChangeOfRings` along the diagram and along its inverse are mutually
inverse, so they identify `Tor_i^{R'}(A', B')` with `Tor_i^R(A, B)`, semilinearly over the induced
isomorphism `A' ⊗_{R'} B' ≃ A ⊗_R B` (`TorChangeOfRings.restrictScalarsTorIsoOfRingEquiv`).

## References

* [Stacks Project, Tag 00M7](https://stacks.math.columbia.edu/tag/00M7)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace TorChangeOfRings

variable {R' A' B' R A B : Type u} [CommRing R'] [CommRing A'] [CommRing B'] [CommRing R]
  [CommRing A] [CommRing B] [Algebra R' A'] [Algebra R' B'] [Algebra R A] [Algebra R B]
  (ρ : R' ≃+* R) (α : A' ≃+* A) (β : B' ≃+* B)
  (hα : ∀ r, α (algebraMap R' A' r) = algebraMap R A (ρ r))
  (hβ : ∀ r, β (algebraMap R' B' r) = algebraMap R B (ρ r))

/-- `R` as an `R'`-algebra along `ρ`. -/
abbrev equivAlgebra : Algebra R' R := ρ.toRingHom.toAlgebra

/-- An `R`-algebra as an `R'`-algebra along `ρ`. -/
abbrev equivAlgebraOver (A : Type u) [CommRing A] [Algebra R A] : Algebra R' A :=
  ((algebraMap R A).comp ρ.toRingHom).toAlgebra

/-- With `R'`-algebra structures on `R` and `A` along `ρ`, the scalar tower `R' → R → A` is
compatible. -/
theorem equivAlgebra_isScalarTower (A : Type u) [CommRing A] [Algebra R A] :
    letI := equivAlgebra ρ
    letI := equivAlgebraOver ρ A
    IsScalarTower R' R A := by
  let := equivAlgebra ρ
  let := equivAlgebraOver ρ A
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `α` as a homomorphism of `R'`-algebras. -/
abbrev equivAlgHom (α : A' ≃+* A) (hα : ∀ r, α (algebraMap R' A' r) = algebraMap R A (ρ r)) :
    letI := equivAlgebraOver ρ A
    A' →ₐ[R'] A :=
  letI := equivAlgebraOver ρ A
  { α.toRingHom with commutes' := hα }

/-- The inverse isomorphisms `ρ.symm` and `α.symm` are compatible with the structure maps:
`α⁻¹ (algebraMap R A r) = algebraMap R' A' (ρ⁻¹ r)`. -/
theorem symm_compat (α : A' ≃+* A) (hα : ∀ r, α (algebraMap R' A' r) = algebraMap R A (ρ r))
    (r : R) : α.symm (algebraMap R A r) = algebraMap R' A' (ρ.symm r) := by
  rw [RingEquiv.symm_apply_eq, hα, RingEquiv.apply_symm_apply]

/-- The map of tensor products of the isomorphisms. -/
abbrev equivTensorProductMap : A' ⊗[R'] B' →+* A ⊗[R] B :=
  letI := equivAlgebra ρ
  letI := equivAlgebraOver ρ A
  letI := equivAlgebraOver ρ B
  haveI := equivAlgebra_isScalarTower ρ A
  haveI := equivAlgebra_isScalarTower ρ B
  tensorProductMap R' R A' B' A B (equivAlgHom ρ α hα) (equivAlgHom ρ β hβ)

/-- The change-of-rings map `Tor_i^{R'}(A', B') ⟶ Tor_i^R(A, B)` of the isomorphisms. -/
abbrev equivChangeMap (i : ℕ) :
    letI := moduleStructure canonicalSystem_nonempty R' A' B' i
    letI := moduleStructure canonicalSystem_nonempty R A B i
    torObj R' i A' B' →ₛₗ[equivTensorProductMap ρ α β hα hβ] torObj R i A B :=
  letI := equivAlgebra ρ
  letI := equivAlgebraOver ρ A
  letI := equivAlgebraOver ρ B
  haveI := equivAlgebra_isScalarTower ρ A
  haveI := equivAlgebra_isScalarTower ρ B
  changeMap canonicalSystem_nonempty R' R A' B' A B i (equivAlgHom ρ α hα) (equivAlgHom ρ β hβ)

/-- The change-of-rings map along the inverse isomorphisms. -/
abbrev equivChangeMapInv (i : ℕ) :
    letI := moduleStructure canonicalSystem_nonempty R A B i
    letI := moduleStructure canonicalSystem_nonempty R' A' B' i
    torObj R i A B →ₛₗ[equivTensorProductMap ρ.symm α.symm β.symm
      (symm_compat ρ α hα) (symm_compat ρ β hβ)] torObj R' i A' B' :=
  equivChangeMap (R' := R) (A' := A) (B' := B) (R := R') (A := A') (B := B') ρ.symm α.symm β.symm
    (symm_compat ρ α hα) (symm_compat ρ β hβ) i

/-- The change-of-rings map along the inverse isomorphisms is a left inverse of
`equivChangeMap`. -/
theorem equivChangeMapInv_equivChangeMap (i : ℕ) (x : torObj R' i A' B') :
    equivChangeMapInv ρ α β hα hβ i (equivChangeMap ρ α β hα hβ i x) = x := by
  let := equivAlgebra ρ
  let := equivAlgebraOver ρ A
  let := equivAlgebraOver ρ B
  have := equivAlgebra_isScalarTower ρ A
  have := equivAlgebra_isScalarTower ρ B
  let := equivAlgebra ρ.symm
  let := equivAlgebraOver ρ.symm A'
  let := equivAlgebraOver ρ.symm B'
  have := equivAlgebra_isScalarTower ρ.symm A'
  have := equivAlgebra_isScalarTower ρ.symm B'
  have : IsScalarTower R' R R' := IsScalarTower.of_algebraMap_eq fun r =>
    (ρ.symm_apply_apply r).symm
  have : IsScalarTower R' R A' := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (algebraMap R' A') (ρ.symm_apply_apply r).symm
  have : IsScalarTower R' R B' := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (algebraMap R' B') (ρ.symm_apply_apply r).symm
  have key := (canonicalLaws canonicalSystem_nonempty).map_comp R' R R' A' B' A B A' B' i
    (equivAlgHom ρ α hα) (equivAlgHom ρ β hβ)
    (equivAlgHom ρ.symm α.symm (symm_compat ρ α hα))
    (equivAlgHom ρ.symm β.symm (symm_compat ρ β hβ)) x
  have eA : ((equivAlgHom ρ.symm α.symm (symm_compat ρ α hα)).restrictScalars R').comp
      (equivAlgHom ρ α hα) = AlgHom.id R' A' := AlgHom.ext fun a => α.symm_apply_apply a
  have eB : ((equivAlgHom ρ.symm β.symm (symm_compat ρ β hβ)).restrictScalars R').comp
      (equivAlgHom ρ β hβ) = AlgHom.id R' B' := AlgHom.ext fun b => β.symm_apply_apply b
  rw [eA, eB, (canonicalLaws canonicalSystem_nonempty).map_id] at key
  exact key.symm

/-- The change-of-rings map along the inverse isomorphisms is a right inverse of
`equivChangeMap`. -/
theorem equivChangeMap_equivChangeMapInv (i : ℕ) (y : torObj R i A B) :
    equivChangeMap ρ α β hα hβ i (equivChangeMapInv ρ α β hα hβ i y) = y :=
  equivChangeMapInv_equivChangeMap ρ.symm α.symm β.symm (symm_compat ρ α hα)
    (symm_compat ρ β hβ) i y

/-- `equivTensorProductMap` sends `a ⊗ₜ b` to `α a ⊗ₜ β b`. -/
theorem equivTensorProductMap_tmul (a : A') (b : B') :
    equivTensorProductMap ρ α β hα hβ (a ⊗ₜ[R'] b) = α a ⊗ₜ[R] β b := by
  simp [equivTensorProductMap, tensorProductMap]
  rfl

/-- The map of tensor products of the inverse isomorphisms is a left inverse of
`equivTensorProductMap`. -/
theorem equivTensorProductMap_symm_comp :
    (equivTensorProductMap ρ.symm α.symm β.symm (symm_compat ρ α hα) (symm_compat ρ β hβ)).comp
      (equivTensorProductMap ρ α β hα hβ) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [RingHom.comp_apply, equivTensorProductMap_tmul, RingHom.id_apply,
      RingEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, RingHom.comp_apply] at hx hy ⊢; rw [hx, hy]

/-- The isomorphism `A' ⊗_{R'} B' ≃ A ⊗_R B` of the isomorphisms. -/
def equivTensorProductRingEquiv : A' ⊗[R'] B' ≃+* A ⊗[R] B :=
  RingEquiv.ofRingHom (equivTensorProductMap ρ α β hα hβ)
    (equivTensorProductMap ρ.symm α.symm β.symm (symm_compat ρ α hα) (symm_compat ρ β hβ))
    (equivTensorProductMap_symm_comp ρ.symm α.symm β.symm (symm_compat ρ α hα)
      (symm_compat ρ β hβ))
    (equivTensorProductMap_symm_comp ρ α β hα hβ)

/-- **`Tor_i` along isomorphisms of algebras.** Restricting the scalars of the
`A' ⊗_{R'} B'`-module `Tor_i^{R'}(A', B')` along the induced isomorphism
`A ⊗_R B ≃ A' ⊗_{R'} B'` gives the `A ⊗_R B`-module `Tor_i^R(A, B)`, the comparison being the
canonical change-of-rings map. -/
def restrictScalarsTorIsoOfRingEquiv (i : ℕ) :
    letI := moduleStructure canonicalSystem_nonempty R' A' B' i
    letI := moduleStructure canonicalSystem_nonempty R A B i
    (ModuleCat.restrictScalars (equivTensorProductRingEquiv ρ α β hα hβ).symm.toRingHom).obj
        (ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B')) ≅
      ModuleCat.of (A ⊗[R] B) (torObj R i A B) :=
  letI := moduleStructure canonicalSystem_nonempty R' A' B' i
  letI := moduleStructure canonicalSystem_nonempty R A B i
  letI : Module (A ⊗[R] B) (ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B')) :=
    Module.compHom _ (equivTensorProductRingEquiv ρ α β hα hβ).symm.toRingHom
  LinearEquiv.toModuleIso
    { toFun := fun x => equivChangeMap ρ α β hα hβ i x
      invFun := fun y => equivChangeMapInv ρ α β hα hβ i y
      map_add' := fun x y => (equivChangeMap ρ α β hα hβ i).map_add x y
      map_smul' := fun t x => by
        change equivChangeMap ρ α β hα hβ i
          ((equivTensorProductRingEquiv ρ α β hα hβ).symm t • x) = t • _
        rw [(equivChangeMap ρ α β hα hβ i).map_smulₛₗ]
        exact congrArg (· • _) ((equivTensorProductRingEquiv ρ α β hα hβ).apply_symm_apply t)
      left_inv := fun x => equivChangeMapInv_equivChangeMap ρ α β hα hβ i x
      right_inv := fun y => equivChangeMap_equivChangeMapInv ρ α β hα hβ i y }

/-- **`Tor_i` along isomorphisms of algebras**, as extension of scalars along the induced
isomorphism `A' ⊗_{R'} B' ≃ A ⊗_R B`. -/
def extendScalarsTorIsoOfRingEquiv (i : ℕ) :
    letI := moduleStructure canonicalSystem_nonempty R' A' B' i
    letI := moduleStructure canonicalSystem_nonempty R A B i
    (ModuleCat.extendScalars.{u, u, u} (equivTensorProductRingEquiv ρ α β hα hβ).toRingHom).obj
        (ModuleCat.of (A' ⊗[R'] B') (torObj R' i A' B')) ≅
      ModuleCat.of (A ⊗[R] B) (torObj R i A B) :=
  letI := moduleStructure canonicalSystem_nonempty R' A' B' i
  letI := moduleStructure canonicalSystem_nonempty R A B i
  (ModuleCat.extendScalarsIsoRestrictScalarsSymm (equivTensorProductRingEquiv ρ α β hα hβ)).app _ ≪≫
    restrictScalarsTorIsoOfRingEquiv ρ α β hα hβ i

end TorChangeOfRings
