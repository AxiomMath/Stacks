module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamRestriction
public import StacksFrontier.RingTheory.DeRham.LaurentResidueTransport
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpen

/-!
# Kähler forms transported along an isomorphism of the base and of the algebra

On a scheme the relative forms over an affine open are the Kähler forms of a map of commutative
rings `φ : Λ ⟶ B`, `Λ = Γ(S, V)` and `B = Γ(X, U)`
(`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`). In a computation one knows an
algebra `C` over a ring `R` together with isomorphisms `Λ ≅ R` and `C ≅ B` compatible with the
structure maps. This file transports the Kähler forms along such isomorphisms, and shows that the
transport is natural in maps of such data.

## Main definitions

* `KaehlerDifferential.baseEquiv`: `Ω[B⁄Λ] ≅ Ω[B⁄R]` when the two bases have the same image.
* `KaehlerDifferential.formsTransport`: `⋀^p Ω[B⁄Λ] ≅ ⋀^p Ω[C⁄R]`.

## Main results

* `KaehlerDifferential.formsTransport_smul`: the transport is semilinear along `e.symm`.
* `KaehlerDifferential.formsTransport_ιMulti_d`: the transport on generators.
* `KaehlerDifferential.formsTransport_formsMap`: the transport is natural.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace KaehlerDifferential

section Base

variable {Λ R B : Type u} [CommRing Λ] [CommRing R] [CommRing B] [Algebra Λ B] [Algebra R B]

/-- **The Kähler differentials over two bases with the same image in `B` agree.** -/
def baseEquiv (b : Λ ≃+* R) (h : ∀ l, algebraMap Λ B l = algebraMap R B (b l)) :
    Ω[B⁄Λ] ≃ₗ[B] Ω[B⁄R] :=
  letI : Algebra Λ R := b.toRingHom.toAlgebra
  haveI : IsScalarTower Λ R B := .of_algebraMap_eq h
  letI : Algebra R Λ := b.symm.toRingHom.toAlgebra
  haveI : IsScalarTower R Λ B := .of_algebraMap_eq fun r => by
    change algebraMap R B r = algebraMap Λ B (b.symm r)
    rw [h, RingEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (map Λ R B B) (map R Λ B B)
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => by simp))
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => by simp))

/-- `baseEquiv` sends `D Λ B x` to `D R B x`. -/
@[simp]
theorem baseEquiv_D (b : Λ ≃+* R) (h : ∀ l, algebraMap Λ B l = algebraMap R B (b l)) (x : B) :
    baseEquiv b h (D Λ B x) = D R B x := by
  let : Algebra Λ R := b.toRingHom.toAlgebra
  have : IsScalarTower Λ R B := .of_algebraMap_eq h
  exact (map_D Λ R B B x).trans rfl

end Base

section Transport

variable {Λ B : CommRingCat.{u}} (φ : Λ ⟶ B) {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
  (b : Λ ≃+* R) (e : C ≃+* B) (h : ∀ l, φ l = e (algebraMap R C (b l)))

variable (R) in
/-- The `R`-algebra structure of `B` transported from `C`. -/
abbrev transportAlgebra : Algebra R B := ((e : C →+* B).comp (algebraMap R C)).toAlgebra

variable (R) in
/-- The identification `C ≅ B` as an isomorphism of `R`-algebras. -/
def transportAlgEquiv : letI := transportAlgebra R e; C ≃ₐ[R] B :=
  letI := transportAlgebra R e
  AlgEquiv.ofRingEquiv (f := e) fun _ => rfl

/-- **The Kähler forms of `φ : Λ ⟶ B` are the Kähler forms of `C` over `R`.** -/
def formsTransport (p : ℕ) :
    ⋀[B]^p ↥(CommRingCat.KaehlerDifferential φ) ≃+ ⋀[C]^p (Ω[C⁄R]) :=
  letI := φ.hom.toAlgebra
  letI := transportAlgebra R e
  let hb : ∀ l, algebraMap Λ B l = algebraMap R B (b l) := h
  ((Stacks.AffineExteriorPower.exteriorPowerCongr (baseEquiv b hb) p).toAddEquiv).trans
    { toFun := formsₛₗ ((transportAlgEquiv R e).symm : B →ₐ[R] C) p
      invFun := formsₛₗ (transportAlgEquiv R e : C →ₐ[R] B) p
      left_inv := formsₛₗ_apply_symm (transportAlgEquiv R e) p
      right_inv := formsₛₗ_symm_apply (transportAlgEquiv R e) p
      map_add' := map_add _ }

/-- The transport is semilinear: `c • x` goes to `e.symm c` times the image of `x`. -/
theorem formsTransport_smul (p : ℕ) (c : B) (x : ⋀[B]^p ↥(CommRingCat.KaehlerDifferential φ)) :
    formsTransport φ b e h p (c • x) = e.symm c • formsTransport φ b e h p x := by
  let := φ.hom.toAlgebra
  let := transportAlgebra R e
  change formsₛₗ _ p (Stacks.AffineExteriorPower.exteriorPowerCongr _ p (c • x)) = _
  rw [LinearEquiv.map_smul, map_smulₛₗ]
  rfl

/-- **The transport on generators**: `d x₁ ∧ ⋯ ∧ d x_p` goes to the wedge of the differentials of
the corresponding elements of `C`. -/
theorem formsTransport_ιMulti_d (p : ℕ) (x : Fin p → B) :
    formsTransport φ b e h p
        (exteriorPower.ιMulti B p fun i ↦ CommRingCat.KaehlerDifferential.d (f := φ) (x i)) =
      exteriorPower.ιMulti C p fun i ↦ D R C (e.symm (x i)) := by
  let := φ.hom.toAlgebra
  let := transportAlgebra R e
  let hb : ∀ l, algebraMap Λ B l = algebraMap R B (b l) := h
  change formsₛₗ _ p (exteriorPower.map p (baseEquiv b hb).toLinearMap
    (exteriorPower.ιMulti B p fun i ↦ D Λ B (x i))) = _
  rw [exteriorPower.map_apply_ιMulti, formsₛₗ_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, LinearEquiv.coe_coe, baseEquiv_D, mapₛₗ_D]
  rfl

end Transport

section Naturality

variable {Λ B₁ B₂ : CommRingCat.{u}} (φ₁ : Λ ⟶ B₁) (φ₂ : Λ ⟶ B₂) (ρ' : B₁ ⟶ B₂)
  (hρ' : φ₁ ≫ ρ' = φ₂) {R C₁ C₂ : Type u} [CommRing R] [CommRing C₁] [CommRing C₂] [Algebra R C₁]
  [Algebra R C₂] (b : Λ ≃+* R) (e₁ : C₁ ≃+* B₁) (e₂ : C₂ ≃+* B₂)
  (h₁ : ∀ l, φ₁ l = e₁ (algebraMap R C₁ (b l))) (h₂ : ∀ l, φ₂ l = e₂ (algebraMap R C₂ (b l)))
  (ρ : C₁ →ₐ[R] C₂) (hρ : ∀ c, e₂ (ρ c) = ρ' (e₁ c))

include hρ in
/-- **The transport is natural**: the map of forms along `ρ' : B₁ ⟶ B₂` is, after transport, the
map of forms along the corresponding `ρ : C₁ → C₂`. -/
theorem formsTransport_formsMap (p : ℕ) (x : ⋀[B₁]^p ↥(CommRingCat.KaehlerDifferential φ₁)) :
    formsTransport φ₂ b e₂ h₂ p
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap φ₁ φ₂ ρ' hρ' p x) =
      formsₛₗ ρ p (formsTransport φ₁ b e₁ h₁ p x) := by
  have hsymm : ∀ c : B₁, e₂.symm (ρ' c) = ρ (e₁.symm c) := fun c => by
    rw [RingEquiv.symm_apply_eq, hρ, RingEquiv.apply_symm_apply]
  refine Stacks.AlgebraicGeometry.AffineOpenDeRham.eq_of_smul_ιMulti_d φ₁ p
    (fun y => formsTransport φ₂ b e₂ h₂ p
      (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap φ₁ φ₂ ρ' hρ' p y))
    (fun y => formsₛₗ ρ p (formsTransport φ₁ b e₁ h₁ p y)) ?_ ?_ ?_ ?_ x
  · rw [Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_zero, map_zero, map_zero, map_zero]
  · intro y z hy hz
    rw [Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_add, map_add, map_add, map_add, hy, hz]
  · intro c y hy
    rw [Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_smul, formsTransport_smul, hy,
      formsTransport_smul, map_smulₛₗ, hsymm]
    rfl
  · intro c
    rw [Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_ιMulti_d, formsTransport_ιMulti_d,
      formsTransport_ιMulti_d, formsₛₗ_ιMulti]
    congr 1
    funext i
    rw [mapₛₗ_D, ← hsymm]

end Naturality

end KaehlerDifferential

end
