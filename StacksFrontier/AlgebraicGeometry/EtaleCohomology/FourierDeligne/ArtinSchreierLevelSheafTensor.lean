module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensorStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCharacterAdd

/-!
# Multiplicativity of Artin–Schreier sheaves with coefficients in a finite ring

Let `Λ` be a finite commutative ring. For characters `χ₁, χ₂ : π₁(X, x̄) → Λˣ` with open kernels,
the multiplication `Λ × Λ → Λ` is equivariant from `Λ_{χ₁} × Λ_{χ₂}` to `Λ_{χ₁χ₂}`, so it defines a
morphism of lisse sheaves `ℱ_{χ₁} ⊗ ℱ_{χ₂} ⟶ ℱ_{χ₁χ₂}` on Mathlib's small étale site
(`Stacks.EtaleCohomology.lisseEtaleSheafTensorHom`), which is an isomorphism: on stalks it is the
multiplication `Λ ⊗_Λ Λ ≅ Λ`. Since the Artin–Schreier character of `g₁ + g₂` is the product of
those of `g₁` and `g₂` (`Stacks.ArtinSchreier.artinSchreierCharacter_add`), this gives
`L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₁ + g₂)` for the Artin–Schreier sheaves with coefficients in `Λ`. On
`𝔸³ = Spec k[x, t, u]` this is the identity `L_ψ(xt) ⊗ L_ψ(tu) ≅ L_ψ(t(x + u))` through which the
composite of two Fourier transforms is computed, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) through Laumon's Fourier transform.

## Main definitions

* `Stacks.EtaleCohomology.characterMulBilinear`: the multiplication of `Λ`, on `ULift Λ`.
* `Stacks.EtaleCohomology.lisseEtaleSheafCharacterTensorIso`: `ℱ_{χ₁} ⊗ ℱ_{χ₂} ≅ ℱ_{χ₁χ₂}`.
* `Stacks.ArtinSchreier.artinSchreierLevelSheafTensorIso`: `L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₁ + g₂)`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section Character

variable (Λ : Type) [CommRing Λ]

/-- **The multiplication of `Λ`**, as a bilinear map on `ULift Λ`. -/
def characterMulBilinear : ULift.{u + 1} Λ →ₗ[Λ] ULift.{u + 1} Λ →ₗ[Λ] ULift.{u + 1} Λ :=
  ((LinearMap.mul Λ Λ).compl₁₂ (ULift.moduleEquiv (R := Λ)).toLinearMap
    (ULift.moduleEquiv (R := Λ)).toLinearMap).compr₂ (ULift.moduleEquiv (R := Λ)).symm.toLinearMap

/-- `characterMulBilinear Λ a b` is the lift of the product `a.down * b.down`. -/
theorem characterMulBilinear_apply (a b : ULift.{u + 1} Λ) :
    characterMulBilinear Λ a b = ULift.up (a.down * b.down) :=
  rfl

end Character

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]
  {χ₁ χ₂ χ : EtaleFundamentalGroup X.1 x →* Λˣ}
  (h₁ : IsOpen (χ₁.ker : Set (EtaleFundamentalGroup X.1 x)))
  (h₂ : IsOpen (χ₂.ker : Set (EtaleFundamentalGroup X.1 x)))
  (h : IsOpen (χ.ker : Set (EtaleFundamentalGroup X.1 x)))

include h₁ h₂ h in
/-- The multiplication is equivariant from `Λ_{χ₁} × Λ_{χ₂}` to `Λ_{χ₁χ₂}`. -/
theorem characterMulBilinear_equivariant (hχ : χ = χ₁ * χ₂) (g : EtaleFundamentalGroup X.1 x)
    (a : (characterContinuousModule Λ χ₁ h₁).obj.obj.obj.V)
    (b : (characterContinuousModule Λ χ₂ h₂).obj.obj.obj.V) :
    characterMulBilinear Λ (((characterContinuousModule Λ χ₁ h₁).obj.obj.obj.ρ g).hom a)
        (((characterContinuousModule Λ χ₂ h₂).obj.obj.obj.ρ g).hom b) =
      ((characterContinuousModule Λ χ h).obj.obj.obj.ρ g).hom (characterMulBilinear Λ a b) := by
  subst hχ
  refine ULift.ext _ _ ?_
  show ((χ₁ g : Λ) * a.down) * ((χ₂ g : Λ) * b.down) = ((χ₁ * χ₂) g : Λ) * (a.down * b.down)
  rw [MonoidHom.mul_apply, Units.val_mul]
  ring

/-- **`ℱ_{χ₁} ⊗ ℱ_{χ₂} ≅ ℱ_{χ₁χ₂}`** for characters `χ₁, χ₂ : π₁(X, x̄) → Λˣ` with open kernels:
the morphism of sheaves attached to the multiplication of `Λ`, an isomorphism because on stalks
it is the multiplication `Λ ⊗_Λ Λ ≅ Λ`. -/
def lisseEtaleSheafCharacterTensorIso (hχ : χ = χ₁ * χ₂) :
    (lisseEtaleSheaf B X x Λ).obj (characterContinuousModule Λ χ₁ h₁) ⊗
        (lisseEtaleSheaf B X x Λ).obj (characterContinuousModule Λ χ₂ h₂) ≅
      (lisseEtaleSheaf B X x Λ).obj (characterContinuousModule Λ χ h) :=
  have hsurj : ∀ r : ULift.{u + 1} Λ, ∃ p q : ULift.{u + 1} Λ, characterMulBilinear Λ p q = r :=
    fun r => ⟨r, ULift.up 1, ULift.ext _ _ (mul_one r.down)⟩
  have hcard : Nat.card (TensorProduct Λ (ULift.{u + 1} Λ) (ULift.{u + 1} Λ)) ≤
      Nat.card (ULift.{u + 1} Λ) :=
    ((Nat.card_congr ((TensorProduct.congr (ULift.moduleEquiv (R := Λ))
      (ULift.moduleEquiv (R := Λ))).trans (TensorProduct.lid Λ Λ)).toEquiv).trans
        (Nat.card_congr (ULift.moduleEquiv (R := Λ)).toEquiv).symm).le
  haveI := isIso_lisseEtaleSheafTensorHom B X x Λ (P := characterContinuousModule Λ χ₁ h₁)
    (Q := characterContinuousModule Λ χ₂ h₂) (R := characterContinuousModule Λ χ h)
    (characterMulBilinear Λ) (characterMulBilinear_equivariant B X x Λ h₁ h₂ h hχ) hsurj hcard
  asIso (lisseEtaleSheafTensorHom B X x Λ (characterMulBilinear Λ)
    (characterMulBilinear_equivariant B X x Λ h₁ h₂ h hχ))

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g₁ g₂ : A)
  [ConnectedSpace (Spec (.of A))] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- **`L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₁ + g₂)`** for the Artin–Schreier sheaves with coefficients in the
finite ring `Λ`, for any choices of points of the fibres of the three Artin–Schreier covers: the
character of `g₁ + g₂` is the product of those of `g₁` and `g₂`. -/
def artinSchreierLevelSheafTensorIso (x : GeometricPoint (Spec (.of A)))
    (p₁ : (finiteEtaleFiberFunctor x).obj (cover k A g₁))
    (p₂ : (finiteEtaleFiberFunctor x).obj (cover k A g₂))
    (p₁₂ : (finiteEtaleFiberFunctor x).obj (cover k A (g₁ + g₂))) :
    artinSchreierLevelSheaf k A g₁ Λ ψ B hX x p₁ ⊗ artinSchreierLevelSheaf k A g₂ Λ ψ B hX x p₂ ≅
      artinSchreierLevelSheaf k A (g₁ + g₂) Λ ψ B hX x p₁₂ :=
  lisseEtaleSheafCharacterTensorIso B (specObject A B hX) x Λ
    (isOpen_ker_artinSchreierCharacter k A g₁ Λ ψ x p₁)
    (isOpen_ker_artinSchreierCharacter k A g₂ Λ ψ x p₂)
    (isOpen_ker_artinSchreierCharacter k A (g₁ + g₂) Λ ψ x p₁₂)
    (artinSchreierCharacter_add ψ x p₁ p₂ p₁₂)

end Stacks.ArtinSchreier
