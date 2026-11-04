module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs

/-!
# Algebraic upper shriek along a surjection is derived Hom

Let `φ : R →+* A` be a surjective homomorphism.  Then `A` is presented by the polynomial algebra
in *no* variables, and for that presentation the algebraic upper shriek functor of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs` is

`φ^!(K) = RHom_P(A, K ⊗_R^L P)[0]` with `P = MvPolynomial (Fin 0) R` ,

so it is `RHom_R(A, -)` up to the two comparisons that `MvPolynomial.C : R →+* P` being an
isomorphism provides: derived base change along an isomorphism agrees with derived coextension
of scalars along it, and derived coextension composes.

## Main definitions

* `Dualizing.PolynomialPresentation.ofSurjective`: the presentation of a surjective
  homomorphism by the polynomial algebra in no variables.
* `Dualizing.PolynomialPresentation.derivedExtensionIsoDerivedHom`: for a presentation whose
  structure map `MvPolynomial.C` has a two-sided inverse, derived base change along it is derived
  coextension of scalars along it.

## Main results

* `Dualizing.upperShriekFunctor_ofSurjective_iso_derivedHom`: for a surjective `φ`, the upper
  shriek functor of its presentation with no variables is `RHom_R(A, -)`.

## References

* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0BZI](https://stacks.math.columbia.edu/tag/0BZI)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Restriction of scalars along a ring homomorphism with a two-sided inverse is right adjoint to
restriction of scalars along that inverse: the two functors are the two directions of the
equivalence `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`, which is an adjoint equivalence. -/
def adjRestrictOfInv {X Y : Type u} [CommRing X] [CommRing Y]
    (ε : X →+* Y) (ε' : Y →+* X) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ y, ε (ε' y) = y) :
    ModuleCat.restrictScalars.{max v u} ε' ⊣ ModuleCat.restrictScalars.{max v u} ε :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    ({ ε with invFun := ε', left_inv := h₁, right_inv := h₂ } : X ≃+* Y)).symm.toAdjunction

namespace PolynomialPresentation

variable {f : R →+* A}

/-- For a presentation whose structure map `MvPolynomial.C : R →+* P` has a two-sided inverse `q`,
derived base change `- ⊗_R^L P` is isomorphic to derived coextension of scalars `RHom_R(P, -)`. -/
def derivedExtensionIsoDerivedHom (p : PolynomialPresentation f) (q : p.Poly →+* R)
    (h₁ : ∀ x, q (MvPolynomial.C x) = x) (h₂ : ∀ y, MvPolynomial.C (q y) = y) :
    p.derivedExtension.{u, v} ≅
      derivedHom.{u, v, u} (MvPolynomial.C : R →+* p.Poly) :=
  letI : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  let adjInvLeft := CategoryTheory.Adjunction.mapDerivedCategory
    (adjRestrictOfInv.{u, v} (MvPolynomial.C : R →+* p.Poly) q h₁ h₂)
  let adjInvRight := CategoryTheory.Adjunction.mapDerivedCategory
    (adjRestrictOfInv.{u, v} q (MvPolynomial.C : R →+* p.Poly) h₂ h₁)
  let adjExtend := CategoryTheory.Adjunction.mapDerivedCategory
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (MvPolynomial.C : R →+* p.Poly))
  let adjHom := Classical.choice
    (restrictScalarsDerived_adj_derivedHom.{u, v, u} (MvPolynomial.C : R →+* p.Poly))
  adjExtend.leftAdjointUniq adjInvLeft ≪≫ (adjHom.rightAdjointUniq adjInvRight).symm

end PolynomialPresentation

/-- The inverse of `MvPolynomial.C : R →+* MvPolynomial (Fin 0) R`, the polynomial algebra in no
variables over `R` being `R` itself. -/
def mvPolynomialEmptyInv (R : Type u) [CommRing R] : MvPolynomial (Fin 0) R →+* R :=
  (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom

/-- The map `mvPolynomialEmptyInv R` sends the constant polynomial `C r` to `r`. -/
@[simp]
theorem mvPolynomialEmptyInv_C (r : R) : mvPolynomialEmptyInv R (MvPolynomial.C r) = r := by
  rw [← MvPolynomial.isEmptyRingEquiv_symm_apply]
  exact (MvPolynomial.isEmptyRingEquiv R (Fin 0)).apply_symm_apply r

/-- Every polynomial `x` in no variables over `R` is the constant polynomial on
`mvPolynomialEmptyInv R x`. -/
@[simp]
theorem C_mvPolynomialEmptyInv (x : MvPolynomial (Fin 0) R) :
    MvPolynomial.C (mvPolynomialEmptyInv R x) = x := by
  rw [← MvPolynomial.isEmptyRingEquiv_symm_apply]
  exact (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm_apply_apply x

/-- The presentation of a surjective ring homomorphism `φ : R →+* A` as a quotient of the
polynomial algebra `MvPolynomial (Fin 0) R` in no variables. -/
def PolynomialPresentation.ofSurjective (f : R →+* A) (hf : Function.Surjective f) :
    PolynomialPresentation f where
  variableCount := 0
  toRingHom := f.comp (mvPolynomialEmptyInv R)
  commutes := by ext r; simp
  surjective := hf.comp (MvPolynomial.isEmptyRingEquiv R (Fin 0)).surjective

/-- Let `φ : R →+* A` be surjective. Then the algebraic upper shriek functor of its presentation
with no variables is isomorphic to the derived coextension-of-scalars functor
`RHom_R(A, -) : D(R) ⥤ D(A)`. -/
theorem upperShriekFunctor_ofSurjective_iso_derivedHom
    (f : R →+* A) (hf : Function.Surjective f) :
    Nonempty ((PolynomialPresentation.ofSurjective f hf).upperShriekFunctor.{u, v} ≅
      derivedHom.{u, v, u} f) := by
  set p := PolynomialPresentation.ofSurjective f hf
  obtain ⟨eComp⟩ := derivedHomCompIso.{u, v} (MvPolynomial.C : R →+* p.Poly) p.toRingHom
  refine ⟨?_ ≪≫ (p.commutes ▸ eComp)⟩
  refine Functor.isoWhiskerLeft p.derivedExtension.{u, v} ?_ ≪≫
    Functor.isoWhiskerRight (p.derivedExtensionIsoDerivedHom.{u, v} (mvPolynomialEmptyInv R)
      mvPolynomialEmptyInv_C C_mvPolynomialEmptyInv)
      (derivedHom.{u, v, u} p.toRingHom)
  exact Functor.isoWhiskerLeft (derivedHom.{u, v, u} p.toRingHom)
      (shiftFunctorZero (DerivedCategory (ModuleCat.{max v u} A)) ℤ) ≪≫
    (derivedHom.{u, v, u} p.toRingHom).rightUnitor

end

end Dualizing

end
