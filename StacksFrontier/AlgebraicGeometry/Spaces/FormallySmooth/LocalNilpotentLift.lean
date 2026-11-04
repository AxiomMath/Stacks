module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.On
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SpecOver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal lifts over a local base with nilpotent maximal ideal

A smooth morphism `f : X ⟶ Y` of algebraic spaces over `S` solves every lifting problem along a
square-zero closed immersion `T ⟶ T'` of affine objects whose ring of global sections over `T'`
is a finite algebra over a local ring with nilpotent maximal ideal — for instance the spectrum of
a finite algebra over an Artinian local ring, or of an Artinian local ring itself. These are the
lifting problems that deformation theory consumes; they are special cases of the implication of
Stacks 04AM from smoothness to formal smoothness
(`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`).

## Main results

* `AlgebraicGeometry.Space.hasFiniteLocalNilpotentSections_specOver`: the spectrum of a finite
  algebra over a local ring with nilpotent maximal ideal is such a test object.
* `AlgebraicGeometry.Space.formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth` and its
  local case `AlgebraicGeometry.Space.formallySmoothOn_hasLocalNilpotentSections_of_isSmooth`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The spectrum of a finite algebra over a local ring with nilpotent maximal ideal has global
sections finite over that ring. -/
theorem hasFiniteLocalNilpotentSections_specOver {A' : Type u} [CommRing A']
    (s₀ : Spec (.of A') ⟶ S) (R₀ : Type u) [CommRing R₀] [IsLocalRing R₀]
    (hR₀ : IsNilpotent (maximalIdeal R₀)) (R : Type u) [CommRing R] [Algebra A' R]
    [Algebra R₀ R] [Module.Finite R₀ R] (hR : B.Contains (Spec (.of R))) :
    HasFiniteLocalNilpotentSections B S hS (specOver B S hS s₀ R hR) := by
  show ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : IsLocalRing R₁) (_ : Algebra R₁ Γ(Spec (.of R), ⊤)),
    IsNilpotent (maximalIdeal R₁) ∧ Module.Finite R₁ Γ(Spec (.of R), ⊤)
  let e : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let : Algebra R₀ Γ(Spec (.of R), ⊤) := ((e : R →+* Γ(Spec (.of R), ⊤)).comp
    (algebraMap R₀ R)).toAlgebra
  let e' : R ≃ₐ[R₀] Γ(Spec (.of R), ⊤) := { e with commutes' := fun _ => rfl }
  exact ⟨R₀, inferInstance, inferInstance, (inferInstance : Algebra R₀ Γ(Spec (.of R), ⊤)), hR₀,
    Module.Finite.equiv e'.toLinearEquiv⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A smooth morphism of algebraic spaces lifts over a finite algebra over a local base with
nilpotent maximal ideal.** A smooth morphism of algebraic spaces over `S` solves every lifting
problem along a square-zero closed immersion of affine objects whose larger object has ring of
global sections finite over a local ring with nilpotent maximal ideal: it is formally smooth
(`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`, Stacks 04AM). -/
@[sga "3 III 2.5" "(a), special case"]
theorem formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f) : FormallySmoothOn (HasFiniteLocalNilpotentSections B S hS) f :=
  (formallySmooth_of_isSmooth' hX hY hf).formallySmoothOn _

/-- **A smooth morphism of algebraic spaces lifts over a local base with nilpotent maximal
ideal**, an Artinian local ring for instance: the local case of
`AlgebraicGeometry.Space.formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth`. -/
@[sga "1 III 3.1" "(i)⇒(iii)", sga "3 III 2.5" "(a), special case"]
theorem formallySmoothOn_hasLocalNilpotentSections_of_isSmooth
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f) : FormallySmoothOn (HasLocalNilpotentSections B S hS) f :=
  (formallySmooth_of_isSmooth' hX hY hf).formallySmoothOn _

end AlgebraicGeometry.Space

end
