module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Basic

/-!
# Graded ring maps of sections of symmetric algebras from semilinear maps of sections

Let `E₁` and `E₂` be quasi-coherent modules on schemes `X₁` and `X₂`, `V₁ ⊆ X₁` and `V₂ ⊆ X₂`
affine opens, `σ : Γ(X₁, V₁) ⟶ Γ(X₂, V₂)` a ring map and `u : Γ(E₁, V₁) ⟶ Γ(E₂, V₂)` a
`σ`-semilinear map. Over an affine open the graded ring of sections of `Sym(Eᵢ)` is the symmetric
algebra of the sections of `Eᵢ` (`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`), so `u`
induces a homomorphism of graded rings `Γ(V₁, Sym E₁) ⟶ Γ(V₂, Sym E₂)` carrying the degree-one
element of a section `x` to the degree-one element of `u(x)`.

Over an affine open every degree-one section of `Sym(E)` is the degree-one element of a section
of `E`.

## Main definitions

* `Stacks.Tag01VMVeryAmple.symSectionGradedHom`: the homomorphism of graded rings.

## Main results

* `Stacks.Tag01VMVeryAmple.symSectionGradedHom_gen`: its value on degree-one elements.
* `Stacks.Tag01VMVeryAmple.exists_eq_genSection_of_mem_grading_one`: degree-one sections over an
  affine open are degree-one elements of sections.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded.AffinePieces
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe u

namespace Stacks.Tag01VMVeryAmple

variable {X₁ X₂ : Scheme.{u}} (E₁ : X₁.Modules) [E₁.IsQuasicoherent] (E₂ : X₂.Modules)
  [E₂.IsQuasicoherent] {V₁ : X₁.Opens} {V₂ : X₂.Opens} (hV₁ : IsAffineOpen V₁)
  (hV₂ : IsAffineOpen V₂)

/-- The degree-one element of the graded ring of sections attached to a section of `E`. -/
abbrev genSection {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (V : X.Opens)
    (x : Γ(E, V)) : (symAlgebra E).sectionRing V :=
  DirectSum.of ((symAlgebra E).sectionPieces V) 1
    (((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)) x)

/-- The degree-one element attached to a section of `E` lies in degree one of the grading. -/
theorem genSection_mem {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (V : X.Opens)
    (x : Γ(E, V)) : genSection E V x ∈ (symAlgebra E).grading V 1 :=
  (symAlgebra E).of_mem_grading V _

/-- **The homomorphism of graded rings of sections induced by a semilinear map of sections**,
over affine opens. -/
def symSectionGradedHom (σ : Γ(X₁, V₁) →+* Γ(X₂, V₂)) (u : Γ(E₁, V₁) →ₛₗ[σ] Γ(E₂, V₂)) :
    (symAlgebra E₁).grading V₁ →+*ᵍ (symAlgebra E₂).grading V₂ where
  __ := ((symSectionRingEquiv E₂ hV₂
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₂)).symm.toRingHom.comp
    (SymmetricAlgebra.mapₛₗ σ u)).comp
      (symSectionRingEquiv E₁ hV₁
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₁)).toRingHom
  map_mem := by
    intro n x hx
    have h1 := (mem_symmetricPower_symSectionRingEquiv E₁ hV₁
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₁) n x).mpr hx
    have h2 := SymmetricAlgebra.mapₛₗ_mem_symmetricPower σ u n h1
    refine (mem_symmetricPower_symSectionRingEquiv E₂ hV₂
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₂) n _).mp ?_
    simpa using h2

/-- **The induced homomorphism carries the degree-one element of `x` to that of `u(x)`.** -/
theorem symSectionGradedHom_gen (σ : Γ(X₁, V₁) →+* Γ(X₂, V₂))
    (u : Γ(E₁, V₁) →ₛₗ[σ] Γ(E₂, V₂)) (x : Γ(E₁, V₁)) :
    symSectionGradedHom E₁ E₂ hV₁ hV₂ σ u (genSection E₁ V₁ x) = genSection E₂ V₂ (u x) := by
  apply (symSectionRingEquiv E₂ hV₂
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E₂)).injective
  change symSectionRingEquiv E₂ hV₂ _ ((symSectionRingEquiv E₂ hV₂ _).symm
      (SymmetricAlgebra.mapₛₗ σ u (symSectionRingEquiv E₁ hV₁ _ (genSection E₁ V₁ x)))) = _
  rw [RingEquiv.apply_symm_apply, symSectionRingEquiv_of_symmetricAlgebraGen,
    symSectionRingEquiv_of_symmetricAlgebraGen, SymmetricAlgebra.mapₛₗ_ι]

/-- **Over an affine open every degree-one section of `Sym(E)` is the degree-one element of a
section of `E`.** -/
theorem exists_eq_genSection_of_mem_grading_one {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) {y : (symAlgebra E).sectionRing V}
    (hy : y ∈ (symAlgebra E).grading V 1) : ∃ x : Γ(E, V), y = genSection E V x := by
  have h1 := (mem_symmetricPower_symSectionRingEquiv E hV
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) 1 y).mpr hy
  have h2 : SymPow.symmetricPower 1 Γ(X, V) Γ(E, V) =
      LinearMap.range (SymmetricAlgebra.ι Γ(X, V) Γ(E, V)) := pow_one _
  rw [h2] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, (symSectionRingEquiv E hV
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)).injective ?_⟩
  rw [symSectionRingEquiv_of_symmetricAlgebraGen, ← hx]

end Stacks.Tag01VMVeryAmple

end
