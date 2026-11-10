module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functoriality
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.AffineChartSections
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# Surjectivity of `Sym` of an epimorphism on affine sections

A morphism `g : ℰ ⟶ ℱ` of modules on a scheme induces the homomorphism
`Stacks.SymGraded.schemeSheafGradedAlgebraHom g : Sym(ℰ) ⟶ Sym(ℱ)` of sheaf-level graded
algebras. When `ℰ` and `ℱ` are quasi-coherent and `g` is an epimorphism, it is surjective on
homogeneous sections over every affine open.

## Main results

* `Stacks.Chow.GenuineChern.surjective_gradedMapₛₗ`: `Symⁿ` of a surjective linear map is
  surjective.
* `Stacks.Chow.GenuineChern.surjectiveOnAffineSections_schemeSheafGradedAlgebraHom`: for an
  epimorphism of quasi-coherent modules, `Sym(g)` is surjective on homogeneous sections over affine
  opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.Chow.GenuineChern

/-- `Symⁿ` of a surjective linear map is surjective. -/
theorem surjective_gradedMapₛₗ {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (n : ℕ) : Function.Surjective (gradedMapₛₗ (n : ℤ) (RingHom.id R) f) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ SymPow.symmetricPower n R N := hy
  rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at hy'
  suffices h : y ∈ (Submodule.map (gradedMapₛₗ (n : ℤ) (RingHom.id R) f)
      (⊤ : Submodule R (gradedPiece (R := R) M n))).map (gradedPiece (R := R) N n).subtype by
    obtain ⟨_, ⟨x, -, rfl⟩, hx⟩ := h
    exact ⟨x, Subtype.ext hx⟩
  refine Submodule.span_le.2 ?_ hy'
  rintro _ ⟨t, rfl⟩
  choose s hs using fun i => hf (t i)
  refine ⟨gradedMapₛₗ (n : ℤ) (RingHom.id R) f
      ⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩,
    ⟨_, trivial, rfl⟩, ?_⟩
  change SymmetricAlgebra.mapₛₗ (RingHom.id R) f (∏ i : Fin n, SymmetricAlgebra.ι R M (s i)) = _
  simp only [map_prod, SymmetricAlgebra.mapₛₗ_ι, hs]

variable {X : Scheme.{u}} {E F : X.Modules} (g : E ⟶ F)
  (hE : IsQuasicoherentPieces E) (hF : IsQuasicoherentPieces F)
  [E.IsQuasicoherent] [F.IsQuasicoherent] [Epi g]

/-- For an epimorphism `g` of quasi-coherent modules, `Sym(g)` is surjective on homogeneous
sections over every affine open. -/
theorem surjectiveOnAffineSections_schemeSheafGradedAlgebraHom :
    Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections
      (schemeSheafGradedAlgebraHom g hE hF) := by
  intro U hU n y
  obtain ⟨y', rfl⟩ := (bijective_sheafifyUnit_app_of_isAffineOpen F hU n).2 y
  obtain ⟨x', hx'⟩ := surjective_gradedMapₛₗ (R := Γ(X, U)) (M := Γ(E, U)) (N := Γ(F, U))
    (g.val.app (op U)).hom (Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X g U hU) n y'
  exact ⟨PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
    (siteGradedPiece E.val n)) (op U) x', (PresheafOfModules.unit_naturality_apply
    (R := X.ringCatSheaf) (α := 𝟙 X.ringCatSheaf.obj) (siteGradedPieceMap g.val n) (op U)
    x').trans (congrArg _ hx')⟩

end Stacks.Chow.GenuineChern

end
