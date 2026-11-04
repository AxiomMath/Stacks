module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsImmersion
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivationKernelDescent

/-!
# Derivation descent along the structure map of an immersion

Let `B` be an algebraic space over a scheme `S` and let `i : Z ⟶ X` be an immersion of algebraic
spaces. The inverse-image form `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` of its structure map is locally surjective
on the small étale site of `Z` (`isLocallySurjective_structureSharpInverseImage_of_isImmersion`),
so the descent of derivations along it applies: a derivation of `i⁻¹𝒪_X` with values in an
`𝒪_Z`-module which annihilates the kernel of `i♯` is the restriction along `i♯` of a unique
derivation of `𝒪_Z`, over an arbitrary presheaf of commutative rings mapping to `i⁻¹𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_derivation_of_structureSharpInverseImage_vanishing`: the
  descent, in unique-factorization form.
* `AlgebraicGeometry.Space.derivationStructureSharpInverseImageKernelEquiv`: the same as a
  bijection.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence of
  an immersion.
* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), the conormal sequence of
  a surjection of sheaves of rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X : AlgebraicSpaces B S hS}

/-- **Derivation descent along `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` for an immersion `i : Z ⟶ X`.**  A derivation
of `i⁻¹𝒪_X` with values in an `𝒪_Z`-module `W`, over an arbitrary base `a`, which annihilates the
kernel of `i♯`, is the restriction along `i♯` of a unique derivation of `𝒪_Z`. -/
theorem existsUnique_derivation_of_structureSharpInverseImage_vanishing (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom)
    {R : (SmallEtale B S hS Z.1)ᵒᵖ ⥤ CommRingCat.{u}}
    (a : R ⟶ (inverseImageStructureSheaf B S hS i).obj)
    (W : Modules.{u, u} B S hS Z.1 Z.2)
    (D : (Stacks.Sites.Conormal.restrictModuleAlong (SmallEtale.topology B S hS Z.1) W
      (structureSharpInverseImage B S hS i).hom).Derivation' a)
    (hD : ∀ (U : (SmallEtale B S hS Z.1)ᵒᵖ) (x : (inverseImageStructureSheaf B S hS i).obj.obj U),
      ((structureSharpInverseImage B S hS i).hom.app U) x = 0 → D.d x = 0) :
    ∃! D' : W.val.Derivation' (a ≫ (structureSharpInverseImage B S hS i).hom),
      ∀ (U : (SmallEtale B S hS Z.1)ᵒᵖ) (x : (inverseImageStructureSheaf B S hS i).obj.obj U),
        D'.d (((structureSharpInverseImage B S hS i).hom.app U) x) = D.d x := by
  have := isLocallySurjective_structureSharpInverseImage_of_isImmersion B S hS i hi
  exact Stacks.Sites.Conormal.existsUnique_derivation_of_vanishing_on_kernel
    (SmallEtale.topology B S hS Z.1) a (structureSharpInverseImage B S hS i) W D hD

/-- **The derivations of `𝒪_Z` are the derivations of `i⁻¹𝒪_X` annihilating the kernel of `i♯`**,
for an immersion `i : Z ⟶ X`. The bijection is restriction along `i♯`. -/
noncomputable def derivationStructureSharpInverseImageKernelEquiv (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom)
    {R : (SmallEtale B S hS Z.1)ᵒᵖ ⥤ CommRingCat.{u}}
    (a : R ⟶ (inverseImageStructureSheaf B S hS i).obj)
    (W : Modules.{u, u} B S hS Z.1 Z.2) :
    W.val.Derivation' (a ≫ (structureSharpInverseImage B S hS i).hom) ≃
      {D : (Stacks.Sites.Conormal.restrictModuleAlong (SmallEtale.topology B S hS Z.1) W
          (structureSharpInverseImage B S hS i).hom).Derivation' a //
        ∀ (U : (SmallEtale B S hS Z.1)ᵒᵖ)
          (x : (inverseImageStructureSheaf B S hS i).obj.obj U),
          ((structureSharpInverseImage B S hS i).hom.app U) x = 0 → D.d x = 0} :=
  haveI := isLocallySurjective_structureSharpInverseImage_of_isImmersion B S hS i hi
  Stacks.Sites.Conormal.derivationKernelEquiv (SmallEtale.topology B S hS Z.1) a
    (structureSharpInverseImage B S hS i) W

end AlgebraicGeometry.Space

end
