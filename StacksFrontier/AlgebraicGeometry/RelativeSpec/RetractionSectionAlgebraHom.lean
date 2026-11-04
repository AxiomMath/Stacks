module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition

/-!
# The section of a retraction, carried along a morphism of algebras

Let `A` and `B` be quasi-coherent algebras on one base `X` and let `ψ : A ⟶ B` be a morphism of
algebras, inducing `Spec_X(ψ) : Spec_X(B) ⟶ Spec_X(A)`
(`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom`). A retraction `ρ : B ⟶ 𝒪_X` of the
structure morphism of `B` cuts out a section `X ⟶ Spec_X(B)` of the projection
(`Stacks.RelativeSpec.retractionSection`), and `ψ ≫ ρ` is a retraction of the structure morphism
of `A`. The two sections are compatible: the section of `ρ` followed by `Spec_X(ψ)` is the
section of `ψ ≫ ρ`.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom` and
  `Stacks.RelativeSpec.AlgebraSheaf.comp_right_hom`: a morphism of algebra sheaves commutes with
  the structure morphisms, and composes, on the underlying presheaves of rings.
* `Stacks.RelativeSpec.comp_retraction_structureMap`: `ψ ≫ ρ` retracts the structure morphism of
  the source algebra.
* `Stacks.RelativeSpec.retractionSection_congr`: the section depends only on the retraction, not
  on the proof that it is one.
* `Stacks.RelativeSpec.retractionSection_comp_relativeSpectrumMapOfAlgebraHom`: **the section of a
  retraction, followed by the comparison of relative spectra, is the section of the composite
  retraction.**

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec

/-- **A morphism of algebra sheaves commutes with the structure morphisms, read on the underlying
presheaves of rings.** -/
theorem AlgebraSheaf.hom_comp_right_hom {S : Scheme.{u}} {A B : AlgebraSheaf S} (f : A ⟶ B) :
    A.hom.hom ≫ f.right.hom = B.hom.hom := by
  show (A.hom ≫ f.right).hom = B.hom.hom
  exact congrArg (fun t => t.hom) f.w

/-- On the underlying presheaves of rings, the `right` component of a composite of morphisms of
algebra sheaves is the composite of the `right` components. -/
theorem AlgebraSheaf.comp_right_hom {S : Scheme.{u}} {A B C : AlgebraSheaf S} (f : A ⟶ B)
    (g : B ⟶ C) : f.right.hom ≫ g.right.hom = (f ≫ g).right.hom := rfl

section

variable {s : RelativeSpecSituation.{u}}
  {ρ ρ' : s.algebra.right.obj ⟶ s.base.presheaf}

/-- **The section cut out by a retraction depends only on the retraction**, not on the proof
that it is one. -/
theorem retractionSection_congr (hρ : s.algebra.hom.hom ≫ ρ = 𝟙 s.base.presheaf)
    (hρ' : s.algebra.hom.hom ≫ ρ' = 𝟙 s.base.presheaf) (h : ρ = ρ') :
    retractionSection s ρ hρ = retractionSection s ρ' hρ' := by
  subst h
  rfl

end

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B) (ρ : B.right.obj ⟶ s.base.presheaf)
  (hρ : B.hom.hom ≫ ρ = 𝟙 s.base.presheaf)

include hρ in
/-- **A retraction of the structure morphism of the target algebra, composed with a morphism of
algebras, retracts the structure morphism of the source algebra.** -/
theorem comp_retraction_structureMap :
    s.algebra.hom.hom ≫ ψ.right.hom ≫ ρ = 𝟙 s.base.presheaf :=
  by rw [← Category.assoc, AlgebraSheaf.hom_comp_right_hom ψ, hρ]

/-- **The section of the relative spectrum of `B` cut out by a retraction `ρ`, followed by the
comparison `Spec_X(B) ⟶ Spec_X(A)` of a morphism of algebras `ψ : A ⟶ B`, is the section of the
relative spectrum of `A` cut out by `ψ ≫ ρ`.** -/
theorem retractionSection_comp_relativeSpectrumMapOfAlgebraHom :
    retractionSection (s.withAlgebra B hB) ρ hρ ≫
        relativeSpectrumMapOfAlgebraHom s B hB ψ =
      retractionSection s (ψ.right.hom ≫ ρ) (comp_retraction_structureMap s B ψ ρ hρ) := by
  refine hom_ext_of_pullback_universalRelativeSpecPair _ _ ?_
  refine Eq.trans ?_
    (pullback_universalRelativeSpecPair_pairToHom
      (retractionPair s (ψ.right.hom ≫ ρ) (comp_retraction_structureMap s B ψ ρ hρ))).symm
  refine pullback_universalRelativeSpecPair_eq _ _ ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => retractionSection (s.withAlgebra B hB) ρ hρ ≫ k)
          (relativeSpectrumMapOfAlgebraHom_toBase s B hB ψ)).trans
        (retractionSection_comp_toBase (s.withAlgebra B hB) ρ hρ))
  · intro U _
    have e₁ : relativeSpectrumMapOfAlgebraHom s B hB ψ ⁻¹ᵁ
          ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) =
        (gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1 := by
      rw [← Scheme.Hom.comp_preimage, relativeSpectrumMapOfAlgebraHom_toBase]
    have e₂ : retractionSection (s.withAlgebra B hB) ρ hρ ⁻¹ᵁ
          ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1) =
        (𝟙 s.base) ⁻¹ᵁ U.1 := by
      rw [← Scheme.Hom.comp_preimage, retractionSection_comp_toBase]
    have key : (universalAlgebraMap s).right.app (op U.1) ≫
          ((relativeSpectrumMapOfAlgebraHom s B hB ψ).appLE
              ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)
              ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1) e₁.ge ≫
            (retractionSection (s.withAlgebra B hB) ρ hρ).appLE
              ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1)
              ((𝟙 s.base) ⁻¹ᵁ U.1) e₂.ge) =
        (retractionPair s (ψ.right.hom ≫ ρ)
          (comp_retraction_structureMap s B ψ ρ hρ)).2.right.app (op U.1) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (retractionSection (s.withAlgebra B hB) ρ hρ).appLE
              ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1)
              ((𝟙 s.base) ⁻¹ᵁ U.1) e₂.ge)
            (relativeSpectrumMapOfAlgebraHom_appLE s B hB ψ U e₁.ge)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => ψ.right.hom.app (op U.1) ≫ k)
              (pairToHom_appLE (retractionPair (s.withAlgebra B hB) ρ hρ) U e₂.ge))))
    exact (congrArg (fun k => (universalAlgebraMap s).right.app (op U.1) ≫ k)
        ((retractionSection (s.withAlgebra B hB) ρ hρ).appLE_comp_appLE
          (relativeSpectrumMapOfAlgebraHom s B hB ψ)
          ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)
          ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1)
          ((𝟙 s.base) ⁻¹ᵁ U.1) e₁.ge e₂.ge).symm).trans key

end Stacks.RelativeSpec

end
