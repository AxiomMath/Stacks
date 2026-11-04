module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentSquare
public import StacksFrontier.Topology.Sheaves.Sheaf.PolynomialAlgebra
import StacksCore.Tactic.StacksAttribute

/-!
# The naive cotangent complex does not depend on the presentation

Let `𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on a topological space and let
`α : ℰ ⟶ ℬ` present `ℬ` as a quotient of the polynomial algebra `𝒜[ℰ]`. The canonical
comparison `𝖭𝖫(α) ⟶ 𝖭𝖫_{ℬ/𝒜}` is a quasi-isomorphism, so a different presentation gives the
same object of `D(ℬ)`.

## Main definitions

* `Stacks.SheafOfModules.presentationNaiveCotangentDerivedIso`: the isomorphism
  `𝖭𝖫(α) ≅ 𝖭𝖫_{ℬ/𝒜}` in `D(ℬ)`.

## References

* [Stacks Project, Tag 08TG](https://stacks.math.columbia.edu/tag/08TG)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {Z : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
  (a : A ⟶ B) (E : Z.Presheaf (Type u))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Z) B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
    (presentation (Opens.grothendieckTopology Z) A B a E α).hom]

/-- For a presentation `α : ℰ ⟶ ℬ` of `ℬ` as a quotient of a polynomial algebra over `𝒜`, the
isomorphism `𝖭𝖫(α) ≅ 𝖭𝖫_{ℬ/𝒜}` in `D(ℬ)` given by the comparison quasi-isomorphism
`𝖭𝖫(α) ⟶ 𝖭𝖫_{ℬ/𝒜}`. -/
@[stacks 08TL "the isomorphism in D(ℬ)", stacks 08TG "the presentation-independence assertion"]
def presentationNaiveCotangentDerivedIso :
    DerivedCategory.Q.obj (presentationNaiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology Z) A B a E α) ≅
      DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology Z) A B a) :=
  haveI : IsIso (DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u}
      (Opens.grothendieckTopology Z) A B a E α)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_naiveCotangentComplexComparison A B a E α)
  asIso (DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u}
    (Opens.grothendieckTopology Z) A B a E α))

end Stacks.SheafOfModules

/-! ### The constructions of the section -/

add_to_stacks 08TG "the polynomial algebra sheaf 𝒜[ℰ] of the section's notation"
  Stacks.Sheaves.PolynomialAlgebra.polynomialAlgebraSheaf

add_to_stacks 08TG "the canonical surjection 𝒜[ℬ] ⟶ ℬ, [b] ↦ b"
  Stacks.Sheaves.PolynomialAlgebra.canonicalPolynomialPresentation

add_to_stacks 08TG "surjectivity of 𝒜[ℬ] ⟶ ℬ"
  Stacks.Sheaves.PolynomialAlgebra.canonicalPolynomialPresentation_surjective

add_to_stacks 08TG "the naive cotangent complex 𝖭𝖫_{ℬ/𝒜} of the section's definition, with \
ℐ/ℐ² in degree -1 and Ω_{𝒜[ℬ]/𝒜} ⊗ ℬ in degree 0"
  Stacks.SheafOfModules.naiveCotangentComplex

add_to_stacks 08TG "the complex 𝖭𝖫(α) attached to a presentation α : ℰ ⟶ ℬ"
  Stacks.SheafOfModules.presentationNaiveCotangentComplex

add_to_stacks 08TG "the canonical ℬ-linear map of complexes 𝖭𝖫_{ℬ/𝒜} ⟶ 𝖭𝖫_{ℬ'/𝒜'} attached to \
a commutative square of sheaves of rings"
  Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare

add_to_stacks 08TG "compatibility of that canonical map of complexes with compositions"
  Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare_comp

add_to_stacks 08TG "the canonical comparison 𝖭𝖫(α) ⟶ 𝖭𝖫_{ℬ/𝒜} and its quasi-isomorphy"
  Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison

add_to_stacks 08TG "compatibility with inverse images, f⁻¹𝖭𝖫_{ℬ/𝒜} ≅ 𝖭𝖫_{f⁻¹ℬ/f⁻¹𝒜}"
  Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso

end
