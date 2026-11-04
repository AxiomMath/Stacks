module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationKernelInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cotangent complex does not depend on the presentation

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site and let `α : E ⟶ B` be a
family of generators presenting `B` over `A`, so that `A[E] ⟶ B` is locally surjective.  The
naive cotangent complex `NL(α)` of that presentation is the two-term complex `K/K² ⟶ B ⊗ Ω`,
and the canonical presentation `α = id_B` gives `NL_{B/A}`.  This file proves that the
canonical comparison map

`NL(α) ⟶ NL_{B/A}`

is a quasi-isomorphism, so that `NL(α)` and `NL_{B/A}` are canonically isomorphic in the derived
category of `B`-modules.  This is Stacks 08TY.

More generally the chain map induced by any morphism of presentations is a quasi-isomorphism,
and the comparison with the canonical presentation is the case `α₂ = id_B`.

Both complexes are concentrated in degrees `-1` and `0`, so by
`CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel` it is enough that the comparison
induce isomorphisms on the kernel and on the cokernel of the single differential, which is the
left-hand map of the conormal sequence of the presentation.  Those two statements are exactly
the degree `-1` and degree `0` halves of Stacks 08TY proved elsewhere:

* on cokernels, `Stacks.SheafOfModules.isIso_cokernel_map_presentationConormalSequence_f`, both
  cokernels being the sheaf of relative differentials `Ω_{B/A}`;
* on kernels, `Stacks.SheafOfModules.isIso_presentationKernelMap`, the map on kernels being
  locally bijective.

## Main results

* `Stacks.SheafOfModules.quasiIso_presentationNaiveCotangentComplexMap`: the chain map induced
  by a morphism of polynomial presentations is a quasi-isomorphism.
* `Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site`: **Stacks 08TY.**  The
  canonical comparison map `NL(α) ⟶ NL_{B/A}` is a quasi-isomorphism.

## Implementation notes

The terms of `NL(α)` are the terms of the conormal sequence only up to the equalities
`Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne` and
`Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero`, because
`HomologicalComplex.double` reads a degree through a case distinction; so the differential and
the two nonzero components of the chain map are the conjugates by those equalities of the maps
of the conormal sequence.  `CategoryTheory.Limits.isIso_kernel_map_of_eqToHom` and its cokernel
companion absorb that conjugation, which is why the two inputs can be quoted at the spelling
they are proved at rather than transported by hand.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the canonical map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z

namespace Stacks.SheafOfModules


open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  (hα : h ≫ α₂ = α₁)

include hα in
/-- **The chain map of a morphism of presentations is a quasi-isomorphism.**  Both naive
cotangent complexes are concentrated in degrees `-1` and `0`, so it is enough that the induced
maps on the kernel and on the cokernel of the conormal map be isomorphisms; the first is
`Stacks.SheafOfModules.isIso_presentationKernelMap` and the second is
`Stacks.SheafOfModules.isIso_cokernel_map_presentationConormalSequence_f`. -/
@[sga "6 0 4.4" "partial"]
theorem quasiIso_presentationNaiveCotangentComplexMap :
    QuasiIso (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα) := by
  have hk : IsIso (kernel.map
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f
      (presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (conormalSequence_f_naturality.{v, u, w, z} J A B
        (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
        (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
        (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
        (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h))) :=
    isIso_presentationKernelMap.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα
  have hc := isIso_cokernel_map_presentationConormalSequence_f.{v, u, w, z} J A B a E₁ E₂ h
    α₁ α₂ hα
  refine CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel _
    (presentationNaiveCotangentComplex_isZero_X.{v, u, w, z} J A B a E₁ α₁)
    (presentationNaiveCotangentComplex_isZero_X.{v, u, w, z} J A B a E₂ α₂) ?_ ?_
  · exact isIso_kernel_map_of_eqToHom
      (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_X_zero.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplex_X_zero.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplex_d_negOne_zero.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_d_negOne_zero.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplexMap_f_negOne.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (presentationNaiveCotangentComplexMap_f_zero.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      _ _ hk
  · exact isIso_cokernel_map_of_eqToHom
      (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_X_zero.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplex_X_zero.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplex_d_negOne_zero.{v, u, w, z} J A B a E₁ α₁)
      (presentationNaiveCotangentComplex_d_negOne_zero.{v, u, w, z} J A B a E₂ α₂)
      (presentationNaiveCotangentComplexMap_f_negOne.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (presentationNaiveCotangentComplexMap_f_zero.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      _ _ hc

end Stacks.SheafOfModules

/-! ### The canonical comparison map -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- **Stacks 08TY.**  For every polynomial presentation `α : E ⟶ B` of `B` over `A` the
canonical comparison map `NL(α) ⟶ NL_{B/A}` is a quasi-isomorphism, so `NL(α)` and `NL_{B/A}`
are canonically isomorphic in the derived category of `B`-modules: the naive cotangent complex
does not depend on the presentation.

The comparison map is the chain map of the morphism of presentations `α : (E, α) ⟶ (B, id)`, so
this is `Stacks.SheafOfModules.quasiIso_presentationNaiveCotangentComplexMap` at the canonical
presentation. -/
@[stacks 08TY "the canonical isomorphism NL(α) ≅ NL_{B/A} in D(B): the comparison map of a
polynomial presentation is a quasi-isomorphism"]
theorem quasiIso_naiveCotangentComplexComparison_site :
    QuasiIso (naiveCotangentComplexComparison.{v, u, w, z} J A B a E α) :=
  quasiIso_presentationNaiveCotangentComplexMap.{v, u, w, z} J A B a E
    (underlyingPresheaf J B) α α (𝟙 _) (Category.comp_id α)

end Stacks.SheafOfModules

end
