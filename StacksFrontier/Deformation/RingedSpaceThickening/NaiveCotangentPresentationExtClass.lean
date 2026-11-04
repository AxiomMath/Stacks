module

public import StacksFrontier.Algebra.Homology.DoubleMappingConeNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble

/-!
# A morphism of presentations carries the class of a conormal homomorphism

Let `α₁ : ℰ₁ ⟶ ℬ` and `α₂ : ℰ₂ ⟶ ℬ` be two polynomial presentations of a sheaf of commutative
rings `ℬ` over `𝒜`, and let `h : ℰ₁ ⟶ ℰ₂` be a morphism of families of generators, that is one
with `h ≫ α₂ = α₁`. It induces a map `𝒥₁/𝒥₁² ⟶ 𝒥₂/𝒥₂²` of conormal sheaves and a chain map
`𝖭𝖫(α₁) ⟶ 𝖭𝖫(α₂)`, and this file proves that the two are compatible with the classes that
homomorphisms out of the conormal sheaves determine in `Ext¹(𝖭𝖫(α), 𝒢)`: the class of the
pullback of `ξ₂ : 𝒥₂/𝒥₂² ⟶ 𝒢` is the class of `ξ₂`, read through the chain map.

## Main results

* `Stacks.SheafOfModules.presentationConormalExtClass_eq`: the compatibility, for the two-term
  structures `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofDoubleNegOne` of
  the two naive cotangent complexes.

## Implementation notes

The content is `CochainComplex.doubleProjQ_naturality`, the naturality of the projection of a
two-term complex onto the shift of its degree `-1` term, applied to the chain map
`Stacks.SheafOfModules.presentationNaiveCotangentComplexMap`. That chain map is built with
`HomologicalComplex.mkHomFromDouble`, and its two components are read off by
`Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne` and
`...presentationNaiveCotangentComplexMap_f_zero`, which spell the identifications of the two
terms as `eqToHom` of the equations
`Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne` and `..._X_zero` where
`CochainComplex.doubleProjQ_naturality` asks for `HomologicalComplex.doubleXIso₀` and
`HomologicalComplex.doubleXIso₁`. The two `have`s below identify the two spellings, exactly as
the proofs of those two lemmas do.

This statement is kept at a general site rather than being proved where it is used, over the
opens of a topological space: the conormal sheaf of a presentation is reached there both as
`Stacks.Sites.Conormal.conormalSheaf` and as the degree `-1` term of the conormal sequence, and
over a ringed space the unifier does not get from one spelling to the other within a
two-million heartbeat budget, while at a general site it does. A consumer therefore instantiates
this statement rather than reproving it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.RingedSpaceThickening (NaiveCotangentTwoTerm)
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe t v u w z

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E₁ E₂ : Functor Cᵒᵖ (Type w))
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max w u v z} (ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v z} (ringSheaf B))

/-- **A morphism of presentations carries the class of a conormal homomorphism to the class of
its pullback.** For `ξ₂ : 𝒥₂/𝒥₂² ⟶ 𝒢` and its pullback `ξ₁` along the map of conormal sheaves
induced by `h : ℰ₁ ⟶ ℰ₂`, the class of `ξ₁` in `Ext¹(𝖭𝖫(α₁), 𝒢)` is the class of `ξ₂` read
through the chain map `𝖭𝖫(α₁) ⟶ 𝖭𝖫(α₂)`. -/
theorem presentationConormalExtClass_eq (h : E₁ ⟶ E₂) (hα : h ≫ α₂ = α₁)
    (ξ₁ : Stacks.Sites.Conormal.conormalSheaf.{v, u, w, z} J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁) B (presentation J A B a E₁ α₁) ⟶ G)
    (ξ₂ : Stacks.Sites.Conormal.conormalSheaf.{v, u, w, z} J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂) B (presentation J A B a E₂ α₂) ⟶ G)
    (hξ : Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
        (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) ≫ ξ₂ = ξ₁) :
    (NaiveCotangentTwoTerm.ofDoubleNegOne
          (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f).conormalExtClass G ξ₁ =
      DerivedCategory.Q.map (presentationNaiveCotangentComplexMap.{v, u, w, z}
          J A E₁ E₂ h B a α₁ α₂ hα) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne
          (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f).conormalExtClass G ξ₂ := by
  have e₀ : ∀ (E : Functor Cᵒᵖ (Type w))
      (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
      [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom],
      HomologicalComplex.doubleXIso₀ (presentationConormalSequence.{v, u, w, z} J A B a E α).f
        ComplexShape.upIntRelNegOneZero =
      eqToIso (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E α) := by
    intro E α _
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  have e₁ : ∀ (E : Functor Cᵒᵖ (Type w))
      (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
      [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom],
      HomologicalComplex.doubleXIso₁ (presentationConormalSequence.{v, u, w, z} J A B a E α).f
        ComplexShape.upIntRelNegOneZero (by decide) =
      eqToIso (presentationNaiveCotangentComplex_X_zero.{v, u, w, z} J A B a E α) := by
    intro E α _
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  have hproj := CochainComplex.doubleProjQ_naturality
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f
    (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f
    ComplexShape.upIntRelNegOneZero (by decide)
    (Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
      (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
      (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα))
    (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
    (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
    (by rw [presentationNaiveCotangentComplexMap_f_negOne, e₀ E₁ α₁, e₀ E₂ α₂]; rfl)
    (by rw [presentationNaiveCotangentComplexMap_f_zero, e₁ E₁ α₁, e₁ E₂ α₂]; rfl)
  have hmc : ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{max w u v z} (ringSheaf B)) 0).map
          (Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
            (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
            (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
            (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
            (freeAlgebraMap J A E₁ E₂ h)
            (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) ≫ ξ₂))⟦(1 : ℤ)⟧' =
      ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{max w u v z} (ringSheaf B)) 0).map
          (Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
            (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
            (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
            (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
            (freeAlgebraMap J A E₁ E₂ h)
            (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)))⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{max w u v z} (ringSheaf B)) 0).map ξ₂)⟦(1 : ℤ)⟧' :=
    (congrArg (fun m ↦ (shiftFunctor (DerivedCategory
          (_root_.SheafOfModules.{max w u v z} (ringSheaf B))) (1 : ℤ)).map m)
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{max w u v z} (ringSheaf B)) 0).map_comp _ ξ₂)).trans
      ((shiftFunctor (DerivedCategory
        (_root_.SheafOfModules.{max w u v z} (ringSheaf B))) (1 : ℤ)).map_comp _ _)
  rw [← hξ]
  simp only [NaiveCotangentTwoTerm.conormalExtClass, NaiveCotangentTwoTerm.ofDoubleNegOne,
    NaiveCotangentTwoTerm.ofDouble_proj]
  refine Eq.trans (congrArg (fun m ↦ CochainComplex.doubleProjQ
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f
    ComplexShape.upIntRelNegOneZero ≫ m) hmc) ?_
  refine Eq.trans (assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ ((DerivedCategory.singleFunctor
    (_root_.SheafOfModules.{max w u v z} (ringSheaf B)) 0).map ξ₂)⟦(1 : ℤ)⟧')
    hproj.symm) ?_
  exact assoc _ _ _

end Stacks.SheafOfModules

end
