module

public import StacksFrontier.Cotangent.BaseChangeQuasiIso
public import StacksFrontier.Cotangent.ResolutionCotangentDerivedNaturality

/-!
# A morphism of resolutions induces a quasi-isomorphism of cotangent complexes

Let `A → B` be a ring map. For every simplicial polynomial resolution `δ : Q_• ⟶ B` of `B` over
`A` in the sense of [Stacks, Tag 08QI] and every morphism `ψ` from it to the standard resolution
over `B`, the induced map `Ω[Q_•⁄A] ⊗_{Q_•} B ⟶ Ω[P_•⁄A] ⊗_{P_•} B = L_{B/A}` of
alternating-face-map complexes is a quasi-isomorphism. This is the principle of
[Stacks, Remark 08QI] that the cotangent complex is computed by any resolution, in the form
`CommAlgCat.CotangentComputedByEveryResolution`.

## Main results

* `CommAlgCat.cotangentComputedByEveryResolution`: every ring map satisfies
  `CommAlgCat.CotangentComputedByEveryResolution`.

## Implementation notes

Both resolutions are read on the small model of the site of polynomial algebras on at most `κ`
variables, for a bound `κ` containing the variables of every term of `Q_•` and of the standard
resolution. [Stacks, Tag 08PU] in `D(B)` identifies each of their complexes with one and the same
object `Lπ_!(i^*Ω_{𝒪/A})`, and it does so functorially in the resolution
(`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`). So the image of the
induced map in `D(B)` is a composite of two isomorphisms, hence an isomorphism, and the map itself
is a quasi-isomorphism.

## References

* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- A morphism of augmented simplicial algebras over `B`, read back as a morphism of simplicial
algebras. -/
def resolutionOverLeftMap {P P' : SimplicialObject (CommAlgCat.{u} A)}
    {ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    {ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    (ψ : resolutionOver ε ⟶ resolutionOver ε') : P ⟶ P' where
  app n := (ψ.app n).left
  naturality _ _ f := congrArg CommaMorphism.left (ψ.naturality f)

/-- The simplicial algebra map underlying a morphism of augmented simplicial algebras over `B`
commutes with the augmentations. -/
lemma resolutionOverLeftMap_comp {P P' : SimplicialObject (CommAlgCat.{u} A)}
    {ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    {ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    (ψ : resolutionOver ε ⟶ resolutionOver ε') : resolutionOverLeftMap ψ ≫ ε' = ε := by
  ext n : 1
  exact Over.w (ψ.app n)

/-- A morphism of augmented simplicial algebras over `B` is recovered by `resolutionOverMap` from
its underlying map of simplicial algebras. -/
lemma resolutionOverMap_resolutionOverLeftMap {P P' : SimplicialObject (CommAlgCat.{u} A)}
    {ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    {ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B}
    (ψ : resolutionOver ε ⟶ resolutionOver ε') :
    resolutionOverMap ε ε' (resolutionOverLeftMap ψ) (resolutionOverLeftMap_comp ψ) = ψ := by
  ext n : 2
  rfl

/-- A bound on the number of variables of every term of a degreewise polynomial simplicial
algebra and of the standard resolution. -/
def resolutionVarBound {P : SimplicialObject (CommAlgCat.{u} A)}
    (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) : Cardinal.{u} :=
  max (standardResolutionVarCardinal A B) (⨆ n, Cardinal.mk (hP n).choose)

/-- Every term of a degreewise polynomial simplicial algebra is a polynomial algebra on at most
`resolutionVarBound hP` variables. -/
lemma isPolynomialAlgebraBelow_resolutionVarBound {P : SimplicialObject (CommAlgCat.{u} A)}
    (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A (resolutionVarBound (B := B) hP) (P.obj n) :=
  ⟨(hP n).choose, (le_ciSup Cardinal.bddAbove_of_small n).trans (le_max_right _ _),
    (hP n).choose_spec⟩

/-- **Remark 08QI: every resolution computes the cotangent complex.** For every simplicial
polynomial resolution `δ : Q_• ⟶ B` of `B` over `A` and every morphism `ψ` from it to the
standard resolution over `B`, the induced map of complexes `Ω[−⁄A] ⊗ B` is a
quasi-isomorphism. -/
theorem cotangentComputedByEveryResolution (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    CotangentComputedByEveryResolution A B := by
  intro Q δ hQ hres ψ
  let κ := resolutionVarBound (B := B) hQ
  have hQκ := isPolynomialAlgebraBelow_resolutionVarBound (B := B) hQ
  have hSκ := standardResolution_isPolynomialAlgebraBelow_of_le A B κ (le_max_left _ _)
  have hnat := smallResolutionCotangentDerivedLowerShriekIso_naturality δ
    (standardResolution.{u, u} A B).hom κ hQκ hSκ (resolutionOverLeftMap ψ)
    (resolutionOverLeftMap_comp ψ) hres.trivialKanFibration
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration
  have hiso : IsIso (DerivedCategory.Q.map (resolutionCotangentComplexMap δ
      (standardResolution.{u, u} A B).hom (resolutionOverLeftMap ψ)
      (resolutionOverLeftMap_comp ψ))) := by
    rw [← Iso.eq_comp_inv] at hnat
    rw [hnat]
    infer_instance
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, resolutionCotangentComplexMap,
    resolutionOverMap_resolutionOverLeftMap] at hiso
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hiso

end CommAlgCat

end
