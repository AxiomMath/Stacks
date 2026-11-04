module

public import StacksFrontier.Homology.KFlat.BifunctorTransport

/-!
# The derived tensor product and an exact monoidal functor

Let `A` and `A'` be abelian monoidal categories whose tensor products are additive in each
variable and admit total tensor complexes, and let `G : A ⥤ A'` be **exact** and **strong
monoidal**. Suppose `G` preserves the antidiagonal coproducts occurring in a total complex and
carries (left) K-flat complexes to (left) K-flat complexes. Then

  `G(K ⊗^L_A L) ≅ G K ⊗^L_{A'} G L`

as an isomorphism of bifunctors on the unbounded derived categories: on **arbitrary** objects
`K`, `L` of `D(A)`, and **natural** in both of them.

This is the comparison of the derived tensor product with an exact restriction or stalk
functor, in the form in which such a functor supplies it: a restriction functor and a stalk
functor are each exact, colimit-preserving and strong monoidal, and the underived comparison
`G(M ⊗ N) ≅ G M ⊗ G N` is their monoidal structure constraint — Stacks 01CB for the stalk and
Stacks 01CD for a restriction. All that the statement below asks beyond that is preservation of
K-flatness, which is Stacks 06YB for a stalk and Stacks 06YC for a pullback.

## Main definitions

* `CochainComplex.KFlatBifunctor.monoidalDerivedTransportIso`: the isomorphism of bifunctors
  on the derived categories.

## Implementation notes

Everything is an instance of `CochainComplex.KFlatBifunctor.derivedTransportIso`, the
bifunctor-generic statement: the degreewise comparison `ε` is the inverse of the monoidality
constraint `CategoryTheory.Functor.Monoidal.μIso`, i.e. the comparison
`CategoryTheory.Functor.OplaxMonoidal.δ`, and its two naturality squares are
`CategoryTheory.Functor.OplaxMonoidal.δ_natural_left` and `δ_natural_right`.

The tensor products of `A` and `A'` are their `MonoidalCategory` instances, read as the
bifunctors `CategoryTheory.MonoidalCategory.curriedTensor`, which is the spelling
`CochainComplex.KFlatMonoidal` uses and in which the derived tensor product of
[Stacks, Tag 06YU] and the monoidal structure of [Stacks, Tag 0FPT] are compared.

## References

* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Lemma 17.16.3 (Tag 01CD)](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.KFlatBifunctor

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  [MonoidalCategory A] [MonoidalCategory A']
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A) (ComplexShape.up ℤ)]
  [(curriedTensor A').Additive] [∀ X : A', ((curriedTensor A').obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor A') (ComplexShape.up ℤ)]
  (G : A ⥤ A') [G.Additive] [G.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G]
  [∀ (K L : CochainComplex A ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G
      (((((curriedTensor A)).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory A']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A')).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A'))]
  [(kFlatQ (curriedTensor A')).IsLocalization (kFlatQuasiIso (curriedTensor A'))]

/-- The degreewise comparison supplied by a strong monoidal functor:
`G(a ⊗ b) ≅ G a ⊗ G b`. -/
abbrev monoidalTransportEps (a b : A) :
    G.obj (((curriedTensor A).obj a).obj b) ≅
      ((curriedTensor A').obj (G.obj a)).obj (G.obj b) :=
  (Functor.Monoidal.μIso G a b).symm

/-- **The derived tensor product commutes with an exact strong monoidal functor preserving
K-flatness**, as an isomorphism of bifunctors on the derived categories:

`G(K ⊗^L_A L) ≅ G K ⊗^L_{A'} G L`

on arbitrary objects of `D(A)`, natural in both variables. -/
def monoidalDerivedTransportIso
    (hKFlatLeft : ∀ K : CochainComplex A ℤ, KFlatLeft (curriedTensor A) K →
      KFlatLeft (curriedTensor A') ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hKFlat : ∀ L : CochainComplex A ℤ, KFlat (curriedTensor A) L →
      KFlat (curriedTensor A') ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    derivedTransportSource (curriedTensor A) G ≅
      derivedTransportTarget (curriedTensor A') G G :=
  derivedTransportIso (curriedTensor A) (curriedTensor A') G G G
    (monoidalTransportEps G)
    (fun f b => (Functor.OplaxMonoidal.δ_natural_left G f b).symm)
    (fun a {_b _b'} g => (Functor.OplaxMonoidal.δ_natural_right G a g).symm)
    hKFlatLeft hKFlat

end CochainComplex.KFlatBifunctor

end
