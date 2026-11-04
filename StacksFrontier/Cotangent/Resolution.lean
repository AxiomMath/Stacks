module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.SimplicialAbelianGroup

/-!
# Resolutions by polynomial simplicial algebras

An augmentation from a simplicial commutative `A`-algebra to an `A`-algebra `B` is a resolution
when every algebra in the simplicial object is a polynomial algebra over `A` and the underlying
augmentation of simplicial sets is a trivial Kan fibration. For a degreewise polynomial
simplicial algebra whose augmentation is surjective in every degree, being a resolution is
equivalent both to the associated complex being quasi-isomorphic to the target and to the
underlying augmentation of simplicial sets being a homotopy equivalence.

## Main definitions

* `CommAlgCat.IsPolynomialAlgebra`: an `A`-algebra is isomorphic to a multivariate polynomial
  algebra over `A`.
* `CommAlgCat.IsResolution`: an augmentation of a simplicial `A`-algebra is a resolution of its
  target over `A`.

## Main results

* `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`: the three equivalent criteria for
  a simplicial polynomial resolution.

## Implementation notes

A polynomial algebra is expressed by the existence of an `A`-algebra equivalence with
`MvPolynomial ι A`; the indexing type is allowed to be arbitrary in the universe of the
algebras. The augmentation is represented as a morphism to the constant simplicial algebra on
`B`. Whiskering it with the forgetful functor gives exactly the underlying morphism of
simplicial sets to which `SSet.trivialKanFibrations` applies. The structure presentation of
`IsResolution` supplies its two defining conditions as projections for downstream use.

The complex associated to a simplicial algebra is the alternating-face complex of its underlying
simplicial abelian group. The three-way equivalence is expressed by `List.TFAE`, retaining the
numbering of the source.

## References

* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

universe u v

namespace CommAlgCat

/-- A commutative `A`-algebra is a polynomial algebra over `A` if it is isomorphic, as an
`A`-algebra, to a multivariate polynomial algebra over `A`. -/
abbrev IsPolynomialAlgebra (A : Type u) [CommRing A] (P : CommAlgCat.{v} A) : Prop :=
  ∃ ι : Type v, Nonempty (MvPolynomial ι A ≃ₐ[A] P)

/-- **Stacks Project, Tag 08QI.**

An augmentation `ε : P• ⟶ B` of a simplicial commutative `A`-algebra is a resolution of `B` over
`A` if every `Pₙ` is a polynomial algebra over `A` and the underlying augmentation of simplicial
sets is a trivial Kan fibration. -/
@[stacks 08QI "resolution"]
structure IsResolution (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (P : SimplicialObject (CommAlgCat.{v} A))
    (ε : P ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B)) : Prop where
  /-- Every term of the simplicial algebra is a polynomial algebra over `A`. -/
  isPolynomialAlgebra : ∀ n : SimplexCategoryᵒᵖ, IsPolynomialAlgebra A (P.obj n)
  /-- The augmentation of the underlying simplicial sets is a trivial Kan fibration. -/
  trivialKanFibration :
    SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{v} A)))

/-- **Stacks Project, Tag 08QI.**

For an augmentation `ε : P• ⟶ B` which is degreewise surjective and whose terms are polynomial
`A`-algebras, the following are equivalent: `ε` is a resolution, the induced map of associated
complexes is a quasi-isomorphism, and the underlying map of simplicial sets is a homotopy
equivalence. -/
@[stacks 08QI "resolution_criteria"]
lemma isResolution_quasiIso_homotopyEquivalence_tfae
    (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (P : SimplicialObject (CommAlgCat.{v} A))
    (ε : P ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B))
    (hP : ∀ n : SimplexCategoryᵒᵖ, IsPolynomialAlgebra A (P.obj n))
    (hε : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (ε.app n).hom) :
    List.TFAE
      [IsResolution A B P ε,
       QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{v}).map
         (Functor.whiskerRight ε
           (forget₂ (CommAlgCat.{v} A) (AlgCat.{v} A) ⋙
            forget₂ (AlgCat.{v} A) (ModuleCat.{v} A) ⋙
            forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}))),
       SimplicialObject.homotopyEquivalences (Type v)
         (Functor.whiskerRight ε (forget (CommAlgCat.{v} A)))] := by
  classical
  let f := Functor.whiskerRight ε
    (forget₂ (CommAlgCat.{v} A) (AlgCat.{v} A) ⋙
      forget₂ (AlgCat.{v} A) (ModuleCat.{v} A) ⋙
      forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v})
  have hforget :
      Functor.whiskerRight f (forget AddCommGrpCat.{v}) =
        Functor.whiskerRight ε (forget (CommAlgCat.{v} A)) := by
    ext n x
    rfl
  tfae_have 1 → 3 := by
    rintro ⟨_, h⟩
    obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := SSet.trivialKanFibrations_isHomotopyEquiv _ h
    exact ⟨g, Relation.EqvGen.rel _ _ ⟨h₁.toSimplicialObjectHomotopy⟩,
      Relation.EqvGen.rel _ _ ⟨h₂.toSimplicialObjectHomotopy⟩⟩
  tfae_have 3 → 2 := fun h =>
    AlgebraicTopology.quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget
      f (hforget.symm ▸ h)
  tfae_have 2 → 1 := fun _ =>
    ⟨hP, hforget ▸
      (SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso f
        fun n => by simpa [f] using hε n)⟩
  tfae_finish

end CommAlgCat

end
