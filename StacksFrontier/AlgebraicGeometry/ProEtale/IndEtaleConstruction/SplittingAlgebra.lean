module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.Presentation

/-!
# The algebra `T(A)` and the sequence obtained by iterating it

For a commutative ring `A`, let `T(A)` be the tensor product over `A` of all the algebras
presented by the elements of `StandardEtalePresentation A`, that is, of all faithfully flat
square étale presentations over `A`. It is realised here concretely as a single polynomial
quotient: one copy of the variables for every presentation, modulo all of their relations.

Every faithfully flat étale `A`-algebra maps to `T(A)`, since it is isomorphic to the algebra
presented by one of the elements of `StandardEtalePresentation A`, and each of those maps to the
tensor product. Iterating `T` gives the sequence `A → T(A) → T²(A) → ⋯` whose colimit is the
faithfully flat ind-étale algebra over which every faithfully flat étale cover splits.

## Main definitions

* `AlgebraicGeometry.ProEtale.splittingAlgebra`, the algebra `T(A)`
* `AlgebraicGeometry.ProEtale.iteratedSplittingDiagram`, the sequence `A → T(A) → T²(A) → ⋯`
* `AlgebraicGeometry.ProEtale.iteratedSplittingColimit`, its colimit

## Main results

* `AlgebraicGeometry.ProEtale.etale_faithfullyFlat_maps_to_splittingAlgebra`

## Implementation notes

Writing `T(A)` as one polynomial quotient rather than as a filtered colimit of finite tensor
products makes it a definition rather than a choice: the construction depends on nothing but `A`.
That it *is* the filtered colimit of the finite tensor products is the content of
`AlgebraicGeometry.ProEtale.finiteStageColimit`.
-/

open CategoryTheory CategoryTheory.Limits MvPolynomial

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- A relation belonging to one of the standard étale presentations, regarded as a polynomial in
the disjoint union of all their variables. -/
noncomputable def splittingRelation {A : Type u} [CommRing A]
    (p : StandardEtalePresentation A) (i : Fin p.variableCount) :
    MvPolynomial (Σ p : StandardEtalePresentation A, Fin p.variableCount) A :=
  rename (fun j ↦ ⟨p, j⟩) (p.relations i)

/-- The algebra `T(A)`. This quotient is the tensor product of all the presented algebras in
`S(A)`, equivalently the filtered colimit of their finite tensor products. -/
abbrev splittingAlgebra (A : Type u) [CommRing A] :=
  MvPolynomial (Σ p : StandardEtalePresentation A, Fin p.variableCount) A ⧸
    Ideal.span (Set.range fun i : Σ p : StandardEtalePresentation A,
      Fin p.variableCount ↦ splittingRelation i.1 i.2)

/-- `T(A)`, regarded as a bundled commutative ring. -/
noncomputable def splittingRing (A : CommRingCat.{u}) : CommRingCat.{u} :=
  CommRingCat.of (splittingAlgebra A)

/-- The canonical map `A → T(A)`. -/
noncomputable def toSplittingRing (A : CommRingCat.{u}) : A ⟶ splittingRing A :=
  CommRingCat.ofHom (algebraMap A (splittingAlgebra A))

/-- The sequence `A, T(A), T²(A), …`. -/
noncomputable def iteratedSplittingRing (A : CommRingCat.{u}) : ℕ → CommRingCat.{u}
  | 0 => A
  | n + 1 => splittingRing (iteratedSplittingRing A n)

/-- A transition map in the sequence of iterated splitting rings. -/
noncomputable def iteratedSplittingMap (A : CommRingCat.{u}) (n : ℕ) :
    iteratedSplittingRing A n ⟶ iteratedSplittingRing A (n + 1) :=
  toSplittingRing (iteratedSplittingRing A n)

/-- The sequential diagram formed by iterating `T`. -/
noncomputable def iteratedSplittingDiagram (A : CommRingCat.{u}) :
    ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (iteratedSplittingMap A)

/-- The colimit of `A → T(A) → T²(A) → ⋯`. -/
noncomputable def iteratedSplittingColimit (A : CommRingCat.{u}) : CommRingCat.{u} :=
  colimit (iteratedSplittingDiagram A)

/-- The coprojection of the algebra presented by `p` into `T(A)`. -/
noncomputable def presentationMapToSplittingAlgebra {A : Type u} [CommRing A]
    (p : StandardEtalePresentation A) :
    presentedAlgebra A p.relations →ₐ[A] splittingAlgebra A :=
  Ideal.quotientMapₐ _ (rename fun j ↦ ⟨p, j⟩) <| Ideal.span_le.mpr <| by
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨⟨p, i⟩, rfl⟩

/-- Every faithfully flat étale `A`-algebra maps to `T(A)`. -/
lemma etale_faithfullyFlat_maps_to_splittingAlgebra {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (he : Algebra.Etale A B) (hf : (algebraMap A B).FaithfullyFlat) :
    Nonempty (B →ₐ[A] splittingAlgebra A) := by
  obtain ⟨p, ⟨e⟩⟩ := exists_standardEtalePresentation_of_etale_faithfullyFlat he hf
  exact ⟨(presentationMapToSplittingAlgebra p).comp e.symm.toAlgHom⟩

end AlgebraicGeometry.ProEtale

end
