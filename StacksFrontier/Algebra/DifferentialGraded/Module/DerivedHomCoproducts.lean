module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-! # Derived Hom out of a bimodule commutes with direct sums

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. The functor `RHom(N, -) : D(B, d) ⥤ D(A, d)` is a
right adjoint, so there is no formal reason for it to preserve a colimit. It does preserve direct
sums as soon as the derived tensor product `- ⊗_A^𝐋 N` carries the regular module `A` to a
compact object of `D(B, d)`, and this file carries out that deduction.

Two inputs are needed, and only one of them is about the bimodule.

* The algebra `A`, viewed in `D(A, d)`, is a weak generator: an object receiving only zero maps
  from the shifts `A[k]` is zero. This is proved here, by dévissage.
* `A` is a compact object of `D(A, d)`, and `A ⊗_A^𝐋 N` is a compact object of `D(B, d)`. These
  are hypotheses below.

## Main results

* `DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`: the image of the
  regular module in `D(A, d)` is a weak generator of `D(A, d)`.
* `DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor`:
  `RHom(N, -)` preserves `Type u`-indexed direct sums when `A` and `A ⊗_A^𝐋 N` are compact.

## Implementation notes

*The weak generator is dévissage, not a computation of morphism groups.* To see that an object
`K` with no nonzero map from a shift of `A` vanishes, consider the property
`T X := "every morphism X ⟶ K[n] vanishes, for every n"`, that is, membership of the left
orthogonal of the shifts of `K`. The left orthogonal of a shift-stable property of objects is a
triangulated subcategory (`CategoryTheory.ObjectProperty.leftOrthogonal.IsTriangulated`), which
is the two-out-of-three clause; it is closed under direct sums because a morphism out of a direct
sum vanishes as soon as all its components do; and it contains every `A[k]` precisely by the
hypothesis on `K`, the right orthogonal of a shift-stable property being again shift-stable. So
Tag 0FQE — `DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts` —
gives `T K`, and taking the morphism `𝟙 K` shows `K` is zero.

*What the compactness hypotheses are.* The generic engine
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` asks for a compact
weak generator `E` of the target of the right adjoint whose image under the left adjoint is again
compact. Here `E` is the image of the regular module in `D(A, d)`, so the first hypothesis is the
compactness of `A` in `D(A, d)` and the second is the compactness of `A ⊗_A^𝐋 N` in `D(B, d)`.

The second is the hypothesis "`N` defines a compact object of `D(B, d)`" of
[Stacks, Tag 09R9](1): the unit of the derived tensor product identifies `A ⊗_A^𝐋 N` with the
class of `N`, and compactness is invariant under isomorphism
(`CategoryTheory.isCompactObject_of_iso`), so the two readings of that hypothesis agree. That
unit isomorphism is `DifferentialGraded.Bimodule.derivedTensorRegularIso`.

The first hypothesis is not one of the hypotheses of Tag 09R9. It is a property of `D(A, d)`
alone, true of every differential graded algebra: it is the instance
`DifferentialGradedModule.isCompactObject_q_regularModule`.

*Two pretriangulated structures on `K(A, d)`.* The adjunction of Tag 09LT is imported through
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedCategoryHom.lean`, which brings the
universe-polymorphic `DifferentialGradedModule.instPretriangulatedHomotopyCategory` — whose
distinguished triangles are the cone triangles — into scope beside
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished triangles
come from admissible short exact sequences. The two agree only by Tag 09KH, which is not
formalized, so they are distinct data; everything about `D(A, d)` in this chapter is stated
against the primed one, and that is the one given priority below, as in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedColimits.lean`.

## References

* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for the adjunction,
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for the dévissage,
  [Tag 09QI](https://stacks.math.columbia.edu/tag/09QI) for the direct sums of `D(A, d)`,
  [Tag 07LS](https://stacks.math.columbia.edu/tag/07LS) for compactness, and
  [Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ) for the engine.
* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) is the result that
  consumes this one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **The algebra generates its derived category.** Let `(A, d)` be a differential graded algebra
over a commutative ring `R`. The image of the regular module `A` in `D(A, d)` is a weak
generator: an object of `D(A, d)` receiving only zero morphisms from the shifts `A[k]` is zero. -/
theorem isWeakTriangulatedGenerator_q_regularModule (A : DifferentialGradedAlgebra R) :
    ObjectProperty.IsWeakTriangulatedGenerator (ObjectProperty.singleton
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) := by
  set E := (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)
  intro K hK
  set P : ObjectProperty (derivedCategory' A) := (ObjectProperty.singleton K).shiftClosure ℤ
  have hPK : P K :=
    ⟨K, 0, ((shiftFunctorZero (derivedCategory' A) ℤ).app K).symm,
      (ObjectProperty.singleton_iff K K).2 rfl⟩
  have hshiftK : ∀ n : ℤ, ((ObjectProperty.singleton E).shiftClosure ℤ).rightOrthogonal
      ((CategoryTheory.shiftFunctor (derivedCategory' A) n).obj K) :=
    fun n => ((ObjectProperty.singleton E).shiftClosure ℤ).rightOrthogonal.le_shift n _ hK
  have key : ∀ X, P.leftOrthogonal X := by
    refine property_of_coproducts_of_two_out_of_three_of_shifts A P.leftOrthogonal
      (fun Kf hKf => ?_) (fun Δ hΔ => ⟨?_, ?_, ?_⟩) (fun k => ?_)
    · exact fun Y f hY => Limits.Sigma.hom_ext _ _ fun i => by
        rw [Limits.comp_zero]; exact hKf i _ hY
    · exact fun h₁ h₂ => P.leftOrthogonal.ext_of_isTriangulatedClosed₃ Δ hΔ h₁ h₂
    · exact fun h₁ h₃ => P.leftOrthogonal.ext_of_isTriangulatedClosed₂ Δ hΔ h₁ h₃
    · exact fun h₂ h₃ => P.leftOrthogonal.ext_of_isTriangulatedClosed₁ Δ hΔ h₂ h₃
    · intro Y f hY
      obtain ⟨K', n, e, ⟨⟩⟩ := hY
      rw [← cancel_mono e.hom, Limits.zero_comp]
      exact hshiftK n (f ≫ e.hom) ⟨E, k, Iso.refl _, (ObjectProperty.singleton_iff E E).2 rfl⟩
  exact (IsZero.iff_id_eq_zero K).2 (key K (𝟙 K) hPK)

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **Derived Hom out of a differential graded bimodule commutes with direct sums.** Let `(A, d)`
and `(B, d)` be differential graded algebras over a commutative ring `R`, let `N` be a
differential graded `(A, B)`-bimodule, and suppose that the regular module `A` is a compact object
of `D(A, d)` and that `A ⊗_A^𝐋 N` is a compact object of `D(B, d)`. Then
`RHom(N, -) : D(B, d) ⥤ D(A, d)` preserves direct sums indexed by any type of the universe in
which compactness is tested. -/
theorem preservesColimitsOfShape_discrete_derivedHomFunctor (N : Bimodule A B)
    [IsCompactObject.{u}
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))]
    [IsCompactObject.{u} ((derivedTensorFunctor N).obj
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))] :
    ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (derivedHomData A B N.rightModule N.leftAction).functor := by
  have adj := derivedTensorFunctor_adj_derivedHomFunctor N
  have : (derivedHomData A B N.rightModule N.leftAction).functor.Additive :=
    adj.right_adjoint_additive
  exact preservesCoproducts_of_isCompactObject_map adj _
    (isWeakTriangulatedGenerator_q_regularModule A) ‹_› ‹_›

end DifferentialGraded.Bimodule

end
