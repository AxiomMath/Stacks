module

public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompactGeneral
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompactUniverse
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceExampleEquivalence

/-! # The regular module is compact at every index universe, at independent universes

Let `(A, d)` be a differential graded algebra over a commutative ring `R : Type u` whose carrier
lies in a universe `v` of its own, and read the derived category `D(A, d)` in the pretriangulated
structure whose distinguished triangles are the cone triangles. The image of the regular module in
`D(A, d)` is `IsCompactObject.{w}` for an arbitrary universe `w`: it is compact when tested against
families indexed by a type in any universe, not only in `Type v` as in
`DifferentialGradedModule.General.isCompactObject_q_regularModule`. This is hypothesis (1) of
[Stacks, Tag 09LZ] for the regular module.

## Main results

* `DifferentialGradedModule.General.exists_hom_q_regularModule_ne_zero_of_not_isZero`: a nonzero
  object of `D(A, d)` receives a nonzero morphism from some shift of the regular module.
* `DifferentialGradedModule.General.small_nonzero_index_of_isColimitCofan`: in a colimit cofan of
  `D(A, d)` indexed by an arbitrary type, the indices carrying a nonzero object form a
  `Type v`-small type.
* `DifferentialGradedModule.General.isCompactObject_q_regularModule_arbitraryUniverse`: the image
  of the regular module in `D(A, d)` is a compact object at an arbitrary index universe.

## References

* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI)
* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace DifferentialGradedModule

attribute [local instance 10000] instPretriangulatedHomotopyCategory

namespace General

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- **A nonzero object of `D(A, d)` receives a nonzero morphism from some shift of the regular
module.** -/
theorem exists_hom_q_regularModule_ne_zero_of_not_isZero {X : derivedCategory.{u, v, v} A}
    (hX : ¬ IsZero X) :
    ∃ (n : ℤ) (f : (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A) ⟶
      X⟦n⟧), f ≠ 0 := by
  by_contra! hcon
  exact hX ((ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero
    ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A))).1
    (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule A)
    X hcon)

/-- **In a colimit cofan of `D(A, d)` indexed by an arbitrary type, the indices carrying a
nonzero object form a `Type v`-small type**, `v` being the universe of the carrier of the
algebra. -/
theorem small_nonzero_index_of_isColimitCofan {ι : Type w} (E : ι → derivedCategory.{u, v, v} A)
    (S : derivedCategory.{u, v, v} A) (j : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S j)) :
    Small.{v} {i : ι // ¬ IsZero (E i)} := by
  classical
  set K := (toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A)
  have hJ (n : ℤ) : Small.{v} {i : ι // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0} := by
    have hs : Small.{v} (K ⟶ S⟦n⟧) := small_hom_q_regularModule A (S⟦n⟧)
    have hcs : IsColimit (Cofan.mk (S⟦n⟧) fun i => (j i)⟦n⟧') :=
      isColimitCofanMkObjOfIsColimit
        (CategoryTheory.shiftFunctor (derivedCategory.{u, v, v} A) n) E j hc
    refine small_of_injective
      (f := fun x : {i : ι // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0} => x.2.choose ≫ (j x.1)⟦n⟧')
      fun a b hab => Subtype.ext ?_
    by_contra hne
    have hof : DirectSum.of (fun i => (K ⟶ (E i)⟦n⟧)) a.1 a.2.choose
        = DirectSum.of (fun i => (K ⟶ (E i)⟦n⟧)) b.1 b.2.choose :=
      injective_cofanMap K (fun i => (j i)⟦n⟧') hcs (by rwa [cofanMap_of, cofanMap_of])
    have h := DFunLike.congr_fun hof a.1
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hne] at h
    exact a.2.choose_spec h
  choose nn ff hff using fun x : {i : ι // ¬ IsZero (E i)} =>
    exists_hom_q_regularModule_ne_zero_of_not_isZero A x.2
  exact small_of_injective
    (f := fun x : {i : ι // ¬ IsZero (E i)} =>
      (⟨nn x, ⟨x.1, ff x, hff x⟩⟩ : Σ n : ℤ, {i : ι // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0}))
    fun a b hab => Subtype.ext (congrArg
      (fun x : (Σ n : ℤ, {i : ι // ∃ f : K ⟶ (E i)⟦n⟧, f ≠ 0}) => (x.2 : ι)) hab)

/-- **The regular module is a compact object of the derived category at an arbitrary index
universe, with the carrier of the algebra in a universe of its own.** Let `(A, d)` be a
differential graded algebra over a commutative ring `R : Type u` with carrier in `Type v`, the
two universes independent. For every universe `w` and every family `Fᵢ`, `i ∈ I`, of objects of
`D(A, d)` indexed by a type `I : Type w` and admitting a direct sum, the canonical map
`⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective. The derived category is read in the
pretriangulated structure whose distinguished triangles are the cone triangles. -/
theorem isCompactObject_q_regularModule_arbitraryUniverse :
    IsCompactObject.{w}
      ((quasiIsomorphisms A).Q.obj ((toHomotopyCategory A).obj (regularModule A))) :=
  isCompactObject_of_small_nonzero_index (isCompactObject_q_regularModule A)
    fun E => small_nonzero_index_of_isColimitCofan A E (∐ E) (Limits.Sigma.ι E)
      (coproductIsCoproduct E)

end General

end DifferentialGradedModule

end
