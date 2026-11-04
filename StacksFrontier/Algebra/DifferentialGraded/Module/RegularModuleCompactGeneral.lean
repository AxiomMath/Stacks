module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-! # The regular module is compact, with the carrier of the algebra in its own universe

Let `(A, d)` be a differential graded algebra over a commutative ring `R : Type u` whose carrier
lies in a universe `v` of its own. `DifferentialGradedModule.isCompactObject_q_regularModule`
says that the image of the regular module in `D(A, d)` is a compact object, but only for
`A : DifferentialGradedAlgebra.{u, u} R` and read in the pretriangulated structure whose
distinguished triangles come from admissible short exact sequences, those being the restrictions
under which `DifferentialGradedModule.quasiIsomorphisms'` is defined. This file repeats that
development in the shape an endomorphism differential graded algebra needs: the two universes
independent, and the derived category the universe-polymorphic
`DifferentialGradedModule.derivedCategory` of
`StacksFrontier/Algebra/DGA/DerivedCategory.lean`, whose pretriangulated structure on `K(A, d)` is
the one whose distinguished triangles are the cone triangles.

Compactness is proved here against families indexed by a type of `Type v`, that being the
universe in which the bundled encoding of [Stacks, Tag 09JJ] provides direct sums of modules.
The index universe is freed in
`StacksFrontier/Algebra/DifferentialGraded/Module/RegularModuleCompactUniverseGeneral.lean`, which
needs the weak generation of `D(A, d)` by the regular module and so has a heavier import.

## Main results

* `DifferentialGradedModule.General.leftOrthogonal_acyclic_toHomotopyCategory_regularModule`:
  the regular module is orthogonal on the left to the acyclic modules — Tag 09K1 at independent
  universes, with the shift taken to be trivial.
* `DifferentialGradedModule.General.exists_eq_sum_comp_directSumInj`: a homomorphism from the
  regular module into a direct sum of differential graded modules is a finite sum of
  homomorphisms into the summands, composed with the coprojections.
* `DifferentialGradedModule.General.isCompactObject_q_regularModule`: **the image of the regular
  module in `D(A, d)` is a compact object**, tested against families indexed by a type of the
  algebra's universe.
* `DifferentialGradedModule.General.small_hom_q_regularModule`: the morphisms of `D(A, d)` out of
  the regular module into any object form a `Type v`-small type.

## Implementation notes

*What is reused and what is repeated.* The algebraic facts about homomorphisms out of the
regular module — that such a homomorphism is right multiplication by its value at the unit, that
the value is a cocycle of degree zero, and that right multiplication by such a cocycle is a
homomorphism — are stated in
`StacksFrontier/Algebra/DifferentialGraded/Module/RegularModuleCompact.lean` with the universes left
to be inferred, hence already at `A : DifferentialGradedAlgebra.{u, v} R` with `u` and `v`
independent; they are used here unchanged. What has to be repeated is everything mentioning the
direct sum of a family of modules or the localization at the quasi-isomorphisms, since the
single-universe development spells those as `DifferentialGradedModule.directSumObj`, whose index
type must lie in `Type u`, and as `DifferentialGradedModule.quasiIsomorphisms'`, which ties the
three universes of the homotopy category together. Their counterparts here are
`DifferentialGradedModule.General.directSumObj` and
`DifferentialGradedModule.quasiIsomorphisms`, and the three reductions of the proof are the ones
the single-universe file documents.

*Smallness without cohomology.* `DifferentialGradedModule.small_hom_shift_q_regularModule` bounds
the morphisms out of the regular module by identifying them with cohomology, a module over
`R : Type u`. Here the bound is read off the construction instead: an object of `D(A, d)` is
isomorphic to the image of an object of `K(A, d)`, the localization functor is bijective on
morphisms out of the regular module because the regular module is orthogonal on the left to the
acyclic modules, and the morphisms of `K(A, d)` form a type of `Type v`. The result is
`Small.{v}` rather than `Small.{u}`, which is the right bound here: the index universe at which
compactness is available below is `v`, not `u`.

## References

* [Stacks Project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS) for compactness,
  [Tag 09QI](https://stacks.math.columbia.edu/tag/09QI) for the direct sums of `D(A, d)`, and
  [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the morphisms out of the regular
  module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v

namespace DifferentialGradedModule

attribute [local instance 10000] instPretriangulatedHomotopyCategory

namespace General

variable {R : Type u} [CommRing R]

/-! ### The regular module is left orthogonal to the acyclic modules -/

/-- **Stacks Tag 09K1 at independent universes**, with the shift taken to be trivial: the regular
module is orthogonal on the left to the acyclic differential graded modules.

A homomorphism from the zeroth shift of the regular module into an acyclic module is
null-homotopic (`DifferentialGradedModule.General.isNullHomotopic_of_acyclic`), and that shift is
the regular module itself up to the isomorphism `DifferentialGradedModule.shiftZeroIso`. -/
theorem leftOrthogonal_acyclic_toHomotopyCategory_regularModule
    (A : DifferentialGradedAlgebra.{u, v} R) :
    (acyclic.{u, v, v} A).leftOrthogonal ((toHomotopyCategory A).obj (regularModule A)) := by
  refine leftOrthogonal_acyclic_of_iso A ((shiftZeroIso A).app (regularModule A)) ?_
  rw [leftOrthogonal_acyclic_iff]
  intro N hN g
  rw [← isNullHomotopic_iff_homotopic_zero]
  exact isNullHomotopic_of_acyclic hN 0 g

/-! ### Homomorphisms from the regular module into a direct sum -/

/-- **A homomorphism from the regular module into a direct sum factors through a finite
subsum.** Its value at the unit is a cocycle of degree zero of `⨁ᵢ Nᵢ`, hence a finitely
supported family of cocycles of degree zero of the `Nᵢ`; the homomorphism is right
multiplication by that value, so it is the sum over the support of right multiplication by the
components, composed with the coprojections.

This is `DifferentialGradedModule.exists_eq_sum_comp_directSumInj` with the index type of the
direct sum taken in the universe of the carrier of the algebra. -/
theorem exists_eq_sum_comp_directSumInj {A : DifferentialGradedAlgebra.{u, v} R} {ι : Type v}
    [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, v, v} A)
    (g : regularModule A ⟶ directSumObj N) :
    ∃ (s : Finset ι) (h : ∀ i, regularModule A ⟶ N i),
      g = ∑ i ∈ s, h i ≫ directSumInj N i := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ⨁ i, (N i).M, g.toFun (1 : A.A) = x := ⟨_, rfl⟩
  have hmem : ∀ i, x i ∈ (N i).grading 0 := by
    have h : g.toFun (1 : A.A) ∈ (directSumObj N).grading 0 := toFun_one_mem_grading g
    rw [hx] at h
    exact h
  have hd : ∀ i, (N i).d (x i) = 0 := by
    intro i
    have h0 : directSumD N (g.toFun (1 : A.A)) = 0 := d_toFun_one g
    rw [hx] at h0
    rw [← directSumD_apply N x i, h0, DirectSum.zero_apply]
  refine ⟨DFinsupp.support x, fun i => rightMulHom (x i) (hmem i) (hd i), hom_ext_toFun_one ?_⟩
  rw [toFun_one_sum, hx]
  refine (DirectSum.sum_support_of x).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Hom.comp_toFun_apply, rightMulHom_toFun_one, directSumInj_toFun_apply,
    DirectSum.lof_eq_of]

/-! ### Compactness of the regular module -/

section Compact

/-- The canonical functor from differential graded modules to the derived category: the quotient
by homotopy followed by the localization at the quasi-isomorphisms. -/
private abbrev toDerived (A : DifferentialGradedAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v, v} A ⥤ derivedCategory.{u, v, v} A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q

variable (A : DifferentialGradedAlgebra.{u, v} R)

section Family

variable {ι : Type v} [DecidableEq ι] (N : ι → DifferentialGradedModule.{u, v, v} A)

/-- The images in `D(A, d)` of the coprojections of `⨁ᵢ Nᵢ` exhibit the image of `⨁ᵢ Nᵢ` as a
direct sum: **Tag 09QI**. -/
private def isColimitCofanDerived :
    IsColimit (Cofan.mk ((toDerived A).obj (directSumObj N))
      fun i => (toDerived A).map (directSumInj N i)) :=
  isColimitCofanMkObjOfIsColimit (toDerived A) N (directSumInj N) (isColimit_directSumObj N)

/-- Every morphism of `D(A, d)` from the regular module into the image of `⨁ᵢ Nᵢ` is the image of
a finite sum of morphisms into the images of the summands. It comes from a morphism of `K(A, d)`
because the regular module is orthogonal on the left to the acyclic modules, hence from a
homomorphism of differential graded modules, which is a finite sum by
`DifferentialGradedModule.General.exists_eq_sum_comp_directSumInj`. -/
private theorem surjective_cofanMap_directSumInj :
    Function.Surjective (cofanMap ((toDerived A).obj (regularModule A))
      fun i => (toDerived A).map (directSumInj N i)) := by
  classical
  intro Ψ
  obtain ⟨ψ, hψ⟩ := (map_q_bijective_of_leftOrthogonal
    (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A)
    ((toHomotopyCategory A).obj (directSumObj N))).2 Ψ
  obtain ⟨g, rfl⟩ : ∃ g : regularModule A ⟶ directSumObj N,
      (toHomotopyCategory A).map g = ψ := by
    induction ψ using Quot.inductionOn with
    | _ g => exact ⟨g, rfl⟩
  obtain ⟨s, h, hsum⟩ := exists_eq_sum_comp_directSumInj N g
  refine ⟨∑ i ∈ s, DirectSum.of _ i ((toDerived A).map (h i)), ?_⟩
  rw [map_sum]
  simp only [cofanMap_of, ← Functor.map_comp]
  rw [← Functor.map_sum, ← hsum]
  exact hψ

/-- The canonical map `⨁ᵢ Hom(A, Q(Nᵢ)) → Hom(A, Q(⨁ᵢ Nᵢ))` is bijective. Injectivity holds for
the test map of any colimit cofan, and surjectivity is
`DifferentialGradedModule.General.surjective_cofanMap_directSumInj`. -/
private theorem bijective_cofanMap_directSumInj :
    Function.Bijective (cofanMap ((toDerived A).obj (regularModule A))
      fun i => (toDerived A).map (directSumInj N i)) :=
  ⟨injective_cofanMap _ _ (isColimitCofanDerived A N), surjective_cofanMap_directSumInj A N⟩

/-- The canonical map `⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective for a family of objects of
`D(A, d)` presented as the images of a family of differential graded modules. The two cofans have
isomorphic families, and the comparison of their vertices is an isomorphism because both exhibit
a direct sum of that family, so bijectivity transfers from
`DifferentialGradedModule.General.bijective_cofanMap_directSumInj`. -/
private theorem bijective_cofanMap_sigmaι_of_iso (F : ι → derivedCategory.{u, v, v} A)
    [HasCoproduct F] (e : ∀ i, (toDerived A).obj (N i) ≅ F i) :
    Function.Bijective
      (cofanMap ((toDerived A).obj (regularModule A)) (Limits.Sigma.ι F)) :=
  bijective_cofanMap_of_iso _ (fun i => (toDerived A).map (directSumInj N i))
    (Limits.Sigma.ι F) e
    ((isColimitCofanDerived A N).coconePointsIsoOfNatIso (coproductIsCoproduct F)
      (Discrete.natIso fun i => e i.as))
    (fun i => (isColimitCofanDerived A N).comp_coconePointsIsoOfNatIso_hom
      (coproductIsCoproduct F) (Discrete.natIso fun i => e i.as) ⟨i⟩)
    (bijective_cofanMap_directSumInj A N)

end Family

/-- **The regular module is a compact object of the derived category**, with the carrier of the
algebra in a universe `v` of its own. For every family `Fᵢ` of objects of `D(A, d)` indexed by a
type of `Type v` the canonical map `⨁ᵢ Hom(A, Fᵢ) → Hom(A, ∐ᵢ Fᵢ)` is bijective.

This is `DifferentialGradedModule.isCompactObject_q_regularModule` with the universe of the base
ring and the universe of the carrier of `A` independent of one another, and read in the
pretriangulated structure whose distinguished triangles are the cone triangles. -/
instance isCompactObject_q_regularModule :
    IsCompactObject.{v}
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A)) where
  bijective_toAddMonoid_rightComp_sigmaι F :=
    bijective_cofanMap_sigmaι_of_iso A
      (fun i => ((quasiIsomorphisms A).Q.objPreimage (F i)).as) F
      (fun i => (quasiIsomorphisms A).Q.objObjPreimageIso (F i))

/-- **The morphisms of `D(A, d)` out of the regular module form a `Type v`-small type**, `v`
being the universe of the carrier of the algebra. The morphisms of `D(A, d)` themselves live in
`Type (max u (v + 1))`, so this is a genuine restriction on their cardinality, and it is what
bounds the size of a family admitting a direct sum.

The target is isomorphic to the image of an object of `K(A, d)`; the localization functor is
bijective on morphisms out of the regular module, that module being orthogonal on the left to the
acyclic modules (`DifferentialGradedModule.General.map_q_bijective_of_leftOrthogonal`); and the
morphisms of `K(A, d)` are homotopy classes of homomorphisms of differential graded modules,
hence a type of `Type v`. -/
theorem small_hom_q_regularModule (T : derivedCategory.{u, v, v} A) :
    Small.{v} ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A) ⟶ T) := by
  have hsm : Small.{v} ((toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q).obj (regularModule A) ⟶
      (quasiIsomorphisms A).Q.obj ((quasiIsomorphisms A).Q.objPreimage T)) :=
    small_of_surjective (f := (quasiIsomorphisms A).Q.map)
      (map_q_bijective_of_leftOrthogonal
        (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A)
        ((quasiIsomorphisms A).Q.objPreimage T)).2
  exact small_of_injective
    (f := fun g => g ≫ ((quasiIsomorphisms A).Q.objObjPreimageIso T).inv)
    fun a b h => (cancel_mono _).1 h

end Compact

end General

end DifferentialGradedModule

end
