module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionCoproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionShiftSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-coherent objects form a strictly full, saturated, triangulated subcategory

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a sheaf of rings on
it and let `(A, d)` be a sheaf of differential graded `O`-algebras. Lemma 24.33.2 of the Stacks
project says that the full subcategory `QC(A, d)` of `D(A, d)` of Definition 24.33.1 — the
objects `M` for which `RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)` is an isomorphism for every morphism
`U → V` of `C` — is a strictly full, saturated, triangulated subcategory of `D(A, d)` preserved by
arbitrary direct sums.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_iff_forall_transposeLocus`: an object lies
  in `QC(A, d)` exactly when, for every morphism `a : V ⟶ U` of `Cᵒᵖ` and every object `Y` of
  `D(A(U), d)`, the map
  `h ↦ ψ ≫ h_{A(V)}` from `RΓ(U, X) ⟶ Y` to `RΓ(V, X) ⟶ Y_{A(V)}` is bijective, where `ψ` is the
  derived restriction map: this is the adjoint form of the invertibility of the canonical map.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_isClosedUnderIsomorphisms`,
  `…qc_isSaturated`, `…qc_isTriangulated` and `…qc_isClosedUnderColimitsOfShape_discrete`: the
  four closure properties.
* `…qc_isClosedUnderIsomorphisms_isSaturated_isTriangulated_isClosedUnderCoproducts`:
  **Tag 0GZA**, the four closure properties together.

## Implementation notes

The source's proof uses that `RΓ(U, -)` is exact and commutes with direct sums, because taking
sections over `U` is exact and commutes with direct sums on a chaotic site, and that
`- ⊗^𝐋_{A(V)} A(U)` is exact and commutes with direct sums. The direct sums are handled exactly
so: `RΓ(U, -)` preserves them (`derivedSections_preservesColimitsOfShape_discrete`), being
computed by the sections of a direct sum of modules, and the derived base change is a left
adjoint.

For the triangulated structure the adjoint form of the condition is used
(`StacksFrontier/CategoryTheory/Triangulated/TransposeLocus.lean`): the locus where the transpose of
the derived restriction map is invertible is a triangulated subcategory as soon as `RΓ(U, -)` and
`RΓ(V, -)` carry the first two morphisms of a distinguished triangle to the first two morphisms of
a distinguished triangle (`derivedSections_isWeaklyTriangulated`) and the derived restriction map
at `X[1]` is the translate of the one at `X` (`shiftSquare_derivedRestrictionMap`). Both are
proved from the modules computing the objects of `D(A, d)`.

The universes of the site, of the sheaf of rings, of the algebra and of the modules are those for
which `D(A, d)` is constructed with its direct sums (Tag 0FT9): the site and the ring in one
universe `u`, the algebra and the modules in a universe `max u v` containing it. Direct sums are
indexed by types of that universe.

## References

* [Stacks Project, Lemma 24.33.2 (Tag 0GZA)](https://stacks.math.columbia.edu/tag/0GZA)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 24.26.8 (Tag 0FT9)](https://stacks.math.columbia.edu/tag/0FT9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open Stacks.DerivedCategoryComparisons (isIso_app_of_retract isIso_app_colimit_of_preserves
  isIso_app_isClosedUnderColimitsOfShape)

universe v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective
attribute [local instance 10000]
  _root_.DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-! ### A bookkeeping identity -/

private theorem eq_comp_comp_of_eq_id {E : Type*} [Category E] {P P' T T' S : E} (φ : P ⟶ P')
    (q : P' ⟶ T) (j : T ⟶ T) (f : T ⟶ T') (g : T' ⟶ S) (ψ : P ⟶ S) (h : ψ = φ ≫ q ≫ f ≫ g)
    (hj : j = 𝟙 _) : ψ = φ ≫ (q ≫ j ≫ f) ≫ g := by
  subst hj
  simp [h]

section Chaotic

variable {C : Type u} [Category.{u} C] {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O))

namespace Chaotic

/-- The derived restriction map at the class of a module is restriction of sections, read
through the identifications of the derived sections with the classes of section modules. -/
theorem derivedRestrictionMap_app_derivedClass (M : DifferentialGradedModule.{u, v, v} A)
    {U V : Cᵒᵖ} (a : V ⟶ U) :
    (derivedRestrictionMap A a).app (derivedClass A M) =
      ((derivedSectionsIso A V).app M).hom ≫ derivedSectionRestriction M a ≫
        (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
          ((derivedSectionsIso A U).app M).inv :=
  eq_comp_comp_of_eq_id _ _ _ _ _ _ (derivedRestrictionMap_app_eq A a M)
    ((congrArg (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
      (CategoryTheory.Quotient.lift.isLift_inv _ _ _ _)).trans
        (CategoryTheory.Functor.map_id _ _))

/-- **The quasi-coherence condition on a module, in adjoint form**: the canonical map
`M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)` is invertible exactly when the class of `M` lies in the locus of
the derived restriction map. -/
theorem isIso_sectionComparison_iff (M : DifferentialGradedModule.{u, v, v} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) :
    IsIso (sectionComparison M a) ↔
      transposeLocus (derivedRestrictionMap A a) (derivedClass A M) := by
  rw [sectionComparison, isIso_homEquiv_symm_iff (sectionBaseChangeAdj A a)]
  exact (forall_bijective_iff_of_eq _ _ ((derivedSectionsIso A V).app M)
    ((derivedSectionsIso A U).app M) (derivedRestrictionMap_app_derivedClass A M a)).symm

/-- **An object of `D(A, d)` lies in `QC(A, d)` exactly when it lies in the locus of every
derived restriction map.** -/
theorem qc_iff_forall_transposeLocus (X : derivedCategory.{u, v, v} A) :
    QC A X ↔ ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U), transposeLocus (derivedRestrictionMap A a) X := by
  constructor
  · intro h U V a
    obtain ⟨M, rfl⟩ := exists_module_eq A X
    exact (isIso_sectionComparison_iff A M a).1 (h M rfl a)
  · rintro h M rfl U V a
    exact (isIso_sectionComparison_iff A M a).2 (h a)

/-- The locus of a derived restriction map is a triangulated subcategory. -/
theorem transposeLocus_derivedRestrictionMap_isTriangulated {U V : Cᵒᵖ} (a : V ⟶ U) :
    (transposeLocus (derivedRestrictionMap A a)).IsTriangulated :=
  transposeLocus_isTriangulated _ (derivedSections_isWeaklyTriangulated A U)
    (derivedSections_isWeaklyTriangulated A V)
    (_root_.DifferentialGradedModule.derivedRestrictionShiftIso (A.sectionRestriction a) 1)
    fun X ↦ ⟨X, ⟨Iso.refl _⟩,
      shiftSquare_derivedRestrictionMap A a (derivedCategoryModule A X)⟩

/-- **`QC(A, d)` is strictly full**: it is closed under isomorphisms. -/
instance qc_isClosedUnderIsomorphisms : (QC A).IsClosedUnderIsomorphisms where
  of_iso e h := (qc_iff_forall_transposeLocus A _).2 fun _ _ a ↦
    (transposeLocus (derivedRestrictionMap A a)).prop_of_iso e
      ((qc_iff_forall_transposeLocus A _).1 h a)

/-- `QC(A, d)` is stable under retracts. -/
instance qc_isStableUnderRetracts : (QC A).IsStableUnderRetracts where
  of_retract rt h := (qc_iff_forall_transposeLocus A _).2 fun _ _ a ↦
    (transposeLocus_iff_isIso _ (sectionBaseChangeAdj A a) _).2
      (isIso_app_of_retract _ rt
        ((transposeLocus_iff_isIso _ (sectionBaseChangeAdj A a) _).1
          ((qc_iff_forall_transposeLocus A _).1 h a)))

/-- **`QC(A, d)` is saturated**: it is closed under direct summands. -/
theorem qc_isSaturated : (QC A).IsSaturated :=
  ObjectProperty.IsSaturated.of_isStableUnderRetracts _

/-- **`QC(A, d)` is a triangulated subcategory of `D(A, d)`.** -/
instance qc_isTriangulated : (QC A).IsTriangulated := by
  have hloc := fun {U V : Cᵒᵖ} (a : V ⟶ U) ↦
    transposeLocus_derivedRestrictionMap_isTriangulated A a
  refine
    { exists_zero := ⟨0, isZero_zero _, (qc_iff_forall_transposeLocus A _).2 fun _ _ a ↦
        have := hloc a
        (transposeLocus (derivedRestrictionMap A a)).prop_of_isZero (isZero_zero _)⟩
      isStableUnderShiftBy := fun n ↦ ⟨fun X hX ↦ (qc_iff_forall_transposeLocus A _).2 fun _ _ a ↦
        have := hloc a
        (transposeLocus (derivedRestrictionMap A a)).le_shift n X
          ((qc_iff_forall_transposeLocus A X).1 hX a)⟩
      ext₂' := fun T hT h₁ h₃ ↦ (QC A).le_isoClosure _
        ((qc_iff_forall_transposeLocus A _).2 fun _ _ a ↦
        have := hloc a
        (transposeLocus (derivedRestrictionMap A a)).ext_of_isTriangulatedClosed₂ T hT
          ((qc_iff_forall_transposeLocus A _).1 h₁ a) ((qc_iff_forall_transposeLocus A _).1 h₃ a)) }

end Chaotic

end Chaotic

/-! ### Direct sums -/

section DirectSums

variable {C : Type u} [Category.{u} C] {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, max u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O))

/-- Taking sections over `U` carries a direct sum of differential graded `A`-modules to a direct
sum of differential graded `A(U)`-modules. -/
instance sectionModuleFunctor_preservesColimit_discrete (U : Cᵒᵖ) {J : Type (max u v)}
    (M : J → DifferentialGradedModule.{u, max u v, max u v} A) :
    PreservesColimit (Discrete.functor M) (sectionModuleFunctor A U) := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (isColimit_sectionModuleCofan M U))

/-- **Derived sections over an object of a chaotic site commute with direct sums**: a direct sum
in `D(A, d)` is computed by a direct sum of modules (Tag 0FT9), whose sections are the direct sum
of the sections, and the class functor of `D(A(U), d)` commutes with direct sums. -/
instance derivedSections_preservesColimitsOfShape_discrete (U : Cᵒᵖ) (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) (derivedSections A U) := by
  have hmod : ∀ M : J → DifferentialGradedModule.{u, max u v, max u v} A,
      PreservesColimit (Discrete.functor M ⋙ HomotopyCategory.quotient A ⋙ toDerivedCategory A)
        (derivedSections A U) := by
    intro M
    have : PreservesColimit (Discrete.functor M)
        (sectionModuleFunctor A U ⋙
          _root_.DifferentialGradedModule.classFunctor (A.sectionAlgebra U)) :=
      comp_preservesColimit _ _
    have : PreservesColimit (Discrete.functor M)
        (HomotopyCategory.quotient A ⋙ toDerivedCategory A ⋙ derivedSections A U) :=
      preservesColimit_of_natIso _ (derivedSectionsIso A U).symm
    exact preservesColimit_of_preserves_colimit_cocone
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
        (isColimit_derivedCofanOfModules_dg.{u, max u v, v} A M))
      (isColimitOfPreserves
        (HomotopyCategory.quotient A ⋙ toDerivedCategory A ⋙ derivedSections A U)
        (coproductIsCoproduct M))
  refine ⟨fun {K} ↦ ?_⟩
  exact preservesColimit_of_iso_diagram (derivedSections A U)
    (Discrete.natIso fun j ↦ Iso.refl (K.obj j) :
      Discrete.functor (fun j ↦ derivedCategoryModule A (K.obj ⟨j⟩)) ⋙
        HomotopyCategory.quotient A ⋙ toDerivedCategory A ≅ K)

namespace Chaotic

/-- **`QC(A, d)` is preserved by arbitrary direct sums.** -/
instance qc_isClosedUnderColimitsOfShape_discrete (J : Type (max u v)) :
    (QC A).IsClosedUnderColimitsOfShape (Discrete J) := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨K, hK⟩
  refine (qc_iff_forall_transposeLocus A _).2 fun U V a ↦ ?_
  have : (sectionBaseChange A a).IsLeftAdjoint := (sectionBaseChangeAdj A a).isLeftAdjoint
  refine (transposeLocus_iff_isIso _ (sectionBaseChangeAdj A a) _).2 ?_
  exact isIso_app_colimit_of_preserves _ _ _ K fun j ↦
    (transposeLocus_iff_isIso _ (sectionBaseChangeAdj A a) _).1
      ((qc_iff_forall_transposeLocus A _).1 (hK j) a)

/-- **Stacks 0GZA.** *Let `C` be a category, viewed as a site with the chaotic topology, let `O`
be a sheaf of rings on `C` and let `(A, d)` be a sheaf of differential graded `O`-algebras. The
subcategory `QC(A, d)` is a strictly full, saturated, triangulated subcategory of `D(A, d)`
preserved by arbitrary direct sums.*

Here `D(A, d)` is the derived category `SheafOfModules.DifferentialGradedModule.derivedCategory`
of Tag 0FT5 with its triangulated structure of Tag 0FT4, and `QC(A, d)` is
`SheafOfModules.DifferentialGradedModule.Chaotic.QC` of Tag 0GZ9. The four conjuncts are, in
order: strict fullness (closure under isomorphisms), saturation (closure under direct summands),
triangulatedness, and closure under the direct sums indexed by an arbitrary type of the universe
of the modules. -/
@[stacks 0GZA]
theorem qc_isClosedUnderIsomorphisms_isSaturated_isTriangulated_isClosedUnderCoproducts :
    (QC A).IsClosedUnderIsomorphisms ∧ (QC A).IsSaturated ∧ (QC A).IsTriangulated ∧
      ∀ J : Type (max u v), (QC A).IsClosedUnderColimitsOfShape (Discrete J) :=
  ⟨inferInstance, qc_isSaturated A, inferInstance, fun _ ↦ inferInstance⟩

end Chaotic

end DirectSums

end DifferentialGradedModule

end SheafOfModules

end
