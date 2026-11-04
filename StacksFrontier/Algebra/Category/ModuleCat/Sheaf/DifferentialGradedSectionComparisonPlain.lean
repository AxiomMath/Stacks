module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionDatum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangePlainComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-!
# The comparison maps of quasi-coherence, computed by plain tensor products

Let `C` be a category with the chaotic topology, `O` a sheaf of commutative rings on it and
`(A, d)` a sheaf of differential graded `O`-algebras. For a morphism `a : V ⟶ U` of `Cᵒᵖ` and a
right differential graded `A`-module `M`, the comparison map of Definition 24.33.1

`RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)`

is defined as an adjoint transpose under the derived adjunction of Tag 0BYX. This file computes
it. Under the identification of the derived sections with the sections it is the comparison
`M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(V) ⊗_{A(V)} A(U)` of Tag 0BZ2 followed by the class of the plain map
`M(V) ⊗_{A(V)} A(U) ⟶ M(U)`, `x ⊗ b ↦ x|_U · b`. In particular, when `M(V)` is orthogonal on the
left to the acyclic modules the comparison map is invertible exactly when that plain map is a
quasi-isomorphism.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Chaotic.plainSectionComparison`: the plain map
  `M(V) ⊗_{A(V)} A(U) ⟶ M(U)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.sectionComparison_eq_plain`: the comparison
  map of a module is the comparison of Tag 0BZ2 followed by the class of the plain map.
* `SheafOfModules.DifferentialGradedModule.sectionComparison_sectionDatum_toDerivedCategory`:
  the comparison map of the section datum at the class of `M` is the comparison map of `M`,
  conjugated by the identifications of derived sections with sections.
* `SheafOfModules.DifferentialGradedModule.isIso_sectionComparison_sectionDatum_iff`: the two are
  invertible together.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace Chaotic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} R}

/-- **The plain comparison map** `M(V) ⊗_{A(V)} A(U) ⟶ M(U)`, `x ⊗ b ↦ x|_U · b`: the transpose
of restriction of sections under extension of scalars along the restriction homomorphism. -/
def plainSectionComparison (M : DifferentialGradedModule.{t, m, m} A) {U V : Cᵒᵖ} (a : V ⟶ U) :
    (DifferentialGraded.Bimodule.tensorCompFunctor
        (DifferentialGraded.Bimodule.regular (A.sectionRestriction a))).obj (M.sectionModule V) ⟶
      M.sectionModule U :=
  DifferentialGraded.Bimodule.plainTranspose (A.sectionRestriction a) (M.sectionModuleRestriction a)

/-- **The comparison map of quasi-coherence is computed by the plain one**: it is the comparison
`M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(V) ⊗_{A(V)} A(U)` of the derived tensor product followed by the class
of `plainSectionComparison`. -/
theorem sectionComparison_eq_plain (M : DifferentialGradedModule.{t, m, m} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) :
    sectionComparison M a =
      (DifferentialGraded.Bimodule.derivedTensorFunctorCounit
          (DifferentialGraded.Bimodule.regular (A.sectionRestriction a))).app
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).obj
            (M.sectionModule V)) ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.map
          ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient
            (DifferentialGraded.Bimodule.regular (A.sectionRestriction a))).inv.app
              (M.sectionModule V)) ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).map
            (plainSectionComparison M a)) :=
  DifferentialGraded.Bimodule.derivedTranspose_eq _ _

/-- **At a module whose sections over `V` are orthogonal on the left to the acyclic modules, the
comparison map is invertible exactly when the plain one is a quasi-isomorphism.** -/
theorem isIso_sectionComparison_iff_quasiIso (M : DifferentialGradedModule.{t, m, m} A)
    {U V : Cᵒᵖ} (a : V ⟶ U)
    (hM : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra V)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).obj
        (M.sectionModule V))) :
    IsIso (sectionComparison M a) ↔
      QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex (A.sectionAlgebra U)).map
        (plainSectionComparison M a)) := by
  have h₁ := DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal
    (DifferentialGraded.Bimodule.regular (A.sectionRestriction a)) _ hM
  rw [sectionComparison_eq_plain, isIso_comp_left_iff, isIso_comp_left_iff,
    _root_.DifferentialGradedModule.isIso_q_map_toHomotopyCategory_map_iff]

end Chaotic

/-! ### The comparison maps of the section datum -/

section SectionDatum

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-- **The comparison map of the section datum at the class of a module is the comparison map of
the module**, conjugated by the identifications `RΓ(V, M) = M(V)` and `RΓ(U, M) = M(U)` of
derived sections with sections. -/
theorem sectionComparison_sectionDatum_toDerivedCategory (M : DifferentialGradedModule.{t, m, m} A)
    {U V : Cᵒᵖ} (a : V ⟶ U) :
    ((sectionDatum A).baseChange a).map ((derivedSectionsIso A V).hom.app M) ≫
        Chaotic.sectionComparison M a =
      sectionComparison (sectionDatum A) a
          ((toDerivedCategory.{t, m, m} A).obj ((HomotopyCategory.quotient A).obj M)) ≫
        (derivedSectionsIso A U).hom.app M := by
  have key : (derivedSectionsIso A V).hom.app M ≫ Chaotic.derivedSectionRestriction M a =
      (derivedRestrictionMap A a).app
          ((toDerivedCategory.{t, m, m} A).obj ((HomotopyCategory.quotient A).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
          ((derivedSectionsIso A U).hom.app M) := by
    have hid : (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
        ((_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
          (A.sectionRestriction a)).inv.app (M.sectionModule U)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    calc _ = ((derivedSectionsIso A V).hom.app M ≫
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
            ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
              (M.sectionModuleRestriction a))) ≫
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
            ((_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
              (A.sectionRestriction a)).inv.app (M.sectionModule U)) ≫
          (_root_.DifferentialGradedModule.derivedRestrictionFactorization
              (A.sectionRestriction a)).inv.app
            ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
              (M.sectionModule U)) := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [derivedRestrictionMap_app_toDerivedCategory A a M]
        refine (congrArg (fun k => _ ≫ k ≫ _) hid).trans ?_
        refine (congrArg (fun k => _ ≫ k) (Category.id_comp _)).trans ?_
        exact (Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k)
          ((Category.assoc _ _ _).trans ((congrArg (fun k => _ ≫ k)
            (Iso.hom_inv_id_app (_root_.DifferentialGradedModule.derivedRestrictionFactorization
              (A.sectionRestriction a)) _)).trans (Category.comp_id _))))
  change (Chaotic.sectionBaseChange A a).map ((derivedSectionsIso A V).hom.app M) ≫
      ((Chaotic.sectionBaseChangeAdj A a).homEquiv _ _).symm
        (Chaotic.derivedSectionRestriction M a) =
    ((Chaotic.sectionBaseChangeAdj A a).homEquiv _ _).symm
      ((derivedRestrictionMap A a).app _) ≫ (derivedSectionsIso A U).hom.app M
  exact (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
    ((congrArg _ key).trans (Adjunction.homEquiv_naturality_right_symm _ _ _))

/-- **The comparison map of the section datum at the class of a module is invertible exactly
when the comparison map of the module is.** -/
theorem isIso_sectionComparison_sectionDatum_iff (M : DifferentialGradedModule.{t, m, m} A)
    {U V : Cᵒᵖ} (a : V ⟶ U) :
    IsIso (sectionComparison (sectionDatum A) a
        ((toDerivedCategory.{t, m, m} A).obj ((HomotopyCategory.quotient A).obj M))) ↔
      IsIso (Chaotic.sectionComparison M a) :=
  (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (((sectionDatum A).baseChange a).mapIso ((derivedSectionsIso A V).app M))
      ((derivedSectionsIso A U).app M) (sectionComparison_sectionDatum_toDerivedCategory M a))

/-- **A module computes a quasi-coherent object exactly when it satisfies the quasi-coherence
condition on modules.** -/
theorem isQC_sectionDatum_iff (M : DifferentialGradedModule.{t, m, m} A) :
    IsQC (sectionDatum A)
        ((toDerivedCategory.{t, m, m} A).obj ((HomotopyCategory.quotient A).obj M)) ↔
      Chaotic.IsQCModule M :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun a =>
    isIso_sectionComparison_sectionDatum_iff M a

end SectionDatum

end SheafOfModules.DifferentialGradedModule

end
