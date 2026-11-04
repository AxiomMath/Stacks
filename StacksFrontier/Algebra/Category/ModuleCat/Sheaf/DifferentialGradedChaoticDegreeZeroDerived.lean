module

public import Mathlib.CategoryTheory.Localization.Quotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZero

/-!
# The derived category of an algebra concentrated in degree zero

Let `C` be a category with the chaotic topology, `R` a sheaf of rings on it and `(A, d)` a sheaf
of differential graded `R`-algebras concentrated in degree zero, identified with a presheaf of
commutative rings `O` (`SheafOfModules.DifferentialGradedModule.DegreeZero.Data`). The
equivalence `Mod(A, d) ≌ Comp(O)`
(`SheafOfModules.DifferentialGradedModule.DegreeZero.equivalence`) respects quasi-isomorphisms
and homotopies, so it induces an equivalence of derived categories

`D(A, d) ≌ D(O)`,

for any model of the derived category of presheaves of `O`-modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.DegreeZero.derivedEquivalence`: the equivalence
  `D(A, d) ≌ D(O)`.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.derivedEquivalenceFac`: its compatibility
  with the localization functors: the class of a differential graded module is sent to the class
  of the corresponding complex of `O`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

namespace DegreeZero

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{a}}
  {A : DifferentialGradedAlgebra.{a, a} R} {O : Cᵒᵖ ⥤ RingCat.{a}} (D : Data A O)
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{w} (PresheafOfModules.{m} O)]

/-- The morphisms of right differential graded modules which are quasi-isomorphisms of the
complexes of `O`-modules. -/
abbrev quasiIsoW : MorphismProperty (DifferentialGradedModule.{a, a, m} A) :=
  (HomologicalComplex.quasiIso (PresheafOfModules.{m} O) (ComplexShape.up ℤ)).inverseImage
    (toComplexFunctor D)

omit [HasDerivedCategory.{w} (PresheafOfModules.{m} O)] in
/-- A morphism of right differential graded modules lies in `quasiIsoW D` if and only if it is a
quasi-isomorphism of the underlying complexes. -/
theorem quasiIsoW_iff {M N : DifferentialGradedModule.{a, a, m} A} (f : M ⟶ N) :
    quasiIsoW D f ↔ QuasiIso f.toHomologicalComplex :=
  quasiIso_toComplexMap_iff D f

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The composition of `toComplexFunctor D` with the localization functor `DerivedCategory.Q` is
a localization functor with respect to `quasiIsoW D`. -/
theorem isLocalization_toComplexFunctor_comp_Q :
    (toComplexFunctor D ⋙ DerivedCategory.Q).IsLocalization (quasiIsoW D) := by
  apply Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{m} O) (ComplexShape.up ℤ)) _ (quasiIsoW D)
    (equivalence D).symm
  · intro X Y f hf
    apply MorphismProperty.le_isoClosure
    exact
      ((HomologicalComplex.quasiIso (PresheafOfModules.{m} O) (ComplexShape.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoMk ((equivalence D).counitIso.app X) ((equivalence D).counitIso.app Y)
          ((equivalence D).counitIso.hom.naturality f).symm)).mpr hf
  · intro X Y f hf
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (PresheafOfModules.{m} O) (ComplexShape.up ℤ)) _ hf
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (equivalence D).counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- Homotopic morphisms of right differential graded modules become equal in the localization
with respect to `quasiIsoW D`. -/
theorem homotopic_factorsThroughLocalization :
    HomRel.FactorsThroughLocalization
      (fun {M N : DifferentialGradedModule.{a, a, m} A} (f g : M ⟶ N) => Homotopic f g)
      (quasiIsoW D) := by
  have := isLocalization_toComplexFunctor_comp_Q D
  intro M N f g ⟨h⟩
  exact (areEqualizedByLocalization_iff (toComplexFunctor D ⋙ DerivedCategory.Q)
    (quasiIsoW D) f g).mpr (DerivedCategory.Q_map_eq_of_homotopy _ (homotopyToComplex D h))

omit [HasDerivedCategory.{w} (PresheafOfModules.{m} O)] in
/-- The class `quasiIsoW D` is the inverse image of the quasi-isomorphisms of the homotopy
category under `HomotopyCategory.quotient A`. -/
theorem quasiIsoW_eq :
    quasiIsoW D = (quasiIsomorphisms.{a, a, m} A).inverseImage (HomotopyCategory.quotient A) := by
  ext M N f
  exact (quasiIsoW_iff D f).trans (quasiIsomorphisms_quotient_map_iff f).symm

/-- The composition of the quotient functor to the homotopy category with `toDerivedCategory A` is
a localization functor with respect to `quasiIsoW D`. -/
theorem isLocalization_quotient_comp_toDerivedCategory :
    (HomotopyCategory.quotient A ⋙ toDerivedCategory.{a, a, m} A).IsLocalization (quasiIsoW D) :=
  Functor.IsLocalization.mk' _ _
    ((homotopic_factorsThroughLocalization D).strictUniversalPropertyFixedTarget'
      (quasiIsoW_eq D) _)
    ((homotopic_factorsThroughLocalization D).strictUniversalPropertyFixedTarget'
      (quasiIsoW_eq D) _)

/-- **The derived category of an algebra concentrated in degree zero is the derived category of
modules over the corresponding presheaf of commutative rings**: `D(A, d) ≌ D(O)`. -/
def derivedEquivalence :
    derivedCategory.{a, a, m} A ≌ DerivedCategory (PresheafOfModules.{m} O) :=
  haveI := isLocalization_quotient_comp_toDerivedCategory D
  haveI := isLocalization_toComplexFunctor_comp_Q D
  Localization.uniq (HomotopyCategory.quotient A ⋙ toDerivedCategory.{a, a, m} A)
    (toComplexFunctor D ⋙ DerivedCategory.Q) (quasiIsoW D)

/-- The equivalence `D(A, d) ≌ D(O)` sends the class of a differential graded module to the class
of the corresponding complex of `O`-modules. -/
def derivedEquivalenceFac :
    (HomotopyCategory.quotient A ⋙ toDerivedCategory.{a, a, m} A) ⋙
        (derivedEquivalence D).functor ≅ toComplexFunctor D ⋙ DerivedCategory.Q :=
  haveI := isLocalization_quotient_comp_toDerivedCategory D
  haveI := isLocalization_toComplexFunctor_comp_Q D
  Localization.compUniqFunctor _ _ (quasiIsoW D)

end DegreeZero

end DifferentialGradedModule

end SheafOfModules

end
