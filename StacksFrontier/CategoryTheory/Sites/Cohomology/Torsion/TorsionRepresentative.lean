module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Complexes with torsion terms representing objects with torsion cohomology

Let `A` be an abelian category equivalent to the category of abelian sheaves on a site. An object
of `D(A)` all of whose cohomology objects are torsion (read through the equivalence) is the class
of a complex all of whose terms are torsion. This is the essential surjectivity half of
[Stacks, Tag 0DD7], `Stacks.Torsion.exists_torsionDerivedEquivalence`, transported along the
equivalence.

## Main results

* `Stacks.Torsion.exists_torsion_complex_of_equivalence`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Torsion

universe w v u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  {A : Type*} [Category* A] [Abelian A] (G : A ≌ Sheaf J AddCommGrpCat.{w})
  [G.functor.Additive] [G.inverse.Additive]

/-- **An object of `D(A)` with torsion cohomology is the class of a complex with torsion
terms**, for `A` equivalent to abelian sheaves on a site, torsion being read through the
equivalence. -/
theorem exists_torsion_complex_of_equivalence (K : DerivedCategory A)
    (hK : ∀ n : ℤ,
      torsionSheafProperty J (G.functor.obj ((DerivedCategory.homologyFunctor A n).obj K))) :
    ∃ P : CochainComplex A ℤ, (∀ p, torsionSheafProperty J (G.functor.obj (P.X p))) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let K' := G.functor.mapDerivedCategory.obj K
  have hK' : torsionCohomologyProperty J K' := fun n =>
    torsionSheafProperty_of_iso J
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso G.functor n).app K).symm
      (hK n)
  obtain ⟨E, ⟨φ⟩⟩ := exists_torsionDerivedEquivalence J
  let Y := E.inverse.obj ⟨K', hK'⟩
  let Yc := DerivedCategory.Q.objPreimage Y
  let ι := (torsionSheafProperty J).ι
  let Tc := (ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj Yc
  let e₁ : DerivedCategory.Q.obj Tc ≅ K' :=
    (ι.mapDerivedCategoryFactors.app Yc).symm ≪≫
      ι.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso Y) ≪≫ (φ.app Y).symm ≪≫
      (torsionCohomologyProperty J).ι.mapIso (E.counitIso.app ⟨K', hK'⟩)
  let DE := Dualizing.mapDerivedCategoryEquivalenceOfEquivalence G
  refine ⟨(G.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj Tc, fun p => ?_, ⟨?_⟩⟩
  · exact torsionSheafProperty_of_iso J (G.counitIso.app _).symm (Yc.X p).property
  · exact (G.inverse.mapDerivedCategoryFactors.app Tc).symm ≪≫
      G.inverse.mapDerivedCategory.mapIso e₁ ≪≫ (DE.unitIso.app K).symm

end Stacks.Torsion
