module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentative
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# Further results on `KInjectiveRepresentative`

Results about the objects of
`StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentative` that need imports beyond
those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe w w' v v' u u'

/-- Every object of the unbounded derived category is represented by a K-injective complex, as
soon as K-injective resolutions exist.

The hypothesis `hres` is Stacks 079P; it is taken as an argument rather than deduced from
`CategoryTheory.IsGrothendieckAbelian` so that the caller controls at which spelling of its
category the instances are resolved. -/
public lemma exists_isKInjective_representative_atModel
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (E : DerivedCategory C) :
    ∃ I : CochainComplex C ℤ, I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  obtain ⟨I, i, hI, hi⟩ := hres (DerivedCategory.Q.objPreimage E)
  have := hi
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- A right derived functor of `F` is computed on a K-injective complex by `F` itself: the
canonical comparison `α` is invertible there, which is Stacks 070K.

Every typeclass fact is an explicit argument, so that the lemma can be applied at a category with
two definitionally equal spellings without instance search having to choose between them. -/
public def rightDerivedObjIsoAtModel
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A : Type u'} [Category.{v'} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (F : C ⥤ A) (hF : F.Additive)
    (RF : DerivedCategory C ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ)))
    (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      RF.obj (DerivedCategory.Q.obj I) := by
  have := hF
  have := hRF
  have := hI
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) hres).2
    DerivedCategory.Qh RF α I inferInstance
  exact (DerivedCategory.quotientCompQhIso A).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).symm.app I) ≪≫
    asIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)) ≪≫
    RF.mapIso ((DerivedCategory.quotientCompQhIso C).app I)

end CategoryTheory

end
