module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import StacksCore.Tactic.StacksAttribute

/-! # Exactness of an unbounded right derived functor

Let `B` be an abelian category admitting K-injective resolutions and let
`F : K(B) ⥤ D` be an exact functor of triangulated categories out of the homotopy category of
cochain complexes. Then any right derived functor `RF : D(B) ⥤ D` of `F` along the
quasi-isomorphisms is again exact, for the shift-commutation datum that
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift` attaches to it.

This is what makes the long exact cohomology sequence of a distinguished triangle available after
applying an unbounded right derived functor, which is how every statement comparing `RF` across a
truncation triangle is proved. The bounded-below counterpart,
`CategoryTheory.Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus`, is
already available for `D⁺`.

The argument is the criterion `CategoryTheory.Functor.isTriangulated_of_leftExtension`: it is
enough to exhibit, for every morphism of `D(B)`, a distinguished triangle of `K(B)` whose first
morphism represents it and at whose three objects the unit of `RF` is invertible. Replacing the
source and target by K-injective resolutions, the morphism is represented by an honest morphism of
K-injective complexes, and the third object of a distinguished triangle on it is again
K-injective, because the K-injective complexes are the right orthogonal of the acyclic ones and a
right orthogonal is closed under the third object of a distinguished triangle.

## Main results

* `Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`: a right derived functor of an
  exact functor out of `K(B)` is exact.

## Implementation notes

The shift-commutation of `RF` is not a hypothesis but the canonical one produced from the unit,
so the statement is given under a `letI` binding that datum, which is how the conclusion
`RF.IsTriangulated` is even typeable.

K-injective resolutions are a hypothesis rather than an instance, since over a Grothendieck
abelian category they are `Stacks.Cohomology.Localization.enoughKInjectives` and elsewhere they
may come from somewhere else.

## References

* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedFunctor

/-- A right derived functor, along the quasi-isomorphisms, of an exact functor out of the
homotopy category of cochain complexes is exact. -/
theorem isTriangulated_of_isRightDerivedFunctor
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (hB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F : HomotopyCategory B (ComplexShape.up ℤ) ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (RF : DerivedCategory B ⥤ D) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))] :
    letI := Functor.IsRightDerivedFunctor.commShift RF α
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ℤ
    RF.IsTriangulated := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ℤ
  have hα := (F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    hB).2 DerivedCategory.Qh RF α
  have reps (X : DerivedCategory B) : ∃ I : CochainComplex B ℤ,
      I.IsKInjective ∧
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ X) := by
    obtain ⟨I, f, hI, hf⟩ := hB (DerivedCategory.Q.objPreimage X)
    exact ⟨I, hI, ⟨(DerivedCategory.quotientCompQhIso B).app I ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩
  refine Functor.isTriangulated_of_leftExtension RF α fun X Y f ↦ ?_
  obtain ⟨I, hI, ⟨eI⟩⟩ := reps X
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := reps Y
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).surjective (eI.hom ≫ f ≫ eJ.inv)
  obtain ⟨Z, k, δ, hT⟩ := distinguished_cocone_triangle g
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have hZ : CochainComplex.IsKInjective Z := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT
      (CochainComplex.IsKInjective.rightOrthogonal I)
      (CochainComplex.IsKInjective.rightOrthogonal J)
  refine ⟨Triangle.mk g k δ, hT, hα I hI, hα J hJ, hα Z hZ,
    ⟨Arrow.isoMk eI eJ ?_⟩⟩
  simp [hg]

end Stacks.DerivedFunctor

end
