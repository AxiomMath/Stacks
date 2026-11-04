module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# An exact functor's derived functor followed by a right derived functor

Let `F : C ⥤ A` be additive and exact, let `w : A ⥤ B` be additive and let `Rw : D(A) ⥤ D(B)` be
a right derived functor of `w` with unit `α`. This file shows that `F.mapDerivedCategory ⋙ Rw` is
a right derived functor of `F ⋙ w`, and names its unit.

**Why this statement exists.** It is the presupposition behind "the bridge for `F ⋙ w` taken at
`F.mapDerivedCategory ⋙ Rw`" in
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`, which takes the
unit `α'` and the `IsRightDerivedFunctor` instance for it as hypotheses and pins `α'`
componentwise with `hα'`. Nothing discharged them; the implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record that as owed at the
consumer. `Stacks.DerivedFunctor.precomposeUnit_app` is exactly that `hα'`.

**Why it is not absoluteness.** The post-composition analogue
`Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose` follows from absoluteness of a right
derived functor computed by K-injective resolutions, and needs nothing of the functor being
composed. Pre-composition is different: the unit of the composite at a K-injective complex `I` of
`C` is the unit of `Rw` at `F(I)`, so it is invertible only once `F(I)` is known to be K-injective
too. That is the hypothesis `hF`, and it is discharged whenever `F` has an exact left adjoint, by
[Stacks, Tag 08BJ] — `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`.

## Main definitions and results

* `Stacks.DerivedFunctor.precomposeSourceIso`, `Stacks.DerivedFunctor.precomposeTargetIso`: the
  two reassociations the unit is built from.
* `Stacks.DerivedFunctor.precomposeUnit` and `Stacks.DerivedFunctor.precomposeUnit_app`: **the
  unit, and its value at an object** — the unit of `Rw` at `F(K)` followed by `Rw` applied to
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted. This is the `hα'` of the
  pre-composition coherence, verbatim.
* `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose`: **`F.mapDerivedCategory ⋙ Rw` is a
  right derived functor of `F ⋙ w` with that unit**, given K-injective resolutions in both
  categories and that `F` preserves K-injectivity.
* `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`: the same with
  the last hypothesis replaced by an exact left adjoint of `F`, which is the form the excision of
  local cohomology needs — restriction of modules to an open subset has the exact left adjoint
  "extension by zero".

## Implementation notes

The criterion is
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`:
a unit invertible at the class of every K-injective complex is the unit of a right derived
functor. Invertibility of the first factor of `precomposeUnit_app` is
`hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` of
`CategoryTheory.Functor` ([Stacks, Tag 070K]) at `F(I)`, and of the second that
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an isomorphism.

`CategoryTheory.IsIso.comp_isIso'` is used rather than the instance `IsIso.comp_isIso`, and
`CategoryTheory.CochainComplex.isKInjective_mapHomologicalComplex_of_exact` is applied to a
`have` promoted with `haveI`: the two spellings `(F.mapHomotopyCategory _).obj (quotient.obj I)`
and `quotient.obj ((F.mapHomologicalComplex _).obj I)` of one object are definitionally equal but
not syntactically so, and instance search does not see through that.

In `precomposeUnit_app` the identity morphism contributed by
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` at `CategoryTheory.Iso.refl (F ⋙ w)` is
removed by a `congrArg` into `CategoryTheory.Functor.map_id`, and the two leading identities are
cancelled by the file-scoped `id_id_comp` rather than by `simp only [Category.id_comp]`, for the
same reason: they sit at two different spellings of one object.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits
open CategoryTheory.Functor
  (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective)
open Stacks.Injectives.KInjectiveResolution
  (isRightDerivedFunctor_of_isIso_app_quotient_isKInjective)

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB wC vC uC

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (w : A ⥤ B) [w.Additive]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)

/-- Two identity morphisms at the head of a composite. Stated at an arbitrary category with the
objects implicit, so that the two identities may be given at different spellings of one object. -/
private theorem id_id_comp {D : Type*} [Category* D] {x x' y z : D} (i : x ⟶ x') (j : x' ⟶ x)
    (f : x ⟶ y) (g : y ⟶ z) (hij : i ≫ j = CategoryStruct.id x) :
    (i ≫ j) ≫ f ≫ g = f ≫ g := by
  rw [hij, Category.id_comp]

/-- The comparison of `(F ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh` with
`F.mapHomotopyCategory _ ⋙ w.mapHomotopyCategory _ ⋙ Qh`: the homotopy-category functor of a
composite is the composite of the homotopy-category functors, reassociated. -/
def precomposeSourceIso :
    (F ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _

/-- The comparison of `F.mapHomotopyCategory _ ⋙ Qh ⋙ Rw` with `Qh ⋙ F.mapDerivedCategory ⋙ Rw`:
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted, under `Rw`. -/
def precomposeTargetIso :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ Rw ≅
      DerivedCategory.Qh ⋙ F.mapDerivedCategory ⋙ Rw :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh.symm Rw ≪≫
      Functor.associator _ _ _

/-- **The unit of `F.mapDerivedCategory ⋙ Rw` as a right derived functor of `F ⋙ w`**: the unit
`α` of `Rw` whiskered by the homotopy-category functor of `F`, between the two reassociations. -/
def precomposeUnit :
    (F ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ F.mapDerivedCategory ⋙ Rw :=
  (precomposeSourceIso F w).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
      (precomposeTargetIso F Rw).hom

/-- **The unit at an object.** The comparison of the two homotopy-category functors and the
reassociations contribute identity morphisms, so what is left is the unit of `Rw` at `F(K)`
followed by `Rw` applied to `CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted — which
is the hypothesis `hα'` of
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`, verbatim. -/
theorem precomposeUnit_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (precomposeUnit F w Rw α).app K =
      α.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        Rw.map (F.mapDerivedCategoryFactorsh.inv.app K) := by
  have h0 : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w))
      (ComplexShape.up ℤ)).inv.app K = CategoryStruct.id
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := rfl
  have h1 : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w))
        (ComplexShape.up ℤ)).inv.app K)
      = CategoryStruct.id (DerivedCategory.Qh.obj
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) :=
    (congrArg DerivedCategory.Qh.map h0).trans (DerivedCategory.Qh.map_id _)
  have h2 : (precomposeUnit F w Rw α).app K =
      (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w))
          (ComplexShape.up ℤ)).inv.app K) ≫ CategoryStruct.id _) ≫
        α.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          CategoryStruct.id _ ≫
            Rw.map (F.mapDerivedCategoryFactorsh.inv.app K) ≫ CategoryStruct.id _ := rfl
  rw [h2, h1]
  simp only [Category.id_comp, Category.comp_id]
  refine id_id_comp _ _ _ _ ?_
  exact Category.comp_id _

variable [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **An exact functor's derived functor followed by a right derived functor is a right derived
functor.** If every cochain complex in `A` and in `C` admits a quasi-isomorphism into a
K-injective one, `F` carries K-injective complexes to K-injective complexes, and `Rw` is a right
derived functor of `w` with unit `α`, then `F.mapDerivedCategory ⋙ Rw` is a right derived functor
of `F ⋙ w` with unit `Stacks.DerivedFunctor.precomposeUnit`.

This is what "the bridge for `F ⋙ w` taken at `F.mapDerivedCategory ⋙ Rw`" presupposes. -/
theorem isRightDerivedFunctor_precompose
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hF : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (F.mapDerivedCategory ⋙ Rw).IsRightDerivedFunctor (precomposeUnit F w Rw α)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_quotient_isKInjective hresC _ _ _ ?_
  intro I hI
  have h1 : IsIso (α.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) :=
    (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresA).2
      DerivedCategory.Qh Rw α _ (hF I hI)
  have h2 : IsIso (Rw.map (F.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) := inferInstance
  rw [precomposeUnit_app]
  exact IsIso.comp_isIso' h1 h2

/-- **The same, for an exact functor with an exact left adjoint.** A functor with an exact left
adjoint carries K-injective complexes to K-injective complexes ([Stacks, Tag 08BJ]), so the
hypothesis on `F` is automatic. This is the form the excision of local cohomology needs:
restriction of modules to an open subset is right adjoint to extension by zero, which is
exact. -/
theorem isRightDerivedFunctor_precompose_of_exact_leftAdjoint (V : A ⥤ C) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] (adj : V ⊣ F)
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    (F.mapDerivedCategory ⋙ Rw).IsRightDerivedFunctor (precomposeUnit F w Rw α)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_precompose F w Rw α hresA hresC fun I hI =>
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact F V adj I

end Stacks.DerivedFunctor

end
