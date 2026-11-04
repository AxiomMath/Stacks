module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The derived adjunction of an exact inclusion and its right adjoint

Let `ι : 𝒜 ⥤ ℳ` be an exact functor of abelian categories with a right adjoint `Q`, and let
`(R, β)` be a total right derived functor of `Q`, relative to the localizations
`DerivedCategory.Qh` of the homotopy categories.  If the functor `D(ι)` that `ι` induces on
derived categories is a left adjoint at all, then the derived adjunction of
`CategoryTheory.Adjunction.derived` exhibits it as left adjoint to `R`, with a unit computed on
complexes by the unit of `ι ⊣ Q` and the comparison `β`.

The typical case is the inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the quasi-coherent modules and
its right adjoint, the coherator, whose derived functor is `RQ_X`: this is the adjunction of
[Stacks, Tag 09T5] for that pair.

## Main definitions

* `Stacks.DerivedCoherator.inclusionDerivedAdjunction` — `D(ι) ⊣ R`.

## Main results

* `Stacks.DerivedCoherator.inclusionDerivedAdjunction_unit_fac_app` — the unit at the class of a
  complex `K` of `𝒜`, followed by `R` of the factorisation of `D(ι)`, is the unit of `ι ⊣ Q` on
  `K` followed by `β` at `ι(K)`.
* `Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_unit_app_iff` — for `ι` fully
  faithful, the unit of `D(ι) ⊣ R` is invertible at `K` exactly when `β` is invertible at
  `ι(K)`.
* `Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_unit` — for `ι` fully faithful, the
  unit is invertible as soon as `β` is invertible at every `ι(K)`.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCoherator

variable {𝒜 ℳ : Type*} [Category* 𝒜] [Category* ℳ] [Abelian 𝒜] [Abelian ℳ]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℳ]
  (ι : 𝒜 ⥤ ℳ) [ι.Additive] [PreservesFiniteLimits ι] [PreservesFiniteColimits ι]
  {Q : ℳ ⥤ 𝒜} [Q.Additive] (adj : ι ⊣ Q)
  (R : DerivedCategory ℳ ⥤ DerivedCategory 𝒜)
  (β : Q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ))]
  [ι.mapDerivedCategory.IsLeftAdjoint]

/-- `D(ι)` is a left derived functor of `ι` along the localizations of the homotopy categories:
its factorisation through `DerivedCategory.Qh` is an isomorphism. -/
instance mapDerivedCategory_isLeftDerivedFunctor :
    ι.mapDerivedCategory.IsLeftDerivedFunctor ι.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ _

/-- `D(ι) ⋙ R` is a left derived functor of `ι ⋙ Qh ⋙ R` along the localization of the homotopy
category of `𝒜`, because the factorisation of `D(ι)` is an isomorphism. -/
instance mapDerivedCategory_comp_isLeftDerivedFunctor :
    (ι.mapDerivedCategory ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ι.mapDerivedCategoryFactorsh.hom R)
      (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ι.mapDerivedCategoryFactorsh R)

/-- **The derived adjunction `D(ι) ⊣ R`** of an exact functor `ι` with right adjoint `Q` and a
total right derived functor `(R, β)` of `Q`, as soon as `D(ι)` is a left adjoint at all.

It is `CategoryTheory.Adjunction.derived` of the adjunction that `ι ⊣ Q` induces on homotopy
categories. -/
def inclusionDerivedAdjunction : ι.mapDerivedCategory ⊣ R :=
  (adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso ℳ (ComplexShape.up ℤ)) ι.mapDerivedCategoryFactorsh.hom β

/-- **The unit of `D(ι) ⊣ R` on a complex.**  At the class `Qh(K)` of a complex `K` of `𝒜`, the
unit followed by `R` of the factorisation `D(ι)(Qh K) ≅ Qh(ι K)` is the class of the unit of
`ι ⊣ Q` at `K` followed by the comparison `β` at `ι(K)`. -/
lemma inclusionDerivedAdjunction_unit_fac_app (K : HomotopyCategory 𝒜 (ComplexShape.up ℤ)) :
    (inclusionDerivedAdjunction ι adj R β).unit.app (DerivedCategory.Qh.obj K) ≫
        R.map (ι.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
          ((adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).unit.app K) ≫
        β.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :=
  Adjunction.derivedη_fac_app (adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) ι.mapDerivedCategoryFactorsh.hom β K

variable [ι.Full] [ι.Faithful]

omit [HasDerivedCategory 𝒜] [HasDerivedCategory ℳ] [PreservesFiniteLimits ι]
  [PreservesFiniteColimits ι] [ι.mapDerivedCategory.IsLeftAdjoint] in
/-- For `ι` fully faithful, the unit of the adjunction `ι ⊣ Q` induced on homotopy categories is
invertible. -/
lemma isIso_mapHomotopyCategoryAdjunction_unit_app
    (K : HomotopyCategory 𝒜 (ComplexShape.up ℤ)) :
    IsIso ((adj.mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).unit.app K) := by
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  obtain ⟨K⟩ := K
  have : IsIso ((Adjunction.mapHomologicalComplexAdjunction adj
      (ComplexShape.up ℤ)).unit.app K) := by
    have : ∀ n, IsIso (((Adjunction.mapHomologicalComplexAdjunction adj
        (ComplexShape.up ℤ)).unit.app K).f n) := fun n => by
      rw [Adjunction.mapHomologicalComplexAdjunction_unit_app_f]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  exact Functor.map_isIso (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ))
    ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).unit.app K)

/-- For `ι` fully faithful, the unit of `D(ι) ⊣ R` is invertible at the class of a complex `K`
exactly when `β` is invertible at `ι(K)`. -/
lemma isIso_inclusionDerivedAdjunction_unit_app_iff
    (K : HomotopyCategory 𝒜 (ComplexShape.up ℤ)) :
    IsIso ((inclusionDerivedAdjunction ι adj R β).unit.app (DerivedCategory.Qh.obj K)) ↔
      IsIso (β.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
  have := isIso_mapHomotopyCategoryAdjunction_unit_app ι adj K
  rw [← isIso_comp_right_iff _ (R.map (ι.mapDerivedCategoryFactorsh.hom.app K)),
    inclusionDerivedAdjunction_unit_fac_app, isIso_comp_left_iff]

/-- For `ι` fully faithful, the unit of `D(ι) ⊣ R` is invertible as soon as `β` is invertible
at `ι(K)` for every complex `K` of `𝒜`. -/
lemma isIso_inclusionDerivedAdjunction_unit
    (h : ∀ K : HomotopyCategory 𝒜 (ComplexShape.up ℤ),
      IsIso (β.app ((ι.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) :
    IsIso (inclusionDerivedAdjunction ι adj R β).unit := by
  have hD : ∀ D : DerivedCategory 𝒜,
      IsIso ((inclusionDerivedAdjunction ι adj R β).unit.app D) := fun D => by
    have := (isIso_inclusionDerivedAdjunction_unit_app_iff ι adj R β
      (DerivedCategory.Qh.objPreimage D)).2 (h _)
    exact (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.objObjPreimageIso D)).1 this
  exact NatIso.isIso_of_isIso_app _

end Stacks.DerivedCoherator
