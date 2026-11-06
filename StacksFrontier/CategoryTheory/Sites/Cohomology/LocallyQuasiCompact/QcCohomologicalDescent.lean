module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcAbelianComparisonApplied
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyOverOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedUnit
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent for the quasi-compact site of a locally quasi-compact space

Let `X` be an object of `LC_qc` and let `a_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism
of topoi to the small site of the underlying space, that is `π_X ∘ ε_X`, the change of topology
followed by the Zariski comparison. Stacks 0D91 asserts that for `K` in `D⁺(X)` the canonical
map

`K ⟶ Ra_{X,*} a_X^{-1} K`

is an isomorphism: the quasi-compact site computes the cohomology of the space.

## Main definitions

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `qcTopologicalAbelianDirectImage`: the direct image `a_{X,*} = π_{X,*} ∘ ε_{X,*}` on abelian
  sheaves, the right adjoint of `qcTopologicalAbelianInverseImage`.
* `qcTopologicalAbelianComparisonAdjunction`: the adjunction `a_X^{-1} ⊣ a_{X,*}`, the
  composite of the Zariski comparison adjunction and the change-of-topology adjunction.
* `qcTopologicalDerivedUnit`: the canonical map `K ⟶ Ra_{X,*}(a_X^{-1}K)` on bounded below
  derived categories.

## Main results

* `isIso_qcTopologicalAbelianComparisonAdjunction_unit_app`: the underived identification
  `a_{X,*}a_X^{-1}F = F`, [Stacks, Tag 09X3].
* `rightAcyclic_qcTopologicalAbelianDirectImage`: `a_X^{-1}F` is right acyclic for `a_{X,*}`,
  that is, `R^q a_{X,*} a_X^{-1}F = 0` for `q > 0`.
* `isIso_qcTopologicalDerivedUnit_app`: **Stacks 0D91**, the canonical map
  `K ⟶ Ra_{X,*}a_X^{-1}K` is an isomorphism for every `K` in `D⁺(X)`.

## Implementation notes

The coefficient category is `AddCommGrpCat.{max (u + 1) v}`. Enough injectives on the three
sheaf categories involved are `enoughInjectives_sheafOpens_site`,
`enoughInjectives_zariskiSliceSheaf` and `enoughInjectives_qcSliceSheaf`.

The derived unit is `Stacks.LerayPullbackComparison.derivedUnit` of the composite adjunction,
whose value on the image of a bounded below complex is `derivedUnit_app_Qh`.

## References

* [Stacks Project, Tag 0D91](https://stacks.math.columbia.edu/tag/0D91)
* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The unit of `RG` (Mathlib's `rightDerivedFunctorPlusUnith`, whose definition is not exposed)
is invertible at `K` exactly when the unit of `Functor.totalRightDerived` is: both are units of
right derived functors of the same functor. -/
private lemma isIso_rightDerivedFunctorPlusUnith_app_iff {D : Type*} {E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D]
    [HasDerivedCategory E] (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) ↔
      IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app K) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)) K]
  exact (isIso_comp_right_iff _ _).symm

namespace CategoryTheory.Functor

/-- **Right acyclicity passes to a composite whose second factor is exact.** If `M` is right
acyclic for `F`, the functor `F` carries injective objects to injective objects and `G`
preserves homology, then `M` is right acyclic for `F ⋙ G`. -/
lemma rightAcyclic_comp_of_preservesHomology {A B C : Type*}
    [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [EnoughInjectives A] [EnoughInjectives B]
    [F.PreservesInjectiveObjects] [G.PreservesHomology]
    (M : A) (hF : F.rightAcyclic M) : (F ⋙ G).rightAcyclic M := by
  have hG : IsIso G.rightDerivedFunctorPlusUnith :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology G
  set K : HomotopyCategory.Plus A := (HomotopyCategory.Plus.singleFunctor A 0).obj M with hK
  have hFK : IsIso (F.rightDerivedFunctorPlusUnith.app K) :=
    (isIso_rightDerivedFunctorPlusUnith_app_iff F K).2 hF
  have hrhs : IsIso (DerivedCategory.Plus.Qh.map
        ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫
      G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) := by
    have h₂ : IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) :=
      NatIso.isIso_app_of_isIso _ _
    have h₃ : IsIso (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) :=
      inferInstance
    infer_instance
  rw [← rightDerivedFunctorPlusComp_fac_app F G K] at hrhs
  have ht : IsIso ((rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K)) :=
    NatIso.isIso_app_of_isIso _ _
  exact (isIso_rightDerivedFunctorPlusUnith_app_iff (F ⋙ G) K).1
    (IsIso.of_isIso_comp_right ((F ⋙ G).rightDerivedFunctorPlusUnith.app K)
      ((rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K)))

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

/-- If the unit of an adjunction `L ⊣ R` between abelian categories is invertible, then the
unit of the induced adjunction on bounded below homotopy categories is invertible at every
object. -/
lemma isIso_mapHomotopyCategoryPlus_unit_app {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    (adj : L ⊣ R) [IsIso adj.unit] (K : HomotopyCategory.Plus A) :
    IsIso (adj.mapHomotopyCategoryPlus.unit.app K) := by
  have t1a := Adjunction.map_restrictFullyFaithful_unit_app
    (adj := adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (hiC := HomotopyCategory.Plus.fullyFaithfulι A)
    (hiD := HomotopyCategory.Plus.fullyFaithfulι B)
    (L := L.mapHomotopyCategoryPlus) (R := R.mapHomotopyCategoryPlus)
    (comm1 := Iso.refl _) (comm2 := Iso.refl _) K
  have t1 : (HomotopyCategory.Plus.ι A).map (adj.mapHomotopyCategoryPlus.unit.app K) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K.obj.as) := by
    have hcancel : ∀ (Y : HomotopyCategory B (ComplexShape.up ℤ))
        (a : (HomotopyCategory.Plus.ι A).obj K ⟶
          (R.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y),
        a ≫ (R.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 Y) ≫
          𝟙 ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) = a := by
      intro Y a
      simp
    exact t1a.trans ((hcancel _ _).trans rfl)
  have hnat : IsIso (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)) := by
    have h : NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ) =
        (NatIso.mapHomologicalComplex (asIso adj.unit) (ComplexShape.up ℤ)).hom := rfl
    rw [h]
    infer_instance
  have hα : IsIso ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K.obj.as) :=
    NatIso.isIso_app_of_isIso _ _
  have hiso : IsIso ((HomotopyCategory.Plus.ι A).map
      (adj.mapHomotopyCategoryPlus.unit.app K)) := by
    rw [t1]
    exact ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapIso
      (asIso ((NatTrans.mapHomologicalComplex adj.unit
        (ComplexShape.up ℤ)).app K.obj.as))).isIso_hom
  exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι A)

end CategoryTheory.Adjunction

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_zariskiSliceSheaf
  enoughInjectives_qcSliceSheaf

/-! ### The comparison `a_X` to the underlying space, on abelian sheaves -/

/-- **The direct image `a_{X,*}` on abelian sheaves**, that is `π_{X,*} ∘ ε_{X,*}`: a sheaf for
the quasi-compact topology on the slice, regarded as a sheaf for the Zariski topology and then
pushed to the small site of the underlying space. It is the right adjoint of
`qcTopologicalAbelianInverseImage`. -/
abbrev qcTopologicalAbelianDirectImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} :=
  qcAbelianDirectImage.{u, w, v} S X ⋙ S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}

section Adjunction

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- **The comparison adjunction `a_X^{-1} ⊣ a_{X,*}` on abelian sheaves**, the composite of the
Zariski comparison adjunction `π_X^{-1} ⊣ π_{X,*}` and the change-of-topology adjunction
`ε_X^{-1} ⊣ ε_{X,*}`. -/
def qcTopologicalAbelianComparisonAdjunction :
    qcTopologicalAbelianInverseImage.{u, w, v} S X ⊣
      qcTopologicalAbelianDirectImage.{u, w, v} S X :=
  (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).comp
    (qcAbelianComparisonAdjunction.{u, w, v} S X)

/-- **The identification `a_{X,*}a_X^{-1}F = F`**, [Stacks, Tag 09X3]: the unit of the
comparison adjunction is invertible at every abelian sheaf `F` on the space. -/
theorem isIso_qcTopologicalAbelianComparisonAdjunction_unit_app
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X).unit.app F) := by
  have hπ : IsIso ((S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit.app F) :=
    have := abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
    NatIso.isIso_app_of_isIso _ _
  have hε : IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F)) :=
    isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
      (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
        (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F))
  rw [qcTopologicalAbelianComparisonAdjunction, Adjunction.comp_unit_app]
  infer_instance

/-- The unit of the comparison adjunction `a_X^{-1} ⊣ a_{X,*}` is a natural isomorphism, that
is, `a_X^{-1}` is fully faithful. -/
instance isIso_qcTopologicalAbelianComparisonAdjunction_unit :
    IsIso (qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X).unit :=
  have : ∀ F, IsIso ((qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X).unit.app F) :=
    fun F ↦ isIso_qcTopologicalAbelianComparisonAdjunction_unit_app.{u, w, v} S X F
  NatIso.isIso_of_isIso_app _

end Adjunction

/-! ### Acyclicity of `a_X^{-1}F` for `a_{X,*}` -/

section Acyclicity

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- **`a_X^{-1}F` is right acyclic for the change of topology `ε_{X,*}`**: the vanishing
`R^i ε_{X,*}(a_X^{-1}F) = 0` for `i > 0`, the second half of clause (1) of
[Stacks, Tag 0DCY]. -/
theorem rightAcyclic_qcAbelianDirectImage_qcTopologicalInverseImage
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcAbelianDirectImage.{u, w, v} S X).rightAcyclic
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) :=
  (rightAcyclic_iff_isZero_rightDerived (qcAbelianDirectImage.{u, w, v} S X) _).2
    fun i hi ↦ isZero_rightDerived_qcAbelianDirectImage_of_vanishingCondition.{u, w, v} S
      (comparisonSituation.{u, w, v} S).vanishingCondition_all X _
      (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F) i hi

/-- **`a_X^{-1}F` is right acyclic for `a_{X,*}`**, that is, the vanishing
`R^q a_{X,*}a_X^{-1}F = 0` for `q > 0`. -/
theorem rightAcyclic_qcTopologicalAbelianDirectImage
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcTopologicalAbelianDirectImage.{u, w, v} S X).rightAcyclic
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) :=
  have : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Functor.rightAcyclic_comp_of_preservesHomology (qcAbelianDirectImage.{u, w, v} S X)
    (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}) _
    (rightAcyclic_qcAbelianDirectImage_qcTopologicalInverseImage.{u, w, v} S X F)

end Acyclicity

/-! ### The derived unit and cohomological descent -/

section Descent

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- **The canonical map `K ⟶ Ra_{X,*}(a_X^{-1}K)`** on bounded below derived categories: the
derived unit of the comparison adjunction `a_X^{-1} ⊣ a_{X,*}`, the inverse image appearing as
the functor it induces degreewise because it is exact. -/
def qcTopologicalDerivedUnit :
    𝟭 (DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) ⟶
      (qcTopologicalAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlus ⋙
        (qcTopologicalAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus :=
  Stacks.LerayPullbackComparison.derivedUnit
    (qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X)

/-- The unit of `Ra_{X,*}` is invertible at `a_X^{-1}K` for every bounded below complex `K` of
abelian sheaves on the space. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_qcTopologicalInverseImage
    (K : HomotopyCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((qcTopologicalAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlusUnith.app
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus.obj K)) :=
  Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n ↦
    rightAcyclic_qcTopologicalAbelianDirectImage.{u, w, v} S X (K.obj.as.X n)

/-- **Stacks 0D91**: cohomological descent for the quasi-compact site. For `X` an object of
`LC_qc` and `K` in `D⁺(X)` the canonical map `K ⟶ Ra_{X,*}a_X^{-1}K` is an isomorphism. -/
@[stacks 0D91 "cohomological descent for LC_qc: for X in LC_qc and K in D^+(X), the canonical map
K -> Ra_{X,*}a_X^{-1}K is an isomorphism"]
theorem isIso_qcTopologicalDerivedUnit_app
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((qcTopologicalDerivedUnit.{u, w, v} S X).app K) := by
  have hQh : ∀ L : HomotopyCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}),
      IsIso ((qcTopologicalDerivedUnit.{u, w, v} S X).app
        (DerivedCategory.Plus.Qh.obj L)) := by
    intro L
    rw [qcTopologicalDerivedUnit, Stacks.LerayPullbackComparison.derivedUnit_app_Qh]
    have h₁ : IsIso (DerivedCategory.Plus.Qh.map
        ((qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X).mapHomotopyCategoryPlus.unit.app
          L)) := by
      have hunit : IsIso (qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X).unit :=
        isIso_qcTopologicalAbelianComparisonAdjunction_unit.{u, w, v} S X
      have : IsIso ((qcTopologicalAbelianComparisonAdjunction.{u, w,
          v} S X).mapHomotopyCategoryPlus.unit.app L) :=
        Adjunction.isIso_mapHomotopyCategoryPlus_unit_app _ L
      infer_instance
    have h₂ := isIso_rightDerivedFunctorPlusUnit_app_qcTopologicalInverseImage.{u, w, v} S X L
    have h₃ : IsIso ((qcTopologicalAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus.map
        ((qcTopologicalAbelianInverseImage.{u, w,
          v} S X).mapDerivedCategoryPlusFactorsh.inv.app L)) := inferInstance
    exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)
  exact (NatTrans.isIso_app_iff_of_iso (qcTopologicalDerivedUnit.{u, w, v} S X)
    (DerivedCategory.Plus.Qh.objObjPreimageIso K)).1 (hQh _)

/-- The canonical map `K ⟶ Ra_{X,*}a_X^{-1}K` is a natural isomorphism. -/
instance isIso_qcTopologicalDerivedUnit : IsIso (qcTopologicalDerivedUnit.{u, w, v} S X) :=
  have := isIso_qcTopologicalDerivedUnit_app.{u, w, v} S X
  NatIso.isIso_of_isIso_app _

end Descent

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
