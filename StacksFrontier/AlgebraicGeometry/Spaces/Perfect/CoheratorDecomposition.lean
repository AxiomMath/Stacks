module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparisonSupplement

/-!
# Decomposing an object of `D(𝒪_X)` against `D_QCoh(𝒪_X)`

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  By Derived
Categories, Lemma 0CQS the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint exactly when
every object `K` of `D(𝒪_X)` is *decomposable*: it sits in a distinguished triangle
`E' ⟶ K ⟶ Q ⟶ E'[1]` with `E'` in `D_QCoh(𝒪_X)` and `Q` right orthogonal to `D_QCoh(𝒪_X)`.  By
Derived Categories, Lemma 0CQR the decomposable objects form a triangulated subcategory.

This file sets up these two facts for algebraic spaces, and proves the step of the first proof
of Stacks 0CR4 that moves decomposability along an étale morphism `j : W ⟶ X`: if
`D_QCoh(𝒪_W) ⥤ D(𝒪_W)` has a right adjoint and `Rj_*` carries `D_QCoh(𝒪_W)` into
`D_QCoh(𝒪_X)`, then `Rj_*L` is decomposable for every `L` in `D(𝒪_W)`.

## Main definitions

* `AlgebraicGeometry.Space.qcohDerivedProp`: `D_QCoh(𝒪_X)`, as a property of the objects of
  `D(𝒪_X)`.
* `AlgebraicGeometry.Space.coheratorDecomposable`: the decomposable objects of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.coheratorDecomposable_eq_top_iff`: Lemma 0CQS for
  `D_QCoh(𝒪_X) ⊆ D(𝒪_X)`.
* `AlgebraicGeometry.Space.coheratorDecomposable_derivedPushforward`: the étale step.

## References

* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks Project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated
  Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `D_QCoh(𝒪_X)`, the complexes of `𝒪_X`-modules with quasi-coherent cohomology sheaves, as a
property of the objects of `D(𝒪_X)`. -/
abbrev qcohDerivedProp (X : AlgebraicSpaces B S hS) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- The objects `K` of `D(𝒪_X)` sitting in a distinguished triangle `E' ⟶ K ⟶ Q ⟶ E'[1]` with
`E'` in `D_QCoh(𝒪_X)` and `Q` right orthogonal to `D_QCoh(𝒪_X)`. -/
abbrev coheratorDecomposable (X : AlgebraicSpaces B S hS) :=
  (qcohDerivedProp B S hS X).extensionProduct (qcohDerivedProp B S hS X).rightOrthogonal

/-- **Stacks 0CQR** for `D_QCoh(𝒪_X)`: the decomposable objects form a triangulated
subcategory of `D(𝒪_X)`. -/
theorem coheratorDecomposable_isTriangulated (X : AlgebraicSpaces B S hS)
    [(qcohDerivedProp B S hS X).IsTriangulated] :
    (coheratorDecomposable B S hS X).IsTriangulated :=
  isTriangulated_extensionProduct_of_le_rightOrthogonal _ _ le_rfl

/-- **Stacks 0CQS** for `D_QCoh(𝒪_X) ⊆ D(𝒪_X)`: the inclusion has a right adjoint if and only if
every object of `D(𝒪_X)` is decomposable. -/
theorem coheratorDecomposable_eq_top_iff (X : AlgebraicSpaces B S hS)
    [(qcohDerivedProp B S hS X).IsTriangulated] :
    coheratorDecomposable B S hS X = ⊤ ↔ (qcohDerivedProp B S hS X).ι.IsLeftAdjoint :=
  ((isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (qcohDerivedProp B S hS X)).1).symm

/-- **The étale step of the first proof of Stacks 0CR4.**  Let `j : W ⟶ X` be an étale morphism
of algebraic spaces such that `D_QCoh(𝒪_W) ⥤ D(𝒪_W)` has a right adjoint, and let `R` be a right
derived functor of `j_*` carrying `D_QCoh(𝒪_W)` into `D_QCoh(𝒪_X)`.  Then `R L` is decomposable
in `D(𝒪_X)` for every `L` in `D(𝒪_W)`: `R` carries a decomposition triangle `L' ⟶ L ⟶ Q` of `L`
to a distinguished triangle, and `R Q` is right orthogonal to `D_QCoh(𝒪_X)` because
`Hom(M, R Q) = Hom(j^*M, Q)` and `j^*M` lies in `D_QCoh(𝒪_W)` (Stacks 08F4). -/
theorem coheratorDecomposable_derivedPushforward {W X : AlgebraicSpaces B S hS} (j : W ⟶ X)
    [(qcohDerivedProp B S hS W).IsTriangulated] (hj : IsEtale B S hS j.hom)
    (hW : (qcohDerivedProp B S hS W).ι.IsLeftAdjoint)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (α : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (hR : ∀ L, qcohDerivedProp B S hS W L → qcohDerivedProp B S hS X (R.obj L))
    (L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    coheratorDecomposable B S hS X (R.obj L) := by
  have hL : coheratorDecomposable B S hS W L := by
    rw [(coheratorDecomposable_eq_top_iff B S hS W).2 hW]; trivial
  obtain ⟨E, Q, a, b, c, hT, hE, hQ⟩ := hL
  have hres := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
  let adj : (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ⊣ R :=
    Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
      (etaleModulePullbackAdjunction B S hS j hj) R α hres
  let := Functor.IsRightDerivedFunctor.commShift R α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : R.IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor hres _ R α
  refine ⟨_, _, _, _, _, R.map_distinguished _ hT, hR E hE, ?_⟩
  intro M g hM
  have h0 : (adj.homEquiv M Q).symm g = 0 :=
    hQ _ (derivedQuasicoherent_etaleModulePullback B S hS j hj M hM)
  rw [← (adj.homEquiv M Q).apply_symm_apply g, h0, Adjunction.homEquiv_unit,
    Functor.map_zero, comp_zero]

end AlgebraicGeometry.Space

end
