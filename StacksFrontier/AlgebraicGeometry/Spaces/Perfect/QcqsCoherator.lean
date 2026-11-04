module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcqsDerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine

/-!
# The derived coherator of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`.  **Stacks
0CR4** asserts that the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint.  This file proves
it by the source's first proof.

By Derived Categories, Lemma 0CQS the right adjoint exists if and only if every object `K` of
`D(𝒪_X)` is decomposable: it sits in a distinguished triangle `E' ⟶ K ⟶ Q ⟶ E'[1]` with `E'` in
`D_QCoh(𝒪_X)` and `Q` right orthogonal to `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.coheratorDecomposable_eq_top_iff`).  The decomposable objects form a
triangulated subcategory (Lemma 0CQR), so the induction principle of Stacks 08GP together with
the relative Mayer–Vietoris triangle of Stacks 08JK reduces to showing that `Rj_*L` is
decomposable for `j : Y ⟶ X` étale with `Y` affine and `L` in `D(𝒪_Y)`
(`AlgebraicGeometry.Space.prop_derivedPushforward_of_affine`).  That is the source's last
paragraph (`AlgebraicGeometry.Space.coheratorDecomposable_derivedPushforward`), with its two
inputs:

* the lemma for the affine `Y`, which the source deduces from Stacks 08H0 and 071Q:
  `AlgebraicGeometry.Space.isLeftAdjoint_qcohDerivedProp_ι_of_isAffineSpace`, Stacks 0CR0 for the
  underlying affine scheme moved along `ε^*` (Stacks 071Q) and the identification of small étale
  sites;
* `Rj_*` carries `D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_X)`, which the source cites as Stacks 08FA:
  `AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_qcqs`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs`: **Stacks 0CR4**.

## References

* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks Project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

/-- Stacks 0CR4 for an algebraic space given as an object of `AlgebraicSpaces`. -/
theorem isLeftAdjoint_qcohDerivedProp_ι_of_qcqs
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hFqc : IsQuasiCompactSpace B S hS X.1) (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    (qcohDerivedProp B S hS X).ι.IsLeftAdjoint := by
  have := qcohDerivedProp_isTriangulated B S hS X
  have := coheratorDecomposable_isTriangulated B S hS X
  refine (coheratorDecomposable_eq_top_iff B S hS X).1 (eq_top_iff.2 fun K _ => ?_)
  let e : 𝟭 (Modules.{u, u} B S hS X.1 X.2) ⋙ modulePushforward B S hS (𝟙 X) ≅
      𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
    Functor.leftUnitor _ ≪≫ modulePushforwardIdIso B S hS X
  let eHC : (modulePushforward B S hS (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryIdIso
        (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
      Functor.mapHomotopyCategoryIdIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)
  let e' : DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) ≅
      (modulePushforward B S hS (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
    (Functor.isoWhiskerRight eHC DerivedCategory.Qh).symm
  have hR : (𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))).IsRightDerivedFunctor e'.inv
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ e'
  exact prop_derivedPushforward_of_affine B S hS hZ hFqc hFqs (𝟙 X)
    (coheratorDecomposable B S hS X) (fun _ => ⊤) (fun _ _ _ _ => trivial)
    (fun Y y hy hYaff L _ R α hRα => by
      have := hRα
      exact coheratorDecomposable_derivedPushforward B S hS (y ≫ 𝟙 X)
        (isEtale_comp B S hS hy (isEtale_of_isIso B S hS (𝟙 X.1)))
        (isLeftAdjoint_qcohDerivedProp_ι_of_isAffineSpace B S hS Y hYaff) R α
        (fun M hM => qcohDerivedProp_derivedPushforward_of_qcqs B S hS hZ
          hYaff.isQuasiCompactSpace
          (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ Y.1
            (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hYaff)) hFqs (y ≫ 𝟙 X) R α M hM) L)
    K trivial (𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) e'.inv

/-- **Stacks 0CR4.**  Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`.  The inclusion functor `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint.

The proof is the source's first one; see the module documentation.  The conclusion is
`CategoryTheory.Functor.IsLeftAdjoint`, the existence of a right adjoint, which is what the tag
asserts. -/
@[stacks 0CR4]
theorem quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hFqc : IsQuasiCompactSpace B S hS F) (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    (qcohDerivedProp B S hS ⟨F, hF⟩).ι.IsLeftAdjoint :=
  isLeftAdjoint_qcohDerivedProp_ι_of_qcqs B S hS hZ ⟨F, hF⟩ hFqc hFqs

end AlgebraicGeometry.Space

end
