module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift

/-!
# The comparison `RU₁ ⋙ RU₂ ≅ RU` of exact functors commutes with the shift

For exact functors `U₁ : 𝒜 ⥤ ℬ`, `U₂ : ℬ ⥤ 𝒞`, `U : 𝒜 ⥤ 𝒞` and an isomorphism `c : U₁ ⋙ U₂ ≅ U`,
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact` is the comparison
`RU₁ ⋙ RU₂ ≅ RU` of bounded below right derived functors. This file proves that it is compatible
with the shift by `ℤ`, so that it carries distinguished triangles to isomorphic ones and commutes
with the connecting morphisms of the homology sequence.

Both factors of the comparison are descents along the unit of a right derived functor — the
canonical transformation `R(U₁ ⋙ U₂) ⟶ RU₁ ⋙ RU₂` of [Stacks, Tag 05T2], and the invariance of
`R(-)` under the isomorphism `c` — and the descent of a shift-compatible transformation is
shift-compatible (`Stacks.Triangulated.natTransCommShift_rightDerivedDesc`).

## Main results

* `CategoryTheory.Functor.natTransCommShift_rightDerivedFunctorPlusNatIso` — the invariance
  isomorphism `RF ≅ RG` of an isomorphism `F ≅ G` commutes with the shift.
* `CategoryTheory.Functor.natTransCommShift_rightDerivedFunctorPlusCompIsoOfExact` — the
  comparison `RU₁ ⋙ RU₂ ≅ RU` commutes with the shift.

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory.Functor

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

section NatIso

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  [EnoughInjectives A]

/-- **The invariance isomorphism `RF ≅ RG` of an isomorphism `F ≅ G` commutes with the shift.**
It is the descent along the unit of `RF` of the degreewise action of `F ≅ G` followed by the unit
of `RG`, both of which commute with the shift. -/
public theorem natTransCommShift_rightDerivedFunctorPlusNatIso {F G : A ⥤ B} [F.Additive]
    [G.Additive] (e : F ≅ G) :
    NatTrans.CommShift (rightDerivedFunctorPlusNatIso e).hom ℤ := by
  have h₀ : NatTrans.CommShift (mapHomotopyCategoryPlusNatIso e).hom ℤ := by
    rw [mapHomotopyCategoryPlusNatIso_hom]
    exact Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus e.hom
  have h₁ : NatTrans.CommShift
      (isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerRight (mapHomotopyCategoryPlusNatIso e).hom DerivedCategory.Plus.Qh) ℤ)
  have h₂ : NatTrans.CommShift G.rightDerivedFunctorPlusUnit ℤ := inferInstance
  have h₃ : NatTrans.CommShift
      ((isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).hom ≫
        G.rightDerivedFunctorPlusUnit) ℤ := NatTrans.CommShift.comp _ _ ℤ
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _
    (HomotopyCategory.Plus.quasiIso A) ℤ _ _

end NatIso

section Exact

variable {C₀ : Type u} {C₁ : Type u'} {C₂ : Type u''}
  [Category.{v} C₀] [Category.{v'} C₁] [Category.{v''} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory.{w} C₀] [HasDerivedCategory.{w'} C₁] [HasDerivedCategory.{w''} C₂]
  [EnoughInjectives C₀] [EnoughInjectives C₁]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The comparison `RU₁ ⋙ RU₂ ≅ RU` of exact functors commutes with the shift.** It is the
inverse of the canonical transformation of [Stacks, Tag 05T2] followed by the invariance
isomorphism of `c`, each of which commutes with the shift. -/
public theorem natTransCommShift_rightDerivedFunctorPlusCompIsoOfExact :
    NatTrans.CommShift (rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom ℤ := by
  have h₁ : NatTrans.CommShift (rightDerivedFunctorPlusCompIsoOfRightAcyclic U₁ U₂
      (fun I _ => U₂.rightAcyclic_of_exact (U₁.obj I))).hom ℤ :=
    natTransCommShift_rightDerivedFunctorPlusComp U₁ U₂
  have h₂ := natTransCommShift_rightDerivedFunctorPlusNatIso c
  rw [rightDerivedFunctorPlusCompIsoOfExact_hom]
  infer_instance

end Exact

end CategoryTheory.Functor

end
