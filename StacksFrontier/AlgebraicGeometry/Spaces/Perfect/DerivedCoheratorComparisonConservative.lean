module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardSquareCanonical
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The comparison functor of an algebraic space is conservative

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The comparison
functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 reflects isomorphisms, and it is an
equivalence as soon as the counit of its adjunction with the derived coherator `RQ_X` restricted
to `D_QCoh(𝒪_X)` is invertible.  On an affine algebraic space that counit is invertible.

## Main results

* `AlgebraicGeometry.Space.reflectsIsomorphisms_mapDerivedCategory_quasicoherentSheavesι`: the
  functor of derived categories induced by `ι` reflects isomorphisms.
* `AlgebraicGeometry.Space.reflectsIsomorphisms_quasicoherentDerivedComparison`: the comparison
  functor of Stacks 08F1 reflects isomorphisms.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentDerivedComparison_of_isIso_counit`: the
  comparison functor is an equivalence as soon as the counit of `i_X ⊣ J ⋙ RQ_X` is invertible.
* `AlgebraicGeometry.Space.isIso_comparisonCompιDerivedCoheratorCounit_of_isAffineSpace`: on an
  affine algebraic space the counit of `i_X ⋙ J ⊣ RQ_X` is invertible at every object of
  `D(𝒪_X)` with quasi-coherent cohomology.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompι_commShift` and
  `AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompι_isTriangulated`: `i_X ⋙ J` is an
  exact functor of triangulated categories.
* `AlgebraicGeometry.Space.isIso_comparisonCompιDerivedCoheratorCounit_app_of_isZero` and
  `AlgebraicGeometry.Space.isIso_comparisonCompιDerivedCoheratorCounit_app₁_of_app₂₃`: the counit
  of `i_X ⋙ J ⊣ RQ_X` is invertible at a zero object, and at the first vertex of a distinguished
  triangle as soon as it is invertible at the other two.

## References

* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

section Conservative

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)`. -/
private abbrev qcSheavesι :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι

/-- The inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
private abbrev derivedQcι :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).ι

/-- **The functor of derived categories induced by `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` reflects
isomorphisms.** -/
theorem reflectsIsomorphisms_mapDerivedCategory_quasicoherentSheavesι :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).ι.mapDerivedCategory.ReflectsIsomorphisms := by
  constructor
  intro A A' f hf
  rw [DerivedCategory.isIso_iff] at hf ⊢
  intro n
  have : IsIso ((qcSheavesι B S hS F hF).map
      ((DerivedCategory.homologyFunctor (QuasicoherentSheaves.{u, u} B S hS F hF) n).map f)) :=
    (NatIso.isIso_map_iff (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (qcSheavesι B S hS F hF) n) f).1 (hf n)
  exact isIso_of_reflects_iso _ (qcSheavesι B S hS F hF)

/-- **The comparison functor of Stacks 08F1 reflects isomorphisms.** -/
theorem reflectsIsomorphisms_quasicoherentDerivedComparison :
    (quasicoherentDerivedComparison B S hS F hF).ReflectsIsomorphisms := by
  have := reflectsIsomorphisms_mapDerivedCategory_quasicoherentSheavesι B S hS F hF
  constructor
  intro A A' f hf
  have : IsIso ((qcSheavesι B S hS F hF).mapDerivedCategory.map f) := by
    refine (NatIso.isIso_map_iff (quasicoherentDerivedComparisonCompιIso B S hS F hF) f).1 ?_
    change IsIso ((derivedQcι B S hS F hF).map
      ((quasicoherentDerivedComparison B S hS F hF).map f))
    infer_instance
  exact isIso_of_reflects_iso f (qcSheavesι B S hS F hF).mapDerivedCategory

/-- **The comparison functor of Stacks 08F1 is an equivalence as soon as the counit of its
adjunction with the derived coherator is invertible.** -/
theorem isEquivalence_quasicoherentDerivedComparison_of_isIso_counit
    (hcounit : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS F hF,
      IsIso ((comparisonDerivedCoheratorAdjunctionOfCoherator B S hS F hF).counit.app E)) :
    (quasicoherentDerivedComparison B S hS F hF).IsEquivalence := by
  have := reflectsIsomorphisms_quasicoherentDerivedComparison B S hS F hF
  have := NatIso.isIso_of_isIso_app
    (comparisonDerivedCoheratorAdjunctionOfCoherator B S hS F hF).counit
  exact Stacks.DerivedQCoh.isEquivalence_of_reflectsIsomorphisms_of_isIso_counit
    (comparisonDerivedCoheratorAdjunctionOfCoherator B S hS F hF)

end Conservative

section Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **On an affine algebraic space the counit of `i_X ⋙ J ⊣ RQ_X` is invertible at every object
of `D(𝒪_X)` with quasi-coherent cohomology.** -/
theorem isIso_comparisonCompιDerivedCoheratorCounit_of_isAffineSpace
    (Z : AlgebraicSpaces B S hS) (hZ : IsAffineSpace B S hS Z.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2) :
    IsIso ((comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit.app
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι.obj E)) := by
  have := isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace B S hS Z.1 Z.2 hZ
  exact Stacks.DerivedQCoh.isIso_counit_app_of_restrictFullyFaithful
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z)
    (F' := quasicoherentDerivedComparison B S hS Z.1 Z.2)
    (G' := derivedQcι B S hS Z.1 Z.2 ⋙ derivedCoherator B S hS Z.1 Z.2)
    (Functor.FullyFaithful.id _)
    (Functor.FullyFaithful.ofFullyFaithful (derivedQcι B S hS Z.1 Z.2))
    (Functor.leftUnitor _) (Functor.rightUnitor _).symm E

end Affine

/-! ### The counit is a transformation of exact functors of triangulated categories -/

section Triangulated

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Z : AlgebraicSpaces B S hS)

/-- The shift-compatibility of the comparison functor of Stacks 08F1 followed by the inclusion of
`D_QCoh(𝒪_Z)`, transported from the functor of derived categories induced by the exact inclusion
`ι : QCoh(𝒪_Z) ⥤ Mod(𝒪_Z)`. -/
@[instance_reducible]
instance quasicoherentDerivedComparisonCompι_commShift :
    (quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι).CommShift ℤ :=
  Functor.CommShift.ofIso (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2).symm ℤ

/-- **The comparison functor of Stacks 08F1 followed by the inclusion of `D_QCoh(𝒪_Z)` is an
exact functor of triangulated categories.** -/
instance quasicoherentDerivedComparisonCompι_isTriangulated :
    (quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι).IsTriangulated :=
  haveI : NatTrans.CommShift
      (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2).symm ℤ
  Functor.isTriangulated_of_iso (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2).symm

/-- The counit of `i_Z ⋙ J ⊣ RQ_Z` is invertible at a zero object. -/
theorem isIso_comparisonCompιDerivedCoheratorCounit_app_of_isZero
    (E : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (hE : IsZero E) :
    IsIso ((comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit.app E) :=
  let : (derivedCoherator B S hS Z.1 Z.2).Additive :=
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).right_adjoint_additive
  ((derivedCoherator B S hS Z.1 Z.2 ⋙ (quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
    derivedQcι B S hS Z.1 Z.2)).map_isZero hE).isIso hE _

/-- **The counit of `i_Z ⋙ J ⊣ RQ_Z` is invertible at the first vertex of a distinguished
triangle as soon as it is invertible at the other two.** -/
theorem isIso_comparisonCompιDerivedCoheratorCounit_app₁_of_app₂₃
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)))
    (hT : T ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)))
    (h₂ : IsIso ((comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit.app T.obj₂))
    (h₃ : IsIso ((comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit.app T.obj₃)) :
    IsIso ((comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit.app T.obj₁) := by
  let : (derivedCoherator B S hS Z.1 Z.2).CommShift ℤ :=
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).rightAdjointCommShift ℤ
  let : (comparisonCompιDerivedCoheratorAdjunction B S hS Z).CommShift ℤ :=
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).commShift_of_leftAdjoint ℤ
  let : (derivedCoherator B S hS Z.1 Z.2).IsTriangulated :=
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).isTriangulated_rightAdjoint
  let : (derivedCoherator B S hS Z.1 Z.2).Additive :=
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).right_adjoint_additive
  exact Stacks.DerivedQCoh.isIso_app₁_of_isIso_app₂₃
    (derivedCoherator B S hS Z.1 Z.2 ⋙ (quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
      derivedQcι B S hS Z.1 Z.2)) (𝟭 _)
    (comparisonCompιDerivedCoheratorAdjunction B S hS Z).counit T hT h₂ h₃

end Triangulated

end AlgebraicGeometry.Space

end
