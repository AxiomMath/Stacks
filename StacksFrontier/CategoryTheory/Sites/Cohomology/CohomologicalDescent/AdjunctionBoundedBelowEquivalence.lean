module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.AdjunctionBoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BoundednessOfToposHom

/-!
# The bounded below equivalence for an abstract adjunction of derived categories

For an adjunction `L ⊣ R` between derived categories with `L` identified with the functor induced
by an exact functor `F` which restricts to an equivalence between weak Serre subcategories `𝒜'`
and `𝒜` compatibly with the unit, the adjunction restricts to an equivalence
`D^+_{𝒜'} ≌ D^+_𝒜`, as in Stacks 0D7U.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

/-! ### The argument for an abstract adjunction

The equivalence only uses an adjunction `L ⊣ R` of derived categories whose left adjoint is
identified with the functor induced by an exact functor `F` of abelian categories; the derived
adjunction of a morphism of ringed topoi along which pullback of modules is exact is one. The
statements are read off below for a morphism presented by sites, and in
`BoundedBelowEquivalenceOfToposHom.lean` for an arbitrary morphism of ringed topoi. -/

section Core

variable {𝒞 𝒞' : Type*} [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]
  [Category* 𝒞'] [Abelian 𝒞'] [HasDerivedCategory 𝒞']
  (F : 𝒞' ⥤ 𝒞) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {L : DerivedCategory 𝒞' ⥤ DerivedCategory 𝒞} {R : DerivedCategory 𝒞 ⥤ DerivedCategory 𝒞'}
  (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated] (eL : L ≅ F.mapDerivedCategory)
  (A : ObjectProperty 𝒞) (A' : ObjectProperty 𝒞') [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  (hA : ∀ M, A' M → A (F.obj M))

include hA eL in
omit [L.CommShift ℤ] [L.IsTriangulated] [A'.IsWeakSerreClass] in
/-- `L` carries `D⁺_{𝒜'}` into `D⁺_𝒜`: it preserves boundedness below, and its cohomology objects
are `F` of those of the source. -/
theorem derivedCategoryBPlus_obj_of_iso_adjunctionBoundedBelowEquivalence (K : DerivedCategory 𝒞')
    (hK : DerivedCategoryB.derivedCategoryBPlus A' K) :
    DerivedCategoryB.derivedCategoryBPlus A (L.obj K) := by
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1
  have hGE := isGE_obj_of_iso_adjunctionBoundedBelowDescent F eL K a ha
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨a, hGE⟩, fun q ↦ ?_⟩
  exact A.prop_of_iso (homologyObjIsoOfIsoAdjunctionBoundedBelowDescent F eL K q).symm
    (hA _ (hK.2 q))

/-- If `F` induces an equivalence `𝒜' ≌ 𝒜`, every `M` in `𝒜` is `F N` for some `N` in `𝒜'`. -/
private theorem exists_prop_and_nonempty_iso_obj_of_isEquivalence_lift
    {𝒞 𝒞' : Type*} [Category* 𝒞] [Category* 𝒞'] (F : 𝒞' ⥤ 𝒞) (A : ObjectProperty 𝒞)
    (A' : ObjectProperty 𝒞') (hA : ∀ M, A' M → A (F.obj M))
    (hEquiv : (A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)).IsEquivalence)
    (M : 𝒞) (hM : A M) : ∃ N, A' N ∧ Nonempty (F.obj N ≅ M) := by
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)) ⟨M, hM⟩
  exact ⟨N.obj, N.property, ⟨A.ι.mapIso e⟩⟩

variable (hEquiv : (A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso (adj.unit.app ((DerivedCategory.singleFunctor 𝒞' 0).obj M)))

include hEquiv hUnit eL

omit [L.CommShift ℤ] [L.IsTriangulated] [A.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the object `R ℱ` is the object of `𝒜'` whose image under `F` is `ℱ`.** -/
theorem derivedCategoryBPlus_obj_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence
    (M : 𝒞) (hM : A M) :
    DerivedCategoryB.derivedCategoryBPlus A'
      (R.obj ((DerivedCategory.singleFunctor 𝒞 0).obj M)) := by
  obtain ⟨N, hN', ⟨e⟩⟩ :=
    exists_prop_and_nonempty_iso_obj_of_isEquivalence_lift F A A' hA hEquiv M hM
  have hN := hUnit N hN'
  have eL' := singleFunctorObjIsoOfIsoAdjunctionBoundedBelowDescent F eL N ≪≫
    (DerivedCategory.singleFunctor 𝒞 0).mapIso e
  have eR := (@asIso _ _ _ _ _ hN).trans (R.mapIso eL')
  exact (DerivedCategoryB.derivedCategoryBPlus_isClosedUnderIsomorphisms A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A')).of_iso eR
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') N hN')

omit [L.CommShift ℤ] [L.IsTriangulated] [A.IsWeakSerreClass] [A'.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the counit `L R ℱ ⟶ ℱ` is invertible.** Write `ℱ = F ℱ'`; then `ℱ` in
degree zero is `L` of `ℱ'` in degree zero, at which the unit is invertible. -/
theorem isIso_counit_app_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence
    (M : 𝒞) (hM : A M) :
    IsIso (adj.counit.app ((DerivedCategory.singleFunctor 𝒞 0).obj M)) := by
  obtain ⟨N, hN', ⟨e⟩⟩ :=
    exists_prop_and_nonempty_iso_obj_of_isEquivalence_lift F A A' hA hEquiv M hM
  have hN := hUnit N hN'
  have eL' := singleFunctorObjIsoOfIsoAdjunctionBoundedBelowDescent F eL N ≪≫
    (DerivedCategory.singleFunctor 𝒞 0).mapIso e
  have hcounit := Adjunction.isIso_counit_app_obj_of_isIso_unit_app adj _ hN
  exact (NatTrans.isIso_app_iff_of_iso adj.counit eL').mp hcounit

omit [A.IsWeakSerreClass] in
/-- `R` carries `D⁺_𝒜` into `D⁺_{𝒜'}`: it is exact, it preserves boundedness below, and it carries
the cohomology objects of its argument, placed in degree zero, into `D⁺_{𝒜'}`. -/
theorem derivedCategoryBPlus_rightAdjoint_obj_of_iso_adjunctionBoundedBelowEquivalence
    (K : DerivedCategory 𝒞)
    (hK : DerivedCategoryB.derivedCategoryBPlus A K) :
    DerivedCategoryB.derivedCategoryBPlus A' (R.obj K) := by
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  let : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1
  refine DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE R A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A')
    (DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom adj
      (isLE_obj_of_iso_adjunctionBoundedBelowDescent F eL)) K a ha
    fun q ↦ ?_
  exact derivedCategoryBPlus_obj_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence F adj eL
    A A' hA hEquiv hUnit _ (hK.2 q)

/-- **The restriction of an adjunction `L ⊣ R` as above to the bounded below subcategories.** -/
noncomputable def adjunctionBoundedBelowOfIsoAdjunctionBoundedBelowEquivalence :
    (DerivedCategoryB.derivedCategoryBPlus A).lift
        ((DerivedCategoryB.derivedCategoryBPlus A').ι ⋙ L)
        (fun K ↦ derivedCategoryBPlus_obj_of_iso_adjunctionBoundedBelowEquivalence F eL A A' hA
          K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryBPlus A').lift
        ((DerivedCategoryB.derivedCategoryBPlus A).ι ⋙ R)
        (fun K ↦ derivedCategoryBPlus_rightAdjoint_obj_of_iso_adjunctionBoundedBelowEquivalence
          F adj eL A A' hA hEquiv hUnit K.obj K.property) :=
  adj.restrictFullyFaithful
    (DerivedCategoryB.derivedCategoryBPlus A').fullyFaithfulι
    (DerivedCategoryB.derivedCategoryBPlus A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

omit hUnit in
/-- **The equivalence `D⁺_{𝒜'} ≌ D⁺_𝒜` for an abstract adjunction**, granted that the unit is
invertible on `D⁺_{𝒜'}` and the counit on `D⁺_𝒜`: both restricted adjoints are then fully
faithful. -/
noncomputable def equivalenceBoundedBelowOfIsoAdjunctionBoundedBelowEquivalence
    (hUnitPlus : DerivedCategoryB.derivedCategoryBPlus A' ≤ adj.unitIsIso)
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤ adj.counitIsIso) :
    (DerivedCategoryB.derivedCategoryBPlus A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus A).FullSubcategory :=
  letI hL := adj.fullyFaithfulιCompLeftAdjointOfLE hUnitPlus
  letI hR := adj.fullyFaithfulιCompRightAdjointOfLE hCounitPlus
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (adjunctionBoundedBelowOfIsoAdjunctionBoundedBelowEquivalence F adj eL A A' hA hEquiv
    (fun M hM ↦ hUnitPlus _ (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') M hM))).toEquivalence

/-- **Stacks 0D7U for an abstract adjunction.** For an adjunction `L ⊣ R` of derived categories
with `L` identified with the functor induced by an exact functor `F`, and weak Serre
subcategories `𝒜 ⊂ 𝒞`, `𝒜' ⊂ 𝒞'` such that `F` induces an equivalence `𝒜' ⟶ 𝒜` and the unit is
invertible on `𝒜'`, the left adjoint restricts to an equivalence `D⁺_{𝒜'} ≌ D⁺_𝒜`, with
quasi-inverse the restriction of `R`. The unit propagates to `D⁺_{𝒜'}` and the counit to `D⁺_𝒜`
by the abstract forms of Tags 0D7T and 0D7S. -/
noncomputable def equivalenceBoundedBelowAdjunctionBoundedBelowEquivalence :
    (DerivedCategoryB.derivedCategoryBPlus A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus A).FullSubcategory :=
  have hRGE := DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom adj
    (isLE_obj_of_iso_adjunctionBoundedBelowDescent F eL)
  equivalenceBoundedBelowOfIsoAdjunctionBoundedBelowEquivalence F adj eL A A' hA hEquiv
    (fun K hK ↦ isIso_unit_app_of_isIso_homology_adjunctionBoundedBelowDescent adj
      (isGE_obj_of_iso_adjunctionBoundedBelowDescent F eL) hRGE K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦ hUnit _ (hK.2 q))
    (fun K hK ↦ isIso_counit_app_of_isIso_homology_adjunctionBoundedBelowDescent adj
      (isGE_obj_of_iso_adjunctionBoundedBelowDescent F eL) hRGE K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦
        isIso_counit_app_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence F adj eL A A'
          hA hEquiv hUnit _ (hK.2 q))

end Core

end Stacks.Cohomology.CohomologicalDescent

end
