module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackExactness
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Bounded below descent for an abstract adjunction of derived categories

For an adjunction `L ⊣ R` between derived categories whose left adjoint is exact and whose two
adjoints preserve boundedness below, the unit and the counit are invertible at a bounded below
object as soon as they are invertible at each of its cohomology objects placed in degree zero
(the arguments of Stacks 0D7T and 0D7S). A functor identified with the one induced by an exact
functor of abelian categories preserves boundedness below and above.

## References

* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

/-! ### The argument for an abstract adjunction

Everything below is about an adjunction `L ⊣ R` between derived categories whose left adjoint
is exact and commutes with the shift, and whose two functors preserve boundedness below; the
derived pullback of a morphism along which degreewise pullback is exact is one, and its
computation as degreewise pullback is the content of the second half of this section. The
statements are read off at the end for a morphism of ringed topoi presented by sites, and in
`BoundedBelowDescentOfToposHom.lean` for an arbitrary morphism of ringed topoi. -/

section Core

variable {𝒞 𝒞' : Type*} [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]
  [Category* 𝒞'] [Abelian 𝒞'] [HasDerivedCategory 𝒞']
  {L : DerivedCategory 𝒞' ⥤ DerivedCategory 𝒞} {R : DerivedCategory 𝒞 ⥤ DerivedCategory 𝒞'}

section Adjunction

variable (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated]
  (hL : ∀ (K : DerivedCategory 𝒞') (n : ℤ), K.IsGE n → (L.obj K).IsGE n)
  (hR : ∀ (K : DerivedCategory 𝒞) (n : ℤ), K.IsGE n → (R.obj K).IsGE n)

include hL hR in
/-- **Stacks 0D7T for an abstract adjunction.** If `L` is exact and both adjoints preserve
boundedness below, the unit of `L ⊣ R` is invertible at a bounded below `K` as soon as it is
invertible at each cohomology object of `K` placed in degree zero. -/
theorem isIso_unit_app_of_isIso_homology_adjunctionBoundedBelowDescent (K : DerivedCategory 𝒞')
    (hK : DerivedCategory.TStructure.t.plus K)
    (hH : ∀ q : ℤ, IsIso (adj.unit.app ((DerivedCategory.singleFunctor 𝒞' 0).obj
      ((DerivedCategory.homologyFunctor 𝒞' q).obj K)))) :
    IsIso (adj.unit.app K) := by
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  obtain ⟨a, hGE⟩ := hK
  exact NatTrans.isIso_app_of_isGE adj.unit (fun _ _ h ↦ h)
    (fun M m h ↦ hR _ m (hL M m h)) K a hGE hH

include hL hR in
/-- **Stacks 0D7S for an abstract adjunction.** Dually, the counit of `L ⊣ R` is invertible at a
bounded below `K` as soon as it is invertible at each cohomology object of `K` placed in degree
zero. -/
theorem isIso_counit_app_of_isIso_homology_adjunctionBoundedBelowDescent (K : DerivedCategory 𝒞)
    (hK : DerivedCategory.TStructure.t.plus K)
    (hH : ∀ q : ℤ, IsIso (adj.counit.app ((DerivedCategory.singleFunctor 𝒞 0).obj
      ((DerivedCategory.homologyFunctor 𝒞 q).obj K)))) :
    IsIso (adj.counit.app K) := by
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  obtain ⟨a, hGE⟩ := hK
  exact NatTrans.isIso_app_of_isGE adj.counit
    (fun M m h ↦ hL _ m (hR M m h)) (fun _ _ h ↦ h) K a hGE hH

end Adjunction

/-! #### A functor induced by an exact functor of abelian categories -/

variable (F : 𝒞' ⥤ 𝒞) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (eL : L ≅ F.mapDerivedCategory)

/-- **`H^q(L-)` is `F H^q(-)`, naturally**, for a functor `L` identified with the functor induced
on derived categories by the exact functor `F`. -/
noncomputable def compHomologyFunctorIsoOfIsoAdjunctionBoundedBelowDescent (q : ℤ) :
    L ⋙ DerivedCategory.homologyFunctor 𝒞 q ≅ DerivedCategory.homologyFunctor 𝒞' q ⋙ F :=
  Functor.isoWhiskerRight eL (DerivedCategory.homologyFunctor 𝒞 q) ≪≫
    StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F q

/-- `H^q(L K)` is `F H^q(K)`. -/
noncomputable def homologyObjIsoOfIsoAdjunctionBoundedBelowDescent (K : DerivedCategory 𝒞')
    (q : ℤ) :
    (DerivedCategory.homologyFunctor 𝒞 q).obj (L.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor 𝒞' q).obj K) :=
  (compHomologyFunctorIsoOfIsoAdjunctionBoundedBelowDescent F eL q).app K

/-- `L` of an object placed in degree zero is `F` of it, placed in degree zero. -/
noncomputable def singleFunctorObjIsoOfIsoAdjunctionBoundedBelowDescent (M : 𝒞') :
    L.obj ((DerivedCategory.singleFunctor 𝒞' 0).obj M) ≅
      (DerivedCategory.singleFunctor 𝒞 0).obj (F.obj M) :=
  eL.app _ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app M

include eL in
/-- A functor identified with the one induced by an exact functor preserves boundedness
below. -/
theorem isGE_obj_of_iso_adjunctionBoundedBelowDescent (K : DerivedCategory 𝒞') (n : ℤ)
    (hK : K.IsGE n) : (L.obj K).IsGE n := by
  have := hK
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isGE K n i hi)).of_iso
    (homologyObjIsoOfIsoAdjunctionBoundedBelowDescent F eL K i)

include eL in
/-- A functor identified with the one induced by an exact functor preserves boundedness
above. -/
theorem isLE_obj_of_iso_adjunctionBoundedBelowDescent (K : DerivedCategory 𝒞') (n : ℤ)
    (hK : K.IsLE n) : (L.obj K).IsLE n := by
  have := hK
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE K n i hi)).of_iso
    (homologyObjIsoOfIsoAdjunctionBoundedBelowDescent F eL K i)

end Core

end Stacks.Cohomology.CohomologicalDescent

end
