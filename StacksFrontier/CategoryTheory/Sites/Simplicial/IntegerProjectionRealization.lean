module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLiftFace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionDerived
import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedPostnikov

/-!
# The face identity of Stacks 0D9K, against the transition of the realization

Let `S` be a simplicial-site situation and `K` a cartesian object of the derived category of
abelian sheaves on the total site. The Postnikov system of Stacks 0D9I reads its structure map
`X_q ⟶ X_p` as the derived tensor product of `K` with the structure map
`CategoryTheory.SimplicialSiteSituation.integerFace` of the integral resolution of Stacks 09WI,
and the identification `X_n = g_{n!}K_n` of Stacks 0D9E (1) is the comparison
`CategoryTheory.SimplicialSiteSituation.integerProjection`. This file relates them to
`CategoryTheory.SimplicialSiteSituation.realizationTermMap`, the transition of the realization
complex of Stacks 0D9L: the identity

  `integerProjection K q ≫ (- ⊗^L integerFace φ) = realizationTermMap φ ≫ integerProjection K p`

holds as soon as it holds after composing with `g_{q!}` of the derived transition of Stacks 07TF,
with `realizationTermMap φ` replaced by the transpose along `g_{q!} ⊣ g_q^{-1}` of the unit
followed by the derived transition.

## Main results

* `CategoryTheory.SimplicialSiteSituation.realizationTermMap_eq_homEquiv_symm_comp`: the
  transition of the realization of a cartesian system is `g_{q!}` of the inverse of the derived
  transition followed by the transpose of the unit followed by the derived transition.
* `CategoryTheory.SimplicialSiteSituation.derivedInverseImage_map_unit_comp_derivedTransition`:
  the unit followed by the derived transition is the derived functor of the `φ`-labelled leg of
  the sum formula of Stacks 09WG, followed by a compositor.
* `CategoryTheory.SimplicialSiteSituation`
  `.integerProjection_comp_derivedTensorFace_eq_realizationTermMap_of_comp`: the face identity of
  Stacks 0D9K against the transition of the realization follows from the same identity composed
  with `g_{q!}` of the derived transition.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.AbelianSheaves
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialSiteSituation

section Split

variable {S : SimplicialSiteSituation.{u}}
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- For a cartesian system `T`, the transition `g_{q!}T_q ⟶ g_{p!}T_p` of the realization at
`φ : p ⟶ q` is `g_{q!}` of the inverse of `T.map φ`, followed by the transpose along
`g_{q!} ⊣ g_q^{-1}` of the unit of `g_{p!} ⊣ g_p^{-1}` followed by the derived transition of
Stacks 07TF. -/
theorem realizationTermMap_eq_homEquiv_symm_comp (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {p q : SimplexCategory} (φ : p ⟶ q) :
    realizationTermMap T hT φ =
      (S.componentLowerShriekDerived q).map (@inv _ _ _ _ (T.map φ) (hT φ)) ≫
        ((S.componentLowerShriekDerivedAdjunction q).homEquiv
            ((derivedInverseImage S φ).obj (T.obj p)) (realizationTerm S T p)).symm
          ((derivedInverseImage S φ).map
              ((S.componentLowerShriekDerivedAdjunction p).unit.app (T.obj p)) ≫
            (derivedTransition S φ).app (realizationTerm S T p)) := by
  refine Eq.trans (Eq.trans
    (((S.componentLowerShriekDerivedAdjunction q).homEquiv (T.obj q)
      (realizationTerm S T p)).symm_apply_apply (realizationTermMap T hT φ)).symm
    (congrArg ((S.componentLowerShriekDerivedAdjunction q).homEquiv (T.obj q)
      (realizationTerm S T p)).symm (realizationTermMap_homEquiv T hT φ))) ?_
  exact (S.componentLowerShriekDerivedAdjunction q).homEquiv_naturality_left_symm _ _

section DerivedLeg

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.componentFunctorHasCoproductsOfShape
  CategoryTheory.SimplicialSiteSituation.abelianTransitionHasBiproduct

variable (S)

/-- The unit of the derived adjunction `g_{p!} ⊣ g_p^{-1}` followed by the derived transition of
Stacks 07TF is the derived functor of the `φ`-labelled leg of the sum formula of Stacks 09WG,
followed by the compositor of `g_{p!}` and `g_q^{-1}`. -/
theorem derivedInverseImage_map_unit_comp_derivedTransition {p q : SimplexCategory} (φ : p ⟶ q)
    (X : DerivedCategory (Sheaf (S.componentTopology p) Ab.{u})) :
    (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction p).unit.app X) ≫
        (derivedTransition S φ).app ((S.componentLowerShriekDerived p).obj X) =
      (derivedNatTrans (abelianTransition S φ)
            (componentLowerShriekAb S p ⋙ S.restrictAb q)
            (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
                (abelianTransition S φ) ≫
              Functor.whiskerLeft (componentLowerShriekAb S p)
                (S.abelianTransitionOfFiber' φ))).app X ≫
        (derivedCompIso (componentLowerShriekAb S p) (S.restrictAb q)
          (componentLowerShriekAb S p ⋙ S.restrictAb q) (Iso.refl _)).hom.app X := by
  refine Eq.trans (congr_app (derived_component_summand' S φ).symm X) ?_
  refine Eq.trans (NatTrans.comp_app _ _ X) ?_
  exact congrArg
    (fun α => (derivedNatTrans (abelianTransition S φ)
        (componentLowerShriekAb S p ⋙ S.restrictAb q) α).app X ≫
      (derivedCompIso (componentLowerShriekAb S p) (S.restrictAb q)
        (componentLowerShriekAb S p ⋙ S.restrictAb q) (Iso.refl _)).hom.app X)
    (S.componentLowerShriekBiproductIso_ι' φ)

end DerivedLeg

end Split

section Standard

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- The face identity of Stacks 0D9K against the transition of the realization, reduced to the
same identity composed with the derived transition: for a cartesian `K`, the comparison of
Stacks 0D9E in degree `q` followed by the derived tensor product with the structure map of the
integral resolution at `φ : p ⟶ q` is the transition of the realization of the associated
simplicial system of Stacks 0D9H followed by the comparison in degree `p`, as soon as the same
identity holds after composing with `g_{q!}` of the derived transition of Stacks 07TF and
replacing the transition of the realization by the transpose of the unit followed by the derived
transition. -/
theorem integerProjection_comp_derivedTensorFace_eq_realizationTermMap_of_comp
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (hK : S.IsCartesianDerived K)
    {p q : SimplexCategory} (φ : p ⟶ q)
    (h : (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫
          S.integerProjection K q ≫
            ((derivedTensor S.totalTopology).map
              ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                (integerFace S φ))).app K =
        ((S.componentLowerShriekDerivedAdjunction q).homEquiv
            ((derivedInverseImage S φ).obj ((derivedComponent S p).obj K))
            ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))).symm
            ((derivedInverseImage S φ).map
                ((S.componentLowerShriekDerivedAdjunction p).unit.app
                  ((derivedComponent S p).obj K)) ≫
              (derivedTransition S φ).app
                ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))) ≫
          S.integerProjection K p) :
    S.integerProjection K q ≫
        ((derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerFace S φ))).app K =
      realizationTermMap (S.associatedDerivedSystem K)
          (S.associatedDerivedSystem_cartesian K hK) φ ≫
        S.integerProjection K p := by
  have hiso : IsIso ((derivedTransition S φ).app K) := hK φ
  have hcancel : (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫
        realizationTermMap (S.associatedDerivedSystem K)
          (S.associatedDerivedSystem_cartesian K hK) φ =
      ((S.componentLowerShriekDerivedAdjunction q).homEquiv
          ((derivedInverseImage S φ).obj ((derivedComponent S p).obj K))
          ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))).symm
        ((derivedInverseImage S φ).map
            ((S.componentLowerShriekDerivedAdjunction p).unit.app
              ((derivedComponent S p).obj K)) ≫
          (derivedTransition S φ).app
            ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))) := by
    refine Eq.trans (congrArg
      (fun k => (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫ k)
      (realizationTermMap_eq_homEquiv_symm_comp (S.associatedDerivedSystem K)
        (S.associatedDerivedSystem_cartesian K hK) φ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ _)
      ((S.componentLowerShriekDerived q).map_comp ((derivedTransition S φ).app K) _).symm) ?_
    refine Eq.trans (congrArg (fun k => (S.componentLowerShriekDerived q).map k ≫ _)
      (IsIso.hom_inv_id _)) ?_
    refine Eq.trans (congrArg (fun k => k ≫ _)
      ((S.componentLowerShriekDerived q).map_id _)) ?_
    exact Category.id_comp _
  refine (cancel_epi ((S.componentLowerShriekDerived q).map
    ((derivedTransition S φ).app K))).1 (Eq.trans h ?_)
  refine Eq.trans (congrArg (fun k => k ≫ S.integerProjection K p) hcancel.symm) ?_
  exact Category.assoc _ _ _

end Standard

end CategoryTheory.SimplicialSiteSituation

end
