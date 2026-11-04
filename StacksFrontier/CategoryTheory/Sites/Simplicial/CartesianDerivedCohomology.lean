module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerived
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Cartesian derived abelian sheaves are those with cartesian cohomology

Let `S` be a simplicial-site situation. An object `K` of the derived category of abelian sheaves
on its total site is cartesian when every transition `f_φ⁻¹ Kₘ ⟶ Kₙ` is an isomorphism, and its
degree `q` cohomology `Hq(K)` is an abelian sheaf on the total site, cartesian when every
transition `f_φ⁻¹ Hq(K)ₘ ⟶ Hq(K)ₙ` is. This module proves that the two conditions determine
each other: `K` is cartesian exactly when all of its cohomology sheaves are.

## Main results

* `SimplicialSiteSituation.isIso_derivedComponentTransition_app_iff`: the derived transition is
  invertible at `K` exactly when the abelian transition is invertible at every cohomology sheaf of
  `K`.
* `SimplicialSiteSituation.isCartesianDerived_iff_forall_isCartesianAbSheaf_homology` is
  **Stacks 0D7L (1)**: a derived abelian sheaf is cartesian exactly when its cohomology is.

## Implementation notes

Restriction to a simplicial degree and the simplex transitions are exact, so the derived
transition `derivedComponentTransition` is the transition of a natural transformation of exact
functors, and `derivedComponentTransitionAux_app_Q` says that it agrees with the abelian
transition at the image of every cochain complex. That is exactly the hypothesis of
`CategoryTheory.Functor.isIso_app_iff_forall_isIso_app_homology`, which detects invertibility of
such a transition on cohomology; the general statement there is proved from the comparison of
cohomology with an exact functor and the fact that a morphism of a derived category is invertible
exactly when it is invertible on all cohomology objects. The passage from the composite
`derivedComponent' ⋙ derivedInverseImage` to the derived functor of the composite of the abelian
functors contributes only the isomorphism `derivedCompIso`, which is harmless for invertibility.

The passage from the abelian transition to the transition of the underlying sheaf of sets is
`abelianFiberTransition_isIso_iff`, so no computation of the underlying map is needed here.

Clause (2) of Stacks 0D7L, for modules over a sheaf of rings on the total site with flat face
morphisms, is `isCartesianDerivedModule_iff_forall_isCartesianModule_homology` in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomology`.

## References

* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] derivedCategoryTotal derivedCategoryComponent
attribute [local implicit_reducible] derivedInverseImage

section Transition

variable {m n : SimplexCategory} (φ : m ⟶ n)
  (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))

/-- The localization of the abelian transition is invertible at `K` exactly when the abelian
transition is invertible at every cohomology sheaf of `K`. -/
theorem isIso_derivedComponentTransitionAux_app_iff :
    IsIso ((derivedComponentTransitionAux S φ).app K) ↔
      ∀ q : ℤ, IsIso ((abelianComponentTransition S φ).app
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K)) :=
  Functor.isIso_app_iff_forall_isIso_app_homology (abelianComponentTransition S φ)
    (derivedComponentTransitionAux S φ) (derivedComponentTransitionAux_app_Q S φ) K

/-- The derived transition of Stacks 07TF is invertible at `K` exactly when the abelian transition
of Stacks 09WF is invertible at every cohomology sheaf of `K`. -/
theorem isIso_derivedComponentTransition_app_iff :
    IsIso ((derivedComponentTransition S φ).app K) ↔
      ∀ q : ℤ, IsIso ((abelianComponentTransition S φ).app
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K)) := by
  rw [← isIso_derivedComponentTransitionAux_app_iff, derivedComponentTransition_eq,
    NatTrans.comp_app, isIso_comp_left_iff]

end Transition

/-- **Stacks 0D7L (1).** An object of the derived category of abelian sheaves on the total site of
a simplicial site is cartesian if and only if all of its cohomology sheaves are cartesian abelian
sheaves. -/
@[stacks 0D7L "cartesian derived sheaves are those with cartesian cohomology"]
theorem isCartesianDerived_iff_forall_isCartesianAbSheaf_homology
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    IsCartesianDerived' S K ↔
      ∀ q : ℤ, IsCartesianAbSheaf S
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K) := by
  constructor
  · intro hK q _ _ φ
    exact (abelianFiberTransition_isIso_iff S φ _).1
      ((isIso_derivedComponentTransition_app_iff S φ K).1 (hK φ) q)
  · intro hH _ _ φ
    exact (isIso_derivedComponentTransition_app_iff S φ K).2 fun q ↦
      (abelianFiberTransition_isIso_iff S φ _).2 (hH q φ)

end CategoryTheory.SimplicialSiteSituation

end
