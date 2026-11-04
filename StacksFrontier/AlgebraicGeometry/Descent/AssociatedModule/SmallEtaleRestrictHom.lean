module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit

/-!
# Restriction to the small Zariski site is fully faithful on quasi-coherent modules

Let `B` be a big étale site containing a scheme `S`.  Restriction of sheaves of modules along the
inclusion of the small Zariski site of `S` into the small étale site,
`AlgebraicGeometry.SmallEtale.restrictModule`, is the right adjoint of the associated-module
functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4).  The counit of that adjunction is an isomorphism at every
quasi-coherent `𝒪`-module of the small étale site, by
`AlgebraicGeometry.SmallEtale.isIso_counit` together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`; so on the quasi-coherent modules
the right adjoint is fully faithful: on Hom-sets with quasi-coherent source the action of
`AlgebraicGeometry.SmallEtale.restrictModule` is a bijection.

## Main results

* `AlgebraicGeometry.SmallEtale.restrictModule_map_eq_homEquiv`: the action of the right adjoint
  on a morphism is the adjunction bijection applied to that morphism preceded by the counit.
  This is the right triangle identity of the adjunction.
* `AlgebraicGeometry.SmallEtale.bijective_restrictModule_map`: **restriction to the small Zariski
  site is bijective on morphisms out of a quasi-coherent module.**

## Implementation notes

Only the *source* has to be quasi-coherent: the counit is inverted at the source alone, the
target entering the adjunction bijection unrestricted.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The right adjoint on a morphism is the adjunction bijection of that morphism preceded by
the counit.**  This is the right triangle identity of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`. -/
theorem restrictModule_map_eq_homEquiv (G G' : SheafOfModules.{u} (structureSheaf B S hS))
    (ψ : G ⟶ G') :
    (restrictModule B S hS).map ψ =
      (associatedModuleAdjunction B S hS).homEquiv ((restrictModule B S hS).obj G) G'
        ((associatedModuleAdjunction B S hS).counit.app G ≫ ψ) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]

/-- **Restriction to the small Zariski site is bijective on morphisms out of a quasi-coherent
`𝒪`-module of the small étale site.** -/
theorem bijective_restrictModule_map (G G' : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsQuasicoherentOnSite) :
    Function.Bijective ((restrictModule B S hS).map : (G ⟶ G') → _) := by
  have hiso : IsIso ((associatedModuleAdjunction B S hS).counit.app G) :=
    isIso_counit B S hS G hG (isQuasicoherent_restrictModule B S hS G hG)
  have hpre : Function.Bijective
      (fun ψ : G ⟶ G' => (associatedModuleAdjunction B S hS).counit.app G ≫ ψ) := by
    refine ⟨fun ψ ψ' h => (cancel_epi _).1 h, fun t => ⟨inv
      ((associatedModuleAdjunction B S hS).counit.app G) ≫ t, ?_⟩⟩
    simp
  have hfun : ((restrictModule B S hS).map : (G ⟶ G') → _) =
      ((associatedModuleAdjunction B S hS).homEquiv ((restrictModule B S hS).obj G) G') ∘
        (fun ψ : G ⟶ G' => (associatedModuleAdjunction B S hS).counit.app G ≫ ψ) :=
    funext (restrictModule_map_eq_homEquiv B S hS G G')
  rw [hfun]
  exact (((associatedModuleAdjunction B S hS).homEquiv
    ((restrictModule B S hS).obj G) G').bijective).comp hpre

end AlgebraicGeometry.SmallEtale

end
