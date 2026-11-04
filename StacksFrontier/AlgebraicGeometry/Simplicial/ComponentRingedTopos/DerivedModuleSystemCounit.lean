module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealization

/-!
# Transposes of a morphism of simplicial systems, restricted to a component

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site, with flat structure-sheaf transitions. For objects `K`, `K'` of `D(O)` and a morphism
`f : {K_n} ⟶ {K'_n}` of their associated simplicial systems of Stacks 0D9P, the component
`f_m : K_m ⟶ K'_m` in degree `m` has a transpose `Lg_{m!}K_m ⟶ K'` along the derived adjunction
`Lg_{m!} ⊣ Lg_m^*`. This file computes the restriction of that transpose to any degree `n`:

`Lg_n^*(f_m^♭) = Lg_n^*(ε_K) ≫ f_n`,

where `ε_K : Lg_{m!}K_m ⟶ K` is the counit. In words: after restriction to a component, the
transpose of `f_m` factors through the counit at `K`, followed by the component of `f` in that
degree. No cartesianness is needed.

The proof reads both sides on the summands of the direct-sum formula
`Lg_n^*Lg_{m!}K_m = ⨁_{ψ : [m] ⟶ [n]} Lf_ψ^*K_m` of Stacks 0D72 (6), whose summand inclusions are
the canonical legs (`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`). On
the leg at `ψ`, the left-hand side becomes `Lf_ψ^*(f_m)` followed by the transition of `K'`, and
the right-hand side the transition of `K` followed by `f_n`; these agree because `f` is a morphism
of simplicial systems.

## Main results

* `CategoryTheory.SimplicialSiteSituation`
  `.derivedTransitionPullback_map_unit_comp_map_homEquiv_symm`:
  the canonical leg at `ψ`, followed by the restriction of a transpose, is the derived pullback
  of the map it transposes followed by the derived transition.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_map_homEquiv_symm`:
  **the restriction to degree `n` of the transpose of `f_m` is the restriction of the counit
  followed by `f_n`.**

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology CommRingCat.{u}}

/-- **The canonical leg of Stacks 0D72 (6), followed by the restriction of a transpose.** For a
map `a : X ⟶ K'_m` with transpose `a^♭ : Lg_{m!}X ⟶ K'`, the leg
`Lf_ψ^*X ⟶ Lf_ψ^*Lg_m^*Lg_{m!}X ⟶ Lg_n^*Lg_{m!}X` at a simplex map `ψ : [m] ⟶ [n]`, followed by
`Lg_n^*(a^♭)`, is `Lf_ψ^*(a)` followed by the derived transition of `K'`. This is the naturality
of the derived transition and the triangle identity of the adjunction. -/
theorem derivedTransitionPullback_map_unit_comp_map_homEquiv_symm {m n : SimplexCategory}
    (hflat : ∀ (k : SimplexCategory) (φ : m ⟶ k), (S.transitionRingedToposHom O φ).IsFlat)
    {X : DerivedCategory (S.componentRingedTopos O m).Modules}
    {K' : DerivedCategory (S.totalRingedTopos O).Modules}
    (a : X ⟶ (S.derivedComponentModuleRestriction O m).obj K') (ψ : m ⟶ n) :
    (S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekDerivedAdjunction O m hflat).unit.app X) ≫
        (S.derivedComponentModuleTransition O ψ).app
            ((S.componentModuleLowerShriekDerived O m hflat).obj X) ≫
          (S.derivedComponentModuleRestriction O n).map
            (((S.componentModuleLowerShriekDerivedAdjunction O m hflat).homEquiv X K').symm a) =
      (S.derivedTransitionPullback O ψ).map a ≫
        (S.derivedComponentModuleTransition O ψ).app K' :=
  (congrArg (fun k => (S.derivedTransitionPullback O ψ).map
      ((S.componentModuleLowerShriekDerivedAdjunction O m hflat).unit.app X) ≫ k)
    ((S.derivedComponentModuleTransition O ψ).naturality
      (((S.componentModuleLowerShriekDerivedAdjunction O m hflat).homEquiv X K').symm
        a)).symm).trans
  ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (S.derivedComponentModuleTransition O ψ).app K')
      (((S.derivedTransitionPullback O ψ).map_comp _ _).symm.trans
        (congrArg (S.derivedTransitionPullback O ψ).map
          (((S.componentModuleLowerShriekDerivedAdjunction O m hflat).homEquiv_unit _ _
            _).symm.trans
            (Equiv.apply_symm_apply _ _))))))

/-- The comparison of two maps out of a biproduct on one summand, over abstract morphisms: the
summand inclusion followed by the inverse of the decomposition is a leg `l`, and both maps are
known after `l`. Stated abstractly because the composites it rearranges are not type-correct at
the transparency a rewrite builds its motive at. -/
private theorem comp_eq_comp_comp_of_leg {D : Type*} [Category D] {P B Q R W K' Kn : D}
    (ι : P ⟶ B) (inv : B ⟶ Q) (l₁ : P ⟶ R) (l₂ : R ⟶ Q) (x : Q ⟶ K') (y : Q ⟶ Kn)
    (fn : Kn ⟶ K') (a : P ⟶ W) (c' : W ⟶ K') (c : P ⟶ Kn)
    (hs : ι ≫ inv = l₁ ≫ l₂) (hl : l₁ ≫ l₂ ≫ x = a ≫ c') (hc : l₁ ≫ l₂ ≫ y = c)
    (hn : c ≫ fn = a ≫ c') :
    ι ≫ inv ≫ x = ι ≫ inv ≫ y ≫ fn := by
  rw [← Category.assoc, hs, Category.assoc, hl, ← Category.assoc ι, hs, ← hn, ← hc]
  simp only [Category.assoc]

/-- **The restriction to a component of the transpose of a morphism of simplicial systems.**
Let `f : {K_n} ⟶ {K'_n}` be a morphism of the simplicial systems of Stacks 0D9P attached to two
objects `K`, `K'` of `D(O)`, over flat structure-sheaf transitions. For simplicial degrees `m`
and `n`, the restriction to degree `n` of the transpose `Lg_{m!}K_m ⟶ K'` of `f_m` is the
restriction to degree `n` of the counit `Lg_{m!}K_m ⟶ K`, followed by `f_n`.

Both sides are maps out of `Lg_n^*Lg_{m!}K_m`, which the direct-sum formula of Stacks 0D72 (6)
presents as a biproduct of the `Lf_ψ^*K_m` with the canonical legs as inclusions, so it is enough
to compare them on each leg; there they are the two sides of the compatibility of `f` with the
transition at `ψ`. -/
theorem derivedComponentModuleRestriction_map_homEquiv_symm
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    {K K' : DerivedCategory (S.totalRingedTopos O).Modules}
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) (m n : SimplexCategory) :
    (S.derivedComponentModuleRestriction O n).map
        (((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).homEquiv _ K').symm
          (f.app m)) =
      (S.derivedComponentModuleRestriction O n).map
          ((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).counit.app K) ≫
        f.app n := by
  let : Fintype (m ⟶ n) := Fintype.ofFinite (m ⟶ n)
  refine (cancel_epi (S.derivedModuleSumFormula O m n (hflat m)
    ((S.derivedComponentModuleRestriction O m).obj K)).inv).1 ?_
  refine biproduct.hom_ext' _ _ fun ψ => ?_
  have hcounit := derivedTransitionPullback_map_unit_comp_map_homEquiv_symm (hflat m)
    (𝟙 ((S.derivedComponentModuleRestriction O m).obj K)) ψ
  have hc : ((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).homEquiv _ K).symm
      (𝟙 _) = (S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).counit.app K := by
    rw [Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp]
  rw [hc, Functor.map_id, Category.id_comp] at hcounit
  exact comp_eq_comp_comp_of_leg _ _ _ _ _ _ _ _ _ _ (hsummand ψ _)
    (derivedTransitionPullback_map_unit_comp_map_homEquiv_symm (hflat m) (f.app m) ψ) hcounit
    (f.naturality ψ)

end CategoryTheory.SimplicialSiteSituation

end
