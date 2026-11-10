module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization

/-!
# A morphism of simplicial systems is flat over the transitions of the realization

Let `S` be a simplicial-site situation, `K'` an object of the derived category of abelian sheaves
on its total site, and `T` a cartesian simplicial system of the derived categories of the
components with a morphism `f : T ⟶ {K'_n}` into the associated system of `K'` of Stacks 0D9H.
Each component `f_n : T_n ⟶ K'_n` has a transpose `g_{n!}T_n ⟶ K'` along `g_{n!} ⊣ g_n^{-1}`,
and the transitions `g_{n!}T_n ⟶ g_{m!}T_m` of the realization of Stacks 0D9L are available for
every simplex map `φ : ⦋m⦌ ⟶ ⦋n⦌`. This file proves that the transposes are compatible with
those transitions: **the transition at `φ` followed by the transpose in degree `m` is the
transpose in degree `n`, for every `φ`.**

## Main results

* `CategoryTheory.SimplicialSiteSituation.realizationTermMap_comp_homEquiv_symm_of_naturality`:
  for a family `a_k : T_k ⟶ K'_k` compatible with the transition at `φ`, the transition of the
  realization at `φ` followed by the transpose of `a_m` is the transpose of `a_n`.
* `CategoryTheory.SimplicialSiteSituation.realizationTermMap_comp_homEquiv_symm`: the transposes
  of the components of a morphism of simplicial systems are compatible with the transitions of
  the realization.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage
  CategoryTheory.SimplicialSiteSituation.realizationTerm

variable {S : SimplicialSiteSituation.{u}}
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- **The transposes of the components of a morphism of simplicial systems are compatible with
the transitions of the realization.** Let `T` be a cartesian simplicial system of the derived
categories of the components and `f : T ⟶ {K'_n}` a morphism into the associated system of an
object `K'` of the derived category of the total site. For every simplex map `φ : ⦋m⦌ ⟶ ⦋n⦌` the
transition `g_{n!}T_n ⟶ g_{m!}T_m` of the realization, followed by the transpose of `f_m`, is
the transpose of `f_n`. -/
theorem realizationTermMap_comp_homEquiv_symm_of_naturality
    {K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})}
    {T : SimplicialDerivedSystem S} (hT : SimplicialDerivedSystem.Cartesian T)
    (a : ∀ k : SimplexCategory, T.obj k ⟶ (derivedComponent S k).obj K')
    {m n : SimplexCategory} (φ : m ⟶ n)
    (hnat : T.map φ ≫ a n =
      (derivedInverseImage S φ).map (a m) ≫ (derivedTransition S φ).app K') :
    realizationTermMap T hT φ ≫
        ((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm (a m) =
      ((S.componentLowerShriekDerivedAdjunction n).homEquiv (T.obj n) K').symm (a n) := by
  refine ((S.componentLowerShriekDerivedAdjunction n).homEquiv (T.obj n) K').injective ?_
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    realizationTermMap_homEquiv]
  change (@inv _ _ _ _ (T.map φ) (hT φ) ≫
      (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m)) ≫
        (derivedTransition S φ).app ((S.componentLowerShriekDerived m).obj (T.obj m))) ≫
      (derivedComponent S n).map
        (((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm (a m)) =
    a n
  have key : (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m)) ≫
        (derivedInverseImage S φ).map
            ((derivedComponent S m).map
              (((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm
                (a m))) ≫
          (derivedTransition S φ).app K' =
      T.map φ ≫ a n := by
    have htri : (S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m) ≫
          (derivedComponent S m).map
            (((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm (a m)) =
        a m :=
      ((S.componentLowerShriekDerivedAdjunction m).homEquiv_unit _ _ _).symm.trans
        (((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').apply_symm_apply
          (a m))
    rw [← Category.assoc, ← Functor.map_comp, htri, ← hnat]
  rw [Category.assoc, Category.assoc,
    ← derivedTransition_naturality φ
      (((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm (a m)),
    key, IsIso.inv_hom_id_assoc]

/-- **The transposes of the components of a morphism of simplicial systems are compatible with
the transitions of the realization**: for a morphism `f : T ⟶ {K'_n}` into the associated
system of Stacks 0D9H and every simplex map `φ : ⦋m⦌ ⟶ ⦋n⦌`, the transition of the realization at
`φ` followed by the transpose of `f_m` is the transpose of `f_n`. -/
theorem realizationTermMap_comp_homEquiv_symm
    {K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})}
    {T : SimplicialDerivedSystem S} (hT : SimplicialDerivedSystem.Cartesian T)
    (f : SimplicialDerivedSystem.Hom T (S.associatedDerivedSystem K'))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    realizationTermMap T hT φ ≫
        ((S.componentLowerShriekDerivedAdjunction m).homEquiv (T.obj m) K').symm (f.app m) =
      ((S.componentLowerShriekDerivedAdjunction n).homEquiv (T.obj n) K').symm (f.app n) :=
  realizationTermMap_comp_homEquiv_symm_of_naturality hT (fun k => f.app k) φ (f.naturality φ)

end CategoryTheory.SimplicialSiteSituation

end
