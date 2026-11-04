module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AssociatedDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLiftConstruction

/-!
# Lifting a morphism of simplicial systems to the total site (Stacks 0D9K)

In the simplicial-site situation of Stacks 09WE let `K` and `K'` be objects of the unbounded
derived category of abelian sheaves on the total site. Stacks 0D9H attaches to each of them a
simplicial system of the derived categories of the components, with `K_n` the derived restriction
of `K` to degree `n` and the canonical derived transitions of Stacks 07TF for structure maps.
Stacks 0D9K says that if `K` is cartesian and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, then every
morphism `{K_n ⟶ K'_n}` of those systems is induced by a morphism `K ⟶ K'` of the total derived
category.

This file proves that a morphism *out of a cartesian simplicial system* is determined by its
component in degree zero: every object of the simplex category receives the constant map from
`⦋0⦌`, and cartesianness makes the transition along it invertible. Hence, for a cartesian `K`, a
morphism of the associated systems comes from `K ⟶ K'` exactly when its degree-zero component
does. Together with the degree-zero lift
`CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponent_zero_eq`, built from the
Postnikov system of Stacks 0D9I and the comparison of Stacks 0D9E, this gives Stacks 0D9K.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.ShiftedComponentHomVanishing`: hypothesis (2) of
  Stacks 0D9K, the vanishing of `Hom(K_i[i - 1], K'_i)` for `i > 1`.
* `CategoryTheory.SimplicialSiteSituation.associatedDerivedSystemHom`: the morphism of associated
  simplicial systems induced by a morphism of the derived category of the total site.

## Main results

* `CategoryTheory.SimplicialDerivedSystem.Hom.app_eq_of_cartesian`: a morphism out of a cartesian
  simplicial system is determined by its component in simplicial degree zero.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_iff_exists_hom_zero`: for a cartesian `K`, a
  morphism of the associated simplicial systems is induced by a morphism `K ⟶ K'` if and only if
  its degree-zero component is.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_of_isCartesianDerived`: **Stacks 0D9K**.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace CategoryTheory

section Systems

variable {S : SimplicialSiteSituation.{u}}
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- A morphism out of a cartesian simplicial system is determined by its component in simplicial
degree zero. -/
theorem SimplicialDerivedSystem.Hom.app_eq_of_cartesian {T V : SimplicialDerivedSystem S}
    (hT : T.Cartesian) {f g : T.Hom V} (h : f.app ⦋0⦌ = g.app ⦋0⦌) (n : SimplexCategory) :
    f.app n = g.app n := by
  have := hT (SimplexCategory.const ⦋0⦌ n 0)
  rw [← cancel_epi (T.map (SimplexCategory.const ⦋0⦌ n 0)), f.naturality, g.naturality, h]

end Systems

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- Hypothesis (2) of Stacks 0D9K: the group `Hom(K_i[i - 1], K'_i)` of maps from the derived
restriction of `K` to degree `i`, shifted by `i - 1`, to the derived restriction of `K'` to
degree `i` vanishes for every `i > 1`. -/
def ShiftedComponentHomVanishing
    (K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})) : Prop :=
  ∀ i : ℕ, 1 < i →
    ∀ g : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology ⦋i⦌) Ab.{u}))
          ((i : ℤ) - 1)).obj ((derivedComponent S ⦋i⦌).obj K) ⟶
        (derivedComponent S ⦋i⦌).obj K', g = 0

/-- The morphism of the associated simplicial systems of Stacks 0D9H induced by a morphism of the
derived category of the total site: in each simplicial degree the derived restriction of the
morphism. -/
def associatedDerivedSystemHom {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})}
    (γ : K ⟶ K') :
    SimplicialDerivedSystem.Hom (S.associatedDerivedSystem K)
      (S.associatedDerivedSystem K') where
  app n := (derivedComponent S n).map γ
  naturality φ := ((derivedTransition S φ).naturality γ).symm

/-- The degree-`n` component of the morphism of associated systems induced by `γ` is the derived
restriction of `γ` to degree `n`. -/
@[simp]
theorem associatedDerivedSystemHom_app
    {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (γ : K ⟶ K') (n : SimplexCategory) :
    (S.associatedDerivedSystemHom γ).app n = (derivedComponent S n).map γ :=
  rfl

/-- For a cartesian `K`, a morphism of the associated simplicial systems of Stacks 0D9H is
induced by a morphism `K ⟶ K'` of the derived category of the total site if and only if its
component in simplicial degree zero is. -/
theorem exists_hom_iff_exists_hom_zero
    {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (hK : S.IsCartesianDerived K)
    (f : SimplicialDerivedSystem.Hom (S.associatedDerivedSystem K)
      (S.associatedDerivedSystem K')) :
    (∃ γ : K ⟶ K', ∀ n : SimplexCategory, (derivedComponent S n).map γ = f.app n) ↔
      ∃ γ : K ⟶ K', (derivedComponent S ⦋0⦌).map γ = f.app ⦋0⦌ :=
  ⟨fun ⟨γ, hγ⟩ => ⟨γ, hγ ⦋0⦌⟩, fun ⟨γ, hγ⟩ => ⟨γ, fun n =>
    SimplicialDerivedSystem.Hom.app_eq_of_cartesian (S.associatedDerivedSystem_cartesian K hK)
      (f := S.associatedDerivedSystemHom γ) (g := f) hγ n⟩⟩

section StandardLift

/-! ### The lift, at the standard derived category

The statements above hold for every model of the derived category of abelian sheaves on the
total site. Stacks 0D9K is stated below at the standard model `HasDerivedCategory.standard`, on
which the derived tensor product `- ⊗^L_ℤ K` of the Postnikov system of Stacks 0D9I is built.
-/

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- **Stacks 0D9K.** In the simplicial-site situation of Stacks 09WE, let `K` and `K'` be objects
of the derived category of abelian sheaves on the total site. If `K` is cartesian in the sense of
Stacks 07TF (3) and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, then every morphism of the
associated simplicial systems of Stacks 0D9H is induced by a morphism `K ⟶ K'`: there is a
`γ : K ⟶ K'` whose derived restriction to every simplicial degree is the given component. -/
@[stacks 0D9K "a morphism of simplicial systems comes from the total site, at the source's \
hypotheses (1) and (2): the degree-zero lift is \
`CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponent_zero_eq`, which makes the \
source's two omitted computations -- the vanishing of `X_1 ⟶ X_0 ⟶ K'` against the transition of \
the realization, and the reading of the structural map `X_0 ⟶ K` as the counit -- and the \
passage from degree zero to all degrees is \
`CategoryTheory.SimplicialSiteSituation.exists_hom_iff_exists_hom_zero`"]
theorem exists_hom_of_isCartesianDerived
    (K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    (hK : S.IsCartesianDerived K)
    (hHom : S.ShiftedComponentHomVanishing K K')
    (f : SimplicialDerivedSystem.Hom (S.associatedDerivedSystem K)
      (S.associatedDerivedSystem K')) :
    ∃ γ : K ⟶ K', ∀ n : SimplexCategory, (derivedComponent S n).map γ = f.app n :=
  (S.exists_hom_iff_exists_hom_zero hK f).2
    (S.exists_hom_derivedComponent_zero_eq K K' hK hHom f)

end StandardLift

end SimplicialSiteSituation

end CategoryTheory

end
