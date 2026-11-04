module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk
public import StacksFrontier.CategoryTheory.Monoidal.Cartesian.Bimultiplicative

/-!
# Biadditive pairings of discrete `G`-modules as internal pairings of continuous `G`-sets

A discrete `G`-module is a commutative group object in continuous `G`-sets
(`CategoryTheory.commGrpContinuousGSetEquivalence`). A `G`-equivariant pairing of the underlying
sets which is additive in each variable is then a bimultiplicative morphism of these group
objects, in the sense of `CategoryTheory.IsBimultiplicative`. This is the first step in carrying
the invariant pairing `⟨ρ(g) x, ρ^∨(g) y⟩ = ⟨x, y⟩` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) to the finite locally constant sheaves of
Tag 0DV5.

## Main results

* `CategoryTheory.isBimultiplicative_preimage_internalGModule`: a sectionwise biadditive morphism
  of the presheaves on the one-object category of `G` underlying three discrete `G`-modules
  descends to a bimultiplicative morphism of their internal group objects.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u w

/- The cartesian monoidal structure on continuous `G`-sets used for
`CategoryTheory.commGrpContinuousGSetEquivalence`. -/
attribute [local instance] cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace CategoryTheory

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The braided structure of `gsetPresheaf` used for `CategoryTheory.externalGModule`. -/
local instance braidedGsetPresheaf : (gsetPresheaf.{u, w} (G := G)).Braided :=
  .ofChosenFiniteProducts _

open scoped Obj in
/-- **A biadditive pairing of discrete `G`-modules is an internal bimultiplicative pairing.**
Let `β` be a morphism from the product of the presheaves of sets on the one-object category of
`G` underlying `M` and `N` to the one underlying `L`, that is, a `G`-equivariant map of sets
`M × N → L`. If it is additive in each variable, then it descends to a bimultiplicative morphism
`internalGModule M ⊗ internalGModule N ⟶ internalGModule L` of continuous `G`-sets. -/
theorem isBimultiplicative_preimage_internalGModule (M N L : ContinuousGAddCommGrp.{u, w} G)
    (β : gsetPresheaf.obj (internalGModule M).X ⊗ gsetPresheaf.obj (internalGModule N).X ⟶
      gsetPresheaf.obj (internalGModule L).X)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hβ : ∀ x y, β.app (SingleObj.star G) (x, y) = P x y) :
    IsBimultiplicative (gsetPresheafFullyFaithful.preimage
      (Functor.OplaxMonoidal.δ gsetPresheaf (internalGModule M).X (internalGModule N).X ≫ β)) := by
  refine IsBimultiplicative.preimage gsetPresheafFullyFaithful ?_
  rw [isBimultiplicative_iff_app]
  have hmul : ∀ (A : ContinuousGAddCommGrp.{u, w} G) (a b : A.obj.obj.V),
      (MonObj.mul (X := gsetPresheaf.obj (internalGModule A).X)).app (SingleObj.star G) (a, b) =
        a + b := by
    intro A a b
    let : GrpObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj A)) :=
      Sites.AbelianSheaf.presheafGrpObj (gmodulePresheaf.obj A)
    let : IsCommMonObj (gsetPresheaf.obj ((ContinuousGAddCommGrp.forgetAction G).obj A)) :=
      (Sites.AbelianSheaf.presheafCommGrp.obj (gmodulePresheaf.obj A)).comm
    exact ConcreteCategory.congr_hom (CC := fun X : Type w => X)
      (congr_app (mul_mapCommGrp_pullCommGrp (gsetPresheafFullyFaithful.{u, w} (G := G))
        ((ContinuousGAddCommGrp.forgetAction G).obj A)) (SingleObj.star G)) (a, b)
  rintro ⟨⟩
  refine ⟨fun x x' y => ?_, fun x y y' => ?_⟩
  · erw [hβ, hmul M, map_add, AddMonoidHom.add_apply, hmul L, hβ, hβ]
  · erw [hβ, hmul N, map_add, hmul L, hβ, hβ]

end CategoryTheory

end
