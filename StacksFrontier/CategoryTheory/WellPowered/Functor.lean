module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# A functor category into a well-powered category is well-powered

Let `A` have pullbacks. A subobject `S` of `F : K ⥤ A` is determined by the family
`fun k => Subobject.mk (S.arrow.app k)` of subobjects of the values of `F`. The target of this
injection is `∀ k, Subobject (F.obj k)`, which is `w`-small when `K` is `w`-small and `A` is
`CategoryTheory.WellPowered.{w}`.

## Main results

* `Stacks.FunctorWellPowered.le_of_forall_app_le`: the subobject order on `K ⥤ A` is detected
  pointwise.
* `Stacks.FunctorWellPowered.wellPowered`: `K ⥤ A` is `WellPowered.{w}`.

## Implementation notes

`HasPullbacks A` is used only through `CategoryTheory.NatTrans.mono_iff_mono_app`, so that each
`S.arrow.app k` is a monomorphism.

`LocallySmall.{w} (K ⥤ A)` is a hypothesis rather than a conclusion, because
`CategoryTheory.WellPowered` carries it as an instance argument. It is not implied by
`LocallySmall.{w} A` and `Small.{w} K` in general: the hom types of `K ⥤ A` live in
`Type (max u₁ v₂)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ w u₁ u₂

namespace Stacks.FunctorWellPowered

variable {K : Type u₁} [Category.{v₁} K] {A : Type u₂} [Category.{v₂} A] [HasPullbacks A]

/-- The subobject order on a functor category is detected pointwise: if
`Subobject.mk (S.arrow.app k) ≤ Subobject.mk (T.arrow.app k)` for every `k`, then `S ≤ T`. -/
theorem le_of_forall_app_le {F : K ⥤ A} {S T : Subobject F}
    (h : ∀ k, Subobject.mk (S.arrow.app k) ≤ Subobject.mk (T.arrow.app k)) : S ≤ T := by
  have key := fun k => Subobject.ofMkLEMk_comp (h k)
  refine Subobject.le_of_comm
    { app := fun k => Subobject.ofMkLEMk (S.arrow.app k) (T.arrow.app k) (h k)
      naturality := fun k l φ => ?_ } ?_
  · rw [← cancel_mono (T.arrow.app l), Category.assoc, key l, Category.assoc,
      T.arrow.naturality φ, ← Category.assoc, key k, S.arrow.naturality φ]
  · exact NatTrans.ext (funext key)

/-- If `K` is `w`-small, `A` has pullbacks and is locally `w`-small and `w`-well-powered, and
`K ⥤ A` is locally `w`-small, then `K ⥤ A` is `w`-well-powered. -/
instance wellPowered [Small.{w} K] [LocallySmall.{w} A] [WellPowered.{w} A]
    [LocallySmall.{w} (K ⥤ A)] : WellPowered.{w} (K ⥤ A) where
  subobject_small F := small_of_injective
    (f := fun (S : Subobject F) (k : K) => Subobject.mk (S.arrow.app k))
    fun _ _ hst => le_antisymm (le_of_forall_app_le fun k => (congrFun hst k).le)
      (le_of_forall_app_le fun k => (congrFun hst k).ge)

end Stacks.FunctorWellPowered
