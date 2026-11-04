module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# An equivalence of sites stays a dense subsite inclusion on the slices

Let `F : C ⥤ D` be an equivalence of categories which is at the same time the inclusion of a
dense subsite for topologies `J` on `C` and `K` on `D`, and let `X : C`. This file shows that
`Over.post F : Over X ⥤ Over (F.obj X)` is again a dense subsite inclusion, for the localized
topologies `J.over X` and `K.over (F.obj X)`.

Everything a dense subsite inclusion provides is therefore available on the slices: continuity,
cocontinuity, and — by `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` — an equivalence of
sheaf categories.

## Main results

* `CategoryTheory.Functor.isDenseSubsite_overPost` — **`Over.post F` is a dense subsite inclusion
  of the localized sites.**

## Implementation notes

The covering condition is `CategoryTheory.Sieve.overEquiv_functorPushforward_post`: pushing a
sieve of `Over X` forward along `Over.post F` and then down to `D` is the same as pushing it down
to `C` and then forward along `F`, because `Over.post F ⋙ Over.forget _ = Over.forget X ⋙ F`.
Membership in a localized topology being membership of the pushed-down sieve
(`CategoryTheory.GrothendieckTopology.mem_over_iff`), the condition reduces to the one for `F`.

Cover density, local fullness and local faithfulness are read off `Over.post F` being an
equivalence of categories, which it is because `F` is: an equivalence is cover dense for any
topology, and a full and faithful functor is locally full and locally faithful. That is the only
place the hypothesis that `F` is an equivalence is used; the covering condition holds for any
dense subsite inclusion.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)

/-- **An equivalence of sites induces a dense subsite inclusion of the slices.** For `F : C ⥤ D`
an equivalence of categories which exhibits `(C, J)` as a dense subsite of `(D, K)`, and `X : C`,
the functor `Over.post F : Over X ⥤ Over (F.obj X)` exhibits `(Over X, J.over X)` as a dense
subsite of `(Over (F.obj X), K.over (F.obj X))`.

The covering condition is that of `F`, transported by
`CategoryTheory.Sieve.overEquiv_functorPushforward_post`; cover density, local fullness and local
faithfulness hold because `Over.post F` is again an equivalence of categories. -/
theorem isDenseSubsite_overPost [F.IsEquivalence] [F.IsDenseSubsite J K] (X : C) :
    (Over.post (X := X) F).IsDenseSubsite (J.over X) (K.over (F.obj X)) := by
  refine { functorPushforward_mem_iff := fun {Y S} => ?_ }
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_functorPushforward_post]
  exact Functor.IsDenseSubsite.functorPushforward_mem_iff (G := F) (J := J) (K := K)

end CategoryTheory.Functor

end
