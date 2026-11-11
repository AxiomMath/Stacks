module

public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Stalks of a sheaf at a point induced by a representably flat functor

A special case of Stacks 05V1, through Mathlib's `GrothendieckTopology.Point.comap`. Here the
functor `u : C ⥤ D` is assumed continuous, cover-preserving and *representably flat*, with
inverse image `u.sheafPullback A J K`. This is not the Stacks notion of a morphism of sites:
Stacks 00X1 (`CategoryTheory.Functor.IsMorphismOfSites`) only asks `u` to be continuous with
`u_s` exact, and for sites without finite limits representable flatness is strictly stronger.

For a point `q` of `(D, K)`, Mathlib's `q.comap u hu : J.Point` has fiber `u ⋙ q.fiber`, and
the stalks of a sheaf `F` on `C` at it and of its inverse image at `q` agree,
`F_p ≅ (u_s F)_q`, naturally in `F`, for an arbitrary target category `A` with the required
(co)limits.

Stacks 05V1 itself, for an arbitrary morphism of sites in the sense of 00X1, is
`CategoryTheory.Functor.IsMorphismOfSites.exists_point_fiber_eq_and_sheafFiber_iso` in
`StacksFrontier.CategoryTheory.Sites.Point.OfMorphismOfSites`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits

universe w v u₁ u₂

/-- The natural isomorphism of stalk functors
`(q.comap u hu).sheafFiber ≅ u.sheafPullback A J K ⋙ q.sheafFiber` for a representably flat,
cover-preserving continuous `u`, given by Mathlib's
`GrothendieckTopology.Point.sheafFiberComapIso`. -/
noncomputable def point_morphism_sites_iso
    {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) [RepresentablyFlat u] [u.IsContinuous J K]
    (hu : CoverPreserving J K u)
    (q : Point.{w} K)
    [InitiallySmall (u ⋙ q.fiber).Elements]
    (A : Type*) [Category.{v} A] [HasProducts.{w} A]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [HasColimitsOfSize.{w, w} A] :
    (q.comap u hu).sheafFiber (A := A) ≅ u.sheafPullback A J K ⋙ q.sheafFiber :=
  q.sheafFiberComapIso u hu A

/-- The case of Stacks 05V1 where `u : C ⥤ D` is representably flat and cover-preserving:
for a point `q` of `(D, K)`, the stalk functor at the induced point `q.comap u hu` of
`(C, J)` is isomorphic to taking the inverse image along `u` and then the stalk at `q`.
Stacks 05V1 for an arbitrary morphism of sites is
`CategoryTheory.Functor.IsMorphismOfSites.exists_point_fiber_eq_and_sheafFiber_iso`. -/
theorem point_morphism_sites
    {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) [RepresentablyFlat u] [u.IsContinuous J K]
    (hu : CoverPreserving J K u)
    (q : Point.{w} K)
    [InitiallySmall (u ⋙ q.fiber).Elements]
    (A : Type*) [Category.{v} A] [HasProducts.{w} A]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [HasColimitsOfSize.{w, w} A] :
    Nonempty ((q.comap u hu).sheafFiber (A := A) ≅ u.sheafPullback A J K ⋙ q.sheafFiber) :=
  ⟨point_morphism_sites_iso u hu q A⟩
