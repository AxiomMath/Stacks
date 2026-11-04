module

public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Stalks of a sheaf at a point induced by a morphism of sites

Stacks tag 05V1. A morphism of sites `f : D → C` is given, in the Stacks convention, by a
functor `u : C ⥤ D` in the opposite direction which is continuous, cover-preserving and
representably flat, with inverse image `f⁻¹ = u.sheafPullback A J K`. A point `q` of
`(D, K)` is a fiber functor `q.fiber : D ⥤ Type w` (tag 00Y5) with associated stalk
functor `q.sheafFiber : Sheaf K A ⥤ A` (tag 04EH).

Composing, `v ∘ u = u ⋙ q.fiber` is a point `p = q.comap u hu` of `(C, J)` — the first
assertion of 05V1, which here is the well-typedness of `q.comap u hu : J.Point` — and the
stalks of a sheaf `F` on `C` at `p` and of its inverse image at `q` agree:
`F_p ≅ (f⁻¹F)_q`, naturally in `F`. The target `A` is an arbitrary category with the
required (co)limits; the sheaves-of-sets case is `A := Type w`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits

universe w v u₁ u₂

/-- The natural isomorphism of stalk functors
`(q.comap u hu).sheafFiber ≅ u.sheafPullback A J K ⋙ q.sheafFiber` of Stacks 05V1, given
by Mathlib's `GrothendieckTopology.Point.sheafFiberComapIso`. -/
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

/-- **Stacks 05V1.** For a point `q` of `(D, K)` and a morphism of sites given by
`u : C ⥤ D`, the stalk functor at the induced point `q.comap u hu` of `(C, J)` is
isomorphic to taking the inverse image along `u` and then the stalk at `q`. -/
@[stacks 05V1]
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
