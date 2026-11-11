module

public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.Point.Exactness
public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransport
public import StacksFrontier.CategoryTheory.Sites.Point.ToposPoints
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# The point induced by a point along a morphism of sites

Stacks 05V1. Let `f : D → C` be a morphism of sites (Stacks 00X1,
`CategoryTheory.Functor.IsMorphismOfSites`) given by a continuous functor `u : C ⥤ D` whose
induced functor `u_s = f⁻¹ : Sh(C) ⥤ Sh(D)` on sheaves of sets is exact. Let `q` be a point of
`D` with fiber functor `v = q.fiber : D ⥤ Set`. Then `v ∘ u = u ⋙ q.fiber` is the fiber
functor of a point `p` of `C`, and `(f⁻¹ F)_q = F_p` for every sheaf of sets `F` on `C`,
naturally in `F`.

No flatness or cover-preservation hypothesis on `u` is made beyond those of Stacks 00X1.
Mathlib's `CategoryTheory.GrothendieckTopology.Point.comap` builds the point only for a
representably flat, cover-preserving `u`; for sites without finite limits representable
flatness is strictly stronger than exactness of `u_s`.

## Proof

Mathlib's notion of a point asks for the category of elements of the fiber functor to be
cofiltered, and for covering sieves to be jointly surjective on fibers. Both are obtained from
the point of the topos `Sh(C)` given by the composite morphism of topoi
`Sh(pt) → Sh(D) → Sh(C)`, whose inverse image is `u_s ⋙ q.sheafFiber`, a left exact left
adjoint: `PointOfTopos.exists_sitePoint_fiber_eq` (Stacks 00YA) produces a point of `C`
with fiber `U ↦ q⁻¹(u_s(h_U^#))`. This fiber is identified with `U ↦ q.fiber (u U)` by
`u_s(h_U^#) ≅ h_{u(U)}^#` (`Sheaf.sheafifiedYonedaCompSheafPullbackIso`) and
`q⁻¹(h_V^#) ≅ q.fiber V`, and the point is transported along this isomorphism
(`Stacks.SitePointFiberIso.pointOfFiberIso`), so that its fiber is `u ⋙ q.fiber` on the nose.
The stalk identification is then `Point.sheafFiberIsoOfFiberEq`: the skyscraper functors
satisfy `p_* = u^s ∘ q_*` on the nose, and conjugating gives `p⁻¹ ≅ q⁻¹ ∘ u_s`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.fiberIsoSheafifiedYonedaCompSheafFiber`: the
  natural isomorphism `q.fiber ≅ h_•^# ⋙ q.sheafFiber`.
* `CategoryTheory.Functor.IsMorphismOfSites.comapPoint`: the point `p` of `C`, with fiber
  `u ⋙ q.fiber`.
* `CategoryTheory.Functor.IsMorphismOfSites.sheafFiberComapPointIso`: the natural
  isomorphism `p.sheafFiber ≅ u_s ⋙ q.sheafFiber`.

## Main results

* `CategoryTheory.Functor.IsMorphismOfSites.exists_point_fiber_eq_and_sheafFiber_iso`:
  Stacks 05V1.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Opposite GrothendieckTopology

universe v u

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The fiber of a point `Φ` at `X` is the stalk at `Φ` of the sheafified representable `h_X^#`,
naturally in `X`: the natural-isomorphism form of `PointOfTopos.fiberToSheafYoneda`. -/
def fiberIsoSheafifiedYonedaCompSheafFiber (Φ : Point.{max u v} J) :
    Φ.fiber ≅ Sheaf.sheafifiedYoneda J ⋙ Φ.sheafFiber :=
  Φ.shrinkYonedaCompPresheafFiberIso.symm ≪≫
    Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda.{u}.symm Φ.presheafFiber ≪≫
    Functor.isoWhiskerLeft uliftYoneda.{u} (Φ.presheafToSheafCompSheafFiberIso _).symm ≪≫
    (Functor.associator _ _ _).symm

end GrothendieckTopology.Point

namespace Functor.IsMorphismOfSites

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
  (hu : u.IsMorphismOfSites J K) (q : Point.{u} K)

/-- The point of the topos `Sh(C)` obtained by composing the point of the topos `Sh(D)`
attached to `q` with the morphism of topoi `Sh(D) → Sh(C)` attached to `hu`. Its inverse image
is `u_s ⋙ q.sheafFiber`. -/
def compPointOfTopos : PointOfTopos.{u, u, u} J :=
  hu.morphismOfTopoi.compPoint q.pointOfTopos

/-- The inverse image of `hu.compPointOfTopos q` is `u_s ⋙ q.sheafFiber`. -/
theorem compPointOfTopos_inverseImage :
    haveI := hu.isContinuous
    (hu.compPointOfTopos q).inverseImage =
      u.sheafPullback (Type u) J K ⋙ q.sheafFiber (A := Type u) :=
  rfl

/-- The fiber `U ↦ q⁻¹(u_s(h_U^#))` of the point of the topos `hu.compPointOfTopos q` is
isomorphic to `u ⋙ q.fiber`. -/
def sheafifiedYonedaCompInverseImageIso :
    Sheaf.sheafifiedYoneda J ⋙ (hu.compPointOfTopos q).inverseImage ≅ u ⋙ q.fiber :=
  haveI := hu.isContinuous
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaCompSheafPullbackIso u J K)
      (q.sheafFiber (A := Type u)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft u q.fiberIsoSheafifiedYonedaCompSheafFiber.symm

/-- **The point `p = v ∘ u` of Stacks 05V1.** For a morphism of sites `f : D → C` given by
`u : C ⥤ D` and a point `q` of `D`, the point of `C` whose fiber functor is `u ⋙ q.fiber`
(`comapPoint_fiber`). -/
def comapPoint : Point.{u} J :=
  Stacks.SitePointFiberIso.pointOfFiberIso
    (Classical.choose (PointOfTopos.exists_sitePoint_fiber_eq (hu.compPointOfTopos q)))
    (eqToIso (Classical.choose_spec
        (PointOfTopos.exists_sitePoint_fiber_eq (hu.compPointOfTopos q))) ≪≫
      hu.sheafifiedYonedaCompInverseImageIso q)

/-- The fiber functor of `hu.comapPoint q` is `u ⋙ q.fiber`. -/
@[simp]
theorem comapPoint_fiber : (hu.comapPoint q).fiber = u ⋙ q.fiber :=
  rfl

/-- **The stalk identification of Stacks 05V1.** The stalk functor at the point
`p = hu.comapPoint q` is the inverse image `f⁻¹ = u_s` followed by the stalk functor at `q`:
`F_p ≅ (f⁻¹ F)_q`, naturally in the sheaf of sets `F`. -/
def sheafFiberComapPointIso :
    haveI := hu.isContinuous
    (hu.comapPoint q).sheafFiber (A := Type u) ≅
      u.sheafPullback (Type u) J K ⋙ q.sheafFiber (A := Type u) :=
  haveI := hu.isContinuous
  q.sheafFiberIsoOfFiberEq u (hu.comapPoint q) rfl

/-- **Stacks 05V1.** Let `f : D → C` be a morphism of sites given by the continuous functor
`u : C ⥤ D` (Stacks 00X1: `u_s` is exact) and let `q` be a point of `D` with fiber functor
`v = q.fiber`. Then `v ∘ u = u ⋙ q.fiber` is the fiber functor of a point `p` of `C`, and
there is an identification `(f⁻¹ F)_q ≅ F_p`, natural in the sheaf of sets `F` on `C`.

The point is `hu.comapPoint q` and the identification is `hu.sheafFiberComapPointIso q`. -/
@[stacks 05V1 "Stated for the morphisms of sites of Stacks 00X1
  (`Functor.IsMorphismOfSites`), with no flatness or cover-preservation assumption on `u`;
  the canonical point is `IsMorphismOfSites.comapPoint` and the canonical identification of
  stalk functors is `IsMorphismOfSites.sheafFiberComapPointIso`."]
theorem exists_point_fiber_eq_and_sheafFiber_iso :
    haveI := hu.isContinuous
    ∃ p : Point.{u} J, p.fiber = u ⋙ q.fiber ∧
      Nonempty (p.sheafFiber (A := Type u) ≅
        u.sheafPullback (Type u) J K ⋙ q.sheafFiber (A := Type u)) :=
  ⟨hu.comapPoint q, rfl, ⟨hu.sheafFiberComapPointIso q⟩⟩

end Functor.IsMorphismOfSites

end CategoryTheory
