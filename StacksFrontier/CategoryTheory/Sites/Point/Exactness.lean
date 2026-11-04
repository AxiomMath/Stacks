module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-!
# Exactness of `u_s` detected by a conservative family of points

Stacks 0F4G: let `u : C ⥤ D` be a continuous functor of sites and let `{(q_i, v_i)}_{i ∈ I}`
be a conservative family of points of `D`. If each composite `u_i = v_i ∘ u` defines a point
of `C`, then `u` defines a morphism of sites `f : D → C`.

Being a morphism of sites (`CategoryTheory.Functor.IsMorphismOfSites`, Stacks 00X1) adds to
continuity the exactness of `f⁻¹ = u_s`, and the right-exactness half is automatic because
`u_s` is a left adjoint. So the content is left exactness of `u_s`, which is
`preservesFiniteLimits_sheafPullback_of_points` below.

## Rendering of the hypotheses

* A conservative family of points is `ObjectProperty.IsConservativeFamilyOfPoints`, i.e. the
  stalk functors `Sh(D) ⥤ Set` of its members jointly reflect isomorphisms.
* "each `u_i = v_i ∘ u` defines a point of `C`" is a family `Ψ` of points of `C` together
  with `hΨ : (Ψ Φ).fiber = u ⋙ Φ.fiber`. This is the literal hypothesis: `Point.fiber` is
  the functor `u_i`, and all the remaining fields of `GrothendieckTopology.Point` are
  propositions, so a point of `C` "given by the functor `u_i`" is exactly such a pair. It is
  weaker than asking `u` to be representably flat and cover preserving, which is what
  Mathlib's `Point.comap` requires in order to *construct* such a point.

## Proof

Stacks computes `(f⁻¹F)_{q_i} = F_{p_i}`. That identification is
`Point.sheafFiberIsoOfFiberEq` below, a `comap`-free form of Mathlib's
`Point.sheafFiberComapIso`: the skyscraper sheaf functor of a point depends only on its
fiber, so the comparison `q_{i*} ∘ u^s = p_{i*}` of right adjoints holds on the nose, and
conjugating it gives the isomorphism of left adjoints.

Each `(Ψ Φ).sheafFiber` is left exact — for Mathlib's notion of a point that is a
consequence of cofilteredness rather than an assumption — so each composite
`u_s ⋙ Φ.sheafFiber` is left exact. A conservative family jointly reflects limits
(`JointlyReflectIsomorphisms.jointlyReflectsLimit`), which upgrades this to left exactness
of `u_s` itself.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite GrothendieckTopology

universe u

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}

/-- The skyscraper sheaf functor of a point `Ψ` of `(C, J)` whose fiber is `u ⋙ Φ.fiber`
agrees on the nose with `q_* ∘ u^s`, where `q` is the point `Φ` of `(D, K)`.

Both sides send `M` to the sheaf `X ↦ ∏_{x ∈ Φ.fiber (u X)} M`; the sheaf condition is a
proposition, so the two functors are equal and not merely isomorphic. -/
theorem skyscraperSheafFunctor_eq_of_fiber_eq (Φ : Point.{u} K) (u : C ⥤ D)
    [u.IsContinuous J K] (Ψ : Point.{u} J) (h : Ψ.fiber = u ⋙ Φ.fiber) :
    Φ.skyscraperSheafFunctor (A := Type u) ⋙ u.sheafPushforwardContinuous (Type u) J K =
      Ψ.skyscraperSheafFunctor := by
  obtain ⟨f, _, _, _⟩ := Ψ
  simp only [] at h
  subst h
  rfl

/-- **The identification `(f⁻¹F)_q = F_p` of Stacks 0F4G.** If `u : C ⥤ D` is continuous,
`Φ` is a point of `(D, K)` and `Ψ` is a point of `(C, J)` whose fiber is the composite
`u ⋙ Φ.fiber`, then the stalk functor of `Ψ` is the composite of `u_s = f⁻¹` with the stalk
functor of `Φ`.

This is Mathlib's `Point.sheafFiberComapIso` with the hypotheses that let `Point.comap`
build `Ψ` replaced by `Ψ` itself: conjugating the equality
`skyscraperSheafFunctor_eq_of_fiber_eq` of the right adjoints gives the isomorphism of the
left adjoints. -/
noncomputable def sheafFiberIsoOfFiberEq (Φ : Point.{u} K) (u : C ⥤ D)
    [u.IsContinuous J K] (Ψ : Point.{u} J) (h : Ψ.fiber = u ⋙ Φ.fiber) :
    Ψ.sheafFiber (A := Type u) ≅ u.sheafPullback (Type u) J K ⋙ Φ.sheafFiber :=
  (conjugateIsoEquiv ((u.sheafAdjunctionContinuous (Type u) J K).comp
      Φ.skyscraperSheafAdjunction) Ψ.skyscraperSheafAdjunction).symm
    (eqToIso (Φ.skyscraperSheafFunctor_eq_of_fiber_eq u Ψ h))

end GrothendieckTopology.Point

namespace Functor

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K]
  {P : ObjectProperty (Point.{u} K)}

/-- **Stacks 0F4G**, the exactness step. If `{(q_i, v_i)}` is a conservative family of points
of `(D, K)` and each composite `u_i = v_i ∘ u` is the fiber of a point `Ψ i` of `(C, J)`, then
`u_s : Sh(C) ⥤ Sh(D)` is left exact.

For each `i` the composite `u_s ⋙ (q_i)`-stalk is the `Ψ i`-stalk
(`Point.sheafFiberIsoOfFiberEq`), which is left exact; since the stalk functors at the `q_i`
jointly reflect isomorphisms they jointly reflect limits, so `u_s` preserves finite
limits. -/
theorem preservesFiniteLimits_sheafPullback_of_points
    (hP : P.IsConservativeFamilyOfPoints)
    (Ψ : P.FullSubcategory → Point.{u} J)
    (hΨ : ∀ Φ : P.FullSubcategory, (Ψ Φ).fiber = u ⋙ Φ.obj.fiber) :
    PreservesFiniteLimits (u.sheafPullback (Type u) J K) := by
  -- each composite `u_s ⋙ Φ.sheafFiber` is left exact, being the stalk functor of `Ψ Φ`
  have hcomp : ∀ Φ : P.FullSubcategory,
      PreservesFiniteLimits (u.sheafPullback (Type u) J K ⋙
        Φ.obj.sheafFiber (A := Type u)) := fun Φ =>
    preservesFiniteLimits_of_natIso (Φ.obj.sheafFiberIsoOfFiberEq u (Ψ Φ) (hΨ Φ))
  refine ⟨fun T _ _ => ⟨fun {Gd} => ⟨fun {c} hc => ?_⟩⟩⟩
  -- `Sh(D)` has the limit of the transported diagram, ...
  have : HasLimit (Gd ⋙ u.sheafPullback (Type u) J K) :=
    (hasLimitsOfShape_of_hasFiniteLimits _ T).has_limit _
  -- ... and each composite `u_s ⋙ (q_i)`-stalk sends the limit cone `c` to a limit cone,
  -- so joint reflection of limits shows `u_s` maps `c` to a limit cone.
  refine ⟨JointlyReflectIsomorphisms.jointlyReflectsLimit
    (F := fun Φ : P.FullSubcategory => Φ.obj.sheafFiber (A := Type u))
    hP.jointlyReflectIsomorphisms_type (fun Φ => ?_)⟩
  have hpres : PreservesLimit Gd (u.sheafPullback (Type u) J K ⋙
      Φ.obj.sheafFiber (A := Type u)) :=
    ((hcomp Φ).preservesFiniteLimits T).preservesLimit
  exact isLimitOfPreserves (u.sheafPullback (Type u) J K ⋙ Φ.obj.sheafFiber) hc

/-- **Stacks 0F4G.** Let `u : C ⥤ D` be a continuous functor of sites. Let `{(q_i, v_i)}`
be a conservative family of points of `D`. If each functor `u_i = v_i ∘ u` defines a point
of `C`, then `u` defines a morphism of sites `f : D → C`. -/
@[stacks 0F4G]
theorem isMorphismOfSites_of_points
    (hP : P.IsConservativeFamilyOfPoints)
    (Ψ : P.FullSubcategory → Point.{u} J)
    (hΨ : ∀ Φ : P.FullSubcategory, (Ψ Φ).fiber = u ⋙ Φ.obj.fiber) :
    u.IsMorphismOfSites J K :=
  (u.isMorphismOfSites_iff_preservesFiniteLimits J K).2
    (u.preservesFiniteLimits_sheafPullback_of_points hP Ψ hΨ)

end Functor

end CategoryTheory
