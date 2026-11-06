module

public import StacksCore.CategoryTheory.Inertia
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedIsomLifting
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaMonomorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Unramified morphisms preserving automorphism groups (Stacks 0DU9)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site.
**Stacks 0DU9** says that if `f` is unramified (**Stacks 0CIT**) then the following are
equivalent:

1. the canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of Stacks 06R5
   (`CategoryTheory.inertiaPullbackComparison`) is an isomorphism, and
2. `f` induces an isomorphism between the automorphism groups at `x` and at `f(x)`
   (`AlgebraicGeometry.Stack.InducesIsomorphismAt`, Stacks 0DTW) for every `x ∈ |𝒳|`.

Condition (1) is rendered as in the base-change statement of Stacks 0DUB
(`AlgebraicGeometry.Stack.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange`):
the comparison functor is an equivalence **over** the big fppf site, which is what
`CategoryTheory.IsEquivalenceOver` certifies for that specific functor.

## Main results

* `AlgebraicGeometry.Stack.inertiaPullbackComparison_isEquivalenceOver_iff_inducesIsomorphismAt`:
  **Stacks 0DU9**.
* `AlgebraicGeometry.Stack.inducesIsomorphismAt_of_inertiaPullbackComparison_isEquivalenceOver`:
  the implication (1) `⟹` (2), which holds for an arbitrary 1-morphism.
* `AlgebraicGeometry.Stack.inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt`:
  the implication (2) `⟹` (1) for an unramified 1-morphism.

## Implementation notes

*(1) `⟹` (2).* An equivalence over the base is in particular an equivalence
(`CategoryTheory.IsEquivalenceOver.isEquivalence`), hence full and essentially surjective, and a
full and essentially surjective inertia comparison induces bijections on automorphism groups at
*every* object of `𝒳` (`CategoryTheory.Functor.bijective_verticalAutMap`). Condition (2) at a
point asks for exactly that at the objects lying above a field-valued representative of the
point, by `AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_forall_representatives`
(Stacks 0DTV). Unramifiedness is not used.

*(2) `⟹` (1).* By
`CategoryTheory.nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts` the
comparison is an equivalence over the site as soon as `f` reflects commuting squares of
automorphisms — which faithfulness of `f` gives — and every vertical automorphism of the image
`f(x)` of an object `x` over a scheme `T` is the image of a vertical automorphism of `x`. The
source obtains both from the morphism `G ⟶ H` of automorphism group algebraic spaces over a
chart, which is étale (Stacks 0DU8 and 0CJ0) and, by (2), surjective and universally injective,
hence an isomorphism (Stacks 05W5). The argument here uses the same two facts — the relative
diagonal is unramified, and the hypothesis at field points — read through the open-immersion
property of an unramified diagonal (Stacks 05W1), see
`StacksFrontier/AlgebraicGeometry/Stacks/UnramifiedIsomLifting.lean`:

* `f` is Deligne–Mumford, so `Δ_f` is representable and unramified; an endomorphism `a` of `x`
  killed by `f` gives the automorphism `(𝟙, a)` of `Δ_f(x)`, whose restriction to every
  field-valued point lifts along `Δ_f` by (2), so it lifts over `T`, which forces `a = 𝟙`. Hence
  `f` is faithful (`AlgebraicGeometry.Stack.faithful_homFunctor_of_isDM`).
* A faithful 1-morphism of algebraic stacks is representable by algebraic spaces (Stacks 04Y5,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`), and
  an unramified 1-morphism representable by algebraic spaces is unramified in the sense of
  Stacks 04XB (`AlgebraicGeometry.Stack.isRelativelyUnramified_of_isUnramified`). A vertical
  automorphism `β` of `f(x)` lifts along `f` at every field-valued point by (2), so it lifts over
  `T` (`AlgebraicGeometry.Stack.exists_map_eq_of_isUnramified_of_isRepresentable`).

## References

* [Stacks Project, Tag 0DU9](https://stacks.math.columbia.edu/tag/0DU9)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The implication (1) `⟹` (2) of Stacks 0DU9.** If the canonical comparison
`ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is an equivalence over the
big fppf site, then `f` induces an isomorphism between the automorphism groups at `x` and at
`f(x)` for every point `x` of `|𝒳|`. No unramifiedness is needed for this implication. -/
theorem inducesIsomorphismAt_of_inertiaPullbackComparison_isEquivalenceOver
    (f : 𝒳 ⟶ 𝒴)
    (h : Nonempty (IsEquivalenceOver
      (RelativeInertia.toBase 𝒳.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴.val.val.p)
        𝒳.val.val.p 𝒴.val.val.p (RelativeInertia.π 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom))))
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) :
    InducesIsomorphismAt B S hS f q := by
  obtain ⟨E⟩ := h
  have := E.isEquivalence
  refine (inducesIsomorphismAt_iff_forall_representatives B S hS f q).mpr fun p _ b _ => ?_
  exact Functor.bijective_verticalAutMap 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) b

/-- **The implication (2) `⟹` (1) of Stacks 0DU9, for a 1-morphism representable by algebraic
spaces.** An unramified 1-morphism of algebraic stacks which is representable by algebraic spaces
and induces an isomorphism between the automorphism groups at every point of its source has
inertia comparison an equivalence over the big fppf site. -/
theorem inertiaPullbackComparison_isEquivalenceOver_of_isRepresentable
    (f : 𝒳 ⟶ 𝒴) (hu : IsUnramified B S hS f)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q) :
    Nonempty (IsEquivalenceOver
      (RelativeInertia.toBase 𝒳.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴.val.val.p)
        𝒳.val.val.p 𝒴.val.val.p (RelativeInertia.π 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom))) := by
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hF : F ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hfaith : F.Faithful := faithful_homFunctor_of_isDM B S hS f hu.1 hauto
  refine nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts pX pY F hF
    (fun A B m hm => F.map_injective (by rw [F.map_comp, F.map_comp]; exact hm)) ?_
  intro x β hβ
  have hβ' : pY.IsHomLift (𝟙 (pX.obj x)) β.asIso.hom := by
    refine IsHomLift.of_fac' pY _ _ (Functor.congr_obj hF x) (Functor.congr_obj hF x) ?_
    rw [hβ]
    simp
  obtain ⟨α, hα, hFα⟩ := exists_map_eq_of_isUnramified_of_isRepresentable B S hS f hrep hu hauto
    x β.asIso.hom hβ'
  have _ : IsIso α := Functor.isIso_of_fiber_isGroupoid
    (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid _) α hα
  refine ⟨Aut.of (asIso α), ?_, hFα⟩
  show pX.map α = _
  rw [IsHomLift.fac' pX (𝟙 (pX.obj x)) α]
  simp

/-- **The implication (2) `⟹` (1) of Stacks 0DU9.** An unramified 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks which induces an isomorphism between the automorphism groups at `x` and at
`f(x)` for every `x ∈ |𝒳|` has its inertia comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` an equivalence over the
big fppf site.

`f` is faithful by `AlgebraicGeometry.Stack.faithful_homFunctor_of_isDM`, hence representable
by algebraic spaces (Stacks 04Y5), and then
`AlgebraicGeometry.Stack.inertiaPullbackComparison_isEquivalenceOver_of_isRepresentable`
applies. -/
theorem inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt
    (f : 𝒳 ⟶ 𝒴) (hu : IsUnramified B S hS f)
    (hauto : ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS f q) :
    Nonempty (IsEquivalenceOver
      (RelativeInertia.toBase 𝒳.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴.val.val.p)
        𝒳.val.val.p 𝒴.val.val.p (RelativeInertia.π 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom))) :=
  inertiaPullbackComparison_isEquivalenceOver_of_isRepresentable B S hS f hu
    (AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful B S hS f
      (faithful_homFunctor_of_isDM B S hS f hu.1 hauto)) hauto

/-- **Stacks 0DU9.** Let `f : 𝒳 ⟶ 𝒴` be an unramified 1-morphism of algebraic stacks over `S`.
Then the canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of Stacks 06R5 is an isomorphism (an
equivalence over the big fppf site) if and only if `f` induces an isomorphism between the
automorphism groups at `x` and at `f(x)` (Stacks 0DTW) for every `x ∈ |𝒳|`. -/
@[stacks 0DU9]
theorem inertiaPullbackComparison_isEquivalenceOver_iff_inducesIsomorphismAt
    (f : 𝒳 ⟶ 𝒴) (hu : IsUnramified B S hS f) :
    Nonempty (IsEquivalenceOver
      (RelativeInertia.toBase 𝒳.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴.val.val.p)
        𝒳.val.val.p 𝒴.val.val.p (RelativeInertia.π 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor f.hom))
      (inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom))) ↔
      ∀ q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
        InducesIsomorphismAt B S hS f q :=
  ⟨fun h q => inducesIsomorphismAt_of_inertiaPullbackComparison_isEquivalenceOver B S hS f h q,
    inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS f hu⟩

end AlgebraicGeometry.Stack

end
