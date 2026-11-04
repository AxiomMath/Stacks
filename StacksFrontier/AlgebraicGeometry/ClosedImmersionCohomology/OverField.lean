module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic

/-!
# Cohomology over a field does not change along a closed immersion

`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso` compares the cohomology of `G`
on `Z` with that of `i_* G` on `X` as modules over `Γ(X, ⊤)`. For a scheme over a field the
cohomology is regarded as a `k`-vector space by restricting scalars further along `k ⟶ Γ(X, ⊤)`,
and this file performs that last restriction. The point of doing it is that finite
dimensionality is a statement about the `k`-structure and does **not** transport along a merely
additive isomorphism, so the `Γ(X, ⊤)`-linear comparison has to be pushed all the way down to
`k` before it can be used.

The composite `k ⟶ Γ(X, ⊤) ⟶ Γ(Z, ⊤)` is the structure map of `Z` over `k` — that is the only
compatibility needed, and it is `Scheme.Hom.appLE_comp_top`.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`: for a closed
  immersion `i : Z ⟶ X` and `f : X ⟶ Spec k`, the `k`-linear isomorphism
  `Hⁿ(Z, G) ≅ Hⁿ(X, i_* G)`.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion`:
  finite dimensionality transports across it.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_pushforward_of_isFinite`:
  **[Stacks, Tag 02O6] for a coherent module pushed forward from a closed subscheme that is
  finite over `k`**, unconditionally. This is the shape in which base case (2) of the
  [Stacks, Tag 01YH] dévissage of [Stacks, Tag 02O6] is consumed.

## Implementation notes

The `IsFinite` hypothesis is on the composite `i ≫ f`, the structure morphism of `Z` over `k` —
not on `i` and not on `f`. A closed immersion into a scheme that is *not* finite over `k` can
still have finite source, and that is the case the dévissage produces: a coherent module on a
curve whose support is a proper closed subset is pushed forward from a closed subscheme of
dimension `≤ 0`.

What this file does **not** do, so that no consumer assumes it: it does not produce the closed
subscheme. Going from "`M` is coherent on `X` with support a proper closed subset" to
"`M ≅ i_* G` for a closed immersion `i` with `i ≫ f` finite and `G` coherent" needs
`AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero` together with the step
from dimension `≤ 0` to finiteness over `k`, and neither is performed here.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- **Cohomology over a field is unchanged by pushing forward along a closed immersion**: the
isomorphism `Hⁿ(Z, G) ≅ Hⁿ(X, i_* G)` of `k`-vector spaces, for `i : Z ⟶ X` a closed immersion
and `f : X ⟶ Spec k` a structure morphism. -/
noncomputable def cohomologyOverFieldPushforwardIsoOfIsClosedImmersion
    [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) (G : Z.Modules) (n : ℕ) :
    cohomologyOverField k (i ≫ f) G n ≅
      cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n :=
  ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
      (i.app (⊤ : X.Opens)).hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appLE ⊤ ⊤ (by simp)).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, Scheme.Hom.appLE_comp_top i f (by simp) (by simp)]
        rfl) _ ≪≫
    (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward i G n).symm

/-- Finite dimensionality of cohomology transports along a closed immersion. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion
    [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) (G : Z.Modules) (n : ℕ)
    (h : FiniteDimensional k (cohomologyOverField k (i ≫ f) G n)) :
    FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n) :=
  Module.Finite.equiv
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f G n).toLinearEquiv

/-- **[Stacks, Tag 02O6] for a module pushed forward from a closed subscheme finite over the
base field**, unconditionally: if `Z` is finite over `k`, `i : Z ⟶ X` is a closed immersion and
`G` is coherent on `Z`, then every `Hⁿ(X, i_* G)` is a finite-dimensional `k`-vector space.

This is base case (2) of the [Stacks, Tag 01YH] dévissage of [Stacks, Tag 02O6], in the shape
`Stacks.Cohomology.CohomologyFinitenessDevissage` consumes: the finiteness input for a coherent
module supported on a proper closed subset of a curve, once that subset is presented as a closed
subscheme finite over `k`. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_isFinite
    [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsFinite (i ≫ f)]
    (G : Z.Modules) [G.IsCoherent] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n) :=
  finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k i f G n
    (finiteDimensional_cohomologyOverField_of_isFinite k (i ≫ f) G n)

end AlgebraicGeometry

end
