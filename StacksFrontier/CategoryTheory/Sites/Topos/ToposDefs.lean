module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Topoi and morphisms of topoi

## Main results

* `LeftAdjointsPreserveFiniteLimits`: the left-exactness requirement in the definition of a
  morphism of topoi (Stacks 00XA).

Tags covered: 00XA.
-/

@[expose] public section

open CategoryTheory

/-- **Stacks 00XA.** A *topos* is a category `Sheaf J A` of sheaves on a site, and a *morphism of
topoi* `f` from `Sheaf K A` to `Sheaf J A` is a pair of functors `f_* : Sheaf K A ⥤ Sheaf J A` and
`f⁻¹ : Sheaf J A ⥤ Sheaf K A` such that `f⁻¹ ⊣ f_*` bifunctorially and `f⁻¹` is left exact. This
records the second requirement: the left adjoint of such a pair preserves finite limits. -/
@[stacks 00XA]
def LeftAdjointsPreserveFiniteLimits (C : Type*) [Category C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] (K : GrothendieckTopology D)
    (A : Type*) [Category A] : Prop :=
  ∀ (f_star : Sheaf K A ⥤ Sheaf J A) (f_inv : Sheaf J A ⥤ Sheaf K A),
    (f_inv ⊣ f_star) → Limits.PreservesFiniteLimits f_inv
