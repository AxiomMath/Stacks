module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# A lower shriek of abelian sheaves is exact as soon as it preserves monomorphisms

The lower shriek of abelian sheaves along a continuous functor of sites is a left adjoint, so it
is right exact for free. Its left exactness is the content of a theorem, but once it is known to
preserve monomorphisms no further geometry is needed: a right exact additive functor between
abelian categories which preserves monomorphisms preserves homology, hence all finite limits.
This file isolates that passage, so that a proof of monomorphism preservation — the form in which
left exactness of a lower shriek is usually established, and the form in which the comparison
theorems for cohomology on a bigger site consume it — upgrades to full exactness.

## Main results

* `Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms`: a right
  exact additive functor between abelian categories which preserves monomorphisms preserves
  finite limits.
* `Stacks.Sites.AbelianLowerShriek.exactFunctor_of_preservesMonomorphisms`: the same, stated as
  exactness.
* `Stacks.Sites.AbelianLowerShriek.exactFunctor_sheafPullback_of_preservesMonomorphisms`: the
  lower shriek of abelian sheaves along a continuous functor of sites is exact as soon as it
  preserves monomorphisms.

## Implementation notes

The hypothesis of the general statement is right exactness rather than the existence of a right
adjoint, because that is all the argument uses and because the two lower-shriek functors of
`Mathlib.CategoryTheory.Sites.Pullback` — the one built from an abstract right adjoint and the one
built from left Kan extension and sheafification — are then both covered without transporting
along their comparison isomorphism.

Additivity of the lower shriek is deduced from additivity of restriction through the adjunction,
rather than from preservation of biproducts, because restriction is additive at the level of
presheaves and the hom-group of sheaves is the hom-group of the underlying presheaves.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Sites.AbelianLowerShriek

section Abstract

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- **A right exact additive functor between abelian categories which preserves monomorphisms
preserves finite limits.** Right exactness gives the cokernel half of homology preservation and
monomorphism preservation gives the kernel half, so the functor preserves homology; an additive
functor preserving homology is left exact. -/
theorem preservesFiniteLimits_of_preservesMonomorphisms (F : A ⥤ B) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesMonomorphisms] : PreservesFiniteLimits F :=
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels F
  F.preservesFiniteLimits_of_preservesHomology

/-- **A right exact additive functor between abelian categories which preserves monomorphisms is
exact.** -/
theorem exactFunctor_of_preservesMonomorphisms (F : A ⥤ B) [F.Additive]
    [PreservesFiniteColimits F] [F.PreservesMonomorphisms] : exactFunctor A B F :=
  (exactFunctor_iff F).2 ⟨preservesFiniteLimits_of_preservesMonomorphisms F, inferInstance⟩

end Abstract

section Sites

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type*) [Category* A]

/-- **Restriction of sheaves along a continuous functor is additive.** The hom-group of sheaves is
the hom-group of the underlying presheaves, where restriction is precomposition. -/
instance additive_sheafPushforwardContinuous [Preadditive A] [G.IsContinuous J K] :
    (G.sheafPushforwardContinuous A J K).Additive where
  map_add := by intro X Y f g; ext U; exact rfl

variable [Abelian A] [G.IsContinuous J K] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]

/-- **The lower shriek of abelian sheaves is right exact.** It is a left adjoint of restriction. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits
      (Functor.sheafPullbackConstruction.sheafPullback G A J K) :=
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).isLeftAdjoint
  inferInstance

/-- **The lower shriek of abelian sheaves is additive.** Restriction is additive and the lower
shriek is its left adjoint. -/
instance additive_sheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback G A J K).Additive :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).left_adjoint_additive

/-- **The lower shriek of abelian sheaves along a continuous functor of sites is exact as soon as
it preserves monomorphisms.** Right exactness is automatic, being a left adjoint; the remaining
content is the hypothesis. -/
theorem exactFunctor_sheafPullback_of_preservesMonomorphisms [HasSheafify J A] [HasSheafify K A]
    [(Functor.sheafPullbackConstruction.sheafPullback G A J K).PreservesMonomorphisms] :
    exactFunctor (Sheaf J A) (Sheaf K A)
      (Functor.sheafPullbackConstruction.sheafPullback G A J K) :=
  exactFunctor_of_preservesMonomorphisms _

end Sites

end Stacks.Sites.AbelianLowerShriek

end
