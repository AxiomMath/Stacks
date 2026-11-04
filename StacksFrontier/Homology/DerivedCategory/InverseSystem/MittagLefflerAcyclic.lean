module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Mittag--Leffler inverse systems are right acyclic for the inverse limit

An inverse system of abelian groups indexed by `ℕᵒᵖ` whose underlying diagram of sets is
Mittag--Leffler is right acyclic for the inverse-limit functor, in the sense of
`CategoryTheory.Functor.rightAcyclic` ([Stacks, Tag 0157]): the complex `A[0]` computes the right
derived functor of `lim` on the bounded below derived category. This is the class of objects
adapted to `lim` in the sense of [Stacks, Tag 05T8], and the two hypotheses of that tag are the
construction of a monomorphism into a Mittag--Leffler system and the behaviour of the class in a
short exact sequence.

## Main results

* `Rlim.rightAcyclic_lim_of_isMittagLeffler`: **a Mittag--Leffler inverse system is right
  acyclic for `lim`.**

## What is and is not proved

The two hypotheses of [Stacks, Tag 05T8] for the class of Mittag--Leffler systems are proved in
`StacksFrontier/Homology/DerivedCategory/InverseSystem/Rlim.lean`: `Rlim.exists_mono_mittagLeffler`
embeds every inverse system in a Mittag--Leffler one, by the tower of initial products of its
terms, and `Rlim.mittagLeffler_shortExact_map_lim` is the behaviour of the class in a short exact
sequence. This module only combines them through `CategoryTheory.Functor.le_rightAcyclic`.

The theorem is stated with the existence of the right derived functor as an instance argument
rather than bundled in an existential, which is the form a consumer can use: under
`EnoughInjectives` of the category of inverse systems that instance is supplied by Mathlib, and
`Stacks.RightDerivedComp.rightAcyclic_iff_acyclic` then turns the conclusion into the vanishing
of Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` of `lim` in positive degrees.

Not proved here: anything about the *unbounded* derived functor of `lim`. The existence and
computation of that functor is [Stacks, Tag 07KW], which is
`Rlim.lim_hasRightDerivedFunctor_and_computations` in `Rlim.lean`.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 02N1](https://stacks.math.columbia.edu/tag/02N1)
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory Opposite

namespace Rlim

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The inverse-limit functor on inverse systems of abelian groups is additive. -/
noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **A Mittag--Leffler inverse system of abelian groups is right acyclic for the inverse
limit.** That is, the complex `A[0]` computes the right derived functor of
`lim : (ℕᵒᵖ ⥤ Ab) ⥤ Ab` on the bounded below derived category, in the sense of
[Stacks, Tag 0157].

This is [Stacks, Tag 05T8] for the class of Mittag--Leffler systems, whose two hypotheses are
`Rlim.exists_mono_mittagLeffler` and `Rlim.mittagLeffler_shortExact_map_lim`; the class is
adapted to `lim` because a quotient of a Mittag--Leffler system is Mittag--Leffler and because
the inverse limit of a short exact sequence with Mittag--Leffler kernel system stays short
exact, both parts of [Stacks, Tag 02N1].

The existence of the right derived functor is an instance argument; under
`CategoryTheory.EnoughInjectives` of the category of inverse systems it is supplied by
Mathlib's derivability structure of injective objects. Read through
`Stacks.RightDerivedComp.rightAcyclic_iff_acyclic`, the conclusion says that Mathlib's
`ℕ`-indexed `CategoryTheory.Functor.rightDerived` of `lim` vanishes on `A` in every positive
degree. -/
@[sga "4½ Etat_0 4.2.3.2" "special case"]
theorem rightAcyclic_lim_of_isMittagLeffler
    [((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso Rlim.InvSystemAb.{u})]
    (A : Rlim.InvSystemAb.{u}) (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightAcyclic A :=
  Functor.le_rightAcyclic (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u})
    (fun B => (B ⋙ forget Ab.{u}).IsMittagLeffler)
    (fun X => by
      obtain ⟨B, i, hi, hB⟩ := exists_mono_mittagLeffler X
      exact ⟨B, hB, i, hi⟩)
    mittagLeffler_shortExact_map_lim A hA

end Rlim

end
