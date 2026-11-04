module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons

/-!
# Affine objects of the big fppf site are absolutely quasi-separated

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine`: the presheaf
  represented by an affine object of the big fppf site over `S` is absolutely quasi-separated.

## Implementation notes

An affine scheme is a quasi-separated topological space, so the represented presheaf satisfies
condition (iota) of Stacks 03JX, and that condition gives absolute quasi-separatedness.

The statement had three declarations with the same one-line proof, in
`Spaces/ConstructiblePointsQuasiSeparated.lean`, `Spaces/FinitePresentation/QcqsCriterion.lean`
and `Spaces/MaximalNonSchematicQuotient.lean`, no two of which import one another. Two of the
three were identical up to binder placement — one bound `hZ` in its signature while the other
took it from a section `variable` block — so comparing signature text makes them look distinct;
they were found by reading the bodies, not by hashing the signatures.

It lives in a module of its own rather than in any of them. The ingredient,
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme`
(`Spaces/Decent/ConditionComparisons.lean:175`), has a closure of 1593 modules which is already
contained in the closure of all three consumers (3636, 3075 and 2852), so this module adds
exactly one module to each.

The surviving form is the general one, taking the terminal-containment witness `hZ` as a
parameter, with `B`, `S` and `hS` explicit as the majority of the call sites passed them. The
copy in `Spaces/ConstructiblePointsQuasiSeparated.lean` fixed `hZ` to
`AlgebraicGeometry.BigFppfSite.contains_terminal`; that is this statement at
`hZ := B.contains_terminal`, so the general form is a strengthening and no call site loses
anything.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine object of the site over `S` represents an absolutely quasi-separated algebraic
space.** An affine scheme is a quasi-separated topological space, so the represented presheaf
satisfies condition (iota) of Stacks 03JX, which gives absolute quasi-separatedness. -/
theorem isAbsolutelyQuasiSeparated_yoneda_of_isAffine
    (hZ : B.Contains (⊤_ Scheme.{u})) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T) :=
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj T) hZ
    ⟨T, inferInstance, ⟨Functor.RepresentableBy.yoneda T⟩⟩

end AlgebraicGeometry.Space

end
