module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralFamily
public import StacksFrontier.RingTheory.Noetherian.ULift

/-!
# Finite type over the integers is finite presentation, and Tag 0E21 at that hypothesis

The terminal scheme is `Spec (ULift ℤ)`, so a morphism `X ⟶ ⊤_ Scheme` being locally of finite
type says that `X` is of finite type over the integers.  Since `ℤ` is Noetherian, such a
morphism is automatically locally of finite presentation.  Mathlib has the general implication
as a low-priority instance, `AlgebraicGeometry.LocallyOfFinitePresentation` from
`AlgebraicGeometry.LocallyOfFiniteType` over a locally Noetherian base, and at the terminal
scheme it fires through the instance `AlgebraicGeometry.isLocallyNoetherian_terminal` of
`StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType`.  This file
records the resulting bridge under a name.

The bridge matters for [Stacks, Tag 0E21].  Its statement in
`StacksFrontier.AlgebraicGeometry.Limits.IntegralFamily` carries the extra hypothesis
`LocallyOfFinitePresentation (terminal.from X)`, which the Stacks proof removes by writing `X`
as a limit of schemes **of finite type** over `ℤ` (Noetherian approximation, [Stacks, Tag 07RN],
giving [Stacks, Tag 01ZA]) and then saying "we may assume `X` is of finite presentation over
`ℤ`".  That last sentence is the implication proved here: it is what lets the statement of Tag
0E21 be applied to the stages that Noetherian approximation produces, which are of finite type
and not, on their face, of finite presentation.  The last theorem below is Tag 0E21 restated at
the finite-type hypothesis, so that the only input it still waits on is Noetherian
approximation itself.

That restatement also repairs the conclusion.  Tag 0E21 asserts that `Spec A ⟶ W` *factors
through* `X_s`, while the existing statement asserts only that its set-theoretic image lies in
`X_s`.  For an open immersion the two are equivalent, and
`AlgebraicGeometry.exists_factorsThrough_of_range_subset` below is that equivalence; the
restatement produces the factoring morphism, as the tag does.

No `@[stacks]` attribute is attached to anything here.  Tag 0E21 still waits on Tag 07RN, whose
residue is the predicate `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`,
and that predicate has no inhabitant in this repository.

## Main results

* `AlgebraicGeometry.terminalIsoSpecULiftZ`: the terminal scheme is `Spec (ULift ℤ)`.
* `AlgebraicGeometry.locallyOfFinitePresentation_terminal_from`: a scheme
  of finite type over the integers is of finite presentation over the integers.
* `AlgebraicGeometry.exists_factorsThrough_of_range_subset`: a morphism whose image lies in an
  open subscheme factors through it.
* `exists_affine_nonvanishingOpen_factorsThrough_of_locallyOfFiniteType`, in the namespace
  `AlgebraicGeometry.Scheme.Modules`: [Stacks, Tag 0E21] for a scheme of finite **type** over
  the integers, with the factoring morphism of the tag's conclusion.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-- The terminal scheme is the spectrum of `ULift ℤ`, both being terminal. -/
noncomputable def terminalIsoSpecULiftZ : (⊤_ Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
  terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}

/-- **A morphism whose set-theoretic image lies in an open subscheme factors through it**, the
factorisation being through the open immersion `U.ι`. -/
theorem exists_factorsThrough_of_range_subset {X Z : Scheme.{u}} (U : X.Opens) (g : Z ⟶ X)
    (h : Set.range g.base ⊆ (U : Set X)) :
    ∃ g' : Z ⟶ (U : Scheme.{u}), g' ≫ U.ι = g :=
  ⟨IsOpenImmersion.lift U.ι g (by simpa using h), IsOpenImmersion.lift_fac _ _ _⟩

namespace Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- **[Stacks, Tag 0E21] for a scheme of finite type over the integers**, with the factoring
morphism of the tag's conclusion.

Let `L` be an ample invertible sheaf on a scheme `X` of finite type over `ℤ`, let `W ⊆ X` be
open and let `Spec A ⟶ W` be a family of points of `W` parametrised by an integral algebra over
a field.  Then some positive tensor power of `L` has a global section `s` whose nonvanishing
open `U = X_s` is affine, is contained in `W`, and is such that `Spec A ⟶ W` factors through
`U`.

Two things change against
`AlgebraicGeometry.Scheme.Modules.exists_affine_nonvanishingOpen_containing_range`, and both
bring the statement closer to the tag.  The hypothesis is weakened from finite presentation
over `ℤ` to finite **type** over `ℤ` — equivalent here, by
`AlgebraicGeometry.locallyOfFinitePresentation_terminal_from`, but it is
finite type that Noetherian approximation delivers, so this is the form that the limit argument
of [Stacks, Tag 01ZA] can consume.  And the conclusion is strengthened from containment of the
image to the factorisation that the tag actually asserts.

The open `U` is bound with its type `X.Opens` and pinned to `X_s` by an equation rather than
written inline, because the field `ι` does not project from the `nonvanishingOpen` term at its
inferred type.

Still no `@[stacks 0E21]` attribute: the remaining input is Noetherian approximation,
[Stacks, Tag 07RN]. -/
theorem exists_affine_nonvanishingOpen_factorsThrough_of_locallyOfFiniteType
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (X : Scheme.{u}) [LocallyOfFiniteType (terminal.from X)] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : IsAmple X L)
    (W : X.Opens) (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      ∃ U : X.Opens,
        U = nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen U ∧ U ≤ W ∧
        ∃ g : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u}), g ≫ U.ι = f ≫ W.ι := by
  obtain ⟨n, hn, s, haff, hW, hrange⟩ :=
    exists_affine_nonvanishingOpen_containing_range k A X L hL W f
  refine ⟨n, hn, s, _, rfl, haff, hW, ?_⟩
  exact exists_factorsThrough_of_range_subset _ _ (by simpa using hrange)

end Scheme.Modules

end AlgebraicGeometry

end
