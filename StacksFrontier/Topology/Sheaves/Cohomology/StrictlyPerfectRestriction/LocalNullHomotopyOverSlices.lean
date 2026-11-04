module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Topology.Sheaves.Over
public import StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLift
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# Local null-homotopy of a map out of a strictly perfect complex

Stacks 08C7. Let `X` be a ringed space, let `E` be a strictly perfect complex of
`𝒪_X`-modules concentrated in degrees `≥ a`, and let `α : E ⟶ F` be a map to a complex whose
cohomology sheaves vanish in all degrees `≥ a`. Then every point of `X` has an open
neighbourhood over which `α` becomes null-homotopic. In particular this holds when `F` is
acyclic.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_isZero_homology`: the
  statement above, for a strictly perfect complex concentrated in degrees `≥ a` and a target
  with vanishing cohomology in degrees `≥ a`.
* `AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_acyclic`: the special case of
  an acyclic target.

## Implementation notes

Both results are delegations to
`Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology` and
`Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_acyclic`, which carry the
proof: a downward induction on the degrees where `E` can be nonzero, in which the component of
`α` in the top degree that still matters is written as a coboundary over a small enough open
set. The two statements are the same statement — `StrictlyPerfect.OXMod`,
`StrictlyPerfect.IsStrictlyPerfect` and `StrictlyPerfect.structureSheafOfRings` are the same
declarations on both sides — and these are the names under which the two parts of Tag 08C7 are
used from the ringed-space files, so they are kept.

Restriction to an open subspace is applied degreewise through
`SheafOfModules.overFunctor (StrictlyPerfect.structureSheafOfRings X) U`, which is the form in
which the conclusion is a homotopy between morphisms of complexes of modules over `𝒪_X|_U` on
the site `Over U`.

All universes coincide, as they must for `StrictlyPerfect.OXMod` to exist: the ring universe
and the space universe of the ringed space have to agree, and `StrictlyPerfect.OXMod` fixes the
module universe to the same one. This is the case the whole strictly-perfect ladder — Stacks
08C4, 08C5, 08C6 and 08CB — is developed in.

## References

* [Stacks Project, Tag 08C7](https://stacks.math.columbia.edu/tag/08C7)
* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}
variable {E F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (α : E ⟶ F)

/-- A map from a strictly perfect complex concentrated in degrees at least
`a` is locally null-homotopic if the target's cohomology vanishes in those
degrees.

This is the ringed-space-facing name for
`Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology`, which
carries the proof. -/
@[stacks 08C7 "part (2)", sga "6 I 4.1" "ringed space"]
theorem exists_local_homotopy_zero_of_isZero_homology (a : ℤ)
    (hE : StrictlyPerfect.IsStrictlyPerfect E) (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) :=
  _root_.Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology
    α a hE hE₀ hF

/-- A map from a strictly perfect complex to an acyclic complex is locally
null-homotopic.

This is the ringed-space-facing name for
`Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_acyclic`, which carries the
proof. -/
@[stacks 08C7 "part (1)", sga "6 I 4.1" "ringed space"]
theorem exists_local_homotopy_zero_of_acyclic
    (hE : StrictlyPerfect.IsStrictlyPerfect E) (hF : F.Acyclic) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) :=
  _root_.Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_acyclic α hE hF

end AlgebraicGeometry.RingedSpace

end
