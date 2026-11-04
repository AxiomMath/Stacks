module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Properness and closed points of irreducible schemes

Removing a closed point from an irreducible scheme of positive dimension leaves an open
subscheme which is no longer proper over the base. This is the obstruction which prevents a
positive-dimensional variety from being covered by proper opens, and it is the reason a
complete curve cannot have a closed point deleted.

## Main results

* `AlgebraicGeometry.not_isProper_compl_singleton`: the complement of a closed point in an
  irreducible scheme of positive dimension is not proper over any base over which the
  scheme is separated.

## Implementation notes

The open complement is represented by the corresponding `Scheme.Opens` and its canonical open
immersion into the original scheme. The statement is given over an arbitrary base scheme: the
proof only uses that the original scheme is separated over that base. The source is the special
case in which the base is the spectrum of a field.

## References

* [Stacks Project, Tag 0A24](https://stacks.math.columbia.edu/tag/0A24)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks 0A24.** Removing a closed point from an irreducible scheme of positive dimension
gives an open subscheme which is not proper over any base over which the scheme is separated. -/
@[stacks 0A24]
public lemma not_isProper_compl_singleton
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [IrreducibleSpace X] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : 0 < topologicalKrullDim X) :
    let U : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩
    ¬ IsProper (U.ι ≫ f) := by
  classical
  dsimp only
  set U : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩ with hU
  have : Nontrivial X := by
    by_contra h
    have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    exact (not_le_of_gt hdim) (topologicalKrullDim_zero_of_discreteTopology X)
  intro hproper
  have : UniversallyClosed (U.ι ≫ f) := hproper.toUniversallyClosed
  have : UniversallyClosed U.ι := .of_comp_of_isSeparated U.ι f
  simpa [U] using (nonempty_preirreducible_inter
    (by simpa [U] using U.ι.isClosedMap.isClosed_range.isOpen_compl)
    U.2 (Set.singleton_nonempty x) (Set.nonempty_compl_of_nontrivial x))

end AlgebraicGeometry
