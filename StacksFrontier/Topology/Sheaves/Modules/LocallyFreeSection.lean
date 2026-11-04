module

public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
import StacksCore.Tactic.StacksAttribute

/-!
# Locally free sheaves: the covering set of Stacks 01C5

Stacks 01C5 is a *section* tag — `\section{Locally free sheaves}` of the chapter on sheaves of
modules, which opens "Let `(X, O_X)` be a ringed space". It states no mathematics of its own, so
by the covering-set rule its tag belongs on the declarations that carry the section's content,
and this module places it there. Every one of those declarations is already proved elsewhere in
this library or in Mathlib; nothing is proved here, and nothing is restated here.

## The section's content, and where each item lives

The section contains one definition in three parts and five lemmas.

* 01C6, the definition, in three parts. Part (1), *locally free*, is Mathlib's
  `SheafOfModules.IsLocallyFree`. Parts (2) and (3), *finite locally free* and *finite locally
  free of rank `r`*, are `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and
  `.IsFiniteLocallyFreeOfRank` of `StacksFrontier.Topology.Sheaves.Modules.LocallyFree`.
* 01C7, that a locally free sheaf is quasi-coherent, is Mathlib's
  `SheafOfModules.instIsQuasicoherentOfIsLocallyFree`, already recorded under its own tag in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
* 01C8, that the pullback of a locally free module along a morphism of ringed spaces is locally
  free, is `pullback_isLocallyFree` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePullback`.
* 01C9, the locally constant rank function of a locally free sheaf on a ringed space all of whose
  structure-sheaf stalks are nonzero, is `LocallyFreeRank.exists_locallyConstant_rank` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank`.
* 089Q, that a map of finite locally free modules of the same rank `r` is an isomorphism exactly
  when it is surjective, is `Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank` of
  `StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank`.
* 0BCI, that over local stalks a direct summand of a finite locally free module is finite locally
  free, is `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_retract` of
  `StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract`.

Taken together these eight declarations state everything the section asserts, so they are the
covering set of 01C5 and each carries the section tag below. The section's two remarks — that
the stalks `O_{X, x}` are allowed to be the zero ring, which is why 01C9 carries a nonvanishing
hypothesis, and that a finite direct sum of locally free sheaves is locally free while an
infinite one need not be — are unlabelled prose in the source and assert nothing under 01C5.

## Implementation notes

The covering set is spread over six modules and two of its members are Mathlib declarations, so
the tag cannot be written as an attribute at the point of definition. `add_to_stacks` is the
mechanism this library uses for exactly that situation: it records a tag against a declaration
already elaborated, and its duplicate check is per declaration-and-tag pair, so one tag over
several declarations is recorded once for each. The precedent is 01C7 itself, recorded over three
declarations in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.

## References

* [Stacks Project, Tag 01C5](https://stacks.math.columbia.edu/tag/01C5)
-/

@[expose] public section

-- Tag 01C5 is the section tag of `\section{Locally free sheaves}`; these eight declarations are
-- its covering set, one for each labelled item the section contains.
add_to_stacks 01C5 "section tag; 01C6 (1), locally free" SheafOfModules.IsLocallyFree
add_to_ega "0 5.4.1" "more general" SheafOfModules.IsLocallyFree
add_to_ega "III 7.9.1" SheafOfModules.IsLocallyFree
add_to_ega "IV 21.5.3" "partial" SheafOfModules.IsLocallyFree
add_to_stacks 01C5 "section tag; 01C6 (2), finite locally free"
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
add_to_stacks 01C5 "section tag; 01C6 (3), of rank r"
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
add_to_stacks 01C5 "section tag; 01C7, locally free ⇒ quasi-coherent"
  SheafOfModules.instIsQuasicoherentOfIsLocallyFree
add_to_stacks 01C5 "section tag; 01C8, pullback is locally free" pullback_isLocallyFree
add_to_stacks 01C5 "section tag; 01C9, locally constant rank"
  LocallyFreeRank.exists_locallyConstant_rank
add_to_stacks 01C5 "section tag; 089Q, iso iff surjective in equal rank"
  Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank
add_to_stacks 01C5 "section tag; 0BCI, summand of finite locally free"
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_retract
