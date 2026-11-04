module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksCore.Tactic.StacksAttribute

/-!
# Proper morphisms with finite fibres are finite

[Stacks, Tag 02LS] lists four equivalent conditions on a morphism of schemes `f : X ⟶ S`:

1. `f` is finite;
2. `f` is proper with finite fibres;
3. `f` is proper and locally quasi-finite;
4. `f` is universally closed, separated, locally of finite type and has finite fibres.

Equivalence of (1) and (3) is Zariski's main theorem and is already in Mathlib, as
`AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`. This file adds the two
conditions phrased through the *fibres*, (2) and (4), which neither Mathlib nor this library
had. Both come from (1) ⟺ (3) and Mathlib's characterization of locally quasi-finite morphisms
by finiteness of their fibres, `locallyQuasiFinite_iff_finite_preimage_singleton`; condition (4)
is then condition (2) with `AlgebraicGeometry.IsProper` unfolded into its three parents.

A fibre criterion in terms of dimension is proved alongside: a fibre of dimension at most `0` of
a quasi-compact morphism locally of finite type is finite. Together with condition (2) this is
the form in which the tag is used by the fibre-dimension induction of [Stacks, Tag 095U].

## Main results

* `AlgebraicGeometry.isFinite_iff_isProper_and_forall_finite_preimage_singleton` —
  **[Stacks, Tag 02LS], (1) ⟺ (2)**: a morphism of schemes is finite exactly when it is proper
  and every fibre is finite.
* `isFinite_iff_isSeparated_universallyClosed_locallyOfFiniteType_and_finite_fibres` —
  **[Stacks, Tag 02LS], (1) ⟺ (4)**: the same with properness spelled out.
* `AlgebraicGeometry.finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero` — a fibre of
  topological Krull dimension at most `0` of a quasi-compact morphism locally of finite type is
  finite.

## Implementation notes

No quasi-compactness hypothesis appears in the two equivalences even though
`locallyQuasiFinite_iff_finite_preimage_singleton` needs one: `AlgebraicGeometry.IsProper`
contains `AlgebraicGeometry.UniversallyClosed`, which already yields
`AlgebraicGeometry.QuasiCompact`. The source's properness, which asks for finite type rather
than merely locally of finite type, is therefore matched exactly by `IsProper` here.

The dimension criterion runs through local Artinianness rather than through dimension theory on
the fibre: a fibre of a morphism locally of finite type is locally Noetherian, a locally
Noetherian scheme of dimension at most `0` is locally Artinian, and a locally Artinian scheme is
discrete. A fibre of a quasi-compact morphism is compact, and a compact discrete space is
finite.

## References

* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 02LS], condition (1) ⟺ condition (2).** A morphism of schemes is finite
exactly when it is proper and all of its fibres are finite.

The source's properness is `AlgebraicGeometry.IsProper`, which contains
`AlgebraicGeometry.UniversallyClosed` and hence `AlgebraicGeometry.QuasiCompact`, so no further
hypothesis is needed to pass between finiteness of the fibres and local quasi-finiteness. -/
@[stacks 02LS "condition (1) <=> condition (2): a morphism of schemes is finite exactly when it \
is proper with finite fibres. PROVED outright, with no hypothesis beyond the two sides of the \
equivalence: Mathlib's IsFinite.iff_isProper_and_locallyQuasiFinite is the tag's own \
(1) <=> (3), and locallyQuasiFinite_iff_finite_preimage_singleton turns local quasi-finiteness \
into finiteness of the fibres. Properness in Mathlib's sense contains universal closedness and \
therefore quasi-compactness, so the source's finite-type requirement is met.",
  ega "III 4.4.11" "more general",
  ega "III 4.4.2" "more general",
  ega "IV 18.12.4"]
theorem isFinite_iff_isProper_and_forall_finite_preimage_singleton {X S : Scheme.{u}}
    (f : X ⟶ S) :
    IsFinite f ↔ IsProper f ∧ ∀ s : S, (f ⁻¹' {s}).Finite := by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite f]
  exact and_congr_right fun _ ↦ locallyQuasiFinite_iff_finite_preimage_singleton

/-- **[Stacks, Tag 02LS], condition (1) ⟺ condition (4).** A morphism of schemes is finite
exactly when it is separated, universally closed, locally of finite type and has finite fibres.
This is the previous equivalence with `AlgebraicGeometry.IsProper` unfolded into its three
parents. -/
@[stacks 02LS "condition (1) <=> condition (4): a morphism of schemes is finite exactly when it \
is separated, universally closed, locally of finite type and has finite fibres. PROVED outright \
from condition (1) <=> condition (2) by unfolding Mathlib's IsProper into its three parents.",
  ega "III 4.4.2" "more general"]
theorem isFinite_iff_isSeparated_universallyClosed_locallyOfFiniteType_and_finite_fibres
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsFinite f ↔ (IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f) ∧
      ∀ s : S, (f ⁻¹' {s}).Finite := by
  rw [isFinite_iff_isProper_and_forall_finite_preimage_singleton f, isProper_iff]

/-- A fibre of topological Krull dimension at most `0` of a quasi-compact morphism locally of
finite type is finite. The fibre is locally Noetherian, hence locally Artinian by the dimension
bound, hence discrete; it is compact because `f` is quasi-compact, and a compact discrete space
is finite. -/
@[ega "0 14.1.9" "necessity, special case"]
theorem finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (s : S)
    (hdim : topologicalKrullDim (f.fiber s) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    (f ⁻¹' {s}).Finite := by
  have : IsLocallyNoetherian (f.fiber s) := isLocallyNoetherian_fiber_of_locallyOfFiniteType f s
  have : IsLocallyArtinian (f.fiber s) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (by simpa using hdim)
  have : Finite (f.fiber s) := finite_of_compact_of_discrete
  have : Finite (f ⁻¹' {s} : Set X) := Finite.of_equiv _ (f.fiberHomeo s).toEquiv
  exact Set.toFinite _

end AlgebraicGeometry

end
