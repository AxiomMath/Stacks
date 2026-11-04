module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Jacobson
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.RingTheory.ZariskiPair
public import StacksFrontier.Topology.Constructible.NormalForm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inputs for the essentially-finite-type closedness criterion

The point-set facts are collected here, each stated over library vocabulary, for use in the
proof that the essentially-finite-type extension condition forces closedness of all
finite-dimensional affine-space base changes.

## Main results

* `exists_open_punctured_subset_of_specializes`: in a Noetherian sober space, if an open set
  misses a closed point `c` and no other point specializing to `c` is outside it, then `c` has
  an open neighbourhood whose puncture at `c` lies in that open set.
* `exists_closedPoint_mem_of_isConstructible` and `exists_open_closedPoint_mem`: a nonempty
  constructible set contains a point closed in the whole space when the space is Jacobson, and
  contains a point closed in some open subspace in general.

## Implementation notes

The Nagata statement is the Nagata case of Stacks 035A and the three point-set statements are
the topological steps of the proof of Stacks 0GWV.  They are separated from the geometric
argument because none of them mentions a morphism of schemes.  Stacks 02IM parts (1) and (3),
also needed by that argument, are imported from
`StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic`.

## References

* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.NagataExtensionClosed

/-! ### Point-set steps -/

/-- In a Noetherian sober `T0` space, let `c` be a closed point outside an open set `U` such
that no point other than `c` specializing to `c` lies outside `U`.  Then `c` has an open
neighbourhood whose puncture at `c` is contained in `U`.  The proof passes to the closed
complement of `U`, in which `{c}` is an irreducible component. -/
theorem exists_open_punctured_subset_of_specializes
    {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    [T0Space T] (c : T) (hc : IsClosed ({c} : Set T))
    (U : Set T) (hU : IsOpen U) (hcU : c ∉ U)
    (hgen : ∀ z, z ∉ U → z ⤳ c → z = c) :
    ∃ V : Set T, IsOpen V ∧ c ∈ V ∧ V \ {c} ⊆ U := by
  classical
  let F := Uᶜ
  let c' : F := ⟨c, hcU⟩
  have : QuasiSober F := hU.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  have hc' : IsClosed ({c'} : Set F) := by
    convert hc.preimage continuous_subtype_val using 1
    ext z
    simp [c', Subtype.ext_iff]
  have hcomp : ({c'} : Set F) ∈ irreducibleComponents F := by
    refine ⟨isIrreducible_singleton, ?_⟩
    intro Z hZ hcZ
    have heq : hZ.genericPoint = c' := Subtype.ext <| hgen _ hZ.genericPoint.2 <|
      (hZ.isGenericPoint_genericPoint_closure.specializes
        (subset_closure (hcZ (Set.mem_singleton c')))).map continuous_subtype_val
    have hcl : closure Z = {c'} := by
      rw [← hZ.genericPoint_closure_eq, heq, hc'.closure_eq]
    exact hcl ▸ subset_closure
  obtain ⟨W, hW, hWne, hWsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hcomp
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp hW
  obtain ⟨z, hz⟩ := hWne
  obtain rfl : z = c' := hWsub hz
  refine ⟨V, hV, ?_, ?_⟩
  · rwa [← hVW] at hz
  · intro x hx
    by_contra hxU
    have hxW : (⟨x, hxU⟩ : F) ∈ W := by
      rw [← hVW]
      exact hx.1
    exact hx.2 (congrArg Subtype.val (hWsub hxW))

/-- A nonempty constructible subset of a Jacobson space contains a point that is closed in the
whole space.  The normal form of a constructible set reduces this to the locally closed case. -/
@[ega "IV 8.1.3" "more general"]
theorem exists_closedPoint_mem_of_isConstructible
    {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    {E : Set T} (hE : Topology.IsConstructible E) (hne : E.Nonempty) :
    ∃ t ∈ E, IsClosed ({t} : Set T) := by
  obtain ⟨s, hs, rfl⟩ := Topology.isConstructible_iff_exists_finset_biUnion_inter_compl.mp hE
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨t, ht, htc⟩ := nonempty_inter_closedPoints ⟨x, hxp⟩
    ((hs p hp).1.isLocallyClosed.inter (hs p hp).2.2.1.isClosed_compl.isLocallyClosed)
  exact ⟨t, Set.mem_iUnion₂.mpr ⟨p, hp, ht⟩, htc⟩

/-- A nonempty constructible subset of a Noetherian `T0` space meets some open subspace in a
point closed in that subspace: take one of the opens appearing in the normal form of the
constructible set. -/
theorem exists_open_closedPoint_mem
    {T : Type*} [TopologicalSpace T] [T0Space T] [NoetherianSpace T]
    {E : Set T} (hE : Topology.IsConstructible E) (hne : E.Nonempty) :
    ∃ (U : Opens T) (x : U), x.1 ∈ E ∧ IsClosed ({x} : Set U) := by
  obtain ⟨s, hs, rfl⟩ := Topology.isConstructible_iff_exists_finset_biUnion_inter_compl.mp hE
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
  let U : Opens T := ⟨p.1, (hs p hp).1⟩
  have hcl : IsClosed (Subtype.val ⁻¹' p.2ᶜ : Set U) :=
    (hs p hp).2.2.1.isClosed_compl.preimage continuous_subtype_val
  have : NoetherianSpace U := NoetherianSpace.set _
  obtain ⟨y, hy, hycl⟩ := hcl.exists_closed_singleton ⟨⟨x, hxp.1⟩, hxp.2⟩
  exact ⟨U, y, Set.mem_iUnion₂.mpr ⟨p, hp, y.2, hy⟩, hycl⟩

end Stacks.AlgebraicGeometry.NagataExtensionClosed
