module

public import StacksFrontier.Topology.Connected.ClopenIntersection

/-!
# Intersections of clopens in a quasi-compact space

In a quasi-compact space with a basis of quasi-compact opens whose pairwise intersections are
quasi-compact, a subset is an intersection of clopen subsets exactly when it is closed and a
union of connected components.

## Main definitions

* `IsUnionOfConnectedComponents`: a subset containing the connected component of each of its
  points.
* `IsIntersectionOfClopens`: a subset that is an intersection of a family of clopen subsets.

## Main results

* The hypotheses on `X` — the quasi-compact opens form a basis for the topology, and the
  intersection of two quasi-compact opens is quasi-compact — are Mathlib's `PrespectralSpace`
  and `QuasiSeparatedSpace`.
* `main_theorem04PL`: the two descriptions of such a subset agree.
-/

@[expose] public section

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- A subset `T ⊆ X` is a *union of connected components of `X`* if for every
`x ∈ T`, the connected component of `x` in `X` is entirely contained in `T`. -/
def IsUnionOfConnectedComponents (T : Set X) : Prop :=
  ∀ x ∈ T, connectedComponent x ⊆ T

/-- A subset `T` is an intersection of clopen subsets of `X`: there is a family
`{U α}` of clopen subsets such that `T = ⋂ α, U α`. -/
def IsIntersectionOfClopens (T : Set X) : Prop :=
  ∃ (A : Type u) (U : A → Set X), (∀ α, IsClopen (U α)) ∧ T = ⋂ α, U α

/-- An intersection of clopen subsets is closed. -/
lemma IsIntersectionOfClopens.isClosed {T : Set X} (hT : IsIntersectionOfClopens T) :
    IsClosed T := by
  obtain ⟨A, U, hU, rfl⟩ := hT
  exact isClosed_iInter fun α => (hU α).isClosed

/-- An intersection of clopen subsets is a union of connected components, because a clopen set
contains the connected component of each of its points. -/
lemma IsIntersectionOfClopens.isUnionOfConnectedComponents {T : Set X}
    (hT : IsIntersectionOfClopens T) : IsUnionOfConnectedComponents T := by
  obtain ⟨A, U, hU, rfl⟩ := hT
  exact fun x hx => subset_iInter fun α => (hU α).connectedComponent_subset (mem_iInter.mp hx α)

/-- In a quasi-compact, quasi-separated space with a basis of quasi-compact opens, a closed union
of connected components is separated from any point outside it by a clopen set: the connected
component of the point is the intersection of the clopens through it (Stacks 005F), and
quasi-compactness of `T` cuts that intersection down to a finite subfamily. -/
lemma exists_isClopen_superset_notMem_of_isUnionOfConnectedComponents
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hTcl : IsClosed T) (hT : IsUnionOfConnectedComponents T)
    {x : X} (hx : x ∉ T) : ∃ W : Set X, IsClopen W ∧ T ⊆ W ∧ x ∉ W := by
  have hqc : ∀ ⦃U V : Set X⦄, IsOpen U → IsCompact U → IsOpen V → IsCompact V →
      IsCompact (U ∩ V) := fun U V => QuasiSeparatedSpace.inter_isCompact U V
  have hdisj : Disjoint T (⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen_of_compactSpace
      PrespectralSpace.isTopologicalBasis (fun _ hU => hU.2) hqc x]
    exact (disjoint_left.mpr fun y hy hyT =>
      hx (hT y hyT (connectedComponent_eq hy ▸ mem_connectedComponent))).symm
  obtain ⟨u, hu⟩ := hTcl.isCompact.elim_finite_subfamily_closed
    (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } => (Z : Set X))
    (fun ⟨_, hZ, _⟩ => hZ.isClosed) hdisj
  exact ⟨(⋂ Z ∈ u, (Z : Set X))ᶜ, (isClopen_biInter_finset fun ⟨_, hZ, _⟩ _ => hZ).compl,
    disjoint_left.mp hu, fun hxc => hxc (mem_biInter fun ⟨_, _, hxZ⟩ _ => hxZ)⟩

/-- In a quasi-compact, quasi-separated space with a basis of quasi-compact opens, a closed union
of connected components is an intersection of clopen subsets: take the clopens separating it from
each point of its complement. -/
lemma isIntersectionOfClopens_of_isClosed_of_isUnionOfConnectedComponents
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hTcl : IsClosed T) (hT : IsUnionOfConnectedComponents T) :
    IsIntersectionOfClopens T := by
  choose W hWcl hWsup hWmem using fun x (hx : x ∉ T) =>
    exists_isClopen_superset_notMem_of_isUnionOfConnectedComponents hTcl hT hx
  refine ⟨↑(Tᶜ), fun x : ↑(Tᶜ) => W x.1 x.2, fun x => hWcl x.1 x.2,
    Subset.antisymm (subset_iInter fun x => hWsup x.1 x.2) fun y hy => ?_⟩
  by_contra hyT
  exact hWmem y hyT (mem_iInter.mp hy ⟨y, hyT⟩)

/-- **Stacks 04PL**.
If `X` is quasi-compact, has a basis of quasi-compact opens, and the intersection of two
quasi-compact opens is quasi-compact, then a subset `T ⊆ X` is an intersection of clopen
subsets if and only if `T` is closed and is a union of connected components of `X`. -/
@[stacks 04PL]
theorem main_theorem04PL
    [CompactSpace X]
    (hbasis : PrespectralSpace X)
    (hinter : QuasiSeparatedSpace X)
    (T : Set X) :
    IsIntersectionOfClopens T ↔ (IsClosed T ∧ IsUnionOfConnectedComponents T) :=
  have : PrespectralSpace X := hbasis
  have : QuasiSeparatedSpace X := hinter
  ⟨fun hT => ⟨hT.isClosed, hT.isUnionOfConnectedComponents⟩,
    fun ⟨hTcl, hTunion⟩ =>
      isIntersectionOfClopens_of_isClosed_of_isUnionOfConnectedComponents hTcl hTunion⟩

end
