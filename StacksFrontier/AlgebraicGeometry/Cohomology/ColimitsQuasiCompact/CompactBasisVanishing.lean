module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing
public import StacksFrontier.Topology.Bases.QuasiCompactOpens

/-!
# Cohomology over a quasi-compact open, from a basis of quasi-compact opens

Let `X` be a topological space with a basis of quasi-compact opens whose binary intersections
are again quasi-compact — hypotheses (H1) and (H2) of Stacks 0069 — and let `R` be a sheaf of
rings on `X`. Stacks 01EW computes the higher cohomology of a sheaf of `R`-modules from the
Čech cohomology of a cofinal collection of open covers. This file instantiates it at the
collection of *finite covers of a quasi-compact open by quasi-compact opens*, which is the
instance the proof of Stacks 01FF uses: on such a space the cohomology of a quasi-compact open
is computed by finite Čech complexes, and that is what makes it commute with filtered colimits.

## Main definitions

* `Stacks.Cohomology.CompactBasis.compactCovers`: the finite open covers all of whose members
  are quasi-compact. The basis of quasi-compact opens itself is
  `Stacks.Cohomology.Basis.compactOpens`.

## Main results

* `Stacks.Cohomology.CompactBasis.isCompact_coe_iInf`: under (H2) a nonempty finite infimum
  of quasi-compact opens is quasi-compact.
* `Stacks.Cohomology.CompactBasis.isBasis_compactOpens`: under (H1) the quasi-compact opens
  form a basis.
* `Stacks.Cohomology.CompactBasis.exists_compactCover_refines`: under (H1) and (H2) the finite
  covers by quasi-compact opens are cofinal among the open covers of a quasi-compact open.
* `Stacks.Cohomology.CompactBasis.isZero_hgroup_of_cechCohomologyIsZero`: under (H1) and (H2),
  if the positive-degree Čech cohomology of a sheaf of modules vanishes for every finite cover
  by quasi-compact opens, then its higher cohomology vanishes over every quasi-compact open.
* `Stacks.Cohomology.CompactBasis.cechCohomologyIsZero_of_injective`: an injective sheaf of
  modules has vanishing positive-degree Čech cohomology for every open cover.

## Implementation notes

The cofinality input that Stacks 01EW asks for is conclusion (C3) of Stacks 0069,
`hasCofinalCompactRefinements_of_isCompact_isOpen`, transported from set-indexed families to
the `Stacks.Cohomology.Basis.OpenCover` structure. The finite index set produced there lives in
`Type 0`, so it is lifted with `ULift` to the universe of `X`, which `OpenCover.ι` requires.

Stacks 01EW also asks that *all* the multiple intersections occurring in the Čech complex of a
cover lie in the basis, not only the pairwise ones recorded by (C3). That is supplied by
`isCompact_coe_iInf`: a nonempty finite infimum of quasi-compact opens is quasi-compact under
(H2) alone, by induction on the length of the tuple. Finiteness of the covers is part of
`compactCovers` rather than derived, because it both comes for free from (C3) and is needed by
the consumers of the Čech hypothesis.

`cechCohomologyIsZero_of_injective` is fixed at coefficient universe `u`, the universe of the
space. `Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque` (Stacks 09SZ) is
stated with the index type of the cover in the same universe as the coefficients, whereas
`Stacks.Cohomology.Basis.OpenCover.ι` lies in the universe of `X`. The other results are
universe-polymorphic in the coefficients, exactly as Stacks 01EW is.

## References

* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis

universe w v u

namespace Stacks.Cohomology.CompactBasis

variable {X : Type u} [TopologicalSpace X]

/-- A nonempty finite infimum of quasi-compact opens is quasi-compact, given that the
intersection of two quasi-compact opens is quasi-compact. This is the form the Čech complex
needs: its degree-`p` term involves the intersections selected by the tuples
`Fin (p + 1) → ι`, which are never empty. -/
theorem isCompact_coe_iInf (h2 : QuasiSeparatedSpace X) :
    ∀ (m : ℕ) (V : Fin (m + 1) → Opens X), (∀ k, IsCompact (V k : Set X)) →
      IsCompact ((⨅ k, V k : Opens X) : Set X) := by
  intro m
  induction m with
  | zero =>
    intro V hV
    have h : (⨅ k, V k) = V 0 := by
      refine le_antisymm (iInf_le _ 0) (le_iInf fun k => ?_)
      exact Fin.cases le_rfl (fun k' => k'.elim0) k
    rw [h]
    exact hV 0
  | succ m ih =>
    intro V hV
    have key : (⨅ k, V k) = V 0 ⊓ ⨅ k : Fin (m + 1), V k.succ := by
      refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun k => iInf_le _ k.succ))
        (le_iInf fun k => ?_)
      exact Fin.cases inf_le_left (fun k' => inf_le_right.trans (iInf_le _ k')) k
    rw [key]
    simpa using h2.inter_isCompact _ _ (V 0).isOpen (hV 0)
      (⨅ k : Fin (m + 1), V k.succ).isOpen (ih (fun k => V k.succ) (fun k => hV k.succ))

/-- Under hypothesis (H1) of Stacks 0069 the quasi-compact opens form a basis: they contain a
basis and consist of opens. -/
theorem isBasis_compactOpens (h1 : PrespectralSpace X) :
    Opens.IsBasis (compactOpens X) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨V, -, rfl⟩
    exact V.isOpen
  · intro a s ha hs
    obtain ⟨t, htB, hat, hts⟩ := h1.isTopologicalBasis.exists_subset_of_mem_open ha hs
    exact ⟨t, ⟨⟨t, h1.isTopologicalBasis.isOpen htB⟩, htB.2, rfl⟩, hat, hts⟩

/-- The finite open covers of `X` whose members are all quasi-compact. This is the collection
`Cov` at which Stacks 01EW is instantiated in the proof of Stacks 01FF. -/
def compactCovers (X : Type u) [TopologicalSpace X] : Set (OpenCover X) :=
  {W : OpenCover X | Finite W.ι ∧ ∀ i, IsCompact (W.obj i : Set X)}

/-- The open covered by a finite cover with quasi-compact members is itself quasi-compact. -/
theorem isCompact_carrier_of_mem_compactCovers {W : OpenCover X} (hW : W ∈ compactCovers X) :
    IsCompact (W.carrier : Set X) := by
  obtain ⟨_, hc⟩ := hW
  simpa [← W.iSup_eq] using isCompact_iUnion hc

/-- **Cofinality of the finite quasi-compact covers.** Under hypotheses (H1) and (H2) of Stacks
0069, every open cover of a quasi-compact open `U` is refined by a finite cover of `U` whose
members are quasi-compact. This is conclusion (C3) of Stacks 0069 in the shape Stacks 01EW
consumes it. -/
theorem exists_compactCover_refines (h1 : PrespectralSpace X)
    (h2 : QuasiSeparatedSpace X) (U : Opens X) (hU : U ∈ compactOpens X)
    (V : OpenCover X) (hV : V.carrier = U) :
    ∃ W ∈ compactCovers X, W.carrier = U ∧ W.Refines V := by
  classical
  have hcov : (U : Set X) ⊆ ⋃ i, (V.obj i : Set X) := by
    rw [← Opens.coe_iSup, V.iSup_eq, hV]
  obtain ⟨ι', J, W', hWopen, hWcomp, hWunion, -, hWsub⟩ :=
    hasCofinalCompactRefinements_of_isCompact_isOpen h1 h2 U.isOpen hU
      (K := V.ι) (fun i => (V.obj i : Set X)) (fun i => (V.obj i).isOpen) hcov
  refine ⟨{ ι := ULift.{u} {j // j ∈ J}
            carrier := U
            obj := fun j => ⟨W' j.down.1, hWopen _ j.down.2⟩
            iSup_eq := ?_ }, ⟨inferInstance, fun i => hWcomp _ i.down.2⟩, rfl,
          hV.symm, fun j => ?_⟩
  · apply Opens.ext
    rw [Opens.coe_iSup, hWunion]
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨j, hj⟩ => ⟨j.down.1, j.down.2, hj⟩, fun ⟨j, hj, hx⟩ => ⟨ULift.up ⟨j, hj⟩, hx⟩⟩
  · exact hWsub _ j.down.2

/-- **The Čech cohomology of an injective sheaf of modules vanishes in positive degrees**, for
every open cover. The abelian sheaf underlying an injective sheaf of modules is flasque (Stacks
01EP) and a flasque sheaf has no positive-degree Čech cohomology (Stacks 09SZ). -/
theorem cechCohomologyIsZero_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (I : SheafOfModules.{u} R) [Injective I] (W : OpenCover X) (n : ℕ) (hn : 0 < n) :
    CechCohomologyIsZero R I W n := by
  let _ : TopCat.Sheaf.IsFlasque (X := TopCat.of X)
      (F := (SheafOfModules.toSheaf R).obj I) :=
    Stacks.Cohomology.CechSheaf.underlying_isFlasque I
  exact Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (X := TopCat.of X) ((SheafOfModules.toSheaf R).obj I) W.carrier W.obj W.iSup_eq.symm n hn

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}]
  [EnoughInjectives (SheafOfModules.{max u w} R)]

/-- **Cohomology over a quasi-compact open from finite Čech covers.** Let `X` have a basis of
quasi-compact opens whose binary intersections are quasi-compact, and let `F` be a sheaf of
`R`-modules whose Čech cohomology vanishes in positive degrees for every finite cover by
quasi-compact opens. Then `Hⁿ(U, F) = 0` for every quasi-compact open `U` and every `n > 0`.

This is Stacks 01EW with the basis taken to be all quasi-compact opens and the collection of
covers taken to be the finite covers by quasi-compact opens; the cofinality hypothesis of
Stacks 01EW is then conclusion (C3) of Stacks 0069. It is the step the proof of Stacks 01FF
applies to the colimit of a system of injectives. -/
theorem isZero_hgroup_of_cechCohomologyIsZero
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    (F : SheafOfModules.{max u w} R)
    (hCech : ∀ W : OpenCover X, Finite W.ι → (∀ i, IsCompact (W.obj i : Set X)) →
      ∀ n : ℕ, 0 < n → CechCohomologyIsZero R F W n)
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup R U n F) :=
  Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis
    R F (compactOpens X) (isBasis_compactOpens h1) (compactCovers X)
    (fun W hW => ⟨isCompact_carrier_of_mem_compactCovers hW, hW.2,
      fun p s => isCompact_coe_iInf h2 p (fun k => W.obj (s k)) fun k => hW.2 (s k)⟩)
    (exists_compactCover_refines h1 h2) (fun W hW m hm => hCech W hW.1 hW.2 m hm) U hU n hn

end Stacks.Cohomology.CompactBasis

end
