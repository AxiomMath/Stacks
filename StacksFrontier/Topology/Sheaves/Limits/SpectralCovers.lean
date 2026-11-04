module

public import StacksFrontier.Topology.Spectral.InverseLimits
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections

/-!
# Cofinal finite covers with quasi-compact intersections

A quasi-compact open `U` of a prespectral quasi-separated space satisfies
`DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers U`: every open covering of `U` is refined
by a finite covering of `U` all of whose pairwise intersections are quasi-compact. In particular
this holds for the preimage `p_j⁻¹Vⱼ` in the inverse limit of a cofiltered diagram of spectral
spaces of a quasi-compact open `Vⱼ` of a component.

## Main definitions

* `SpectralDiagram.comapProj`: the preimage in the inverse limit of an open of a component.

## Main results

* `hasFiniteCompactCofinalCovers_of_isCompact`: in a prespectral quasi-separated space, every
  quasi-compact open has a cofinal system of finite open coverings with quasi-compact pairwise
  intersections.
* `SpectralDiagram.hasFiniteCompactCofinalCovers_comapProj`: for a diagram of spectral spaces
  with spectral transition maps over a cofiltered index category, the preimage in the inverse
  limit of a quasi-compact open of a component has a cofinal system of finite open coverings
  with quasi-compact pairwise intersections.
-/

@[expose] public section

open CategoryTheory TopologicalSpace DirectedColimitOfSheaves

universe v u
universe v'

/-- In a prespectral quasi-separated space, every quasi-compact open `U` has a cofinal system of
finite open coverings with quasi-compact pairwise intersections. -/
theorem hasFiniteCompactCofinalCovers_of_isCompact {X : TopCat.{u}}
    [PrespectralSpace X] [QuasiSeparatedSpace X] (U : Opens X)
    (hU : IsCompact (U : Set X)) : HasFiniteCompactCofinalCovers U := by
  intro J V hVU hVcov
  have hnbhd : ∀ p : U, ∃ B : Opens X, IsCompact (B : Set X) ∧ (p : X) ∈ B ∧ ∃ j, B ≤ V j := by
    intro p
    obtain ⟨j, hpj⟩ := Opens.mem_iSup.mp (hVcov p.2)
    obtain ⟨B, hBcp, hBo, hpB, hBV⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between (isCompact_singleton (x := (p : X)))
        (V j).isOpen (Set.singleton_subset_iff.mpr hpj)
    exact ⟨⟨B, hBo⟩, hBcp, Set.singleton_subset_iff.mp hpB, j, hBV⟩
  choose B hBcp hBmem ref hBV using hnbhd
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun p : U ↦ (B p : Set X))
    (fun p ↦ (B p).isOpen) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hBmem ⟨x, hx⟩⟩)
  refine ⟨↥s, inferInstance, fun p ↦ B p.1, fun p ↦ (hBV p.1).trans (hVU _), fun x hx ↦ ?_,
    fun p ↦ ⟨ref p.1, hBV p.1⟩,
    fun p q ↦ (hBcp p.1).inter_of_isOpen (hBcp q.1) (B p.1).isOpen (B q.1).isOpen⟩
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxp⟩

namespace SpectralDiagram

variable {J : Type v} [Category.{v'} J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J)

/-- The preimage in the inverse limit of an open of the `j`-th component of the diagram. -/
noncomputable def comapProj (j : J) (V : Opens (D.F.obj j)) : Opens D.invLimit :=
  ⟨D.projFun j ⁻¹' V, V.isOpen.preimage (D.projFun_continuous j)⟩

/-- A point of the limit lies in `comapProj j V` exactly when its `j`-th coordinate lies in `V`. -/
@[simp]
lemma mem_comapProj {j : J} {V : Opens (D.F.obj j)} {x : D.invLimit} :
    x ∈ D.comapProj j V ↔ D.projFun j x ∈ V :=
  Iff.rfl

/-- The preimage `p_j⁻¹V` of a quasi-compact open `V` of the `j`-th component is
quasi-compact. -/
lemma isCompact_comapProj (j : J) (V : Opens (D.F.obj j))
    (hV : IsCompact (V : Set (D.F.obj j))) :
    IsCompact ((D.comapProj j V : Opens D.invLimit) : Set D.invLimit) :=
  (spectralDiagram_proj_isSpectralMap D j).isCompact_preimage_of_isOpen V.isOpen hV

/-- The preimage `p_j⁻¹V` of a quasi-compact open of a component has a cofinal system of finite
open coverings with quasi-compact pairwise intersections. -/
theorem hasFiniteCompactCofinalCovers_comapProj (j : J) (V : Opens (D.F.obj j))
    (hV : IsCompact (V : Set (D.F.obj j))) :
    HasFiniteCompactCofinalCovers (D.comapProj j V) :=
  hasFiniteCompactCofinalCovers_of_isCompact _ (D.isCompact_comapProj j V hV)

end SpectralDiagram
