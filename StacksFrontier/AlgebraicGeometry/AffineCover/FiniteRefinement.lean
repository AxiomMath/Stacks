module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Spaces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a covering family of a quasi-compact scheme to a finite affine one

A covering family of the site of opens of a scheme is an arbitrary family of opens whose
supremum is the whole space. On a quasi-compact scheme such a family is refined by a *finite*
family of *affine* opens: the affine opens form a basis, so every point has an affine
neighbourhood inside some member of the family, and quasi-compactness extracts finitely many of
those. On a quasi-separated scheme the pairwise intersections of the refinement are then
quasi-compact.

This is the shape in which local data attached to a covering family — a trivialisation of a
finite locally free module, say — is turned into finitely many pieces whose overlaps have
quasi-compact sections.

## Main results

* `AlgebraicGeometry.exists_finite_affine_subcover`: **a covering family of the site of opens of
  a quasi-compact scheme is refined by a finite family of affine opens.**
* `AlgebraicGeometry.coversTop_of_iSup_eq_top`: a family of opens with supremum `⊤` covers the
  terminal object of the site of opens.
* `AlgebraicGeometry.isCompact_inf_of_isAffineOpen`: **the intersection of two affine opens of a
  quasi-separated scheme is quasi-compact.**

## Implementation notes

The refinement is indexed by a `Finset` of points of `X`, one affine neighbourhood being chosen
for each point and finitely many of them retained; the index type is therefore in `Type u`, as
`CategoryTheory.GrothendieckTopology.CoversTop` on the site of opens of `X : Scheme.{u}`
requires of the families it is applied to in that universe. The member of the original family
containing each piece is recorded, since the data attached to that member is what the piece
inherits.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A covering family of the site of opens of a quasi-compact scheme is refined by a finite
family of affine opens.** -/
@[sga "3 IV 6.3" "(c)"]
theorem exists_finite_affine_subcover {X : Scheme.{u}} [CompactSpace X] {I : Type*}
    (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology (X : TopCat)).CoversTop U) :
    ∃ (K : Type u) (_ : Fintype K) (V : K → X.Opens) (r : K → I),
      (∀ k, IsAffineOpen (V k)) ∧ (∀ k, V k ≤ U (r k)) ∧ ⨆ k, V k = ⊤ := by
  classical
  rw [Opens.coversTop_iff] at hU
  have hmem : ∀ x : X, ∃ (i : I) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ U i := by
    intro x
    obtain ⟨i, hi⟩ := hU.exists_mem x
    obtain ⟨W, hWaff, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨i, W, hWaff, hxW, hWU⟩
  choose ii WW hWaff hWmem hWU using hmem
  obtain ⟨t, ht⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (WW x : Set X)) (fun x ↦ (WW x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hWmem x⟩)
  refine ⟨(t : Finset X), inferInstance, fun k ↦ WW k.1, fun k ↦ ii k.1,
    fun k ↦ hWaff k.1, fun k ↦ hWU k.1, ?_⟩
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset ?_)
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(⟨i, hi⟩ : (t : Finset X)), hxi⟩

/-- A family of opens whose supremum is the whole space is a covering family of the site of
opens. -/
theorem coversTop_of_iSup_eq_top {X : Scheme.{u}} {K : Type*} (V : K → X.Opens)
    (hV : ⨆ k, V k = ⊤) : (Opens.grothendieckTopology (X : TopCat)).CoversTop V := by
  rw [Opens.coversTop_iff]
  exact hV

/-- **The intersection of two affine opens of a quasi-separated scheme is quasi-compact.** -/
theorem isCompact_inf_of_isAffineOpen {X : Scheme.{u}} [QuasiSeparatedSpace X] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsCompact ((U ⊓ V : X.Opens) : Set X) :=
  QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU.isCompact V.isOpen hV.isCompact


end AlgebraicGeometry

end
