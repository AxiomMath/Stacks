module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing

/-!
# Finite standard open coverings of an affine open are cofinal

Let `X` be a scheme and let `U` be an affine open of `X`. A *finite standard open covering* of
`U` is the family of ambient basic opens `X.basicOpen (g i)` attached to a finite family
`g : Fin n → Γ(X, U)` of sections whose basic opens cover `Spec Γ(X, U)`, that is, which
satisfies `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`. These coverings are the ones
for which Čech cohomology of a quasi-coherent module vanishes, by
`Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover` (Tag 01X9).

This file proves the two combinatorial facts about that system of coverings which the
Čech-to-derived comparison of [Stacks, Tag 01EW] consumes when it is applied, as in
[Stacks, Tag 01XB], with basis the affine opens of `X` and covering system the finite standard
open coverings of affine opens:

* the opens occurring in the Čech complex of such a covering are again affine opens, so the
  system is closed under the finite intersections appearing in its Čech complexes
  (condition (1) of Tag 01EW), and
* every open covering of an affine open is refined by a finite standard open covering of it, so
  these coverings are cofinal among the open coverings of a basis open (condition (2) of
  Tag 01EW).

The second is the scheme-level form of [Stacks, Tag 01HS] part (2), which
`PrimeSpectrum.exists_finite_basicOpen_refinement` proves for a basic open of an affine
spectrum.

## Main results

* `Stacks.Cohomology.Cech.isAffineOpen_iInf_basicOpen`: a finite intersection of basic opens of
  sections over an affine open is an affine open.
* `Stacks.Cohomology.Cech.isAffineOpen_inter`: the same for the intersections `inter` selected by
  a tuple, which are the opens occurring in the Čech complex.
* `Stacks.Cohomology.Cech.exists_isStandardOpenCoverOfSpectrum_refinement`: every family of opens
  covering an affine open is refined by a finite standard open covering of that affine open.

## Implementation notes

The affine open `U` stays an open of the ambient scheme `X` and the members of a covering are the
ambient basic opens `X.basicOpen (g i)`, exactly as in `StacksDraft.Ch30.Sec2.Tag01X9`, so no
restriction comparison along `U ⟶ X` appears.

The refinement is produced by the source's argument: the affine opens form a basis, so each point
of `U` lies in an affine open contained in a member of the given covering; shrinking that
intersection to a basic open of `U` by `AlgebraicGeometry.exists_basicOpen_le_affine_inter` gives
a covering of `U` by basic opens each contained in a member of the given covering; and `U` is
quasi-compact, so finitely many of them suffice. The index type of the given covering is allowed
to live in its own universe.

The standard-covering condition is recorded in the ring-theoretic form of
[Stacks, Tag 01HT], a statement about `Spec Γ(X, U)`, and is obtained from the geometric covering
condition `⨆ j, X.basicOpen (g j) = U` through `AlgebraicGeometry.IsAffineOpen`'s
`iSup_basicOpen_eq_self_iff`; both forms are returned, since Tag 01X9 consumes the first and the
cofinality condition of Tag 01EW the second.

## References

* [Stacks Project, Tag 01HS](https://stacks.math.columbia.edu/tag/01HS)
* [Stacks Project, Tag 01HT](https://stacks.math.columbia.edu/tag/01HT)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex

universe v u

namespace Stacks.Cohomology.Cech

variable {X : Scheme.{u}}

/-- A finite intersection of basic opens of sections over an affine open `U` is an affine open:
it is the basic open of the product of those sections. -/
theorem isAffineOpen_iInf_basicOpen {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (g : Fin n → Γ(X, U)) {m : ℕ} (x : Fin (m + 1) → Fin n) :
    IsAffineOpen (⨅ k, X.basicOpen (g (x k))) := by
  rw [← basicOpen_tupleProd]
  exact hU.basicOpen _

/-- The opens occurring in the Čech complex of a standard open covering of an affine open `U` are
affine opens. This is condition (1) of [Stacks, Tag 01EW] for the system of finite standard open
coverings of affine opens. -/
theorem isAffineOpen_inter {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))
    {m : ℕ} (x : Fin (m + 1) → Fin n) :
    IsAffineOpen (inter (fun i ↦ X.basicOpen (g i)) x) := by
  rw [inter_eq_basicOpen]
  exact hU.basicOpen _

/-- **Any open covering of an affine open of a scheme is refined by a finite standard open
covering of it.** This is the scheme-level form of [Stacks, Tag 01HS] part (2), and it is
condition (2) of [Stacks, Tag 01EW] for the system of finite standard open coverings of affine
opens: the returned family `g` of sections over `U` satisfies the standard-covering condition of
[Stacks, Tag 01HT], its ambient basic opens cover `U`, and each of them is contained in a member
of the given family. -/
@[stacks 01HS "part (2), for an affine open of a scheme"]
theorem exists_isStandardOpenCoverOfSpectrum_refinement {U : X.Opens} (hU : IsAffineOpen U)
    {ι : Type v} (W : ι → X.Opens) (hW : U ≤ ⨆ i, W i) :
    ∃ (n : ℕ) (g : Fin n → Γ(X, U)) (a : Fin n → ι),
      PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ∧ (⨆ j, X.basicOpen (g j)) = U ∧
        ∀ j, X.basicOpen (g j) ≤ W (a j) := by
  classical
  -- Each point of `U` lies in a basic open of `U` contained in a member of `W`.
  have hlocal : ∀ y : U, ∃ (i : ι) (f : Γ(X, U)),
      X.basicOpen f ≤ W i ∧ (y : X) ∈ X.basicOpen f := by
    intro y
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp (hW y.2)
    obtain ⟨A, hA, hyA, hAW⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := W i) (x := (y : X)) hyi
    obtain ⟨f, s, hfs, hyf⟩ := exists_basicOpen_le_affine_inter hU hA (y : X) ⟨y.2, hyA⟩
    exact ⟨i, f, hfs ▸ (X.basicOpen_le s).trans hAW, hyf⟩
  choose i₀ f₀ hle₀ hmem₀ using hlocal
  -- `U` is quasi-compact, so finitely many of those basic opens already cover it.
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover
    (fun y : U ↦ (X.basicOpen (f₀ y) : Set X)) (fun y ↦ (X.basicOpen (f₀ y)).isOpen)
    (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hmem₀ ⟨y, hy⟩⟩)
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  have hcover : (⨆ j, X.basicOpen (f₀ (e.symm j))) = U := by
    refine le_antisymm (iSup_le fun j ↦ X.basicOpen_le _) fun y hy ↦ ?_
    obtain ⟨_, ⟨z, rfl⟩, hyz⟩ := ht hy
    obtain ⟨hz, hyz⟩ := Set.mem_iUnion.mp hyz
    exact le_iSup (fun j ↦ X.basicOpen (f₀ (e.symm j))) (e ⟨z, hz⟩) (by simpa using hyz)
  refine ⟨Fintype.card t, fun j ↦ f₀ (e.symm j), fun j ↦ i₀ (e.symm j), ?_, hcover,
    fun j ↦ hle₀ (e.symm j)⟩
  -- The ring-theoretic standard-covering condition, from the geometric one.
  change (⨆ j, PrimeSpectrum.basicOpen (f₀ (e.symm j))) = PrimeSpectrum.basicOpen (1 : Γ(X, U))
  rw [PrimeSpectrum.basicOpen_one]
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    (hU.iSup_basicOpen_eq_self_iff.mp (by simpa only [iSup_range'] using hcover))

end Stacks.Cohomology.Cech

end
