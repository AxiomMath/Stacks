module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Operations
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic

/-!
# Capturing sections in a finite type sheaf of ideals

On a quasi-compact and quasi-separated scheme every quasi-coherent sheaf of ideals is the
directed union of the finite type sheaves of ideals below it. This file states that fact in the
vocabulary of `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, in the two shapes its
consumers use: the *capture* form, which produces a finite type sheaf of ideals below `K`
containing a prescribed finite set of sections of `K` over one affine open, and the *union*
form, which is the supremum over the whole family.

The capture form is what an injectivity argument on a colimit needs. Two sections of a
quotient algebra which agree are lifted over an affine open `U` of the base, their difference
lands in the ideal of `K` over `U`, and to see it die at a finite stage one needs a sheaf of
ideals defined on *all* of the ambient scheme — not merely on `U` — which is of finite type and
still contains that difference. That is exactly the statement below.

## Main results

* `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_forall_mem`: **the capture lemma**, for a
  finite set of sections over one affine open.
* `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_mem`: the capture lemma for a single
  section.
* `Stacks.FiniteTypeIdealSheaf.directedOn_isFiniteType_le`: the finite type sheaves of ideals
  below `K` are directed.
* `Stacks.FiniteTypeIdealSheaf.iSup_isFiniteType_eq`: **[Stacks, Tag 01PG] at a sheaf of
  ideals** in the finite type vocabulary — `K` is the supremum of that directed family.

## Implementation notes

Nothing new is proved about schemes here. The work is
`Stacks.IdealSheafFiniteType.exists_le_fg_at_chart` and
`Stacks.IdealSheafFiniteType.exists_le_fg_of_list`, which are [Stacks, Tag 01PF] read at a
sheaf of ideals, together with
`Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover`, which spreads finite generation from a
finite affine cover to every affine open; the capture lemma is the composite of the three, with
the affine open carrying the sections absorbed first and the members of the cover absorbed
afterwards. The union form is then read off from
`AlgebraicGeometry.isSupOfFinitePresentation_of_qcqs` by reindexing along
`AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType`, which identifies the two
descriptions of the index family.

In particular no dictionary between `AlgebraicGeometry.Scheme.IdealSheafData` and the
quasi-coherent submodules of the structure sheaf is needed: Tag 01PG is available natively at a
sheaf of ideals, so its module form is not transported. The dictionary does exist, as
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, and is simply not used.

`@[stacks 01PG]` is **withheld**, and so is `@[stacks 01PF]`: both tags are already registered at
the level of a quasi-coherent module — 01PG in `StacksFrontier.AlgebraicGeometry.ColimitClose.Basic`
and in `StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit`, 01PF in
`StacksFrontier.AlgebraicGeometry.AffineExtend.Induction` — and at the level of a sheaf of ideals
the supremum statement below is a restatement of
`AlgebraicGeometry.isSupOfFinitePresentation_of_qcqs`, which is where the proof lives.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.FiniteTypeIdealSheaf

variable {Y : Scheme.{u}}

/-- **The capture lemma.** On a quasi-compact and quasi-separated scheme, a finite set of
sections of a quasi-coherent sheaf of ideals `K` over an affine open `U` is already carried by
a finite type sheaf of ideals below `K`, defined on the whole scheme.

The affine open `U` is absorbed first, with no opens to preserve; the members of a finite
affine cover are absorbed one at a time afterwards, each step preserving the values already
achieved, and finite generation then spreads from that cover to every affine open. -/
theorem exists_isFiniteType_le_forall_mem [CompactSpace Y] [QuasiSeparatedSpace Y]
    (K : Y.IdealSheafData) (U : Y.affineOpens) (s : Finset Γ(Y, U.1))
    (hs : ∀ x ∈ s, x ∈ K.ideal U) :
    ∃ J : Y.IdealSheafData, J.IsFiniteType ∧ J ≤ K ∧ ∀ x ∈ s, x ∈ J.ideal U := by
  classical
  obtain ⟨σ, hσ⟩ := (IsOpenCover.mk (iSup_affineOpens_eq_top Y)).exists_finite_of_compactSpace
  obtain ⟨J₀, hJ₀K, -, hJ₀fg, hJ₀s⟩ := Stacks.IdealSheafFiniteType.exists_le_fg_at_chart K
    (ι := Empty) (fun e ↦ e.elim) (fun e ↦ e.elim) U s hs
  obtain ⟨J, hJK, hJs, -, hJL⟩ := Stacks.IdealSheafFiniteType.exists_le_fg_of_list K U s
    σ.toList J₀ hJ₀K hJ₀s hJ₀fg
  exact ⟨J, Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover J
    (fun i : σ ↦ (i.1 : Y.affineOpens)) hσ.iSup_eq_top
    (fun i ↦ hJL _ (Finset.mem_toList.2 i.2)), hJK, hJs⟩

/-- **The capture lemma for a single section.** On a quasi-compact and quasi-separated scheme a
section of a quasi-coherent sheaf of ideals `K` over an affine open already lies in a finite
type sheaf of ideals below `K`. -/
theorem exists_isFiniteType_le_mem [CompactSpace Y] [QuasiSeparatedSpace Y]
    (K : Y.IdealSheafData) (U : Y.affineOpens) (x : Γ(Y, U.1)) (hx : x ∈ K.ideal U) :
    ∃ J : Y.IdealSheafData, J.IsFiniteType ∧ J ≤ K ∧ x ∈ J.ideal U := by
  classical
  obtain ⟨J, hJft, hJK, hJs⟩ := exists_isFiniteType_le_forall_mem K U {x}
    fun y hy ↦ Finset.mem_singleton.mp hy ▸ hx
  exact ⟨J, hJft, hJK, hJs x (Finset.mem_singleton_self x)⟩

/-- The finite type sheaves of ideals below a fixed quasi-coherent sheaf of ideals are directed:
their supremum is again of finite type and still below. No hypothesis on the scheme is
needed. -/
theorem directedOn_isFiniteType_le (K : Y.IdealSheafData) :
    DirectedOn (· ≤ ·) {J : Y.IdealSheafData | J.IsFiniteType ∧ J ≤ K} :=
  fun J hJ J' hJ' ↦
    ⟨J ⊔ J', ⟨hJ.1.sup hJ'.1, sup_le hJ.2 hJ'.2⟩, le_sup_left, le_sup_right⟩

/-- **[Stacks, Tag 01PG] at a sheaf of ideals, in the finite type vocabulary.** On a
quasi-compact and quasi-separated scheme a quasi-coherent sheaf of ideals is the supremum of
the finite type sheaves of ideals below it; by `directedOn_isFiniteType_le` that supremum is
directed, so it is a directed union. -/
theorem iSup_isFiniteType_eq [CompactSpace Y] [QuasiSeparatedSpace Y] (K : Y.IdealSheafData) :
    (⨆ J : {J : Y.IdealSheafData // J.IsFiniteType ∧ J ≤ K}, J.1) = K := by
  refine le_antisymm (iSup_le fun J ↦ J.2.2) ?_
  refine (isSupOfFinitePresentation_of_qcqs K).ge.trans (iSup_le fun J ↦ ?_)
  exact le_iSup_of_le
    ⟨J.1, (finitePresentation_subschemeι_iff_isFiniteType J.1).mp J.2.1, J.2.2⟩ le_rfl

end Stacks.FiniteTypeIdealSheaf

end
