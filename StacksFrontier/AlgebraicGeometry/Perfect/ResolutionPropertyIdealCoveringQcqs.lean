module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.RetrocompactOpen

/-!
# A scheme with an ideal-cut-out affine covering is quasi-compact and quasi-separated

The hypotheses of [Stacks, Tag 0F89], packaged as
`AlgebraicGeometry.IsIdealAffineCovering`, force the scheme to be quasi-compact and
quasi-separated.  That is the first sentence of the proof of the substantial direction of that
tag, and it is what lets the reduction to the Noetherian case invoke absolute Noetherian
approximation ([Stacks, Tag 01ZA]), which asks for exactly those two properties.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_isFiniteType_idealPow`: the finite
  type condition that `AlgebraicGeometry.IsIdealAffineCovering` records for the sheaf of ideals
  as a *module* gives back finite generation of every `I.ideal V`.
* `AlgebraicGeometry.IsIdealAffineCovering.compactSpace`: the scheme is quasi-compact.
* `AlgebraicGeometry.IsIdealAffineCovering.quasiSeparatedSpace`: the scheme is quasi-separated.

## Implementation notes

**Why the finite type bridge is needed in this direction.**
`AlgebraicGeometry.IsIdealAffineCovering` records finite type for the module
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow (I j) 1`, because that is the form the
conclusion of [Stacks, Tag 0F89] uses.  Every statement about the vanishing locus, on the other
hand, is phrased for `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, finite generation
of every `I.ideal V`.  `Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow` goes
from the ideal side to the module side; the converse is recorded here.

**Quasi-separatedness without passing to the open subscheme.** The intersection `U k ⊓ U l` is
the part of the affine open `U k` where the ideal `I l` does not vanish.  Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_inter` computes that vanishing locus inside
`U k` as the zero locus of the single ideal `(I l).ideal ⟨U k, _⟩` of `Γ(X, U k)`, and that ideal
is finitely generated, so the intersection is the union of the finitely many basic opens of a
generating set.  Each such basic open is affine, hence quasi-compact, and a finite union of
quasi-compact sets is quasi-compact.  No sheaf of ideals on the open subscheme `U k` is formed,
and `AlgebraicGeometry.isCompact_of_isFiniteType_idealSheafData` — [Stacks, Tag 01PH] in the
direction (4) ⟹ (2), which would need such an ideal — is not used.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Finite generation of every `I.ideal V` from finite type of the sheaf of ideals read as a
module.  This is the converse of
`Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow` at `n = 1`. -/
theorem Scheme.IdealSheafData.isFiniteType_of_isFiniteType_idealPow (I : X.IdealSheafData)
    (h : (idealPow I 1).IsFiniteType) : I.IsFiniteType := by
  intro V
  have hsub : ((idealPowerMultiple I 1 (structureModule X)).toSubmodule.obj (op V.1) :
      Submodule Γ(X, V.1) Γ(X, V.1)).FG :=
    Module.Finite.iff_fg.mp (moduleFinite_sections_on_affine (idealPow I 1) V.1 V.2)
  rwa [obj_idealPow_affineOpen I 1 V, pow_one] at hsub

namespace IsIdealAffineCovering

variable {m : ℕ} {U : Fin m → X.Opens} {I : Fin m → X.IdealSheafData}

/-- The sheaves of ideals of an ideal-cut-out affine covering are of finite type in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`. -/
theorem idealSheafData_isFiniteType (h : IsIdealAffineCovering X U I) (j : Fin m) :
    (I j).IsFiniteType :=
  Scheme.IdealSheafData.isFiniteType_of_isFiniteType_idealPow (I j) (h.isFiniteType j)

/-- The members of an ideal-cut-out affine covering form an open cover. -/
theorem isOpenCover (h : IsIdealAffineCovering X U I) : IsOpenCover U := h.iSup_eq_top

/-- **A scheme with an ideal-cut-out affine covering is quasi-compact**: it is covered by
finitely many affine, hence quasi-compact, opens. -/
theorem compactSpace (h : IsIdealAffineCovering X U I) : CompactSpace X := by
  refine ⟨?_⟩
  have hcov : (Set.univ : Set X) = ⋃ j, ((U j : Set X)) := by
    refine (Set.eq_univ_of_forall fun x => ?_).symm
    have hx : x ∈ (⨆ j, U j) := by
      rw [h.iSup_eq_top]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  rw [hcov]
  exact isCompact_iUnion fun j => (h.isAffineOpen j).isCompact

/-- The intersection of two members of an ideal-cut-out affine covering is quasi-compact: inside
the affine open `U k` it is the complement of the zero locus of the finitely generated ideal
`(I l).ideal ⟨U k, _⟩`, hence the union of the finitely many basic opens of a generating set. -/
theorem isCompact_inter (h : IsIdealAffineCovering X U I) (k l : Fin m) :
    IsCompact (X := X) ((U k : Set X) ∩ (U l : Set X)) := by
  classical
  obtain ⟨s, hs⟩ := h.idealSheafData_isFiniteType l ⟨U k, h.isAffineOpen k⟩
  have hzl : X.zeroLocus (U := U k) ((I l).ideal ⟨U k, h.isAffineOpen k⟩)
      = X.zeroLocus (U := U k) (s : Set Γ(X, U k)) := by
    rw [← hs]
    exact X.zeroLocus_span _
  have hsupp : ((I l).support : Set X) ∩ (U k : Set X)
      = X.zeroLocus (U := U k) (s : Set Γ(X, U k)) ∩ (U k : Set X) :=
    hzl ▸ Scheme.IdealSheafData.coe_support_inter (I l) ⟨U k, h.isAffineOpen k⟩
  have key : ∀ x ∈ (U k : Set X), x ∈ (U l : Set X) ↔
      x ∉ X.zeroLocus (U := U k) (s : Set Γ(X, U k)) := fun x hxk => by
    have := Set.ext_iff.mp hsupp x
    simp only [h.support_eq l, Set.mem_inter_iff, Set.mem_compl_iff, hxk, and_true] at this
    rw [← this, not_not]
  have hzero : (U k : Set X) ∩ (U l : Set X)
      = ⋃ f ∈ (s : Set Γ(X, U k)), (X.basicOpen f : Set X) := by
    ext x
    constructor
    · rintro ⟨hxk, hxl⟩
      have hx := (key x hxk).mp hxl
      rw [Scheme.mem_zeroLocus_iff] at hx
      push Not at hx
      obtain ⟨f, hf, hxf⟩ := hx
      exact Set.mem_biUnion hf hxf
    · intro hx
      obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.mp hx
      have hxk : x ∈ (U k : Set X) := X.basicOpen_le f hxf
      exact ⟨hxk, (key x hxk).mpr fun hz => (Scheme.mem_zeroLocus_iff _ _ _).mp hz f hf hxf⟩
  rw [hzero]
  exact s.isCompact_biUnion fun f _ => ((h.isAffineOpen k).basicOpen f).isCompact

/-- **A scheme with an ideal-cut-out affine covering is quasi-separated.**  This is
[Stacks, Tag 01KO] in the form of Mathlib's
`AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`, fed with
`AlgebraicGeometry.IsIdealAffineCovering.isCompact_inter`. -/
theorem quasiSeparatedSpace (h : IsIdealAffineCovering X U I) : QuasiSeparatedSpace X :=
  Scheme.quasiSeparatedSpace_of_isOpenCover U h.isOpenCover h.isAffineOpen h.isCompact_inter

end IsIdealAffineCovering

end AlgebraicGeometry

end
