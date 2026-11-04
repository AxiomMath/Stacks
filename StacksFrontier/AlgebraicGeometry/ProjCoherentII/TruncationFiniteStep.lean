module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TruncationFinite

/-!
# Finiteness of the truncated twisted global sections when the degrees step down by `δ`

`StacksFrontier/AlgebraicGeometry/ProjCoherentII/TruncationFinite.lean` proves that the truncation
`⨁_{n ≥ k} Γ(X, ℱ(n))` of the twisted global sections on `X = Proj 𝒮` is a finite `S`-module once

* each homogeneous piece spans a finitely generated `S`-submodule, and
* above some degree every homogeneous piece lies in the `S`-span of the piece **one** degree
  below.

The second hypothesis is degree-one generation, and it is **false** for a graded ring that is not
generated in degree one: if `S = k[f]` with `f` homogeneous of degree `2`, then every homogeneous
piece in an odd degree is zero while its neighbours need not be, so no piece is contained in the
span of the piece one degree below. This file replaces the step `1` by an arbitrary positive step
`δ`, which is what the Veronese reduction of [Stacks, Tag 0B5R] produces: there the degrees of the
homogeneous generators of `S` over `S₀` have a least common multiple `d`, and the generation
statement that is available relates `Γ(X, ℱ(n))` to `Γ(X, ℱ(n - d))`.

Nothing changes in the argument except the size of the finite window that the high degrees walk
down into: with a step of `δ` a degree above `max k B + δ` walks down to a degree in
`(max k B, max k B + δ]`, so the window has to reach `δ` further than before. It is therefore the
*same* `Stacks.AlgebraicGeometry.ProjTwistedSections.truncationWindow`, taken at `max k B + δ`
rather than at `B`; no second window object is introduced.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections`
  `.coe_twistedGlobalSectionsGrading_subset_truncationWindow_step`: with a step of `δ` the
  homogeneous pieces of degree `≥ k` all lie in the window reaching `max k B + δ`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsTruncation_eq_iSup_step`: the
  truncation *is* that window.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.fg_twistedGlobalSectionsTruncation_step` and
  `Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation_step`:
  the truncation is a finitely generated, respectively finite, `S`-module.

## Implementation notes

The walk down is a strong induction on `(d - k).toNat` rather than the `Int.le_induction` of the
one-step file: a step of `δ` does not reach the immediate predecessor, so there is no successor
case to appeal to, and the decreasing quantity has to be exhibited.

The hypothesis `hstep` is applied only in degrees above `max k B + δ`, never merely above `B`.
That is what keeps the landing degree inside the window: from `d > max k B + δ` one step reaches
`d - δ > max k B ≥ k`, so the piece walked into is still a piece of the truncation. Applying
`hstep` as soon as `d > B` would allow a landing degree below `k`, where the grading is not part
of the truncation at all.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistSheafOfModules twistedGlobalSections)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

variable [Module S (twistedGlobalSections 𝒮 F)]
  (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : twistedSectionsComponent 𝒮 F n),
    (a : S) • (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s :
        twistedGlobalSections 𝒮 F) =
      DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮 F i n a s))

/-- **The high degrees walk down into the window, in steps of `δ`.** If every homogeneous piece of
degree `> B` lies in the `S`-span of the piece `δ` degrees below, then every homogeneous piece of
degree `≥ k` lies in the `S`-span of the pieces of degrees `k, …, max k B + δ`. -/
theorem coe_twistedGlobalSectionsGrading_subset_truncationWindow_step (k B : ℤ) {δ : ℤ}
    (hδ : 0 < δ)
    (hstep : ∀ d : ℤ, B < d →
      (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
        Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (d - δ) :
          Set (twistedGlobalSections 𝒮 F)))
    (d : ℤ) (hd : k ≤ d) :
    (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
      truncationWindow 𝒮 F k (max k B + δ) := by
  have hwin : ∀ m : ℤ, k ≤ m → m ≤ max k B + δ →
      Submodule.span S (twistedGlobalSectionsGrading 𝒮 F m :
          Set (twistedGlobalSections 𝒮 F)) ≤ truncationWindow 𝒮 F k (max k B + δ) :=
    fun m hm hmB => le_iSup (fun j : Finset.Icc k (max k (max k B + δ)) =>
      Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (j : ℤ) :
        Set (twistedGlobalSections 𝒮 F)))
      ⟨m, Finset.mem_Icc.mpr ⟨hm, le_max_of_le_right hmB⟩⟩
  -- strong induction on the number of steps still to be taken
  induction hn : (d - k).toNat using Nat.strong_induction_on generalizing d with
  | _ N IH =>
    rcases le_or_gt d (max k B + δ) with hle | hgt
    · exact Set.Subset.trans Submodule.subset_span (hwin d hd hle)
    · refine Set.Subset.trans (hstep d (by omega)) (Submodule.span_le.mpr ?_)
      exact IH ((d - δ - k).toNat) (by omega) (d - δ) (by omega) rfl

include hsmul in
/-- **The truncation is the span of the window, with a step of `δ`.** Under the `δ`-step
hypothesis the degree-`≥ k` truncation of the twisted global sections is generated by the
homogeneous pieces of degrees `k, …, max k B + δ`. -/
theorem twistedGlobalSectionsTruncation_eq_iSup_step (k B : ℤ) {δ : ℤ} (hδ : 0 < δ)
    (hstep : ∀ d : ℤ, B < d →
      (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
        Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (d - δ) :
          Set (twistedGlobalSections 𝒮 F))) :
    twistedGlobalSectionsTruncation 𝒮 F hsmul k = truncationWindow 𝒮 F k (max k B + δ) := by
  refine le_antisymm ?_ ?_
  · rw [twistedGlobalSectionsTruncation_eq_span 𝒮 F hsmul k]
    refine Submodule.span_le.mpr (Set.iUnion₂_subset fun m hm => ?_)
    exact coe_twistedGlobalSectionsGrading_subset_truncationWindow_step 𝒮 F k B hδ hstep m
      (Set.mem_Ici.mp hm)
  · refine iSup_le fun m => Submodule.span_le.mpr ?_
    exact coe_twistedGlobalSectionsGrading_subset_truncation 𝒮 F hsmul k (m : ℤ)
      (Finset.mem_Icc.mp m.2).1

include hsmul in
/-- **The degree-`≥ k` truncation of the twisted global sections is a finitely generated
`S`-module**, provided each homogeneous piece spans a finitely generated submodule and the pieces
above degree `B` are spanned by the pieces `δ` degrees below them. -/
theorem fg_twistedGlobalSectionsTruncation_step (k B : ℤ) {δ : ℤ} (hδ : 0 < δ)
    (hfg : ∀ d : ℤ, (Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
      Set (twistedGlobalSections 𝒮 F))).FG)
    (hstep : ∀ d : ℤ, B < d →
      (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
        Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (d - δ) :
          Set (twistedGlobalSections 𝒮 F))) :
    (twistedGlobalSectionsTruncation 𝒮 F hsmul k).FG := by
  rw [twistedGlobalSectionsTruncation_eq_iSup_step 𝒮 F hsmul k B hδ hstep]
  exact Submodule.fg_iSup _ fun m => hfg (m : ℤ)

include hsmul in
/-- **The degree-`≥ k` truncation of the twisted global sections is a finite `S`-module** under
the `δ`-step hypothesis, in the `Module.Finite` spelling. -/
theorem moduleFinite_twistedGlobalSectionsTruncation_step (k B : ℤ) {δ : ℤ} (hδ : 0 < δ)
    (hfg : ∀ d : ℤ, (Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
      Set (twistedGlobalSections 𝒮 F))).FG)
    (hstep : ∀ d : ℤ, B < d →
      (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
        Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (d - δ) :
          Set (twistedGlobalSections 𝒮 F))) :
    Module.Finite S (twistedGlobalSectionsTruncation 𝒮 F hsmul k) :=
  Module.Finite.iff_fg.mpr (fg_twistedGlobalSectionsTruncation_step 𝒮 F hsmul k B hδ hfg hstep)

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
