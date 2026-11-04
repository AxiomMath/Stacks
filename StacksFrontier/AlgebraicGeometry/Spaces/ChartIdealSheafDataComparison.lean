module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The chart sheaf of ideals, read at the comparison chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `ℐ ⊆ 𝒪_X`
be a sheaf of ideals and let `A` be an étale scheme chart of `X`.  Two different étale charts of
`X` are attached to a Zariski open `W` of the chart's scheme:

* `AlgebraicGeometry.Space.openChart … A W`, which is `W` with the open immersion taken by
  `CategoryTheory.Functor.preimage`, and over which
  `AlgebraicGeometry.Space.idealSheafDataOfChart` reads the ideal of sections of `ℐ`;
* `AlgebraicGeometry.Space.openChartOfComparison … A W`, which is `W` carried through the two
  comparison equivalences, and over which
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleSemilinear.lean` computes the sections
  of the chart restriction of an `𝒪_X`-module.

The two charts are equal — `AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj` —
but not definitionally, so a statement about one is not a statement about the other.  This file
relabels the *ideal* side: the ideal which `AlgebraicGeometry.Space.idealSheafDataOfChart`
attaches to `W` is the ideal of sections of `ℐ` over the *comparison* chart, transported along
the composite scalar map `AlgebraicGeometry.Space.chartSectionsRingHom` of the chart sections
identification.  That is what makes the two computations of the sections of `ℐⁿ𝒢` over an affine
open — the space-side
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite` and the
scheme-side `Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul` — statements about one and
the same ideal.

## Main results

* `AlgebraicGeometry.Space.openChartTopRingHom_chartSectionsRingHom` and
  `AlgebraicGeometry.Space.chartSectionsRingHom_openChartTopRingHom`: **the composite scalar map
  of the chart sections identification and the comparison `Γ(W, ⊤) ≅ Γ(A, W)` along which
  `AlgebraicGeometry.Space.openChartIdeal` transports the ideal of sections are mutually
  inverse.**  Both are the comparison `AlgebraicGeometry.Scheme.Opens.topIso`, read in the two
  directions.
* `AlgebraicGeometry.Space.mem_chartSectionIdeal_congr` and
  `AlgebraicGeometry.Space.chartSectionIdeal_openChartOfComparison`: the ideal of sections of `ℐ`
  over equal charts is the same ideal; in particular the two charts attached to `W` carry the
  same one.
* `AlgebraicGeometry.Space.openChartIdeal_eq_map_chartSectionIdeal` and
  `AlgebraicGeometry.Space.map_chartSectionsRingHom_openChartIdeal`: **the ideal of
  `AlgebraicGeometry.Space.idealSheafDataOfChart` at `W` is the ideal of sections of `ℐ` over the
  comparison chart**, in the two directions of the composite scalar map.
* `AlgebraicGeometry.Space.isAffine_chartScheme_openChartOfComparison`: the comparison chart of an
  affine open is affine, which is the hypothesis under which the space-side computation applies.

## Implementation notes

**The relabelling is done on ideals of one fixed ring, never on charts.**  Transporting the ideal
of sections along the equality of charts directly is not possible: `ℐ.obj (op P)` is an ideal of
`AlgebraicGeometry.Space.chartRing … P`, so its type moves with `P` and
`congrArg` does not apply.  What is true, and is what
`AlgebraicGeometry.Space.mem_chartSectionIdeal_congr` records, is that *membership* transports:
the statement is heterogeneous in the element, so the chart can be generalized and the equality
substituted.  Both of the ideals produced by `AlgebraicGeometry.Space.openChartIdeal` and by the
comparison chart are then ideals of `Γ(A, W)`, where there is nothing left to transport.

**The two chart rings are definitionally equal even though the two charts are not.**  The
discrepancy between the charts is in the open immersion only — `CategoryTheory.Functor.preimage`
against `CategoryTheory.ObjectProperty.homMk` — and the scheme underlying both is the same term,
so the sections of `𝒪_X` over them are the same term.  This is why
`AlgebraicGeometry.Space.openChartTopRingHom`, whose source is spelled at
`AlgebraicGeometry.Space.openChart`, can be composed with
`AlgebraicGeometry.Space.chartSectionsRingHom`, whose target is spelled at
`AlgebraicGeometry.Space.openChartOfComparison`.

**Only the ideal side is relabelled here.**  The module side — that the sections over `W` of the
chart restriction of a submodule `𝒩 ⊆ 𝒢` sit inside the sections of the chart restriction of `𝒢`
as `𝒩(openChartOfComparison … W)` sits inside `𝒢(openChartOfComparison … W)` — is the naturality
in the module of
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat`, and is not stated
anywhere; `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` is naturality
of the isomorphism of sheaves, which is a different statement and does not evaluate it on
sections.

No hypothesis beyond the data is carried: no quasi-coherence, no coherence, no affineness except
in the one statement about affineness, and no declaration here carries a `stacks` tag — this is
one input to the chart description of Stacks 07UM, not a clause of it.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Ideal

/-- **An ideal is recovered from its image along a ring map with a left inverse.**  If
`g : S →+* R` undoes `f : R →+* S`, then `g` carries the image of `I` along `f` back onto `I`. -/
theorem map_map_of_leftInverse {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (I : _root_.Ideal R) :
    _root_.Ideal.map g (_root_.Ideal.map f I) = I := by
  refine le_antisymm (_root_.Ideal.map_le_iff_le_comap.2
    (_root_.Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) fun x hx => ?_
  · rw [_root_.Ideal.mem_comap, _root_.Ideal.mem_comap, hgf x]
    exact hx
  · have hmem := _root_.Ideal.mem_map_of_mem g (_root_.Ideal.mem_map_of_mem f hx)
    rwa [hgf x] at hmem

end Stacks.Ideal

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The two directions of the comparison of scalars -/

/-- **The transport of `AlgebraicGeometry.Space.openChartIdeal` undoes the composite scalar map
of the chart sections identification.**  Both are `AlgebraicGeometry.Scheme.Opens.topIso`: the
component of `AlgebraicGeometry.SmallEtale.structureMap` at `W` is its inverse, and the two
remaining factors of `AlgebraicGeometry.Space.chartSectionsRingHom` contribute nothing. -/
theorem openChartTopRingHom_chartSectionsRingHom (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) (r : Γ(chartScheme A, W)) :
    openChartTopRingHom B S hS X A W (chartSectionsRingHom B S hS X A W r) = r :=
  W.topIso.inv_hom_id_apply r

/-- **The composite scalar map of the chart sections identification undoes the transport of
`AlgebraicGeometry.Space.openChartIdeal`.** -/
theorem chartSectionsRingHom_openChartTopRingHom (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (y : chartRing B S hS X.1 X.2 (openChart B S hS X.1 A W)) :
    chartSectionsRingHom B S hS X A W (openChartTopRingHom B S hS X A W y) = y :=
  W.topIso.hom_inv_id_apply y

/-! ### The ideal of sections over equal charts -/

/-- **Membership in the ideal of sections of a sheaf of ideals transports along an equality of
charts.**  The statement is heterogeneous in the element, so the chart can be generalized and the
equality substituted; the ideal itself cannot be transported, its type moving with the chart. -/
theorem mem_chartSectionIdeal_congr (ℐ : IdealSheaves B S hS X.1 X.2)
    {P P' : SmallEtale B S hS X.1} (h : P = P')
    (a : chartRing B S hS X.1 X.2 P) (a' : chartRing B S hS X.1 X.2 P') (ha : HEq a a') :
    (a ∈ chartSectionIdeal B S hS X.1 X.2 ℐ P)
      = (a' ∈ chartSectionIdeal B S hS X.1 X.2 ℐ P') := by
  subst h
  rw [eq_of_heq ha]

/-- **The two charts attached to a Zariski open of the chart scheme carry the same ideal of
sections.**  The chart which the comparison equivalences produce and the chart cut out by the
open are equal by `AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`, and the ring
of sections of `𝒪_X` over them is the same term, so the two ideals of sections are ideals of one
ring and are equal. -/
theorem chartSectionIdeal_openChartOfComparison (ℐ : IdealSheaves B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    chartSectionIdeal B S hS X.1 X.2 ℐ (openChartOfComparison B S hS X A W)
      = chartSectionIdeal B S hS X.1 X.2 ℐ (openChart B S hS X.1 A W) :=
  Submodule.ext fun a =>
    (mem_chartSectionIdeal_congr B S hS X ℐ
      (openChart_eq_chartLocalization_opensObj B S hS X A W) a a HEq.rfl).to_iff

/-! ### The chart sheaf of ideals at the comparison chart -/

/-- **The ideal of `AlgebraicGeometry.Space.idealSheafDataOfChart` at a Zariski open `W` of the
chart scheme is the ideal of sections of `ℐ` over the comparison chart of `W`**, transported
along the comparison `Γ(W, ⊤) ≅ Γ(A, W)`. -/
theorem openChartIdeal_eq_map_chartSectionIdeal (ℐ : IdealSheaves B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    openChartIdeal B S hS X ℐ A W
      = Ideal.map (openChartTopRingHom B S hS X A W)
          (chartSectionIdeal B S hS X.1 X.2 ℐ (openChartOfComparison B S hS X A W)) :=
  congrArg (fun I => Ideal.map (openChartTopRingHom B S hS X A W) I)
    (chartSectionIdeal_openChartOfComparison B S hS X ℐ A W).symm

/-- **The composite scalar map of the chart carries the ideal of
`AlgebraicGeometry.Space.idealSheafDataOfChart` at `W` onto the ideal of sections of `ℐ` over the
comparison chart of `W`.**  This is the direction in which the scheme-side computation of the
sections of `ℐⁿ𝒢` is matched with the space-side one. -/
theorem map_chartSectionsRingHom_openChartIdeal (ℐ : IdealSheaves B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    Ideal.map (chartSectionsRingHom B S hS X A W) (openChartIdeal B S hS X ℐ A W)
      = chartSectionIdeal B S hS X.1 X.2 ℐ (openChartOfComparison B S hS X A W) :=
  (congrArg (fun I => Ideal.map (chartSectionsRingHom B S hS X A W) I)
      (openChartIdeal_eq_map_chartSectionIdeal B S hS X ℐ A W)).trans
    (Stacks.Ideal.map_map_of_leftInverse (openChartTopRingHom B S hS X A W)
      (chartSectionsRingHom B S hS X A W)
      (chartSectionsRingHom_openChartTopRingHom B S hS X A W) _)

/-! ### Affineness of the comparison chart -/

/-- **The comparison chart of an affine open of the chart scheme is affine.**  Its scheme is the
open subscheme cut out by the open, which is affine exactly when the open is.  This is the
hypothesis under which
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite` applies at
the comparison chart. -/
theorem isAffine_chartScheme_openChartOfComparison (A : SmallEtale B S hS X.1)
    {W : (chartScheme A).Opens} (hW : IsAffineOpen W) :
    IsAffine (chartScheme (openChartOfComparison B S hS X A W)) := hW

end AlgebraicGeometry.Space

end
