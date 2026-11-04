module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus

/-!
# The Fitting stratification of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
an `𝒪_F`-module.  The Fitting ideal sheaves `AlgebraicGeometry.Space.fittingIdeal` of `G` form an
increasing chain

`Fit₀(G) ⊆ Fit₁(G) ⊆ Fit₂(G) ⊆ … ⊆ 𝒪_F`,

so the closed sets they cut out decrease.  This file proves that monotonicity, computes the
sections of the Fitting ideal sheaf over an affine étale chart on which the sections of `G` are
spanned by `r` elements — there they are the whole structure sheaf — and deduces that the
intersection of the Fitting zero loci is empty as soon as every point of `F` lies on such a
chart.

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_mono` and
  `AlgebraicGeometry.Space.monotone_fittingIdeal`: the Fitting ideal sheaves increase with the
  index.
* `AlgebraicGeometry.Space.fittingIdeal_obj_eq_top_of_fittingIdealOnChart_eq_top` and
  `AlgebraicGeometry.Space.fittingIdeal_obj_eq_top_of_span_eq_top`: over an affine étale chart
  whose sections of `G` are spanned by `r` elements, the `r`-th Fitting ideal sheaf has all of
  `𝒪_F` as its sections.
* `AlgebraicGeometry.Space.idealUnitLocus_fittingIdeal_mono` and
  `AlgebraicGeometry.Space.idealZeroLocus_fittingIdeal_antitone`: the Fitting unit loci increase
  and the Fitting zero loci decrease.
* `AlgebraicGeometry.Space.mem_idealUnitLocus_fittingIdeal_of_span_eq_top`: a point on such a
  chart lies in the `r`-th Fitting unit locus.
* `AlgebraicGeometry.Space.iInter_idealZeroLocus_fittingIdeal_eq_empty`: the intersection of the
  Fitting zero loci is empty when every point lies on an affine étale chart over which the
  sections of `G` are spanned by finitely many elements.

## Implementation notes

`AlgebraicGeometry.Space.fittingIdeal` is the *smallest* sheaf submodule of `𝒪_F` whose sections
over every affine étale chart contain the chartwise Fitting ideal of Stacks 07ZA, so in general
only the inclusion `AlgebraicGeometry.Space.mem_fittingIdeal_of_mem_fittingIdealOnChart` of the
chartwise ideal into the sections is available, and not the reverse.  That inclusion is enough
for everything below: each statement here concludes that some section *is* in the Fitting ideal
sheaf, or that its sections are all of `𝒪_F`, and never that a section is not.  Monotonicity goes
the same way, through `sInf_le_sInf`: a sheaf submodule containing the chartwise `Fit_s` contains
the chartwise `Fit_r` for `r ≤ s`, so the defining family for `s` is contained in the one for
`r`.

The zero locus used here is `AlgebraicGeometry.Space.idealZeroLocus`, the *point set* of the
closed subspace cut out by a sheaf of ideals, so that the statements below need nothing about the
closed subspaces themselves.  The Fitting closed subspaces are
`AlgebraicGeometry.Space.exists_fittingClosedSubspaces`, and clause (1) of Stacks 0CZ9 is stated
about them as `AlgebraicGeometry.Space.iInf_fittingClosedSubspace_eq_sheafify_bot`.

## References

* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The chain of Fitting ideal sheaves -/

/-- The chartwise Fitting ideals of Stacks 07ZA increase with the index. -/
theorem fittingIdealOnChart_mono (G : Modules.{u, m} B S hS F hF) {r s : ℕ} (hrs : r ≤ s)
    (U : SmallEtale B S hS F)
    [Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))] :
    fittingIdealOnChart B S hS F hF G r U ≤ fittingIdealOnChart B S hS F hF G s U :=
  Stacks.Fitting.fittingIdeal_monotone (R := chartRing B S hS F hF U)
    (M := G.val.obj (op U)) (Int.ofNat_le.2 hrs)

/-- **The Fitting ideal sheaves of an `𝒪_F`-module increase with the index**, so the closed sets
they cut out decrease.

A sheaf submodule of `𝒪_F` whose sections over every affine étale chart contain the chartwise
`Fit_s` contains the chartwise `Fit_r` there too, for `r ≤ s`; so the family whose infimum is the
`s`-th Fitting ideal sheaf is contained in the family for `r`, and the infimum grows. -/
theorem fittingIdeal_mono (G : Modules.{u, m} B S hS F hF) {r s : ℕ} (hrs : r ≤ s) :
    fittingIdeal B S hS F hF G r ≤ fittingIdeal B S hS F hF G s := by
  classical
  refine sInf_le_sInf fun I hI V hV a ha ↦ hI V hV a ?_
  split at ha
  next finiteSections =>
    rw [dite_eq_left finiteSections]
    exact fittingIdealOnChart_mono G hrs V ha
  next notFiniteSections => exact ha.elim

/-- The Fitting ideal sheaves of an `𝒪_F`-module, as a monotone family. -/
theorem monotone_fittingIdeal (G : Modules.{u, m} B S hS F hF) :
    Monotone fun r : ℕ ↦ fittingIdeal B S hS F hF G r :=
  fun _ _ hrs ↦ fittingIdeal_mono G hrs

/-! ### Charts on which a Fitting ideal sheaf is the whole structure sheaf -/

/-- Over an affine étale chart on which the chartwise Fitting ideal is the unit ideal, the
sections of the Fitting ideal sheaf are all of `𝒪_F`. -/
theorem fittingIdeal_obj_eq_top_of_fittingIdealOnChart_eq_top
    (G : Modules.{u, m} B S hS F hF) (r : ℕ) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    [Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U))]
    (h : fittingIdealOnChart B S hS F hF G r U = ⊤) :
    (fittingIdeal B S hS F hF G r).obj (op U) = ⊤ :=
  eq_top_iff.2 fun a _ ↦
    mem_fittingIdeal_of_mem_fittingIdealOnChart G r U hU a (h ▸ Submodule.mem_top)

/-- **Over an affine étale chart on which the sections of `G` are spanned by `r` elements, the
`r`-th Fitting ideal sheaf is the whole structure sheaf.**

This is the chartwise computation `fittingIdeal_basic_properties` of Stacks 07ZA, transported
to the Fitting ideal sheaf. -/
theorem fittingIdeal_obj_eq_top_of_span_eq_top
    (G : Modules.{u, m} B S hS F hF) {r : ℕ} (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (s : Fin r → G.val.obj (op U))
    (hs : Submodule.span (chartRing B S hS F hF U) (Set.range s) = ⊤) :
    (fittingIdeal B S hS F hF G r).obj (op U) = ⊤ := by
  classical
  have hfin : Module.Finite (chartRing B S hS F hF U) (G.val.obj (op U)) :=
    ⟨⟨Finset.univ.image s, by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact hs⟩⟩
  refine fittingIdeal_obj_eq_top_of_fittingIdealOnChart_eq_top G r U hU ?_
  exact (fittingIdeal_basic_properties.{u, m, m, u}
    (R := chartRing B S hS F hF U) (M := G.val.obj (op U))).1 r ⟨s, hs⟩

/-! ### The Fitting unit and zero loci -/

variable (B S hS) in
/-- The unit loci of the Fitting ideal sheaves increase with the index. -/
theorem idealUnitLocus_fittingIdeal_mono (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, m} B S hS X.1 X.2) {r s : ℕ} (hrs : r ≤ s) :
    idealUnitLocus B S hS X (fittingIdeal B S hS X.1 X.2 G r) ⊆
      idealUnitLocus B S hS X (fittingIdeal B S hS X.1 X.2 G s) :=
  idealUnitLocus_mono B S hS X (fittingIdeal_mono G hrs)

variable (B S hS) in
/-- **The Fitting zero loci decrease with the index**: the point sets of the closed subspaces
`Z_r` of Stacks 0CZ9 form a decreasing chain. -/
theorem idealZeroLocus_fittingIdeal_antitone (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, m} B S hS X.1 X.2) {r s : ℕ} (hrs : r ≤ s) :
    idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 G s) ⊆
      idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 G r) :=
  idealZeroLocus_antitone B S hS X (fittingIdeal_mono G hrs)

variable (B S hS) in
/-- A point lying on an affine étale chart over which the sections of `G` are spanned by `r`
elements lies in the `r`-th Fitting unit locus, hence outside the `r`-th Fitting zero locus. -/
theorem mem_idealUnitLocus_fittingIdeal_of_span_eq_top (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, m} B S hS X.1 X.2) {r : ℕ} (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (s : Fin r → G.val.obj (op U))
    (hs : Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) = ⊤)
    {x : points B S hS X.1}
    (hx : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom)) :
    x ∈ idealUnitLocus B S hS X (fittingIdeal B S hS X.1 X.2 G r) :=
  ⟨U, fittingIdeal_obj_eq_top_of_span_eq_top G U hU s hs, hx⟩

variable (B S hS) in
/-- **The intersection of the Fitting zero loci is empty**, as soon as every point of the
algebraic space lies on an affine étale chart over which the sections of `G` are spanned by
finitely many elements.

This is the point-set form of clause (1) of Stacks 0CZ9: near any point the sections of `G` are
spanned by finitely many elements, and from that index on the Fitting ideal sheaf is the whole
structure sheaf there.  The hypothesis is the local generation of `G`, carried explicitly; for
a quasi-coherent module of finite type it is supplied by
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite` and
`AlgebraicGeometry.Space.exists_affine_chart_span_eq_top_of_module_finite`. -/
theorem iInter_idealZeroLocus_fittingIdeal_eq_empty (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, m} B S hS X.1 X.2)
    (hgen : ∀ x : points B S hS X.1, ∃ (r : ℕ) (U : SmallEtale B S hS X.1)
      (s : Fin r → G.val.obj (op U)),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) ∧
        Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) = ⊤ ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom)) :
    (⋂ r : ℕ, idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 G r)) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  obtain ⟨r, U, s, hU, hs, hxU⟩ := hgen x
  exact (Set.mem_iInter.1 hx r)
    (mem_idealUnitLocus_fittingIdeal_of_span_eq_top B S hS X G U hU s hs hxU)

end AlgebraicGeometry.Space

end
