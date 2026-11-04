module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Factorization
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical chart of the diagonal is an affine open

`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Basic` computes the conormal class
`Stacks.LeibnizDerivation.cls f U` of [Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
on `Stacks.LeibnizDerivation.chart f U`, the intersection of the two preimages of `U` read on the
coborder neighbourhood of the diagonal. Everything in that construction is valid for an arbitrary
open `U`, and nothing there says the chart is *affine* — which is what the affine computation of
the tag needs, because every description of a section of an ideal sheaf by an element of an ideal
(`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal`) and every
passage to the affine model of [Stacks, Tag 01R3] is stated at an affine open.

This file proves it. For `V` an affine open of `S` and `U` an affine open of `X` with
`U ≤ f ⁻¹ᵁ V`:

* `pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U` is an affine open of `X ×_S X`
  (`isAffineOpen_ambientChart`);
* it lies inside the coborder neighbourhood of the diagonal (`le_coborderRange_ambientChart`);
* so `chart f U`, which is its preimage under the inclusion of that neighbourhood
  (`coborderRange_ι_preimage_ambientChart`, by `rfl`), is an affine open of the coborder
  neighbourhood (`isAffineOpen_chart`).

Together with `Stacks.LeibnizDerivation.chart_preimage`, which says the preimage of `chart f U`
under `Δ.liftCoborder` is `U`, this makes `Δ.liftCoborder ∣_ chart f U` a closed immersion
*between affine schemes* whose ideal sheaf is the one `cls f U` is computed from.

## Main definitions

* `Stacks.LeibnizDerivation.ambientChart`: the open
  `pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U` of `X ×_S X`, of which `chart f U` is the
  restriction to the coborder neighbourhood.
* `Stacks.LeibnizDerivation.diagRes`: the diagonal restricted to `U ⟶ ambientChart f U`.
* `Stacks.LeibnizDerivation.fstRes`: the first projection restricted to
  `ambientChart f U ⟶ U`; it retracts `diagRes`.

## Main results

* `Stacks.LeibnizDerivation.diagonal_preimage_ambientChart`: the preimage of the ambient chart
  under the diagonal is `U`, each projection retracting the diagonal.
* `Stacks.LeibnizDerivation.diagRes_comp_fstRes`: the restricted first projection retracts the
  restricted diagonal.
* `Stacks.LeibnizDerivation.surjective_diagRes_appTop`: hence the restricted diagonal is
  surjective on global sections — a *split* surjection, with no affineness used.
* `Stacks.LeibnizDerivation.isAffineOpen_ambientChart`: the ambient chart is affine.
* `Stacks.LeibnizDerivation.isClosedImmersion_diagRes`: the restricted diagonal is a closed
  immersion.
* `Stacks.LeibnizDerivation.le_coborderRange_ambientChart`: the ambient chart lies inside the
  coborder neighbourhood of the diagonal.
* `Stacks.LeibnizDerivation.isAffineOpen_chart`: **`chart f U` is an affine open of the coborder
  neighbourhood.**

## Route

The ambient chart is affine by `AlgebraicGeometry.isAffineOpen_inf_preimage`, which is exactly the
statement that `U ×_V U` is affine for `U`, `V` affine.

The closed immersion is obtained without any ring theory: `AlgebraicGeometry.pullback.diagonal_fst`
makes `fstRes` a retraction of `diagRes`, so `diagRes` is a *split* epimorphism on global sections,
and `AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine` turns that into a closed
immersion once both ends are affine. In particular the identification of the ambient chart's ring
of sections with `Γ(X, U) ⊗_{Γ(S, V)} Γ(X, U)` — Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` — is *not* needed for this, and
surjectivity of the multiplication map of a tensor product is never used.

The containment in the coborder neighbourhood is then the topological maximality argument of
`Stacks.Conormal.subset_coborder_of_closure_inter_subset`. It cannot be
`Stacks.Conormal.le_coborderRange_of_comp_eq`, which asks for a closed-immersion factorization of
the *whole* diagonal through the ambient chart; the diagonal only meets the chart over `U`. What
replaces it: `ambientChart_ι_image_range_diagRes` identifies the range of `diagRes` with the
preimage of the range of the diagonal, `IsOpen.inter_closure` moves a closure across the open
chart, and `Topology.IsInducing.closure_eq_preimage_closure_image` transports the closure to the
chart, where the range is closed because `diagRes` is a closed immersion.

Finally `AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion` descends affineness along the
inclusion of the coborder neighbourhood, whose range is the neighbourhood itself
(`AlgebraicGeometry.Scheme.Opens.opensRange_ι`), and that containment is the previous paragraph.

## Vocabulary

No clause of any Stacks tag is stated here and **no `stacks` attribute is attached.** Every statement is an input to [Stacks, Tag 08S2] and to the part (2) clauses of
[Stacks, Tag 01R3]; nothing about the conormal sheaf, an ideal sheaf or `Ideal.Cotangent` appears.

Nothing is Noetherian, finite, quasi-compact or separated, and `f` is an arbitrary morphism of
schemes: the diagonal is used only as an immersion with two retractions.

## Universe situation

A single universe `u` (`Scheme.{u}`), forced by `AlgebraicGeometry.isAffineOpen_inf_preimage`.

## Transparency gotchas

`AlgebraicGeometry.Scheme.Hom.resLE` carries a containment proof mentioning the morphism, and the
proof produced by `inf_le_left` at `ambientChart f U` arrives with the `CompleteLattice` path to
`LE` rather than `TopologicalSpace.Opens.instPartialOrder`'s. The two are definitionally equal and
a `rw` with `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` then reports "did not find an occurrence of
the pattern" on a goal that contains it. The containments are therefore given names
(`ambientChart_le_fst_preimage`), whose *declared* types fix the instance, and the two
`resLE`-composition facts are named (`diagRes_comp_ι`, `fstRes_comp_ι`) so that no proof term is
ever exposed by unfolding a definition inside `rw`.

`AlgebraicGeometry.Scheme.Hom.base` is not a constant that `congrArg` can be applied to; the
pointwise consequences of the two composition facts are taken with
`congrArg (fun g => g.base b)` instead.

`Set (Limits.pullback f f)` does not elaborate under `open CategoryTheory.Limits` — `pullback`
resolves in the category of types — so the ambient chart's carrier is written `(… : Set _)`.

## What is not done

* **No clause of [Stacks, Tag 08S2] is discharged.** In particular nothing here says that
  `Stacks.LeibnizDerivation.kaehlerToConormal` is invertible, which is the single statement
  separating `StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine` from the statement of Tag 08S2.
* **No ring of sections is computed.** The identification
  `Γ(X ×_S X, ambientChart f U) ≅ Γ(X, U) ⊗_{Γ(S, V)} Γ(X, U)` is not stated; only surjectivity of
  the restricted diagonal on sections is, and that is proved by exhibiting a retraction, which
  says nothing about the kernel. So the ideal of the restricted diagonal is *not* identified with
  `KaehlerDifferential.ideal`, and `Stacks.DiagonalConormal.ker_lmulHom` is not applied.
* **No presentation of the restricted diagonal as `Spec.map (Ideal.Quotient.mk I)`.** The data
  `(I, e, he)` that `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` consumes is
  not produced here; what is produced is the hypothesis `IsAffineOpen` that any such presentation
  needs, and the closed immersion whose ideal `I` would be.
* **Nothing elementwise.** No section of any sheaf is carried across any comparison; the
  obstruction recorded in the "What is not done" section of
  `StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine` is untouched.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LeibnizDerivation

section DiagChart

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)

/-- **The ambient chart of the diagonal over an open `U` of `X`:** the intersection of the two
preimages of `U` under the two projections of `X ×_S X`, read on `X ×_S X` itself rather than on
the coborder neighbourhood. `Stacks.LeibnizDerivation.chart f U` is its restriction to that
neighbourhood, by `coborderRange_ι_preimage_ambientChart`. -/
noncomputable def ambientChart : (Limits.pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U

/-- **`chart f U` is the restriction of the ambient chart to the coborder neighbourhood.** Both
sides are the intersection of two preimages, and a preimage of a preimage is the preimage of the
composite definitionally, so this is `rfl`. -/
theorem coborderRange_ι_preimage_ambientChart :
    (pullback.diagonal f).coborderRange.ι ⁻¹ᵁ ambientChart f U = chart f U := rfl

/-- **The preimage of the ambient chart under the diagonal is `U`.** Each of the two factors has
preimage `U`, because each projection retracts the diagonal. -/
theorem diagonal_preimage_ambientChart :
    pullback.diagonal f ⁻¹ᵁ ambientChart f U = U := by
  have h₁ : pullback.diagonal f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ U) = U :=
    congrArg (fun m : X ⟶ X => m ⁻¹ᵁ U) (pullback.diagonal_fst f)
  have h₂ : pullback.diagonal f ⁻¹ᵁ (pullback.snd f f ⁻¹ᵁ U) = U :=
    congrArg (fun m : X ⟶ X => m ⁻¹ᵁ U) (pullback.diagonal_snd f)
  rw [ambientChart, Scheme.Hom.preimage_inf, h₁, h₂, inf_idem]

/-- `U` is contained in the preimage of the ambient chart, which is the direction
`AlgebraicGeometry.Scheme.Hom.resLE` consumes. -/
theorem le_diagonal_preimage_ambientChart : U ≤ pullback.diagonal f ⁻¹ᵁ ambientChart f U :=
  (diagonal_preimage_ambientChart f U).ge

/-- The ambient chart is contained in the preimage of `U` under the first projection. Named for
its declared type, which fixes the `LE` instance; see the module docstring. -/
theorem ambientChart_le_fst_preimage : ambientChart f U ≤ pullback.fst f f ⁻¹ᵁ U :=
  inf_le_left

/-- The ambient chart is contained in the preimage of `U` under the second projection. -/
theorem ambientChart_le_snd_preimage : ambientChart f U ≤ pullback.snd f f ⁻¹ᵁ U :=
  inf_le_right

/-- **The diagonal restricted to the ambient chart**, a morphism `U ⟶ ambientChart f U` of open
subschemes. Its preimage bookkeeping is `diagonal_preimage_ambientChart`. -/
noncomputable def diagRes : U.toScheme ⟶ (ambientChart f U).toScheme :=
  (pullback.diagonal f).resLE (ambientChart f U) U (le_diagonal_preimage_ambientChart f U)

/-- **The first projection restricted to the ambient chart**, a morphism
`ambientChart f U ⟶ U`. It retracts `diagRes` (`diagRes_comp_fstRes`). -/
noncomputable def fstRes : (ambientChart f U).toScheme ⟶ U.toScheme :=
  (pullback.fst f f).resLE U (ambientChart f U) (ambientChart_le_fst_preimage f U)

/-- The restricted diagonal followed by the inclusion of the ambient chart is the inclusion of `U`
followed by the diagonal. -/
theorem diagRes_comp_ι :
    diagRes f U ≫ (ambientChart f U).ι = U.ι ≫ pullback.diagonal f :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The restricted first projection followed by the inclusion of `U` is the inclusion of the
ambient chart followed by the first projection. -/
theorem fstRes_comp_ι :
    fstRes f U ≫ U.ι = (ambientChart f U).ι ≫ pullback.fst f f :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The restricted first projection retracts the restricted diagonal.** Both sides become the
inclusion of `U` after composing with that inclusion, which is a monomorphism, and there the
identity is `AlgebraicGeometry.pullback.diagonal_fst`. -/
theorem diagRes_comp_fstRes : diagRes f U ≫ fstRes f U = 𝟙 U.toScheme := by
  rw [← cancel_mono U.ι, Category.assoc, fstRes_comp_ι, ← Category.assoc, diagRes_comp_ι,
    Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.id_comp]

/-- **The restricted diagonal is surjective on global sections**, with an explicit section: the
retraction `fstRes` gives one. Nothing affine is used, and in particular the ring of sections of
the ambient chart is not computed; this is a split surjection, so it says nothing about the
kernel. -/
theorem surjective_diagRes_appTop : Function.Surjective (diagRes f U).appTop := by
  intro x
  refine ⟨(fstRes f U).appTop x, ?_⟩
  have h := congrArg Scheme.Hom.appTop (diagRes_comp_fstRes f U)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
  exact congr($h x)

/-- **The ambient chart is an affine open of `X ×_S X`** when `U` and `V` are affine. This is
`AlgebraicGeometry.isAffineOpen_inf_preimage` at `g = f` and `V = U`. -/
theorem isAffineOpen_ambientChart {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) : IsAffineOpen (ambientChart f U) :=
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  AlgebraicGeometry.isAffineOpen_inf_preimage f f hUV hUV

/-- **The restricted diagonal is a closed immersion.** Both ends are affine — `U` by hypothesis
and the ambient chart by `isAffineOpen_ambientChart` — and the map on global sections is
surjective by `surjective_diagRes_appTop`, so
`AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine` applies. No identification of the
ambient chart's sections with a tensor product is involved. -/
theorem isClosedImmersion_diagRes {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) : IsClosedImmersion (diagRes f U) :=
  have : IsAffine U.toScheme := hU
  have : IsAffine (ambientChart f U).toScheme := isAffineOpen_ambientChart f U hV hU hUV
  IsClosedImmersion.of_surjective_of_isAffine _ (surjective_diagRes_appTop f U)

/-- On points, the restricted diagonal followed by the inclusion of the ambient chart is the
inclusion of `U` followed by the diagonal. -/
private theorem ambientChart_ι_base_diagRes_base (b : U.toScheme) :
    (ambientChart f U).ι.base ((diagRes f U).base b) =
      (pullback.diagonal f).base (U.ι.base b) := by
  simpa using congrArg (fun g : U.toScheme ⟶ Limits.pullback f f => g.base b)
    (diagRes_comp_ι f U)

/-- **The range of the restricted diagonal, read in `X ×_S X`, is the part of the range of the
diagonal lying over the ambient chart.** This is `diagRes_comp_ι` on points together with
`diagonal_preimage_ambientChart`: the image of the range is the image of `U`, which is the image
of a preimage, and `Set.image_preimage_eq_inter_range` cuts that down to an intersection. -/
@[ega "I 5.3.16" "Underlying-space clause"]
theorem ambientChart_ι_image_range_diagRes :
    (ambientChart f U).ι.base '' Set.range (diagRes f U).base =
      Set.range (pullback.diagonal f).base ∩ (ambientChart f U : Set _) := by
  have hUpre : (U : Set X) = (pullback.diagonal f).base ⁻¹'
      (ambientChart f U : Set _) :=
    congrArg (fun O : X.Opens => (O : Set X)) (diagonal_preimage_ambientChart f U).symm
  rw [← Set.range_comp, show (ambientChart f U).ι.base ∘ (diagRes f U).base =
    (pullback.diagonal f).base ∘ U.ι.base from
      funext (ambientChart_ι_base_diagRes_base f U), Set.range_comp,
    Scheme.Opens.range_ι, hUpre, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- **The ambient chart lies inside the coborder neighbourhood of the diagonal.** The diagonal is
a closed immersion over the chart (`isClosedImmersion_diagRes`), so its range meets the chart in a
set closed *in the chart*, and the maximality criterion
`Stacks.Conormal.subset_coborder_of_closure_inter_subset` then puts the chart inside the coborder.

`Stacks.Conormal.le_coborderRange_of_comp_eq` does not apply: it asks for a closed-immersion
factorization of the whole diagonal through the chart, and the diagonal meets the chart only over
`U`. The replacement is topological — `IsOpen.inter_closure` to move the closure inside the open
chart, and `Topology.IsInducing.closure_eq_preimage_closure_image` to transport it along the
chart's inclusion, where `ambientChart_ι_image_range_diagRes` identifies the set whose closure is
being taken. -/
theorem le_coborderRange_ambientChart {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ambientChart f U ≤ (pullback.diagonal f).coborderRange := by
  have : IsClosedImmersion (diagRes f U) := isClosedImmersion_diagRes f U hV hU hUV
  refine Stacks.Conormal.subset_coborder_of_closure_inter_subset ?_
  rintro x ⟨hxc, hxW⟩
  obtain ⟨a, rfl⟩ : x ∈ Set.range (ambientChart f U).ι.base := by
    rw [Scheme.Opens.range_ι]; exact hxW
  have hin : (ambientChart f U).ι.base a ∈
      closure ((ambientChart f U : Set _) ∩
        Set.range (pullback.diagonal f).base) :=
    (ambientChart f U).isOpen.inter_closure ⟨hxW, hxc⟩
  have hind : Topology.IsInducing (ambientChart f U).ι.base :=
    (ambientChart f U).ι.isOpenEmbedding.isInducing
  have hcl : IsClosed (Set.range (diagRes f U).base) :=
    (diagRes f U).isClosedEmbedding.isClosed_range
  have hmem : a ∈ Set.range (diagRes f U).base := by
    rw [← hcl.closure_eq, hind.closure_eq_preimage_closure_image]
    show (ambientChart f U).ι.base a ∈ closure _
    rw [ambientChart_ι_image_range_diagRes, Set.inter_comm]
    exact hin
  obtain ⟨b, rfl⟩ := hmem
  exact ⟨U.ι.base b, (ambientChart_ι_base_diagRes_base f U b).symm⟩

/-- **The canonical chart of [Stacks, Tag 08S2] is an affine open of the coborder
neighbourhood**, for `U` an affine open of `X` lying inside the preimage of an affine open `V` of
`S`.

`chart f U` is the preimage of the ambient chart under the inclusion of the coborder neighbourhood
(`coborderRange_ι_preimage_ambientChart`), that ambient chart is affine
(`isAffineOpen_ambientChart`) and contained in the neighbourhood
(`le_coborderRange_ambientChart`), and
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion` descends affineness along an open
immersion whose range contains the open.

With `Stacks.LeibnizDerivation.chart_preimage`, this makes `Δ.liftCoborder ∣_ chart f U` a closed
immersion between affine schemes: the affine shape in which the conormal sections over `U` can be
computed. -/
theorem isAffineOpen_chart {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) : IsAffineOpen (chart f U) := by
  rw [← coborderRange_ι_preimage_ambientChart]
  refine (isAffineOpen_ambientChart f U hV hU hUV).preimage_of_isOpenImmersion
    (pullback.diagonal f).coborderRange.ι ?_
  rw [Scheme.Opens.opensRange_ι]
  exact le_coborderRange_ambientChart f U hV hU hUV

end DiagChart

end Stacks.LeibnizDerivation

end
