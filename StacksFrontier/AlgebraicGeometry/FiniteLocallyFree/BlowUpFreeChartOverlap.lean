module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartGlue
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelOfFunctor

/-!
# The two trivialisations of a module glued from two opens agree over the overlap

`AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle` glues two sheaves of modules `M₁`
and `M₂`, given on two opens `U₁` and `U₂` of a scheme and identified over the overlap through a
module `L` there, into a sheaf of modules `K` on the scheme, and returns identifications of the
restrictions of `K` with `M₁` and with `M₂`.  It says nothing about how those two identifications
are related.  That relation is what is proved here:  restricting the first one to the overlap and
following it with the comparison `σ ⟨false⟩` of `M₁` with `L` gives the same isomorphism
`K|_{U₁ ⊓ U₂} ≅ L` as doing the same with the second one and `σ ⟨true⟩`.

Without it the glued module carries no usable comparison at all beyond its two charts separately:
an isomorphism of `K`, or of an inverse image of `K`, with a third module can be built chart by
chart, but the two pieces can only be glued once they are known to agree over the overlap, and
*that* agreement is a consequence of this one.  It is an input of the comparison `b^*N ≅ 𝒢` in
the essential surjectivity half of [Stacks, Tag 0EXD] for the almost blowup square of
[Stacks, Example 0EVH].

## Main definitions

* `AlgebraicGeometry.TwoOpensGlue.chartRestrictIso`: **the trivialisation of the glued module over
  the overlap, read through the `i`-th chart** -- the `i`-th comparison isomorphism restricted
  along the inclusion of the overlap into the `i`-th open, followed by `σ i`.

## Main results

* `AlgebraicGeometry.TwoOpensGlue.chartRestrictIso_false_eq_true`: **the two trivialisations of
  the glued module over the overlap agree.**
* `AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle_compat`:
  `AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle` with that agreement carried
  along.

## Implementation notes

The proof is the three-step argument of
`AlgebraicGeometry.AffineChartKernels.chartRestrictIso_inf`, which proves the same statement for
the glueing datum of the quasi-coherent kernels of an integral transform, specialised to the
two-element family of `AlgebraicGeometry.TwoOpensGlue`:

* both isomorphisms are rewritten by
  `AlgebraicGeometry.restrictCompIso_hom_map_restrictChartIso` as the *transposed* comparison
  `Stacks.SheafOfModules.ModulesGlueData.chartAdjunct` -- a morphism of modules on the ambient
  scheme, hence independent of the chart -- restricted to the range of the inclusion of the
  overlap, followed by a chart comparison and by `σ i`;
* the two transposed comparisons are identified over that range by the lemma
  `restrictFunctor_map_chartAdjunct_comp_iso_of_le_opensRange` of
  `AlgebraicGeometry.RestrictIsoGlueData`,
  which inserts the comparison datum of the glueing between them, and the datum is here
  `AlgebraicGeometry.TwoOpensGlue.transIso`, whose off-diagonal value
  `AlgebraicGeometry.middleChartIso` unfolds to a composite of `σ ⟨false⟩` and `σ ⟨true⟩` in which
  everything else cancels;
* the resulting identity over the range of the inclusion of the overlap is transported back to
  the overlap itself along `AlgebraicGeometry.openLift`, which is an isomorphism there, by
  `AlgebraicGeometry.restrictFunctor_map_injective_of_isIso`.

The open of the ambient scheme at which the middle step is applied is
`((U₁ ⊓ U₂).ι).opensRange` rather than `U₁ ⊓ U₂`:  the two are equal, by
`AlgebraicGeometry.Scheme.Opens.opensRange_ι`, but only the former is the range of the morphism
`AlgebraicGeometry.openLift` factors through, which is what the middle and last steps are stated
at.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace TwoOpensGlue

variable {S : Scheme.{u}} (U₁ U₂ : S.Opens) (M₁ : U₁.toScheme.Modules) (M₂ : U₂.toScheme.Modules)
  {L : (U₁ ⊓ U₂).toScheme.Modules}
  (σ : ∀ i, Scheme.Modules.restrict (mdl U₁ U₂ M₁ M₂ i) (mid U₁ U₂ i) ≅ L)

/-- The comparison datum of the two-chart glueing datum is
`AlgebraicGeometry.TwoOpensGlue.transIso`. -/
theorem glueData_iso (i j : ULift.{u} Bool) {W : S.Opens}
    (hi : W ≤ ((opn U₁ U₂ i).ι).opensRange) (hj : W ≤ ((opn U₁ U₂ j).ι).opensRange) :
    (glueData U₁ U₂ M₁ M₂ σ).iso i j hi hj = transIso U₁ U₂ M₁ M₂ σ i j hi hj :=
  rfl

/-- The modules of the two-chart glueing datum are `AlgebraicGeometry.TwoOpensGlue.mdl`. -/
theorem glueData_mod (i : ULift.{u} Bool) :
    (glueData U₁ U₂ M₁ M₂ σ).mod i = mdl U₁ U₂ M₁ M₂ i :=
  rfl

/-- The range of the inclusion of the overlap lies in the range of the inclusion of each of the
two opens. -/
theorem opensRange_inf_ι_le (i : ULift.{u} Bool) :
    ((U₁ ⊓ U₂).ι).opensRange ≤ ((opn U₁ U₂ i).ι).opensRange := by
  rw [Scheme.Opens.opensRange_ι]
  exact inf_le_opensRange_opn U₁ U₂ i

/-- **The trivialisation of the glued module over the overlap, read through the `i`-th chart**:
the `i`-th comparison isomorphism of the glued module, restricted along the inclusion of the
overlap into the `i`-th open, followed by the comparison `σ i` of the `i`-th module with the
module `L` on the overlap. -/
def chartRestrictIso (i : ULift.{u} Bool) :
    Scheme.Modules.restrict (glueData U₁ U₂ M₁ M₂ σ).glued (U₁ ⊓ U₂).ι ≅ L :=
  restrictChartIso (opn U₁ U₂ i).ι ((glueData U₁ U₂ M₁ M₂ σ).chartIso i) (mid U₁ U₂ i)
    (mid_comp U₁ U₂ i) ≪≫ σ i

/-- **The two trivialisations of the glued module over the overlap agree.**  Restricting the
comparison of the glued module with `M₁` to the overlap and following it with `σ ⟨false⟩` gives
the same isomorphism `K|_{U₁ ⊓ U₂} ≅ L` as restricting the comparison with `M₂` and following it
with `σ ⟨true⟩`.

This is the two-chart case of the agreement that
`AlgebraicGeometry.AffineChartKernels.chartRestrictIso_inf` proves for the glueing datum of the
quasi-coherent kernels of an integral transform, and the proof is the same three steps. -/
theorem chartRestrictIso_false_eq_true :
    chartRestrictIso U₁ U₂ M₁ M₂ σ ⟨false⟩ = chartRestrictIso U₁ U₂ M₁ M₂ σ ⟨true⟩ := by
  have hZ : ((U₁ ⊓ U₂).ι).opensRange ≤ ((U₁ ⊓ U₂).ι).opensRange := le_rfl
  have h1 := (glueData U₁ U₂ M₁ M₂ σ).restrictFunctor_map_chartAdjunct_comp_iso_of_le_opensRange
    ⟨false⟩ ⟨true⟩ (opensRange_inf_ι_le U₁ U₂ ⟨false⟩) (opensRange_inf_ι_le U₁ U₂ ⟨true⟩)
  have key := fun i : ULift.{u} Bool =>
    restrictCompIso_hom_map_restrictChartIso (opn U₁ U₂ i).ι (U₁ ⊓ U₂).ι
      (mid U₁ U₂ i) (mid_comp U₁ U₂ i)
      ((glueData U₁ U₂ M₁ M₂ σ).toModulesGlueData.chartAdjunct i)
      ((glueData U₁ U₂ M₁ M₂ σ).chartIso i)
      ((glueData U₁ U₂ M₁ M₂ σ).toModulesGlueData.restrictFunctor_map_chartAdjunct i)
      (σ i) hZ
  have hiso : IsIso (openLift (U₁ ⊓ U₂).ι hZ) := by
    rw [← eq_openLift _ hZ _ (Scheme.Hom.isoOpensRange_inv_comp _)]
    infer_instance
  refine Iso.ext (restrictFunctor_map_injective_of_isIso (openLift (U₁ ⊓ U₂).ι hZ) ?_)
  rw [← cancel_epi (restrictCompIso (openLift (U₁ ⊓ U₂).ι hZ) (U₁ ⊓ U₂).ι
    (openLift_comp _ hZ) (glueData U₁ U₂ M₁ M₂ σ).toModulesGlueData.glued).hom]
  simp only [chartRestrictIso]
  refine (key ⟨false⟩).trans ?_
  refine Eq.trans ?_ (key ⟨true⟩).symm
  rw [glueData_iso] at h1
  dsimp only [RestrictIsoGlueData.toModulesGlueData_mod, glueData_mod] at h1 ⊢
  rw [← h1]
  simp only [transIso, middleChartIso, restrictPushforwardIsoOfRestrictIso, restrictMiddleIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Two sheaves of modules on two opens covering a scheme, identified over the overlap through
a module there, come from a sheaf of modules on the scheme, and its two trivialisations agree
over the overlap.**  This is
`AlgebraicGeometry.TwoOpensGlue.exists_restrict_iso_of_middle` with the agreement
`AlgebraicGeometry.TwoOpensGlue.chartRestrictIso_false_eq_true` carried along, which is what
turns the two restricted comparisons of the glued module with a third module into one global
comparison. -/
theorem exists_restrict_iso_of_middle_compat :
    ∃ (K : S.Modules) (κ : ∀ i, Scheme.Modules.restrict K (opn U₁ U₂ i).ι ≅
        mdl U₁ U₂ M₁ M₂ i),
      restrictChartIso (opn U₁ U₂ ⟨false⟩).ι (κ ⟨false⟩) (mid U₁ U₂ ⟨false⟩)
            (mid_comp U₁ U₂ ⟨false⟩) ≪≫ σ ⟨false⟩ =
        restrictChartIso (opn U₁ U₂ ⟨true⟩).ι (κ ⟨true⟩) (mid U₁ U₂ ⟨true⟩)
            (mid_comp U₁ U₂ ⟨true⟩) ≪≫ σ ⟨true⟩ :=
  ⟨(glueData U₁ U₂ M₁ M₂ σ).glued, (glueData U₁ U₂ M₁ M₂ σ).chartIso,
    chartRestrictIso_false_eq_true U₁ U₂ M₁ M₂ σ⟩

end TwoOpensGlue

end AlgebraicGeometry

end
