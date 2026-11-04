module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartOverlap

/-!
# The descended bundle carries its two trivialisations compatibly

`AlgebraicGeometry.exists_isFiniteLocallyFree_restrict_iso_of_isIso_restrict_free` descends a
finite locally free module `𝒢` on `X'`, free over `b ⁻¹ᵁ U`, to a finite locally free module `N`
on `X`, and returns the two identifications of the restrictions of `N` -- with the free module
over `U`, and with the inverse image of `𝒢` along the section of `b` over `V`.  Those two
identifications are returned separately, and nothing relates them.

This file returns them *together with* their agreement over the overlap `U ⊓ V`, through the two
comparisons `AlgebraicGeometry.overlapIsoFamily` the glueing was performed with.  The agreement is
`AlgebraicGeometry.TwoOpensGlue.chartRestrictIso_false_eq_true`; all that is done here is to carry
it through the instantiation, and to repeat the check of finite local freeness on the two opens of
the cover.

The agreement is what the comparison `b^*N ≅ 𝒢` of the essential surjectivity half of
[Stacks, Tag 0EXD] is glued from:  over `b ⁻¹ᵁ U` that comparison is built from the trivialisation
of `N` over `U` and from `α`, over `b ⁻¹ᵁ V` from the identification of `N` over `V` with the
inverse image of `𝒢`, and the two agree over `b ⁻¹ᵁ (U ⊓ V)` precisely because the two
trivialisations of `N` agree over `U ⊓ V`.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFree_restrict_iso_compat_of_isIso_restrict_free`:
  **the descent, with the agreement of the two trivialisations over the overlap.**

## Implementation notes

The two identifications are returned as one family indexed by `ULift Bool`, at the modules
`AlgebraicGeometry.TwoOpensGlue.mdl` and the opens `AlgebraicGeometry.TwoOpensGlue.opn` of the
two-element glueing rather than at `U`, `V` and the two modules separately.  The two spellings
have the same type, by reduction of the families at their indices, but only the former lets
`IsOpenImmersion (AlgebraicGeometry.TwoOpensGlue.mid U V ⟨false⟩)` be synthesised: instance search
does not perform that reduction, so at the unfolded spelling the chart comparison
`AlgebraicGeometry.restrictChartIso` cannot be elaborated.

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

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {U V : X.Opens} [IsIso (b ∣_ V)]
  {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-- **A finite locally free module on `X'`, free over the preimage of `U` and pulled back along
the section of `b` over `V`, descends to a finite locally free module on `X` whose two
trivialisations agree over the overlap.**

This is `AlgebraicGeometry.exists_isFiniteLocallyFree_restrict_iso_of_isIso_restrict_free` with
the agreement `AlgebraicGeometry.TwoOpensGlue.chartRestrictIso_false_eq_true` of the two chart
comparisons of the glued module carried along, which is the datum the comparison `b^*N ≅ 𝒢` is
glued from. -/
theorem exists_isFiniteLocallyFree_restrict_iso_compat_of_isIso_restrict_free
    (hUV : U ⊔ V = ⊤) [Finite I] (hG : Scheme.Modules.IsFiniteLocallyFree G)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    ∃ (N : X.Modules) (κ : ∀ i, Scheme.Modules.restrict N (TwoOpensGlue.opn U V i).ι ≅
        TwoOpensGlue.mdl U V
          (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
          (Scheme.Modules.restrict G (freeChartBaseSection b V)) i),
      Scheme.Modules.IsFiniteLocallyFree N ∧
        restrictChartIso (TwoOpensGlue.opn U V ⟨false⟩).ι (κ ⟨false⟩)
              (TwoOpensGlue.mid U V ⟨false⟩) (TwoOpensGlue.mid_comp U V ⟨false⟩) ≪≫
            overlapIsoFamily b α hα ⟨false⟩ =
          restrictChartIso (TwoOpensGlue.opn U V ⟨true⟩).ι (κ ⟨true⟩)
                (TwoOpensGlue.mid U V ⟨true⟩) (TwoOpensGlue.mid_comp U V ⟨true⟩) ≪≫
            overlapIsoFamily b α hα ⟨true⟩ := by
  obtain ⟨N, κ, hcompat⟩ := TwoOpensGlue.exists_restrict_iso_of_middle_compat U V
    (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (Scheme.Modules.restrict G (freeChartBaseSection b V)) (overlapIsoFamily b α hα)
  refine ⟨N, κ, ?_, hcompat⟩
  have hiSup : (⨆ i, TwoOpensGlue.opn U V i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hUV]
    exact sup_le (le_iSup_of_le ⟨false⟩ le_rfl) (le_iSup_of_le ⟨true⟩ le_rfl)
  refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top (TwoOpensGlue.opn U V) hiSup ?_
  intro i
  refine Scheme.Modules.IsFiniteLocallyFree.of_iso (κ i).symm ?_
  match i with
  | ⟨false⟩ => exact Scheme.Modules.isFiniteLocallyFree_free I
  | ⟨true⟩ => exact Scheme.Modules.IsFiniteLocallyFree.restrict (freeChartBaseSection b V) hG

end AlgebraicGeometry

end
