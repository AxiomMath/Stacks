module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulNested
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismClauseThree
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.AffineDatum

/-!
# Clause (3) of Tag 01O9 for the data a global `(ℒ, ψ)` induces

`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso` proves the
consistency of the clause (3) prescriptions of [Stacks, Tag 01O9] along a nested pair of affine
opens `Z ≤ V` of the base — but for *given* [Stacks, Tag 01NK] data over `Z` and `V`, under a
hypothesis `hχ` saying that the one over `Z` is the one over `V` pulled back.  Its module
docstring records the discharge of `hχ` for the data a **global** `(ℒ, ψ)` induces as the one
thing still missing.

**This file discharges it.**  `…GradedPowerMap.affineDatum` is the induced datum, and
`affineDatum_hchi` is `hχ` for it; `relativeChart_affineDatum_resLE` is the resulting consistency,
restated on the whole covering open of the datum over `Z` so that a gluing along the preimages of
the affine opens of the base can consume it.

## Main results

* `…GradedPowerMap.affineDatum_hchi`: **`hχ` for the induced data.**
* `…GradedPowerMap.image_coveringOpen_affineDatum`: the covering open of the induced datum, read
  back in `X`, is `U(ψ_V)`.
* `…GradedPowerMap.coveringOpen_comap_affineDatum`: for affine `Z ≤ V`, restricting the datum
  along `𝒜(V) → 𝒜(Z)` does not shrink the covering open.
* `…GradedPowerMap.relativeChart_affineDatum_resLE`: **the clause (3) prescriptions are
  consistent**, on the whole covering open.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) {Z V : S.Opens} (h : Z ≤ V)

/-- **The induced [Stacks, Tag 01NK] data over a nested pair of opens of the base are compatible**:
the datum over `Z` is the datum over `V` pulled back along the inclusion
`f^{-1}(Z) ⟶ f^{-1}(V)`, across the comparison
`…ProjChartRatioPullbackLocalMul.restrictCompIso`.

This is the hypothesis `hχ` of
`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso` at the data the
global `(ℒ, ψ)` of [Stacks, Tag 01O8] induces, and the module docstrings of
`StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismFromSections` and
`StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.AffineRestriction` recorded its
discharge as the one thing standing between the clause (3) prescriptions and a glued `r_{ℒ,ψ}`.

Two ingredients: the values of `ψ` commute with restriction of the base open
(`…GradedPowerMap.value_res`), and restriction of the graded ring of sections is restriction on
the homogeneous components (`…SheafGradedAlgebra.resRingHom_apply`); what remains is the coherence
`…ProjChartRatioPullbackLocalMul.natTensorPowCongr_restrictPowSection_res`. -/
public theorem affineDatum_hchi (n : ℕ) (a : A.grading V n) :
    Scheme.Modules.Hom.app
        (natTensorPowCongr (restrictCompIso P.L (f.preimage_mono h)) n).hom ⊤
        ((comap (A.res h) (P.affineDatum Z)).toFun n a)
      = pullSection (T.homOfLE (f.preimage_mono h))
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n ((P.affineDatum V).toFun n a) := by
  have hcomp : A.componentEquiv Z n
        ((A.res h).gradedAddHom n a)
      = (A.piece (n : ℤ)).presheaf.map (homOfLE h).op (A.componentEquiv V n a) :=
    A.resRingHom_apply h (a : A.sectionRing V) n
  show Scheme.Modules.Hom.app
      (natTensorPowCongr (restrictCompIso P.L (f.preimage_mono h)) n).hom ⊤
      (restrictPowSection P.L (f ⁻¹ᵁ Z) n
        (P.value n Z (A.componentEquiv Z n ((A.res h).gradedAddHom n a)))) = _
  rw [hcomp, P.value_res n h]
  exact natTensorPowCongr_restrictPowSection_res P.L (f.preimage_mono h) n
    (P.value n V (A.componentEquiv V n a))


open Stacks.AlgebraicGeometry.RelativeProjFromSections

variable (hZ : IsAffineOpen Z) (hV : IsAffineOpen V)

/-- **The image in `X` of the covering open of the induced datum is `U(ψ_V)`.**  The covering open
of the induced datum is an open of the subscheme `f^{-1}(V)`; read back in `X` it is the open
`…GradedPowerMap.coveringOpenOver` on the nose, nothing being cut away. -/
public theorem image_coveringOpen_affineDatum (W : S.Opens) :
    (f ⁻¹ᵁ W).ι ''ᵁ (P.affineDatum W).coveringOpen = P.coveringOpenOver W := by
  rw [P.coveringOpen_affineDatum W]
  simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using
    inf_eq_right.mpr (P.coveringOpenOver_le_preimage W)

include hZ hV h in
/-- **For affine `Z ≤ V` the open on which the sections restricted from `V` generate is the whole
covering open of the datum over `Z`.**  By the open component of clause (3) the former is the part
of `U(ψ_V)` lying over `f^{-1}(Z)`, and by `…GradedPowerMap.coveringOpenOver_inf_preimage_eq` that
is `U(ψ_Z)`.  So restricting along `𝒜(V) → 𝒜(Z)` loses no points, which is what lets the clause (3)
prescription over `Z` be compared with the one over `V` on all of its own source. -/
public theorem coveringOpen_comap_affineDatum :
    (comap (A.res h) (P.affineDatum Z)).coveringOpen = (P.affineDatum Z).coveringOpen := by
  rw [Stacks.AlgebraicGeometry.RelativeProjFromSections.coveringOpen_comap_eq_preimage h
      (T.homOfLE (f.preimage_mono h)) (P.affineDatum V)
      (restrictCompIso P.L (f.preimage_mono h)) (P.affineDatum Z)
      (P.affineDatum_hchi h),
    P.coveringOpen_affineDatum V, P.coveringOpen_affineDatum Z,
    ← P.coveringOpenOver_inf_preimage_eq hZ hV h,
    Scheme.Hom.preimage_inf, (f ⁻¹ᵁ Z).ι_preimage_self, inf_top_eq,
    ← Scheme.Hom.comp_preimage, T.homOfLE_ι (f.preimage_mono h)]


variable (rp : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)

include hZ hV h in
/-- **Stacks Project, Tag 01O9: the clause (3) prescriptions of the induced data are consistent
along a nested pair of affine opens of the base.**  For affine opens `Z ≤ V` of `S`, the morphism
`r_{ℒ,ψ}` prescribed over `Z` is the one prescribed over `V`, restricted along the inclusion of
`U(ψ_Z)` in `U(ψ_V)`.

Unlike `Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso`, whose
source is the open on which the sections restricted from `V` generate, this is stated on the
**whole** covering open of the datum over `Z` — which `coveringOpen_comap_affineDatum` says is the
same open — and so is the shape a gluing along the preimages of the affine opens of the base
consumes.

Nothing is carried: the data are the ones `…GradedPowerMap.affineDatum` derives from the global
`(ℒ, ψ)`, and the comparison hypothesis is `affineDatum_hchi`. -/
public theorem relativeChart_affineDatum_resLE
    (le' : (P.affineDatum Z).coveringOpen
      ≤ (T.homOfLE (f.preimage_mono h)) ⁻¹ᵁ (P.affineDatum V).coveringOpen) :
    relativeChart rp Z hZ (P.affineDatum Z)
      = (T.homOfLE (f.preimage_mono h)).resLE (P.affineDatum V).coveringOpen
            ((P.affineDatum Z).coveringOpen) le'
        ≫ relativeChart rp V hV (P.affineDatum V) := by
  have hkey := resLE_relativeChart_of_iso rp h hZ hV (T.homOfLE (f.preimage_mono h))
    (P.affineDatum V) (restrictCompIso P.L (f.preimage_mono h)) (P.affineDatum Z)
    (P.affineDatum_hchi h)
  have hEq := P.coveringOpen_comap_affineDatum h hZ hV
  have h2 := congrArg (fun k => (f ⁻¹ᵁ Z).toScheme.homOfLE hEq.ge ≫ k) hkey
  simp only [← Category.assoc, Scheme.homOfLE_homOfLE, Scheme.Hom.map_resLE] at h2
  simpa using h2

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
