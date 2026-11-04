module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.Construction
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero

/-!
# The trace maps on forms in degree zero

Under the degree-zero identifications `Ω^0_{X/ℤ} ≅ 𝒪_X` and `Ω^0_{Y/ℤ} ≅ 𝒪_Y`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`), the degree-zero map
`Θ^0_{Y/X} : f_*Ω^0_{Y/ℤ} ⟶ Ω^0_{X/ℤ}` of a rule satisfying condition (1) of Stacks, Lemma 0FLB
is the trace `Trace_f : f_*𝒪_Y ⟶ 𝒪_X`. This is clause (1) of Stacks, Proposition 0FLC.

## Main results

* `AlgebraicGeometry.FormsTraceRule.IsTrace.comp_relativeDifferentialFormsZeroIso`: for any rule
  with condition (1).
* `AlgebraicGeometry.Scheme.Hom.formsTrace_zero`: for the rule `formsTraceRule`, i.e. for the
  maps `Scheme.Hom.formsTrace`.

## Implementation notes

The identity is checked on sections. A degree-zero form over `f⁻¹U` is `b • 1` with `b` its
image under the degree-zero identification
(`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit_smul_one`), condition
(1) on the unit form (`AlgebraicGeometry.FormsTraceRule.IsTrace.apply_smul_unitForm`) gives
`Θ^0(b • 1) = Trace_f(b) • 1`, and the degree-zero identification of `X` carries `t • 1` back to
`t` (`exteriorPieceZeroIsoUnit_hom_smul_one`). The scalars are taken in `Γ(Y, f⁻¹U)` and
`Γ(X, U)` throughout, in the spelling
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison_zero` uses for the same passage.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace FormsTraceRule

/-- **Stacks 0FLC (1) for any rule with condition (1) of 0FLB**: under the degree-zero
identifications `Ω^0 ≅ 𝒪`, the map `Θ^0_{Y/X}` is the trace `Trace_f : f_*𝒪_Y ⟶ 𝒪_X`. -/
theorem IsTrace.comp_relativeDifferentialFormsZeroIso {Θ : FormsTraceRule.{u}} (h : Θ.IsTrace)
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f) :
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    Θ f hf 0 ≫ (Scheme.Hom.relativeDifferentialFormsZeroIso X.toSpecZ).hom =
      (Scheme.Modules.pushforward f).map
          (Scheme.Hom.relativeDifferentialFormsZeroIso Y.toSpecZ).hom ≫ f.finiteTrace := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show (Scheme.Hom.relativeDifferentialFormsZeroIso X.toSpecZ).hom.val.app (op U)
      ((Θ f hf 0).app U x) =
    f.finiteTrace.app U
      ((Scheme.Hom.relativeDifferentialFormsZeroIso Y.toSpecZ).hom.val.app (op (f ⁻¹ᵁ U)) x)
  obtain ⟨r, hr⟩ : ∃ r : Γ(Y, f ⁻¹ᵁ U),
      (Scheme.Hom.relativeDifferentialFormsZeroIso Y.toSpecZ).hom.val.app (op (f ⁻¹ᵁ U)) x = r :=
    ⟨_, rfl⟩
  have hx := (Scheme.Hom.deRhamAlgebras Y.toSpecZ).exteriorPieceZeroIsoUnit_smul_one
    (op (f ⁻¹ᵁ U)) x r hr
  have hΘ := h.apply_smul_unitForm f hf U r
  rw [hr, ← hx]
  refine (congrArg (ConcreteCategory.hom
    ((Scheme.Hom.relativeDifferentialFormsZeroIso X.toSpecZ).hom.val.app (op U))) hΘ).trans ?_
  exact (Scheme.Hom.deRhamAlgebras X.toSpecZ).exteriorPieceZeroIsoUnit_hom_smul_one (op U) _

end FormsTraceRule

namespace Scheme.Hom

/-- **Stacks 0FLC (1): in degree `0` the trace maps on forms are the trace.** Under the
degree-zero identifications `Ω^0_{X/ℤ} ≅ 𝒪_X` and `Ω^0_{Y/ℤ} ≅ 𝒪_Y`, the map
`Θ^0_{Y/X} : f_*Ω^0_{Y/ℤ} ⟶ Ω^0_{X/ℤ}` of a finite syntomic `f : Y ⟶ X` is
`Trace_f : f_*𝒪_Y ⟶ 𝒪_X`. -/
theorem formsTrace_zero {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f) :
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    f.formsTrace hf 0 ≫ (relativeDifferentialFormsZeroIso X.toSpecZ).hom =
      (Scheme.Modules.pushforward f).map (relativeDifferentialFormsZeroIso Y.toSpecZ).hom ≫
        f.finiteTrace :=
  formsTraceRule_isTrace.comp_relativeDifferentialFormsZeroIso f hf

end Scheme.Hom

end AlgebraicGeometry

end
