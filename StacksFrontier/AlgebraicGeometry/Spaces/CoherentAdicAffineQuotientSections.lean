module

public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent

/-!
# The sections of an adic quotient over an affine chart

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a sheaf of ideals cartesian on affine charts and `M` an
`𝒪_F`-module cartesian on affine charts.  Over an *affine* étale chart `V` the sections of the
adic quotient `M / 𝓘 ^ k M` are the ordinary quotient `M(V) / 𝓘(V) ^ k M(V)`: the quotient
projection is surjective on the sections over `V`, and its kernel there is `𝓘(V) ^ k · M(V)`.

Neither half is formal.  Surjectivity is Descent, Proposition 03DW in degree zero, available
through `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian`; the computation of
the kernel is the identification of the affine sections of `𝓘 ^ k M`,
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isAffine`, which is faithfully
flat descent.

This is the statement that lets the second stabilization of Stacks 087X be checked on sections
over the charts of a covering family, and it is what replaces the affine comparison of
Stacks 087W for the quotients themselves.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerMultiple` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerQuotient` — `𝓘 ^ k M` and
  `M / 𝓘 ^ k M` are cartesian on affine charts when `M` and `𝓘` are.
* `AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` — **the projection onto
  `M / 𝓘 ^ k M` is surjective on the sections over an affine chart.**
* `AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π` — **its kernel there is
  `𝓘(V) ^ k · M(V)`.**

## Implementation notes

Coherence of `M` is not assumed, and neither is local Noetherianity: cartesianness on affine
charts is what both halves consume, and
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerQuotient` is obtained from the
cokernel clause for cartesian modules rather than from coherence of the quotient, which would
require the `Fact` instance carrying local Noetherianity.

The two spellings of `𝓘 ^ k M` — the local-membership closure
`AlgebraicGeometry.Space.idealPowSubmodule` and the least dominating sheaf submodule
`AlgebraicGeometry.Space.idealPowerMultiple`, out of which `Coh(F, 𝓘)` is built — are identified
by `AlgebraicGeometry.Space.idealPowerMultiple_eq_idealPowSubmodule`.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **`𝓘 ^ k M` is cartesian on affine charts** when `M` and `𝓘` are, for the spelling
`AlgebraicGeometry.Space.idealPowerMultiple` out of which `Coh(F, 𝓘)` is built. -/
theorem isCartesianOnAffineCharts_idealPowerMultiple
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ) :
    IsCartesianOnAffineCharts
      (idealPowerMultiple B S hS F hF 𝓘 k M).toSheafOfModules := by
  rw [idealPowerMultiple_eq_idealPowSubmodule B S hS F hF 𝓘 k M]
  exact isCartesianOnAffineCharts_idealPowSubmodule B S hS F hF 𝓘 M hMcart hIcart k

/-- **The adic quotient `M / 𝓘 ^ k M` is cartesian on affine charts** when `M` and `𝓘` are: it is
the cokernel of the inclusion of `𝓘 ^ k M`, and both of its ends are cartesian. -/
theorem isCartesianOnAffineCharts_idealPowerQuotient
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ) :
    IsCartesianOnAffineCharts (idealPowerQuotient B S hS F hF 𝓘 k M) :=
  isCartesianOnAffineCharts_cokernel_of_cartesian
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι
    (isCartesianOnAffineCharts_idealPowerMultiple B S hS F hF 𝓘 hIcart M hMcart k) hMcart

/-- **The projection of `M` onto `M / 𝓘 ^ k M` is surjective on the sections over an affine
chart.**  This is the degree-zero form of Descent, Proposition 03DW: the projection is an
epimorphism whose source and whose kernel `𝓘 ^ k M` are cartesian on affine charts. -/
theorem surjective_val_app_idealPowerQuotient_π
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    Function.Surjective
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)) :=
  surjective_val_app_cokernel_π_of_cartesian
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι
    (isCartesianOnAffineCharts_idealPowerMultiple B S hS F hF 𝓘 hIcart M hMcart k) hMcart V hV

/-- **The kernel of the projection onto `M / 𝓘 ^ k M` on the sections over an affine chart is
`𝓘(V) ^ k · M(V)`.**

A section dies in a sheaf quotient exactly when it is a section of the submodule divided out
(`AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff`), and over an affine chart the sections of
`𝓘 ^ k M` are `𝓘(V) ^ k · M(V)` by
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isAffine`. -/
theorem ker_val_app_idealPowerQuotient_π
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    LinearMap.ker
        ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)).hom =
      chartSectionIdeal B S hS F hF 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V))) := by
  have h : chartSubmodule B S hS F hF (idealPowerMultiple B S hS F hF 𝓘 k M) V =
      chartSectionIdeal B S hS F hF 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V))) := by
    rw [idealPowerMultiple_eq_idealPowSubmodule B S hS F hF 𝓘 k M]
    exact chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS F hF 𝓘 M hMcart hIcart k hV
  refine SetLike.ext fun s => ?_
  rw [LinearMap.mem_ker, ← h]
  exact cokernel_π_app_eq_zero_iff B S hS F hF _ (op V) s

end AlgebraicGeometry.Space

end
