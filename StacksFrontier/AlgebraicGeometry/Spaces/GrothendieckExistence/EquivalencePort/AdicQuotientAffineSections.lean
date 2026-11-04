module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The sections of `M / 𝓘 ^ k M` over an affine chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `𝓘 ⊆ 𝒪_F`
be a sheaf of ideals and `M` an `𝒪_F`-module, both cartesian on affine charts.  Over an affine
étale chart `V` the sections of the adic quotient `M / 𝓘 ^ k M` are the quotient
`M(V) / 𝓘(V) ^ k M(V)` of the sections of `M`, compatibly with the projections
(`AlgebraicGeometry.Space.C1573.adicQuotientSectionsEquivOfIsAffine`).

This is the degree-zero form of Descent, Proposition 03DW, read off from
`AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **The sections of `M / 𝓘 ^ k M` over an affine chart are `M(V) / 𝓘(V) ^ k M(V)`.** -/
def C1573.adicQuotientSectionsEquivOfIsAffine
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    (smallEtaleAdicQuotient B S hS F hF 𝓘 k M).val.obj (op V) ≃ₗ[chartRing B S hS F hF V]
      M.val.obj (op V) ⧸ (chartSectionIdeal B S hS F hF 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))) :=
  ((LinearMap.quotKerEquivOfSurjective
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)).hom
      (surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV)).symm).trans
    (Submodule.quotEquivOfEq _ _
      (ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV))

/-- The identification of the sections of `M / 𝓘 ^ k M` with `M(V) / 𝓘(V) ^ k M(V)` sends the
image of a section of `M` to its class. -/
theorem C1573.adicQuotientSectionsEquivOfIsAffine_projection
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (x : M.val.obj (op V)) :
    adicQuotientSectionsEquivOfIsAffine B S hS F hF 𝓘 hIcart M hMcart k hV
        ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M).val.app (op V) x) =
      Submodule.Quotient.mk x := by
  have h := LinearMap.quotKerEquivOfSurjective_symm_apply
    ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)).hom
    (surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV) x
  exact congrArg (Submodule.quotEquivOfEq _ _
    (ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV)) h

end AlgebraicGeometry.Space

end
