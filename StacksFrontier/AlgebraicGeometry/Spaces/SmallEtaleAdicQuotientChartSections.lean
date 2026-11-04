module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSubsheafAffineSections
public import StacksFrontier.RingTheory.Module.AdicSystem.HomAdicSections

/-!
# The adic quotient tower over an affine chart

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_F` be a sheaf
of ideals and let `Z` be an `𝒪_F`-module, both cartesian on affine charts.  Over an affine étale
chart `V` the sections of the adic quotient are the ordinary quotient of the sections,

`(Z / 𝓘 ^ k Z)(V) ≃ Z(V) / 𝓘(V) ^ k Z(V)`,

as a linear equivalence, and this equivalence carries the transition maps of the sheaf tower
`(Z / 𝓘 ^ n Z)` to the transition maps `AdicCompletion.transitionMap` of the module tower
`(Z(V) / 𝓘(V) ^ n Z(V))`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv` — the identification
  `Z(V) / 𝓘(V) ^ k Z(V) ≃ (Z / 𝓘 ^ k Z)(V)`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv_mk` — it sends the class of a
  section to its image under the projection.
* `AlgebraicGeometry.Space.transition_val_app_smallEtaleAdicQuotientChartSectionsEquiv` — **it
  intertwines the transition maps** of the sheaf tower with those of the module tower.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    [HasCokernels (Modules.{u, m} B S hS F hF)]
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The sections of `Z / 𝓘 ^ k Z` over an affine étale chart are `Z(V) / 𝓘(V) ^ k Z(V)`**: the
projection is surjective on the sections over an affine chart, with kernel `𝓘(V) ^ k · Z(V)`. -/
def smallEtaleAdicQuotientChartSectionsEquiv
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (Z : Modules.{u, m} B S hS F hF) (hZcart : IsCartesianOnAffineCharts Z) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    (Z.val.obj (op V) ⧸ chartSectionIdeal B S hS F hF 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS F hF V) (Z.val.obj (op V))))
        ≃ₗ[chartRing B S hS F hF V]
      (smallEtaleAdicQuotient B S hS F hF 𝓘 k Z).val.obj (op V) :=
  (Submodule.quotEquivOfEq _ _
        (ker_val_app_smallEtaleAdicQuotient_π B S hS F hF 𝓘 hIcart Z hZcart k hV)).symm.trans
    (LinearMap.quotKerEquivOfSurjective _
      (surjective_val_app_smallEtaleAdicQuotient_π B S hS F hF 𝓘 hIcart Z hZcart k hV))

/-- **The identification sends the class of a section of `Z` over the chart to its image under
the projection onto `Z / 𝓘 ^ k Z`.** -/
theorem smallEtaleAdicQuotientChartSectionsEquiv_mk
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (Z : Modules.{u, m} B S hS F hF) (hZcart : IsCartesianOnAffineCharts Z) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) (z : Z.val.obj (op V)) :
    smallEtaleAdicQuotientChartSectionsEquiv B S hS F hF 𝓘 hIcart Z hZcart k hV
        (Submodule.Quotient.mk z) =
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k Z).val.app (op V) z :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _
    (surjective_val_app_smallEtaleAdicQuotient_π B S hS F hF 𝓘 hIcart Z hZcart k hV) z

/-- **The identification intertwines the transition maps.**  The transition map
`(Z / 𝓘 ^ (k + 1) Z)(V) ⟶ (Z / 𝓘 ^ k Z)(V)` of the sheaf tower corresponds to the transition map
`Z(V) / 𝓘(V) ^ (k + 1) Z(V) ⟶ Z(V) / 𝓘(V) ^ k Z(V)` of the module tower, which is Mathlib's
`AdicCompletion.transitionMap`. -/
theorem transition_val_app_smallEtaleAdicQuotientChartSectionsEquiv
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (Z : Modules.{u, m} B S hS F hF) (hZcart : IsCartesianOnAffineCharts Z) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V))
    (w : Z.val.obj (op V) ⧸ chartSectionIdeal B S hS F hF 𝓘 V ^ (k + 1) •
      (⊤ : Submodule (chartRing B S hS F hF V) (Z.val.obj (op V)))) :
    (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 k Z).val.app (op V)
        (smallEtaleAdicQuotientChartSectionsEquiv B S hS F hF 𝓘 hIcart Z hZcart (k + 1) hV w) =
      smallEtaleAdicQuotientChartSectionsEquiv B S hS F hF 𝓘 hIcart Z hZcart k hV
        (AdicCompletion.transitionMap (chartSectionIdeal B S hS F hF 𝓘 V) (Z.val.obj (op V))
          (Nat.le_succ k) w) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ w
  rw [← hz, smallEtaleAdicQuotientChartSectionsEquiv_mk,
    show AdicCompletion.transitionMap (chartSectionIdeal B S hS F hF 𝓘 V) (Z.val.obj (op V))
      (Nat.le_succ k) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z from rfl,
    smallEtaleAdicQuotientChartSectionsEquiv_mk]
  exact congrArg
    (fun φ : Z ⟶ smallEtaleAdicQuotient B S hS F hF 𝓘 k Z => φ.val.app (op V) z)
    (smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓘 k Z)

end AlgebraicGeometry.Space

end
