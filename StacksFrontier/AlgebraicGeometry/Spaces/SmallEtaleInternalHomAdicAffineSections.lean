module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSubsheafAffineSections

/-!
# The sections of the adic quotients of the internal Hom over an affine chart

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and `M`, `N` coherent
`𝒪_F`-modules, and write `𝓗 = 𝓗om_{𝒪_F}(M, N)`.  Over an *affine* étale chart `V` the sections of
`𝓗 / 𝓘 ^ k 𝓗` are the ordinary quotient `𝓗(V) / 𝓘(V) ^ k 𝓗(V)`.

Here `𝓗` is quasi-coherent by Stacks 03M1(6), hence cartesian on affine charts by Stacks 03DX(2),
and its sections lie in the universe `u + 1`.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent` — the
  internal Hom of two coherent modules is cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_smallEtaleInternalHomAdicQuotient_π` — **the
  projection of `𝓗` onto `𝓗 / 𝓘 ^ k 𝓗` is surjective on the sections over an affine chart.**
* `AlgebraicGeometry.Space.ker_val_app_smallEtaleInternalHomAdicQuotient_π` — **its kernel there
  is `𝓘(V) ^ k · 𝓗(V)`.**

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M N : Modules.{u, u} B S hS F hF)

variable [HasCokernels (Modules.{u, u + 1} B S hS F hF)]

omit [HasCokernels (Modules.{u, u + 1} B S hS F hF)] in
/-- **The internal Hom of two coherent `𝒪_F`-modules is cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) :
    IsCartesianOnAffineCharts (smallEtaleInternalHom B S hS F hF M N) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse.{u, u + 1} B S hS F hF _
    (isQuasicoherentOnSite_smallEtaleInternalHom_of_isCoherent B S hS F hF M N hM hN)

/-- **The projection of `𝓗om_{𝒪_F}(M, N)` onto its quotient by `𝓘 ^ k` is surjective on the
sections over an affine étale chart**, for a quasi-coherent sheaf of ideals and coherent `M`,
`N`. -/
theorem surjective_val_app_smallEtaleInternalHomAdicQuotient_π
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    Function.Surjective
      ((cokernel.π (idealPowerSubsheaf B S hS F hF 𝓘 k
        (smallEtaleInternalHom B S hS F hF M N)).ι).val.app (op V)) :=
  surjective_val_app_smallEtaleAdicQuotient_π B S hS F hF 𝓘
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS F hF _ hI) _
    (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS F hF M N hM hN) k hV

/-- **The kernel of that projection on the sections over an affine étale chart is
`𝓘(V) ^ k · 𝓗om_{𝒪_F}(M, N)(V)`.** -/
theorem ker_val_app_smallEtaleInternalHomAdicQuotient_π
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) (k : ℕ)
    {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    LinearMap.ker
        ((cokernel.π (idealPowerSubsheaf B S hS F hF 𝓘 k
          (smallEtaleInternalHom B S hS F hF M N)).ι).val.app (op V)).hom =
      chartSectionIdeal B S hS F hF 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS F hF V)
          ((smallEtaleInternalHom B S hS F hF M N).val.obj (op V))) :=
  ker_val_app_smallEtaleAdicQuotient_π B S hS F hF 𝓘
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS F hF _ hI) _
    (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS F hF M N hM hN) k hV

end AlgebraicGeometry.Space

end
