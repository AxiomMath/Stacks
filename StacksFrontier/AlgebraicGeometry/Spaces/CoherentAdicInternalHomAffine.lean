module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomAffine

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.AdicSectionsAffineDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.SliceHomEvaluationAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.RingTheory.AdicCompletion.HomBijection.HomCompletionLevels
public import StacksCore.Tactic.StacksAttribute

/-!
# The adic sections of the internal hom of coherent modules on an algebraic space

Let `F` be a locally Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`M`, `N` coherent `𝒪_F`-modules, with `𝓗 = 𝓗om_{𝒪_F}(M, N)`.  Then

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallAdicEquiv`: the bijection of Stacks 08B6.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section Quotient

variable (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

end Quotient

/-! ### The bijection of Stacks 08B6 -/

section Affine

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (M N : Modules.{u, u} B S hS F hF) [hM : IsCoherent B S hS F hF M]
    [hN : IsCoherent B S hS F hF N]

include hI in
/-- **Stacks 08B6.**  Let `F` be a locally Noetherian algebraic space over a scheme `S`, let
`𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals and let `M`, `N` be coherent `𝒪_F`-modules.  Put
`𝓗 = 𝓗om_{𝒪_F}(M, N)`.  Then

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`,

the inverse limit of the global sections of the ideal-power quotients of `𝓗` being the
morphisms of inverse systems of `𝒪_F`-modules from the completion of `M` to the completion of
`N`; since `Coh(F, 𝓘)` is a full subcategory of the inverse systems of `𝒪_F`-modules, this is
`Mor_{Coh(F, 𝓘)}(M^∧, N^∧)`.  Here `𝓗` is the internal hom at the module universe of the
schemes, `AlgebraicGeometry.Space.smallEtaleInternalHomSmall`, whose universe lift is
`AlgebraicGeometry.Space.smallEtaleInternalHom`.  The source asks for `F` Noetherian; local
Noetherianity is all that is used. -/
@[stacks 08B6]
def smallEtaleInternalHomSmallAdicEquiv :
    adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) :=
  by apply C1573.smallEtaleInternalHomSmallAdicEquiv; assumption

end Affine

end AlgebraicGeometry.Space

end
