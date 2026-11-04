module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointHomologyReading

/-!
# Vanishing of cohomology sheaves on a represented algebraic space, read on the Zariski site

Let `U` be an object of the big fppf site over `S` with underlying scheme `X_0`, and let
`E ∈ D_QCoh(𝒪_{h_U})`. If the restriction to the Zariski site of `X_0` of the cohomology sheaf
`H^n(E)` vanishes, then `H^n(E)` vanishes. By Stacks 071Q, `E = Φ(E_0)` for an object
`E_0 ∈ D_QCoh(𝒪_{X_0})`; the restriction of `H^n(Φ(E_0))` is `H^n(E_0)`
(`AlgebraicGeometry.Space.representedEquivalenceHomologyRestrictIso`), and
`H^n(Φ(E_0)) = ε^* H^n(E_0)`.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_of_isZero_restrictToChartScheme_homology`.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

-- The same choice of models as
-- `AlgebraicGeometry.Space.representedEquivalenceHomologyRestrictIso`: the locally small model
-- where a global instance exists (modules on the Zariski site), the standard model on small étale
-- sites, where none applies.
attribute [local instance low] HasDerivedCategory.standard

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **`H^n(Φ E_0) = ε^* H^n(E_0)`** for `E_0 ∈ D_QCoh(𝒪_{X_0})`, `Φ` the equivalence of
Stacks 071Q. -/
def representedEquivalenceHomologyIso
    (E : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS U).functor.obj E).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).obj E.obj) :=
  let e := Stacks.Injectives.grothendieckModelEquiv.{u}
    (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules
  let E' := e.inverse.obj E.obj
  let h₁ := (representedZariskiDerivedPullbackHomologyIso B S hS U n).app E'
  let h₂ : (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).obj E' ≅
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).obj E.obj :=
    ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso _ n).app E').symm ≪≫
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).mapIso
        (e.counitIso.app E.obj)
  h₁ ≪≫ (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).mapIso h₂

/-- **A cohomology sheaf of an object of `D_QCoh` of a represented algebraic space vanishes when
its restriction to the Zariski site does.** -/
theorem isZero_homology_of_isZero_restrictToChartScheme_homology
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (n : ℤ)
    (h : IsZero (restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      ((DerivedCategory.homologyFunctor _ n).obj E.obj) (idEtaleChart B S hS U))) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj E.obj) := by
  let Φ := representedDualityQuasicoherentDerivedEquivalence B S hS U
  let E₀ := Φ.inverse.obj E
  let cH := (DerivedCategory.homologyFunctor _ n).mapIso
    ((ObjectProperty.ι _).mapIso (Φ.counitIso.app E))
  have h₀ : IsZero ((DerivedCategory.homologyFunctor
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).obj E₀.obj) :=
    h.of_iso ((representedEquivalenceHomologyRestrictIso B S hS U E₀ n).symm ≪≫
      (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (idEtaleChart B S hS U)).mapIso cH)
  exact ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map_isZero
    h₀).of_iso
    (cH.symm ≪≫ representedEquivalenceHomologyIso B S hS U E₀ n)

end AlgebraicGeometry.Space

end
