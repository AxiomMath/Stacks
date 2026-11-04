module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffineIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectProperPushforward

/-!
# Base change for the right adjoint of `Rf_*` along a perfect proper morphism

Let `f : X ⟶ Y` be proper and perfect with `Y` affine and Noetherian, let `g : Y' ⟶ Y` be a
morphism with `Y'` affine and `X`, `Y'` Tor independent over `Y`. Then the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an isomorphism for every `K ∈ D_QCoh(𝒪_Y)`
(case (2) of Stacks 0E5I): `Rf_*` preserves perfect objects by Stacks 0E4U.

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect`:
  **Stacks 0E5I (2).**

## References

* [Stacks Project, Tag 0E5I](https://stacks.math.columbia.edu/tag/0E5I)
* [Stacks Project, Tag 0E4U](https://stacks.math.columbia.edu/tag/0E4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0E5I (2).** For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `Y`, `Y'` affine, `Y` Noetherian, `f` proper and perfect, and `X`, `Y'` Tor independent over
`Y`, the base change map `L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an isomorphism for every
`K ∈ D_QCoh(𝒪_Y)`. -/
@[stacks 0E5I "(2)"]
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hf : IsProper B S hS f.hom) (hfp : IsPerfect B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) (hYN : IsNoetherian B S hS hZ Y.1)
    (hY' : IsAffineSpace B S hS Y'.1) (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hf.2.1.2 hY)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f
        (isQuasiSeparated_of_isSeparated B S hS hf.1) hY)
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY'.isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY') hTor).app K) :=
  isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect_pushforward hZ sq _ _ hY hY'
    hTor (fun E hE => by
      have h := isPerfect_derivedModulePushforward_of_isProper B S hS hZ f hYN hfp hf E.obj hE
      rwa [totalRightDerived_modulePushforward_eq] at h) K

end AlgebraicGeometry.Space

end
