module

public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomologyDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenCharacterisation

/-!
# The de Rham numbers of the fibres of a proper smooth morphism as derived-fibre Betti numbers

Let `h : Y ⟶ S` be proper and smooth. By [Stacks, Tag 0FM0] the object `Rh_*Ω^•_{Y/S}` of
`D(𝒪_S)` — the derived direct image of the relative de Rham complex along
`(Y, h^{-1}𝒪_S) ⟶ S` — is perfect and its formation commutes with arbitrary base change. Hence
for a field `K`, a morphism `g : Spec K ⟶ S` and the base change `f : X ⟶ Spec K` of `h` along
`g`, the derived-fibre Betti number of `Rh_*Ω^•_{Y/S}` in degree `n` at the image of the point of
`Spec K` is `dim_K H^n_{dR}(X/K)`, the de Rham cohomology being the library's
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyBaseModule` read as a `K`-module.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.isPseudoCoherent_derivedDeRhamDirectImageUnbounded`:
  `Rh_*Ω^•_{Y/S}` is pseudo-coherent.
* `AlgebraicGeometry.HodgeSpreadingOut.finrank_deRhamCohomology_eq_finrank_sections`: over a
  field, `dim_K H^n_{dR}(X/K)` is the dimension of the global sections of the `n`-th cohomology
  sheaf of `Rf_*Ω^•_{X/K}`.
* `AlgebraicGeometry.HodgeSpreadingOut.derivedFiberBetti_deRhamDirectImage`: the derived-fibre
  Betti numbers of `Rh_*Ω^•_{Y/S}` at the image of `Spec K ⟶ S` are the de Rham numbers of the
  base change to `K`.

## Implementation notes

Over the spectrum of a field the comparison runs through [Stacks, Tag 0D5W] for the de Rham
complex (`AlgebraicGeometry.DeRhamCohomologyDirectImage.deRhamCohomologyModuleIso`), which reads
`H^n_{dR}(X/K)` as `H^n(RΓ(Spec K, Rf_*Ω^•_{X/K}))`, and the computation of the cohomology of
derived global sections on an affine scheme
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`), which reads that as the
global sections of the `n`-th cohomology sheaf.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, pinned at
priority `10000`: every consumed declaration (the base change and perfectness of
[Stacks, Tag 0FM0], the derived-fibre Betti functions) is baked at that model, and the
locally small model of `StacksFrontier.Homology.DerivedCategory.LocallySmall` is a global instance
for `X.Modules` which instance search tries first at plain priority.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange Stacks.Cohomology.DerivedBaseChange

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

section

attribute [local instance 10000] HasDerivedCategory.standard

open DeRhamCohomologyDirectImage

/-- **`Rh_*Ω^•_{Y/S}` is pseudo-coherent** for `h` proper and smooth: it is perfect by
[Stacks, Tag 0FM0]. -/
theorem isPseudoCoherent_derivedDeRhamDirectImageUnbounded {Y S : Scheme.{u}} (h : Y ⟶ S)
    [IsProper h] [Smooth h] :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (derivedDeRhamDirectImageUnbounded h) :=
  Scheme.Modules.isPseudoCoherent_of_isPerfect _
    (ProperSmoothDeRham.isPerfect_derivedPushforward_deRhamComplex h)

/-- The two global sections functors on `𝒪_{Spec K}`-modules, `moduleSpecΓFunctor` and
`globalSectionsOver (𝟙 (Spec K))`, give modules of the same dimension. -/
theorem finrank_moduleSpecΓFunctor_eq_globalSectionsOver (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules) :
    Module.finrank K (moduleSpecΓFunctor.obj M) =
      Module.finrank K ((globalSectionsOver (𝟙 (Spec (.of K)))).obj M) := by
  rfl

/-- **Over a field, the de Rham numbers are the dimensions of the global sections of the
cohomology sheaves of `Rf_*Ω^•_{X/K}`.** For `f : X ⟶ Spec K` quasi-compact and quasi-separated,
`dim_K H^n_{dR}(X/K)` is the dimension of the global sections of the `n`-th cohomology sheaf of
`Rf_*Ω^•_{X/K}`, by [Stacks, Tag 0D5W] and the vanishing of the higher cohomology of
quasi-coherent modules on `Spec K`. -/
theorem finrank_deRhamCohomology_eq_finrank_sections (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [QuasiCompact f] [QuasiSeparated f] (n : ℤ) :
    Module.finrank K ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f n)) =
      Module.finrank K (moduleSpecΓFunctor.obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj
          (derivedDeRhamDirectImageUnbounded f))) := by
  rw [finrank_moduleSpecΓFunctor_eq_globalSectionsOver]
  exact (deRhamCohomologyModuleIso f n ≪≫
    (derivedGlobalSectionsQuasicoherentCompHomologyIso (.of K) n).app (deRhamDirectImageQCoh f) ≪≫
    (globalSectionsOver (𝟙 (Spec (.of K)))).mapIso
      ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).mapIso
        (derivedDeRhamDirectImageUnboundedIso f))).toLinearEquiv.finrank_eq

/-- **The derived-fibre Betti numbers of `Rh_*Ω^•_{Y/S}` are the de Rham numbers of the
fibres.** Let `h : Y ⟶ S` be proper and smooth and let `f : X ⟶ Spec K` be its base change along
`g : Spec K ⟶ S`, for a field `K`. Then the `n`-th derived-fibre Betti number of
`Rh_*Ω^•_{Y/S}` at the image of a point of `Spec K` is `dim_K H^n_{dR}(X/K)`.

The derived-fibre Betti function of `Lg^*Rh_*Ω^•_{Y/S}` is that of `Rh_*Ω^•_{Y/S}` composed with
`g` ([Stacks, Tag 0BDI] part (1)); base change ([Stacks, Tag 0FM0]) identifies
`Lg^*Rh_*Ω^•_{Y/S}` with `Rf_*Ω^•_{X/K}`; and over a field the derived-fibre Betti numbers of
`Rf_*Ω^•_{X/K}` are the dimensions of de Rham cohomology. -/
theorem derivedFiberBetti_deRhamDirectImage {Y S : Scheme.{u}} (h : Y ⟶ S) [IsProper h]
    [Smooth h] (K : Type u) [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {g' : X ⟶ Y}
    {g : Spec (.of K) ⟶ S} (hsq : IsPullback g' f h g) (n : ℤ) (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti S (derivedDeRhamDirectImageUnbounded h)
        (isPseudoCoherent_derivedDeRhamDirectImageUnbounded h) n (g.base pt) =
      Module.finrank K ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of K)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f n)) := by
  have : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance
  have hbc := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback g
    (derivedDeRhamDirectImageUnbounded h)
    (isPseudoCoherent_derivedDeRhamDirectImageUnbounded h) n) pt
  rw [Function.comp_apply] at hbc
  rw [← hbc]
  have := ProperSmoothDeRham.isIso_derivedBaseChangeMap_deRhamComplex hsq
  let e : (derivedPullback g.toLRSHom.toShHom).obj (derivedDeRhamDirectImageUnbounded h) ≅
      derivedDeRhamDirectImageUnbounded f :=
    (derivedPullback g.toLRSHom.toShHom).mapIso
        ((derivedPushforward (inverseImageBaseProjection h)).mapIso
          ((DerivedCategory.quotientCompQhIso _).app
            (ProperSmoothDeRham.deRhamComplexInt h)).symm) ≪≫
      asIso (derivedBaseChangeMap (inverseImageBaseMap g' f h g hsq.w)
          (inverseImageBaseProjection f) (inverseImageBaseProjection h) g.toLRSHom.toShHom
          (inverseImageBaseMap_comp_inverseImageBaseProjection g' f h g hsq.w)
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (ProperSmoothDeRham.deRhamComplexInt h))) ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
          (ProperSmoothDeRham.deRhamBaseChangeComparison g' f h g hsq.w)) ≪≫
      (derivedPushforward (inverseImageBaseProjection f)).mapIso
        ((DerivedCategory.quotientCompQhIso _).app (ProperSmoothDeRham.deRhamComplexInt f))
  have hE := isPseudoCoherent_derivedDeRhamDirectImageUnbounded f
  exact (congrFun (FibreBetti.derivedFiberBetti_eq_of_iso _ _ hE e n) pt).trans
    ((DerivedFibreOverField.derivedFiberBetti_specField K _ hE n pt).trans
      (finrank_deRhamCohomology_eq_finrank_sections K f n).symm)

end

end AlgebraicGeometry.HodgeSpreadingOut
