module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenCharacterisation

/-!
# The Hodge numbers of the fibres of a proper smooth morphism as derived-fibre Betti numbers

Let `h : Y ⟶ S` be proper and smooth. By [Stacks, Tag 0FM0] the object `Rh_*Ω^p_{Y/S}` of
`D(𝒪_S)` is perfect and its formation commutes with arbitrary base change. Hence for a field `K`,
a morphism `g : Spec K ⟶ S` and the base change `f : X ⟶ Spec K` of `h` along `g`, the
derived-fibre Betti number of `Rh_*Ω^p_{Y/S}` in degree `q` at the image of the point of
`Spec K` is the Hodge number `h^{p,q}(X/K) = dim_K H^q(X, Ω^p_{X/K})`.

## Main definitions

* `AlgebraicGeometry.HodgeSpreadingOut.hodgeDirectImage`: the object `Rh_*Ω^p_{Y/S}` of `D(𝒪_S)`.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.isPseudoCoherent_hodgeDirectImage`: it is pseudo-coherent.
* `AlgebraicGeometry.HodgeSpreadingOut.derivedFiberBetti_hodgeDirectImage`: its derived-fibre
  Betti numbers at the image of `Spec K ⟶ S` are the Hodge numbers of the base change to `K`.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

section

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y S : Scheme.{u}} (h : Y ⟶ S)

/-- **`Rh_*Ω^p_{Y/S}`**, the derived direct image of the sheaf of relative differential `p`-forms
placed in degree zero, as an object of `D(𝒪_S)`. -/
abbrev hodgeDirectImage (p : ℕ) : DerivedCategory S.Modules :=
  (derivedPushforward h.toLRSHom.toShHom).obj (ProperSmoothDeRham.formsObj h p)

/-- **`Rh_*Ω^p_{Y/S}` is pseudo-coherent** for `h` proper and smooth: it is perfect by
[Stacks, Tag 0FM0]. -/
theorem isPseudoCoherent_hodgeDirectImage [IsProper h] [Smooth h] (p : ℕ) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (hodgeDirectImage h p) :=
  Scheme.Modules.isPseudoCoherent_of_isPerfect _
    (ProperSmoothDeRham.isPerfect_derivedPushforward_forms h p)

/-- The object `Ω^p_{X/S}` placed in degree zero, read through the homotopy category, is the
image of `Ω^p_{X/S}` under the single functor of the derived category. -/
def formsObjIsoSingle {X T : Scheme.{u}} (f : X ⟶ T) (p : ℕ) :
    ProperSmoothDeRham.formsObj f p ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  (DerivedCategory.quotientCompQhIso _).app _

/-- **The derived-fibre Betti numbers of `Rh_*Ω^p_{Y/S}` are the Hodge numbers of the fibres.**
Let `h : Y ⟶ S` be proper and smooth and let `f : X ⟶ Spec K` be its base change along
`g : Spec K ⟶ S`, for a field `K`. Then the `q`-th derived-fibre Betti number of
`Rh_*Ω^p_{Y/S}` at the image of a point of `Spec K` is `dim_K H^q(X, Ω^p_{X/K})`.

The derived-fibre Betti function of `Lg^*Rh_*Ω^p_{Y/S}` is that of `Rh_*Ω^p_{Y/S}` composed with
`g` ([Stacks, Tag 0BDI] part (1)); base change ([Stacks, Tag 0FM0]) identifies
`Lg^*Rh_*Ω^p_{Y/S}` with `Rf_*Ω^p_{X/K}`; and over a field the derived-fibre Betti numbers of
`Rf_*Ω^p_{X/K}` are the dimensions of the cohomology groups of `Ω^p_{X/K}`. -/
theorem derivedFiberBetti_hodgeDirectImage [IsProper h] [Smooth h] (K : Type u) [Field K]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {g' : X ⟶ Y} {g : Spec (.of K) ⟶ S}
    (hsq : IsPullback g' f h g) (p q : ℕ) (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti S (hodgeDirectImage h p)
        (isPseudoCoherent_hodgeDirectImage h p) q (g.base pt) =
      Module.finrank K (cohomologyOverField K f (Scheme.Hom.relativeDifferentialForms f p) q) := by
  have : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance
  refine (congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback g
    (hodgeDirectImage h p) (isPseudoCoherent_hodgeDirectImage h p) q) pt).symm.trans ?_
  let e : (derivedPullback g.toLRSHom.toShHom).obj (hodgeDirectImage h p) ≅
      ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
    ProperSmoothDeRham.formsBaseChangeIso hsq p ≪≫
      (derivedPushforward f.toLRSHom.toShHom).mapIso (formsObjIsoSingle f p)
  have hE : RingedSpace.IsPseudoCoherent (X := (Spec (.of K)).toRingedSpace)
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) :=
    Scheme.Modules.isPseudoCoherent_of_isPerfect _
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        ((derivedPushforward f.toLRSHom.toShHom).mapIso (formsObjIsoSingle f p))
        (ProperSmoothDeRham.isPerfect_derivedPushforward_forms f p))
  exact (congrFun (FibreBetti.derivedFiberBetti_eq_of_iso _ _ hE e q) pt).trans
    (DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule K f _ hE q pt)

end

end AlgebraicGeometry.HodgeSpreadingOut
