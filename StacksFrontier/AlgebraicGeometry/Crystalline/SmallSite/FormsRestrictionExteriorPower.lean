module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsLocallyQuasicoherent

/-!
# [Stacks, Tag 07IZ] in every degree: `(Ω^i_{X/S})_T = ⋀^i Ω_{T/S,δ}`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and an object
`(U, T, δ)` of the big crystalline category `CRIS(X/S)`, i.e. a
`Crystalline.GlobalCrystallineSituation.Thickening`.  [Stacks, Tag 07IZ] identifies the restriction
of the crystalline differentials `Ω_{X/S}` to the ambient divided power scheme `T` with the sheaf
`Ω_{T/S,δ}` of divided power differentials of [Stacks, Tag 07IW]; the library has that in degree
one, as `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIso`.

This module records the same identification in every degree: the restriction of
`Ω^i_{X/S} = ⋀^i Ω_{X/S}` to `T` is the `i`-th exterior power of `Ω_{T/S,δ}` as an `𝒪_T`-module,
```
(Ω^i_{X/S})_T  ≅  ⋀^i Ω_{T/S,δ}.
```

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `restrictedCrysDifferentialFormsSheafExteriorPowerIso`: **the identification**: for every object
  `A = (U, T, δ)` of `CRIS(X/S)` and every `i : ℕ`, the `𝒪_T`-module `(Ω^i_{X/S})_T` is the `i`-th
  exterior power of the sheaf `Ω_{T/S,δ}` of divided power differentials.
* `crysDifferentialFormsRestrictionSheafExteriorPowerIso`: the same isomorphism read over the
  restriction of `𝒪_{X/S}` to the opens of `T` instead of over `𝒪_T`.
* `restrictedCrysDifferentialsSheafExteriorPowerIso`: the `i`-th exterior power of the degree-one
  identification of [Stacks, Tag 07IZ].
* `restrictedCrysDifferentialFormsSheafIso`: the sheafification of
  `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsIso`.

## Main results

* `restrictedCrysDifferentialFormsSheafExteriorPowerIso_hom` and
  `restrictedCrysDifferentialFormsSheafExteriorPowerIso_inv`: the two directions of the
  identification are the stated composites, with the exterior power written out as
  `AlgebraicGeometry.Scheme.Modules.exteriorPowerMap` applied to the degree-one isomorphism.

## References

* [Stacks Project, Tag 07IW](https://stacks.math.columbia.edu/tag/07IW)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- **The `i`-th exterior power of the degree-one identification of [Stacks, Tag 07IZ].**  The
`𝒪_T`-module `⋀^i (Ω_{X/S})_T` is the `i`-th exterior power of the sheaf `Ω_{T/S,δ}` of divided
power differentials of the ambient divided power scheme of the object `A = (U, T, δ)`, the
isomorphism being the image of
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIso` under the degree-`i`
exterior power functor `AlgebraicGeometry.Scheme.Modules.exteriorPowerFunctor`. -/
def restrictedCrysDifferentialsSheafExteriorPowerIso (A : Thickening S) (i : ℕ) :
    Scheme.Modules.exteriorPower (restrictedCrysDifferentialsSheaf S A) (i : ℤ) ≅
      Scheme.Modules.exteriorPower
        (dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom) (i : ℤ) :=
  (Scheme.Modules.exteriorPowerFunctor A.thickening.target.scheme (i : ℤ)).mapIso
    (restrictedCrysDifferentialsSheafIso S A).symm

/-- **The sheafification of the degree-`i` identification of the restriction with the sectionwise
exterior power**: the image of
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsIso`, an isomorphism of
presheaves of `𝒪_T`-modules, under sheafification. -/
def restrictedCrysDifferentialFormsSheafIso (A : Thickening S) (i : ℕ) :
    restrictedCrysDifferentialFormsSheaf S A i ≅ restrictedCrysFormsSheaf S A i :=
  (PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).mapIso
    (restrictedCrysDifferentialFormsIso S A i)

/-- **[Stacks, Tag 07IZ] in every degree.**  For an object `A = (U, T, δ)` of `CRIS(X/S)` and every
`i : ℕ`, the restriction `(Ω^i_{X/S})_T` of the degree-`i` crystalline differential forms to the
ambient divided power scheme `T` is the `i`-th exterior power, as an `𝒪_T`-module, of the sheaf
`Ω_{T/S,δ}` of divided power differentials of [Stacks, Tag 07IW]:
```
(Ω^i_{X/S})_T  ≅  ⋀^i Ω_{T/S,δ}.
```
The isomorphism is the composite of the sheafification of
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsIso`, of
`Crystalline.GlobalCrystallineSituation.restrictedCrysFormsSheafIso`, and of the `i`-th exterior
power of the degree-one identification
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIso` of
[Stacks, Tag 07IZ]. -/
def restrictedCrysDifferentialFormsSheafExteriorPowerIso (A : Thickening S) (i : ℕ) :
    restrictedCrysDifferentialFormsSheaf S A i ≅
      Scheme.Modules.exteriorPower
        (dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom) (i : ℤ) :=
  restrictedCrysDifferentialFormsSheafIso S A i ≪≫
    restrictedCrysFormsSheafIso S A i ≪≫
      restrictedCrysDifferentialsSheafExteriorPowerIso S A i

/-- The forward direction of `restrictedCrysDifferentialFormsSheafExteriorPowerIso` is the
composite of the three forward directions. -/
@[simp] theorem restrictedCrysDifferentialFormsSheafExteriorPowerIso_hom (A : Thickening S)
    (i : ℕ) :
    (restrictedCrysDifferentialFormsSheafExteriorPowerIso S A i).hom =
      (restrictedCrysDifferentialFormsSheafIso S A i).hom ≫
        (restrictedCrysFormsSheafIso S A i).hom ≫
          Scheme.Modules.exteriorPowerMap (restrictedCrysDifferentialsSheafIso S A).inv (i : ℤ) :=
  rfl

/-- The inverse direction of `restrictedCrysDifferentialFormsSheafExteriorPowerIso` is the
composite of the three inverses, in the opposite order. -/
@[simp] theorem restrictedCrysDifferentialFormsSheafExteriorPowerIso_inv (A : Thickening S)
    (i : ℕ) :
    (restrictedCrysDifferentialFormsSheafExteriorPowerIso S A i).inv =
      (restrictedCrysDifferentialsSheafExteriorPowerIso S A i).inv ≫
        (restrictedCrysFormsSheafIso S A i).inv ≫
          (restrictedCrysDifferentialFormsSheafIso S A i).inv :=
  rfl

/-- **The identification `(Ω^i_{X/S})_T ≅ ⋀^i Ω_{T/S,δ}`, read over the restriction of
`𝒪_{X/S}`.**  The same isomorphism as
`restrictedCrysDifferentialFormsSheafExteriorPowerIso`, with the scalars of both sides read in the
restriction of the structure sheaf of `CRIS(X/S)` to the opens of `T` rather than in `𝒪_T`: its
image under restriction of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`. -/
def crysDifferentialFormsRestrictionSheafExteriorPowerIso (A : Thickening S) (i : ℕ) :
    crysDifferentialFormsRestrictionSheaf S A i ≅
      (SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso A).hom).obj
        (Scheme.Modules.exteriorPower
          (dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom) (i : ℤ)) :=
  (SheafOfModules.restrictScalars
      (Thickening.ringRestrictionSheafStructureIso A).hom).mapIso
    (restrictedCrysDifferentialFormsSheafExteriorPowerIso S A i)

end Crystalline.GlobalCrystallineSituation

end
