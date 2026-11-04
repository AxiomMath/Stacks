module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChangeCartesian

/-!
# The base change of `Rf_*ℱ` for `f` proper and `ℱ` flat over the base, unconditionally

For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `f` proper of finite presentation, and an `𝒪_X`-module `ℱ` of finite presentation and flat
over `S`, the base-change half of [Stacks, Tag 0B91] gives `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`.  This is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.BaseChangeDerivedPushforward`, proved here
with nothing granted.

The proof does not pass through the tensor form at all: the stalk check of the proof of
[Stacks, Tag 0A1D] gives the pointwise condition of [Stacks, Tag 0DJ8] for the comparison
`L(g')^*ℱ ⟶ (g')^*ℱ`, and [Stacks, Tag 0DJ9] turns it into the invertibility of
`Lg^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ`.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isIso_derivedBaseChangeComp_singleDegree`:
  the comparison `Lg^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ` is an isomorphism, for `f` quasi-compact and
  quasi-separated and `ℱ` flat over `S` with `ℱ` and `(g')^*ℱ` quasi-coherent.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward`:
  `BaseChangeDerivedPushforward`.
* `AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_module_of_isPullback`:
  the tensor form of clause (2) of [Stacks, Tag 0B91] with none of the three steps of the source
  proof of [Stacks, Tag 0A1D] granted.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.ProperFlatBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **The comparison `Lg^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ` is an isomorphism** for a cartesian square with
`f` quasi-compact and quasi-separated and an `𝒪_X`-module `ℱ` flat over `S` such that `ℱ` and
`(g')^*ℱ` are quasi-coherent: the composition of the derived base-change map of Stacks 08HY with
`Rf'_*` of `L(g')^*ℱ ⟶ (g')^*ℱ`, at `ℱ` placed in degree zero. -/
theorem isIso_derivedBaseChangeComp_singleDegree {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) (hFq : F.IsQuasicoherent)
    (hF'q : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent)
    (hFflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (derivedBaseChangeComp f g f' g' hsq.w (DerivedCategory.Q.obj (singleDegreeComplex F))
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))) :=
  isIso_derivedBaseChangeComp_of_pointwiseBaseChange hsq _ _ _
    (isQuasicoherent_homology_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm
      (isQuasicoherent_homology_singleFunctor F hFq))
    (isQuasicoherent_homology_of_iso (pullbackComplexSingleIso g' F)
      (isQuasicoherent_homology_singleFunctor _ hF'q))
    (fun x' n => isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver hsq hsq.w
      (singleDegreeComplex F) ⟨0, inferInstance⟩ (isFlatOver_singleDegreeComplex f F hFflat) x' n)

/-- **`Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`** for a cartesian square with `f` quasi-compact and
quasi-separated and an `𝒪_X`-module `ℱ` flat over `S` such that `ℱ` and `(g')^*ℱ` are
quasi-coherent. -/
theorem nonempty_derivedPullback_derivedPushforwardModule_iso {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) (hFq : F.IsQuasicoherent)
    (hF'q : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent)
    (hFflat : IsFlatOver f.toLRSHom.toShHom F) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj (derivedPushforwardModule f F) ≅
      derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F)) :=
  nonempty_derivedPullback_derivedPushforward_singleFunctor_iso hsq F hFq hF'q hFflat

/-- **The base-change half of [Stacks, Tag 0B91], clause (2), in untensored form, holds**: for
every cartesian square with `f` proper of finite presentation and every `𝒪_X`-module `ℱ` of
finite presentation, flat over `S`, `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`. -/
theorem baseChangeDerivedPushforward : BaseChangeDerivedPushforward.{u} := by
  intro X S X' S' f g f' g' hsq hf hproper F hFfp hFflat
  have := hFfp
  exact nonempty_derivedPullback_derivedPushforwardModule_iso hsq F
    (isQuasicoherent_of_isFinitePresentation F)
    (isQuasicoherent_of_isFinitePresentation _) hFflat

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

namespace AlgebraicGeometry.ProperFlatBaseChange

/-- **[Stacks, Tag 0B91], clause (2), the base-change half, in tensor form**, with none of the
three steps of the source proof of [Stacks, Tag 0A1D] granted.  For a cartesian square with `f`
proper of finite presentation and an `𝒪_X`-module `𝒢` of finite presentation, flat over `S`, the
canonical map `Lg^*Rf_*(E ⊗^L 𝒢) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢)` of
`AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism, granted that the two derived
tensor products have quasi-coherent cohomology (`hK`, `hK'`). -/
theorem isIso_tensorFlatBaseChangeMap_module_of_isPullback {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f) (G : X.Modules)
    (hGflat : IsFlatOver f.toLRSHom.toShHom G) (E : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj (singleDegreeComplex G)))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj
            (singleDegreeComplex G))))).IsQuasicoherent) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E (singleDegreeComplex G)) :=
  isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent f g f' g' hsq hf.quasiCompact
    hf.quasiSeparated sq E (singleDegreeComplex G) ⟨0, inferInstance⟩
    (isFlatOver_singleDegreeComplex f G hGflat) hK hK'

end AlgebraicGeometry.ProperFlatBaseChange

end
