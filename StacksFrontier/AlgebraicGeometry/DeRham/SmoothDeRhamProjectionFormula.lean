module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsFlat
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula at the relative de Rham complex

Let `f : X ⟶ S` be a quasi-compact, quasi-separated and smooth morphism of schemes. The relative
de Rham complex `Ω^•_{X/S}` satisfies every hypothesis that [Stacks, Tag 0FML] places on its
complex `𝓕^•`, so conclusions (4) and (5) of that tag hold at it.

## Main definitions

* `Stacks.DeRhamDirectImage.deRhamCochainComplexQcohTerm`: the quasi-coherent `𝒪_X`-module whose
  restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` is the degree-`i` term of the `ℤ`-indexed
  relative de Rham complex — the sheaf `Ω^i_{X/S}` of relative `i`-forms in nonnegative degrees,
  the zero sheaf in negative degrees.

## Main results

* `Stacks.DeRhamDirectImage.deRhamCochainComplexXIsoQcohTerm`: that identification, the
  hypothesis `hFM` of [Stacks, Tag 0FML] at `Ω^•_{X/S}`.
* `Stacks.DeRhamDirectImage.isIso_projectionFormulaMap_deRhamCochainComplex` and
  `Stacks.DeRhamDirectImage.deRhamProjectionFormulaIso`: **conclusion (5) at the relative de Rham
  complex**, `Rf_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} K ≅ Rf_*(Ω^•_{X/S} ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)` for `K` in
  `D_QCoh(𝒪_S)`, in its invertibility and its isomorphism form.
* `Stacks.DeRhamDirectImage.isIso_projectionFormulaMap_deRhamCochainComplex_single`: conclusion
  (5) at a quasi-coherent `𝒪_S`-module placed in a degree and shifted arbitrarily.
* `Stacks.DeRhamDirectImage.deRhamOrdinaryProjectionFormulaIso`: **conclusion (4) at the relative
  de Rham complex**, `Rf_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} G ≅ Rf_*(Ω^•_{X/S} ⊗_{f^{-1}𝒪_S} f^{-1}G)` for a
  quasi-coherent `𝒪_S`-module `G`, with the *ordinary* tensor product on the right.
* `Stacks.DeRhamDirectImage.isIso_projectionFormulaMap_deRhamCochainComplex_relativeForms` and
  `Stacks.DeRhamDirectImage.deRhamRelativeFormsProjectionFormulaIso`: conclusion (5) at
  `K = Ω^p_{Y/S}⟦n⟧`, for `f : X ⟶ Y`, `g : Y ⟶ S` and any shift `n`, in its invertibility and
  its isomorphism form.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.RelativeComplexPushforward
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite
open scoped ZeroObject

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.DeRhamDirectImage

attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The terms of the de Rham complex as restrictions of scalars of quasi-coherent modules -/

/-- The quasi-coherent `𝒪_X`-module whose restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` is the
degree-`i` term of the `ℤ`-indexed relative de Rham complex: the sheaf `Ω^i_{X/S}` of relative
`i`-forms in nonnegative degrees, and the zero sheaf in negative degrees, where the `ℤ`-indexed
complex is the extension by zero of the `ℕ`-indexed one. -/
def deRhamCochainComplexQcohTerm (i : ℤ) : X.Modules :=
  if 0 ≤ i then Scheme.Hom.relativeDifferentialForms f (i.toNat : ℤ) else 0

/-- In a nonnegative degree the module of `deRhamCochainComplexQcohTerm` is the sheaf of relative
differential forms of that degree. -/
theorem deRhamCochainComplexQcohTerm_of_nonneg {i : ℤ} (hi : 0 ≤ i) :
    deRhamCochainComplexQcohTerm f i = Scheme.Hom.relativeDifferentialForms f (i.toNat : ℤ) :=
  if_pos hi

/-- In a negative degree the module of `deRhamCochainComplexQcohTerm` is the zero sheaf. -/
theorem deRhamCochainComplexQcohTerm_of_neg {i : ℤ} (hi : i < 0) :
    deRhamCochainComplexQcohTerm f i = 0 :=
  if_neg (not_le.2 hi)

/-- Every term of `deRhamCochainComplexQcohTerm` is quasi-coherent. -/
theorem isQuasicoherent_deRhamCochainComplexQcohTerm (i : ℤ) :
    (deRhamCochainComplexQcohTerm f i).IsQuasicoherent := by
  rcases lt_or_ge i 0 with hneg | hpos
  · rw [deRhamCochainComplexQcohTerm_of_neg f hneg]
    have : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).IsWeakSerreClass :=
      Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass X
    exact (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero (isZero_zero _)
  · rw [deRhamCochainComplexQcohTerm_of_nonneg f hpos]
    exact Scheme.Hom.isQuasicoherent_relativeDifferentialForms f i.toNat

/-- **The degree-`i` term of the `ℤ`-indexed relative de Rham complex is the restriction of
scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` of a quasi-coherent `𝒪_X`-module.** This is the hypothesis `hFM`
of conclusions (4) and (5) of [Stacks, Tag 0FML] at the complex `Ω^•_{X/S}`: the compatibility
the tag asks of the `f^{-1}𝒪_S`-module structure, in which the complex lives and for whose
differentials it is linear, with a quasi-coherent `𝒪_X`-module structure on the terms, for which
they are not.

In a nonnegative degree it is `HomologicalComplex.extendXIso` followed by the identification
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`; in a negative degree both sides are zero. -/
def deRhamCochainComplexXIsoQcohTerm (i : ℤ) :
    (deRhamCochainComplex f).X i ≅
      (pushforward (toInverseImageBase f)).obj (deRhamCochainComplexQcohTerm f i) :=
  if hi : 0 ≤ i then
    HomologicalComplex.extendXIso
          (show CochainComplex (Modules (inverseImageBase f)) ℕ from Scheme.Hom.deRhamComplex f)
          ComplexShape.embeddingUpNat (i := i.toNat) (Int.toNat_of_nonneg hi) ≪≫
      eqToIso (by
        rw [deRhamCochainComplexQcohTerm_of_nonneg f hi]
        exact Scheme.Hom.deRhamComplex_X f i.toNat)
  else
    IsZero.iso
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
        (fun n => by simpa using ((not_le.1 hi).trans_le (Int.ofNat_zero_le n)).ne'))
      (by
        rw [deRhamCochainComplexQcohTerm_of_neg f (not_le.1 hi)]
        exact (pushforward (toInverseImageBase f)).map_isZero (isZero_zero _))

/-! ### Conclusion (5) at the relative de Rham complex -/

/-- **[Stacks, Tag 0FML] conclusion (5) at the relative de Rham complex.** For `f : X ⟶ S`
quasi-compact, quasi-separated and smooth and `K` an object of `D_QCoh(𝒪_S)`, the
projection-formula morphism of [Stacks, Tag 0B53] at the morphism of ringed spaces
`(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)`,

`Rf_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} K ⟶ Rf_*(Ω^•_{X/S} ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`,

is invertible. -/
theorem isIso_projectionFormulaMap_deRhamCochainComplex [QuasiCompact f] [QuasiSeparated f]
    [Smooth f] (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (deRhamCochainComplex f)) K) :=
  isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded_of_isQuasicoherent f K hK
    (deRhamCochainComplex f) (isLocallyBounded_deRhamCochainComplex f)
    (deRhamCochainComplexQcohTerm f) (isQuasicoherent_deRhamCochainComplexQcohTerm f)
    (deRhamCochainComplexXIsoQcohTerm f)

/-- **[Stacks, Tag 0FML] conclusion (5) at the relative de Rham complex**, read as an
isomorphism,

`Rf_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} K ≅ Rf_*(Ω^•_{X/S} ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`

for `K` in `D_QCoh(𝒪_S)`, the two tensor products being written in the order the morphism of
[Stacks, Tag 0B53] produces them, which is the opposite of the source's. -/
def deRhamProjectionFormulaIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex f)))).obj K ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex f))).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj K)) :=
  relativeComplexProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent f K hK
    (deRhamCochainComplex f) (isLocallyBounded_deRhamCochainComplex f)
    (deRhamCochainComplexQcohTerm f) (isQuasicoherent_deRhamCochainComplexQcohTerm f)
    (deRhamCochainComplexXIsoQcohTerm f)

/-- **[Stacks, Tag 0FML] conclusion (5) at the relative de Rham complex and at a single
quasi-coherent sheaf placed in a degree and shifted.** For `N` a quasi-coherent `𝒪_S`-module the
projection-formula morphism at `K = N[i]⟦n⟧` is invertible. -/
theorem isIso_projectionFormulaMap_deRhamCochainComplex_single [QuasiCompact f]
    [QuasiSeparated f] [Smooth f] (N : S.Modules) (hN : N.IsQuasicoherent) (i n : ℤ) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (deRhamCochainComplex f))
      (((DerivedCategory.singleFunctor (Modules S.toRingedSpace) i).obj N)⟦n⟧)) :=
  isIso_projectionFormulaMap_deRhamCochainComplex f _
    (derivedCategoryB_isQuasicoherent_single_shift (Y := S) N hN i n)

/-! ### Conclusion (4) at the relative de Rham complex -/

/-- **[Stacks, Tag 0FML] conclusion (4) at the relative de Rham complex.** For `f : X ⟶ S`
quasi-compact, quasi-separated and smooth and `G` a quasi-coherent `𝒪_S`-module,

`Rf_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} G ≅ Rf_*(Ω^•_{X/S} ⊗_{f^{-1}𝒪_S} f^{-1}G)`,

the tensor product on the right being the *ordinary* one. -/
def deRhamOrdinaryProjectionFormulaIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (G : Modules S.toRingedSpace) (hG : G.IsQuasicoherent) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex f)))).obj
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
              (deRhamCochainComplex f)).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent f G hG
    (deRhamCochainComplex f) (isLocallyBounded_deRhamCochainComplex f)
    (isFlat_deRhamCochainComplex_X f)
    (deRhamCochainComplexQcohTerm f) (isQuasicoherent_deRhamCochainComplexQcohTerm f)
    (deRhamCochainComplexXIsoQcohTerm f)

/-! ### The instantiation the spectral sequence of Tag 0FMM takes -/

section SpectralSequence

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **[Stacks, Tag 0FML] conclusion (5) at the relative de Rham complex of `f : X ⟶ Y` and at
`K = Ω^p_{Y/S}⟦n⟧`.** For `f` quasi-compact, quasi-separated and smooth, `g : Y ⟶ S` and any
shift `n` (the case `n = -p` being the one of [Stacks, Tag 0FMM]), the projection-formula
morphism at `K = Ω^p_{Y/S}⟦n⟧` is invertible. -/
theorem isIso_projectionFormulaMap_deRhamCochainComplex_relativeForms [QuasiCompact f]
    [QuasiSeparated f] [Smooth f] (p : ℕ) (n : ℤ) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (deRhamCochainComplex f))
      (((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj
        (Scheme.Hom.relativeDifferentialForms g (p : ℤ)))⟦n⟧)) :=
  isIso_projectionFormulaMap_deRhamCochainComplex_single f _
    (Scheme.Hom.isQuasicoherent_relativeDifferentialForms g p) 0 n

/-- **[Stacks, Tag 0FML] conclusion (5) at the relative de Rham complex of `f : X ⟶ Y` and at
`K = Ω^p_{Y/S}⟦n⟧`**, read as an isomorphism,

`Rf_*Ω^•_{X/Y} ⊗^𝐋_{𝒪_Y} Ω^p_{Y/S}⟦n⟧ ≅ Rf_*(Ω^•_{X/Y} ⊗^𝐋_{f^{-1}𝒪_Y} f^{-1}Ω^p_{Y/S}⟦n⟧)`,

the two tensor products being written in the order the morphism of [Stacks, Tag 0B53] produces
them. -/
def deRhamRelativeFormsProjectionFormulaIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (p : ℕ) (n : ℤ) :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj (deRhamCochainComplex f)))).obj
      (((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj
        (Scheme.Hom.relativeDifferentialForms g (p : ℤ)))⟦n⟧) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj (deRhamCochainComplex f))).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj
            (((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj
              (Scheme.Hom.relativeDifferentialForms g (p : ℤ)))⟦n⟧))) :=
  deRhamProjectionFormulaIso f _
    (derivedCategoryB_isQuasicoherent_single_shift (Y := Y)
      (Scheme.Hom.relativeDifferentialForms g (p : ℤ))
      (Scheme.Hom.isQuasicoherent_relativeDifferentialForms g p) 0 n)

end SpectralSequence

end Stacks.DeRhamDirectImage

end
