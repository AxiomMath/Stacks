module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsSituation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.BaseChangeFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.EilenbergWattsBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FinitePresentationAffineBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianStageSituation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula along an affine base change

Let
```
X' --p--> X
|f        |g
Y' --u--> Y
```
be a cartesian square of schemes with `u` affine, and let `F` be a quasi-coherent `𝒪_X`-module.
Then `p` is affine too, and

`p_* p^* F ≅ F ⊗_{𝒪_X} g^* u_* 𝒪_{Y'}`.

When the base is a spectrum, the right-hand side is the value at `Γ(Y', ⊤)` of the geometric
factor `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula` of the
Eilenberg–Watts functor of [Stacks, Tag 0EX3] (b).

All declarations are in the namespace `Stacks.AlgebraicGeometry.AffineBaseChangeProjection`.

## Main definitions

* `pullbackPushforwardUnitIso`: `g^* u_* 𝒪_{Y'} ≅ p_* 𝒪_{X'}`, affine base change at the
  structure sheaf.
* `tensorSwapIso`: symmetry of the tensor product of `𝒪_X`-modules.
* `pushforwardPullbackTensorIso`: **the projection formula for an affine base change**,
  `p_* p^* F ≅ F ⊗_{𝒪_X} g^* u_* 𝒪_{Y'}`, for `u` affine and `F` quasi-coherent.
* `cohomologyPullbackIso`: `H ⁱ(X', p^* F) ≅ H ⁱ(X, F ⊗ g^* u_* 𝒪_{Y'})` in every degree.
* `geometricFactorFormulaObjIso`: over `Y = Spec R` and `Y' = Spec S`, `p_* p^* F ≅ T(S)` for the
  geometric factor `T` of the affine case of [Stacks, Tag 0EX3] (b).
* `cohomologyPullbackGeometricFactorIso`: `H ⁱ(X', p^* F) ≅ H ⁱ(X, T(S))`.

For a cartesian square
```
X --p--> X₀
|g       |g₀
Y --u--> S₀
```
with `g₀` proper onto the affine `S₀` and `Y` affine, let `Φ` be the Eilenberg–Watts functor of
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.situation`.

* `topDegreeFunctorObjIso`: `Φ(Γ(Y, ⊤)) ≅ H ᵈ (X₀, p_* p^* G₀)`.
* `topDegreeFunctorObjCohomologyIso`: `Φ(Γ(Y, ⊤)) ≅ H ᵈ (X, p^* G₀)`, as `Γ(S₀, ⊤)`-modules.

## Main results

* `isZero_cohomology_pullback_iff`: `H ⁱ(X', p^* F)` vanishes exactly when
  `H ⁱ(X, F ⊗ g^* u_* 𝒪_{Y'})` does.
* `isPullback_specMap_appTop`: the square stays cartesian when its two affine bases are replaced
  by their spectra.
* `appTop_comp_eq` and `restrictScalars_appTop_eq`: the two ring maps `Γ(S₀, ⊤) ⟶ Γ(X, ⊤)`
  around the square agree, and so do the two restrictions of scalars.
* `isQuasicoherent_pushforward_pullback`: `p_* p^* G₀` is quasi-coherent.
* `finitePresentation_topDegreeFunctor_obj_self`: for `S₀` Noetherian, `Φ(Γ(S₀, ⊤))` is a
  finitely presented `Γ(S₀, ⊤)`-module.
* `isFinitePresentation_rightDerived_pullback_of_finitePresentation_cohomology`: if the
  `Γ(Y, ⊤)`-module `H ᵈ (X, p^* G₀)` is finitely presented, then so is the sheaf
  `R ᵈ g_* (p^* G₀)`.
* `topDegreeFunctorObjCohomologyIso_hom_apply`: `topDegreeFunctorObjCohomologyIso` on elements.
* `topDegreeFunctorObjCohomologyIso_smul`: under `topDegreeFunctorObjCohomologyIso`, `Φ` applied
  to multiplication by `a : Γ(Y, ⊤)` corresponds to multiplication by `a` on `H ᵈ (X, p^* G₀)`.
* `isFinitePresentation_rightDerived_pullback_of_noetherianModel`: **the affine case of
  [Stacks, Tag 0EX5] at a Noetherian stage** — for `S₀` Noetherian and `G₀` of finite
  presentation, `R ᵈ g_* (p^* G₀)` is of finite presentation, with no Noetherian hypothesis on
  `Y`.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeProjection

/-! ### Bridging the spellings -/

/-- The identification `h^* 𝒪_S ≅ 𝒪_Z` of
`Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`, stated in
`AlgebraicGeometry.Scheme.Modules` with the structure sheaves spelled through
`Scheme.ringCatSheaf`. -/
def pullbackUnitModulesIso {Z S : Scheme.{u}} (h : Z ⟶ S) :
    (Scheme.Modules.pullback h).obj (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅
      (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) :=
  Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso h

/-- **Symmetry of the tensor product of two `𝒪_Z`-modules**, `A ⊗ B ≅ B ⊗ A`, for the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
def tensorSwapIso (Z : Scheme.{u}) (A B : Z.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).obj A).obj B ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).obj B).obj A :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Z.toRingedSpace A B

/-! ### The projection formula for an affine base change -/

section Square

variable {X' X Y' Y : Scheme.{u}} {p : X' ⟶ X} {f : X' ⟶ Y'} {g : X ⟶ Y} {u : Y' ⟶ Y}

/-- **The horizontal morphism of a cartesian square over an affine morphism is affine.** This is
stability of `AlgebraicGeometry.IsAffineHom` under base change, applied to the square read with
`u` as the morphism being based changed along `g`. -/
@[ega "II 1.5.1"]
theorem isAffineHom_of_isPullback (hw : IsPullback p f g u) [IsAffineHom u] : IsAffineHom p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hw.flip inferInstance

/-- **Affine base change at the structure sheaf**: for a cartesian square with `u` affine,

`g^* u_* 𝒪_{Y'} ≅ p_* 𝒪_{X'}`.

[Stacks, Tag 02KG] makes the base-change morphism `g^* u_* ⟶ p_* f^*` invertible at the
structure sheaf of `Y'`, which is quasi-coherent
(`AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`); the identification
`f^* 𝒪_{Y'} ≅ 𝒪_{X'}` then removes the inverse image from the target. -/
@[ega "I 10.14.6" "special case"]
def pullbackPushforwardUnitIso (hw : IsPullback p f g u) [IsAffineHom u] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward u).obj
        (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)) ≅
      (Scheme.Modules.pushforward p).obj
        (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) :=
  haveI := AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hw.flip
    (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)
  asIso ((AffinePushforward.baseChangeNatTrans hw.flip.w).app
      (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)) ≪≫
    (Scheme.Modules.pushforward p).mapIso (pullbackUnitModulesIso f)

/-- **The projection formula for an affine base change.** For a cartesian square
```
X' --p--> X
|f        |g
Y' --u--> Y
```
with `u` affine and `F` a quasi-coherent `𝒪_X`-module,

`p_* p^* F ≅ F ⊗_{𝒪_X} g^* u_* 𝒪_{Y'}`. -/
def pushforwardPullbackTensorIso (hw : IsPullback p f g u) [IsAffineHom u] (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).obj
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward u).obj
          (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules))) :=
  haveI := isAffineHom_of_isPullback hw
  (DerivedAffinePushforward.pushforwardStructureSheafTensorIso p F hF).symm ≪≫
    tensorSwapIso X ((Scheme.Modules.pushforward p).obj
      (SheafOfModules.unit X'.ringCatSheaf : X'.Modules)) F ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).mapIso
      (pullbackPushforwardUnitIso hw).symm

/-! ### The same identity in cohomology -/

/-- **The projection formula for an affine base change, read in cohomology.** For a cartesian
square with `u` affine and `F` a quasi-coherent `𝒪_X`-module, in every degree `i`,

`H ⁱ(X', p^* F) ≅ H ⁱ(X, F ⊗_{𝒪_X} g^* u_* 𝒪_{Y'})`. -/
def cohomologyPullbackIso (hw : IsPullback p f g u) [IsAffineHom u] (F : X.Modules)
    (hF : F.IsQuasicoherent) (i : ℕ) :
    Hgroup X'.ringCatSheaf ⊤ i ((Scheme.Modules.pullback p).obj F) ≅
      Hgroup X.ringCatSheaf ⊤ i
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).obj
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward u).obj
            (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)))) :=
  haveI := isAffineHom_of_isPullback hw
  haveI : ((Scheme.Modules.pullback p).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback p F hF
  Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp p i
      ((Scheme.Modules.pullback p).obj F) ≪≫
    (Hfunctor X.ringCatSheaf ⊤ i).mapIso (pushforwardPullbackTensorIso hw F hF)

/-- **The vanishing form of `cohomologyPullbackIso`**: the cohomology of `p^* F` on `X'` vanishes
in degree `i` exactly when the cohomology on `X` of `F ⊗ g^* u_* 𝒪_{Y'}` does. -/
theorem isZero_cohomology_pullback_iff (hw : IsPullback p f g u) [IsAffineHom u] (F : X.Modules)
    (hF : F.IsQuasicoherent) (i : ℕ) :
    IsZero (Hgroup X'.ringCatSheaf ⊤ i ((Scheme.Modules.pullback p).obj F)) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ i
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).obj
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward u).obj
            (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules))))) :=
  ⟨fun h ↦ h.of_iso (cohomologyPullbackIso hw F hF i).symm,
    fun h ↦ h.of_iso (cohomologyPullbackIso hw F hF i)⟩

end Square

/-! ### Over a spectrum: the geometric factor of the Eilenberg–Watts reduction -/

section AffineBase

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))
  {S : CommRingCat.{u}} (φ : CommRingCat.of R ⟶ S)
  {X' : Scheme.{u}} {p : X' ⟶ W.left} {f : X' ⟶ Spec S}

/-- **The right-hand side of the projection formula is the geometric factor of
[Stacks, Tag 0EX3] (b) evaluated at `S`.** For a cartesian square
```
X' --------p--------> W.left
|f                    |W.hom
Spec S --Spec φ--> Spec R
```
and `F` a quasi-coherent module on `W.left`,

`p_* p^* F ≅ F ⊗ (W.hom)^* (S|_R)^~ = (geometricFactorFormula R W F).obj (S|_R)`,

where `S|_R` is `S` with its scalars restricted along `φ`. -/
def geometricFactorFormulaObjIso (hw : IsPullback p f W.hom (Spec.map φ))
    (F : W.left.Modules) (hF : F.IsQuasicoherent) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ≅
      (TopDegreeBaseChange.geometricFactorFormula R W F).obj
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
  pushforwardPullbackTensorIso hw F hF ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.left.toRingedSpace.sheaf).obj F).mapIso
      ((Scheme.Modules.pullback W.hom).mapIso
        (Scheme.Modules.pushforwardUnitTildeIso φ))

/-- **The cohomology of `p^* F` is the Eilenberg–Watts functor of the affine case of
[Stacks, Tag 0EX3] (b), evaluated at `S`.** In every degree `i`,

`H ⁱ(X', p^* F) ≅ H ⁱ(W.left, (geometricFactorFormula R W F).obj (S|_R))`. -/
def cohomologyPullbackGeometricFactorIso (hw : IsPullback p f W.hom (Spec.map φ))
    (F : W.left.Modules) (hF : F.IsQuasicoherent) (i : ℕ) :
    Hgroup X'.ringCatSheaf ⊤ i ((Scheme.Modules.pullback p).obj F) ≅
      Hgroup W.left.ringCatSheaf ⊤ i
        ((TopDegreeBaseChange.geometricFactorFormula R W F).obj
          ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))) :=
  haveI := isAffineHom_of_isPullback hw
  haveI : ((Scheme.Modules.pullback p).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback p F hF
  Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp p i
      ((Scheme.Modules.pullback p).obj F) ≪≫
    (Hfunctor W.left.ringCatSheaf ⊤ i).mapIso (geometricFactorFormulaObjIso R W φ hw F hF)

end AffineBase

/-! ### Towards [Stacks, Tag 0EX5] over a general base: the Noetherian stage -/

section NoetherianStage

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear
  Stacks.Cohomology.AffineBase.baseSectionsAlgebra

open Stacks.AlgebraicGeometry.NoetherianStageSituation
open Stacks.AlgebraicGeometry.TopDegreeFiniteType
open Stacks.Cohomology.AffineComparison

/-- **The cartesian square of a base change between affine bases, read at a literal `Spec`.**
For a cartesian square
```
X --p--> X₀
|g       |g₀
Y --u--> S₀
```
with `Y` and `S₀` affine, composing the two bases with `AlgebraicGeometry.Scheme.isoSpec` turns
the lower edge into `Spec` of the ring map `u` induces on global functions, and the square stays
cartesian. -/
theorem isPullback_specMap_appTop {X₀ S₀ X Y : Scheme.{u}} {p : X ⟶ X₀} {g : X ⟶ Y}
    {g₀ : X₀ ⟶ S₀} {u : Y ⟶ S₀} [IsAffine Y] [IsAffine S₀] (hsq : IsPullback p g g₀ u) :
    IsPullback p (g ≫ Y.isoSpec.hom) (g₀ ≫ S₀.isoSpec.hom) (Spec.map u.appTop) := by
  refine hsq.of_iso' (Iso.refl X) (Iso.refl X₀) Y.isoSpec.symm S₀.isoSpec.symm ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · change Y.isoSpec.inv ≫ u = Spec.map u.appTop ≫ S₀.isoSpec.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Scheme.isoSpec_hom,
      Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]

section Situation

variable {X₀ S₀ X Y : Scheme.{u}} (g₀ : X₀ ⟶ S₀) [IsProper g₀] [IsAffine S₀] (d : ℕ)
  (hvan : ∀ j : ℤ, (d : ℤ) < j → ∀ G : X₀.Modules, G.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G))

omit [IsProper g₀] [IsAffine S₀] in
/-- **The two ring maps `Γ(S₀, ⊤) ⟶ Γ(X, ⊤)` around a cartesian square agree.** -/
theorem appTop_comp_eq {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} (hsq : IsPullback p g g₀ u) :
    g₀.appTop ≫ p.appTop = u.appTop ≫ g.appTop :=
  (Scheme.Hom.comp_appTop p g₀).symm.trans
    ((congrArg Scheme.Hom.appTop hsq.w).trans (Scheme.Hom.comp_appTop g u))

omit [IsProper g₀] in
/-- **`p_* p^* G₀` is quasi-coherent.** -/
theorem isQuasicoherent_pushforward_pullback (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u) :
    ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj G₀)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X₀.ringCatSheaf).prop_of_iso
    (geometricFactorFormulaObjIso Γ(S₀, ⊤) (CategoryTheory.Over.mk (g₀ ≫ S₀.isoSpec.hom))
      u.appTop (isPullback_specMap_appTop hsq) G₀ hqc).symm
    (TopDegreeBaseChange.isQuasicoherent_geometricFactorFormula Γ(S₀, ⊤)
      (CategoryTheory.Over.mk (g₀ ≫ S₀.isoSpec.hom)) ⟨G₀, hqc⟩ _)

/-- **The value of the Eilenberg–Watts functor `Φ` of the Noetherian stage at the `Γ(S₀, ⊤)`-module
`Γ(Y, ⊤)` is `H ᵈ (X₀, p_* p^* G₀)`.** Here `Φ` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeFunctor` of the situation
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.situation g₀ d hvan`. -/
def topDegreeFunctorObjIso (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u) :
    ((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).obj
        ((ModuleCat.restrictScalars u.appTop.hom).obj
          (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤))) ≅
      (situation g₀ d hvan).topDegreeCohomology
        ⟨(Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj G₀),
          isQuasicoherent_pushforward_pullback g₀ G₀ hqc hsq⟩ :=
  (ModuleCat.restrictScalars _).mapIso
    (((moduleGlobalSections X₀).rightDerived d).mapIso
      (pushforwardIsoTensorTilde g₀ p g u hsq G₀ hqc
        ((Scheme.Modules.pullback p).obj G₀) (Iso.refl _)).symm)

/-- **The Eilenberg–Watts module of the Noetherian stage is a finitely presented
`Γ(S₀, ⊤)`-module**: `Φ(Γ(S₀, ⊤))` is finitely presented, for `g₀` proper onto an affine
**Noetherian** base and `G₀` of finite presentation. -/
theorem finitePresentation_topDegreeFunctor_obj_self [IsNoetherian S₀] (G₀ : X₀.Modules)
    [G₀.IsFinitePresentation] :
    Module.FinitePresentation (situation g₀ d hvan).affineBaseRing
      (((situation g₀ d hvan).topDegreeFunctor
        ⟨G₀, Stacks.Modules.isQuasicoherent_of_isFinitePresentation G₀⟩).obj
          (ModuleCat.of (situation g₀ d hvan).affineBaseRing
            (situation g₀ d hvan).affineBaseRing)) := by
  have hqc : G₀.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation G₀
  have := hqc
  have hmod := finitePresentation_cohomology_of_isFinitePresentation_rightDerived g₀ G₀ d
    (isFinitePresentation_rightDerived_of_moduleFinite_cohomology g₀ G₀ d)
  rw [← topDegreeCohomology_eq g₀ d hvan G₀ hqc] at hmod
  have hmod' : Module.FinitePresentation (situation g₀ d hvan).affineBaseRing
      ((situation g₀ d hvan).topDegreeCohomology ⟨G₀, hqc⟩) := hmod
  exact Module.FinitePresentation.of_equiv
    (((situation g₀ d hvan).topDegreeFunctorObjSelfIso ⟨G₀, hqc⟩).toLinearEquiv).symm

omit [IsProper g₀] [IsAffine S₀] in
/-- For a cartesian square with `g₀` quasi-compact and quasi-separated, `Y` affine and `G₀`
quasi-coherent, if `H ᵈ (X, p^* G₀)` is a finitely presented `Γ(Y, ⊤)`-module, then the sheaf
`R ᵈ g_* (p^* G₀)` is of finite presentation. -/
theorem isFinitePresentation_rightDerived_pullback_of_finitePresentation_cohomology
    [AlgebraicGeometry.QuasiCompact g₀] [AlgebraicGeometry.QuasiSeparated g₀]
    (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u)
    (h : Module.FinitePresentation Γ(Y, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived d).obj
          ((Scheme.Modules.pullback p).obj G₀)))) :
    (((Scheme.Modules.pushforward g).rightDerived d).obj
      ((Scheme.Modules.pullback p).obj G₀)).IsFinitePresentation := by
  have : AlgebraicGeometry.QuasiCompact g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : AlgebraicGeometry.QuasiSeparated g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : ((Scheme.Modules.pullback p).obj G₀).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback p G₀ hqc
  exact isFinitePresentation_rightDerived_of_finitePresentation_cohomology g _ d h

omit [IsProper g₀] [IsAffine S₀] in
/-- **The two restrictions of scalars from `Γ(X, ⊤)` to `Γ(S₀, ⊤)` around the square agree** on
every module. -/
theorem restrictScalars_appTop_eq {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀}
    (hsq : IsPullback p g g₀ u) (M : ModuleCat.{u} Γ(X, ⊤)) :
    (ModuleCat.restrictScalars g₀.appTop.hom).obj
        ((ModuleCat.restrictScalars p.appTop.hom).obj M) =
      (ModuleCat.restrictScalars u.appTop.hom).obj
        ((ModuleCat.restrictScalars g.appTop.hom).obj M) :=
  congrArg (fun φ : Γ(S₀, ⊤) ⟶ Γ(X, ⊤) ↦ (ModuleCat.restrictScalars φ.hom).obj M)
    (appTop_comp_eq g₀ hsq)

/-- **The value of the Eilenberg–Watts functor `Φ` of the Noetherian stage at `Γ(Y, ⊤)` is
`H ᵈ (X, p^* G₀)`**, as an isomorphism of `Γ(S₀, ⊤)`-modules:

`Φ(Γ(Y, ⊤)) ≅ H ᵈ (X, p^* G₀)`,

where `H ᵈ (X, p^* G₀)` is a `Γ(Y, ⊤)`-module with its scalars restricted along `u`. -/
def topDegreeFunctorObjCohomologyIso (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u) :
    ((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).obj
        ((ModuleCat.restrictScalars u.appTop.hom).obj
          (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤))) ≅
      (ModuleCat.restrictScalars u.appTop.hom).obj
        ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X).rightDerived d).obj
            ((Scheme.Modules.pullback p).obj G₀))) :=
  haveI : IsAffineHom p := isAffineHom_of_isPullback hsq
  haveI : ((Scheme.Modules.pullback p).obj G₀).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback p G₀ hqc
  topDegreeFunctorObjIso g₀ d hvan G₀ hqc hsq ≪≫
    eqToIso (topDegreeCohomology_eq g₀ d hvan _
      (isQuasicoherent_pushforward_pullback g₀ G₀ hqc hsq)) ≪≫
    (ModuleCat.restrictScalars g₀.appTop.hom).mapIso
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward p
        ((Scheme.Modules.pullback p).obj G₀) d).symm ≪≫
    eqToIso (restrictScalars_appTop_eq g₀ hsq _)

/-- `H ᵈ (X, p^* G₀)` as a `Γ(Y, ⊤)`-module, the scalars acting through `g` at the open `⊤`. -/
abbrev pullbackCohomologyModule (p : X ⟶ X₀) (g : X ⟶ Y) (G₀ : X₀.Modules) :
    ModuleCat.{u} Γ(Y, ⊤) :=
  (ModuleCat.restrictScalars g.appTop.hom).obj
    (((moduleGlobalSections X).rightDerived d).obj ((Scheme.Modules.pullback p).obj G₀))

/-- `Γ(Y, ⊤)` as a `Γ(S₀, ⊤)`-module, through `u` at the open `⊤`. -/
abbrev baseAlgebraModule (u : Y ⟶ S₀) : ModuleCat.{u} Γ(S₀, ⊤) :=
  (ModuleCat.restrictScalars u.appTop.hom).obj (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤))

/-- **Multiplication by `a : Γ(Y, ⊤)` on `Γ(Y, ⊤)`, as a `Γ(S₀, ⊤)`-linear endomorphism**: the
restriction of scalars along `u` of `LinearMap.mulLeft Γ(Y, ⊤) a`. -/
abbrev mulLeftMap (u : Y ⟶ S₀) (a : Γ(Y, ⊤)) :
    baseAlgebraModule u ⟶ baseAlgebraModule u :=
  (ModuleCat.restrictScalars u.appTop.hom).map
    (ModuleCat.ofHom (LinearMap.mulLeft Γ(Y, ⊤) a))

/-- **`topDegreeFunctorObjCohomologyIso` on elements**: it is `topDegreeFunctorObjIso` followed
by the inverse of `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`. -/
theorem topDegreeFunctorObjCohomologyIso_hom_apply (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u)
    [IsAffineHom p] [((Scheme.Modules.pullback p).obj G₀).IsQuasicoherent]
    (y : (((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).obj
      (baseAlgebraModule u) : Type u)) :
    ((topDegreeFunctorObjCohomologyIso g₀ d hvan G₀ hqc hsq).hom.hom y :
        (pullbackCohomologyModule d p g G₀ : Type u)) =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward p
          ((Scheme.Modules.pullback p).obj G₀) d).inv.hom
        ((topDegreeFunctorObjIso g₀ d hvan G₀ hqc hsq).hom.hom y) := by
  have hE : ((topDegreeFunctorObjCohomologyIso g₀ d hvan G₀ hqc hsq).hom.hom y :
        (pullbackCohomologyModule d p g G₀ : Type u)) =
      (eqToHom (restrictScalars_appTop_eq g₀ hsq _)).hom
        ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward p
            ((Scheme.Modules.pullback p).obj G₀) d).inv.hom
          ((eqToHom (topDegreeCohomology_eq g₀ d hvan _
              (isQuasicoherent_pushforward_pullback g₀ G₀ hqc hsq))).hom
            ((topDegreeFunctorObjIso g₀ d hvan G₀ hqc hsq).hom.hom y))) := rfl
  have hcast : ∀ {M N : ModuleCat.{u} Γ(S₀, ⊤)} (h : M = N) (x : (M : Type u))
      (z : (N : Type u)), HEq x z → (eqToHom h).hom x = z := by
    rintro _ _ rfl x z hxz
    rw [eqToHom_refl]
    exact eq_of_heq hxz
  have h1 : ∀ z : (((situation g₀ d hvan).topDegreeCohomology
          ⟨(Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj G₀),
            isQuasicoherent_pushforward_pullback g₀ G₀ hqc hsq⟩ :
        ModuleCat.{u} Γ(S₀, ⊤)) : Type u),
      ((eqToHom (topDegreeCohomology_eq g₀ d hvan _
          (isQuasicoherent_pushforward_pullback g₀ G₀ hqc hsq))).hom z :
        (((moduleGlobalSections X₀).rightDerived d).obj
          ((Scheme.Modules.pushforward p).obj
            ((Scheme.Modules.pullback p).obj G₀)) : Type u)) = z :=
    fun z ↦ hcast _ _ _ HEq.rfl
  have h2 : ∀ z : (((ModuleCat.restrictScalars g₀.appTop.hom).obj
          ((ModuleCat.restrictScalars p.appTop.hom).obj
            (((moduleGlobalSections X).rightDerived d).obj
              ((Scheme.Modules.pullback p).obj G₀)))) : Type u),
      ((eqToHom (restrictScalars_appTop_eq g₀ hsq
          (((moduleGlobalSections X).rightDerived d).obj
            ((Scheme.Modules.pullback p).obj G₀)))).hom z :
        (pullbackCohomologyModule d p g G₀ : Type u)) = z :=
    fun z ↦ hcast _ _ _ HEq.rfl
  exact hE.trans ((h2 _).trans (congrArg
    (fun z ↦ (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward p
      ((Scheme.Modules.pullback p).obj G₀) d).inv.hom z) (h1 _)))

/-- **The multiplication compatibility of `topDegreeFunctorObjCohomologyIso`.** The functor `Φ`
applied to multiplication by `a : Γ(Y, ⊤)` on `Γ(Y, ⊤)` corresponds, under
`Φ(Γ(Y, ⊤)) ≅ H ᵈ (X, p^* G₀)`, to multiplication by `a` on `H ᵈ (X, p^* G₀)`. -/
theorem topDegreeFunctorObjCohomologyIso_smul (G₀ : X₀.Modules) (hqc : G₀.IsQuasicoherent)
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u)
    (a : Γ(Y, ⊤))
    (y : (((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).obj
      (baseAlgebraModule u) : Type u)) :
    (((topDegreeFunctorObjCohomologyIso g₀ d hvan G₀ hqc hsq).hom.hom
        ((((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).map
          (mulLeftMap u a)).hom y) :
      (pullbackCohomologyModule d p g G₀ : Type u))) =
    a • (((topDegreeFunctorObjCohomologyIso g₀ d hvan G₀ hqc hsq).hom.hom y :
      (pullbackCohomologyModule d p g G₀ : Type u))) := by
  have : IsAffineHom p := isAffineHom_of_isPullback hsq
  have : ((Scheme.Modules.pullback p).obj G₀).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback p G₀ hqc
  let : Linear (Γ(Y, ⊤) : Type u) X.Modules :=
    AlgebraicGeometry.modulesLinear (Γ(Y, ⊤) : Type u)
      (Over.mk (g ≫ Y.isoSpec.hom) : Over (Spec (CommRingCat.of (Γ(Y, ⊤) : Type u))))
  have hD := map_comm ((moduleGlobalSections X₀).rightDerived d)
    (comm_inv (pushforwardIsoTensorTilde g₀ p g u hsq G₀ hqc
        ((Scheme.Modules.pullback p).obj G₀) (Iso.refl _))
      (pushforwardIsoTensorTilde_smul g₀ p g u hsq G₀ hqc
        ((Scheme.Modules.pullback p).obj G₀) (Iso.refl _) a))
  have hA : ((topDegreeFunctorObjIso g₀ d hvan G₀ hqc hsq).hom.hom
        ((((situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩).map
          (mulLeftMap u a)).hom y) :
      (((moduleGlobalSections X₀).rightDerived d).obj
        ((Scheme.Modules.pushforward p).obj
          ((Scheme.Modules.pullback p).obj G₀)) : Type u)) =
      (((moduleGlobalSections X₀).rightDerived d).map
          ((Scheme.Modules.pushforward p).map
            (a • 𝟙 ((Scheme.Modules.pullback p).obj G₀)))).hom
        ((topDegreeFunctorObjIso g₀ d hvan G₀ hqc hsq).hom.hom y) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hD) y
  have hB : ∀ z : ((((moduleGlobalSections X₀).rightDerived d).obj
        ((Scheme.Modules.pushforward p).obj
          ((Scheme.Modules.pullback p).obj G₀))) : Type u),
      ((cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj G₀) d).inv.hom
          ((((moduleGlobalSections X₀).rightDerived d).map
              ((Scheme.Modules.pushforward p).map
                (a • 𝟙 ((Scheme.Modules.pullback p).obj G₀)))).hom z) :
        (pullbackCohomologyModule d p g G₀ : Type u)) =
      a • (show (pullbackCohomologyModule d p g G₀ : Type u) from
        (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj G₀) d).inv.hom z) := by
    intro z
    have hw := cohomologyIsoPushforward_smul_appTop p g
      ((Scheme.Modules.pullback p).obj G₀) d a
      ((cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj G₀) d).inv.hom z)
    rw [Iso.inv_hom_id_apply] at hw
    exact (congrArg (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj G₀) d).inv.hom
      hw).symm.trans (Iso.hom_inv_id_apply _ _)
  refine Eq.trans (topDegreeFunctorObjCohomologyIso_hom_apply g₀ d hvan G₀ hqc hsq _) ?_
  refine Eq.trans (congrArg (fun t ↦
    (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj G₀) d).inv.hom t) hA) ?_
  exact (hB _).trans (congrArg (fun t ↦ a • t)
    (topDegreeFunctorObjCohomologyIso_hom_apply g₀ d hvan G₀ hqc hsq y).symm)

include hvan in
/-- **[Stacks, Tag 0EX5] at the Noetherian stage.** Let `g₀ : X₀ ⟶ S₀`
be proper onto an affine **Noetherian** base, with higher direct images of quasi-coherent modules
vanishing above `d`, let `G₀` be an `𝒪_{X₀}`-module of finite presentation, and let
```
X --p--> X₀
|g       |g₀
Y --u--> S₀
```
be cartesian with `Y` affine. Then `R ᵈ g_* (p^* G₀)` is of finite presentation; `Y` carries no
Noetherian hypothesis. -/
theorem isFinitePresentation_rightDerived_pullback_of_noetherianModel
    [IsNoetherian S₀] (G₀ : X₀.Modules) [G₀.IsFinitePresentation]
    {p : X ⟶ X₀} {g : X ⟶ Y} {u : Y ⟶ S₀} [IsAffine Y] (hsq : IsPullback p g g₀ u) :
    (((Scheme.Modules.pushforward g).rightDerived d).obj
      ((Scheme.Modules.pullback p).obj G₀)).IsFinitePresentation := by
  have hqc : G₀.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation G₀
  have := (situation g₀ d hvan).additive_topDegreeFunctor ⟨G₀, hqc⟩
  have := (situation g₀ d hvan).linear_topDegreeFunctor ⟨G₀, hqc⟩
  have := (situation g₀ d hvan).preservesFiniteColimits_topDegreeFunctor ⟨G₀, hqc⟩
  have := fun J : Type u ↦
    (situation g₀ d hvan).preservesColimitsOfShape_discrete_topDegreeFunctor ⟨G₀, hqc⟩ J
  let : Algebra (situation g₀ d hvan).affineBaseRing Γ(Y, ⊤) := u.appTop.hom.toAlgebra
  let : Module (situation g₀ d hvan).affineBaseRing
      ((pullbackCohomologyModule d p g G₀ : Type u)) :=
    Module.compHom _ u.appTop.hom
  have : IsScalarTower (situation g₀ d hvan).affineBaseRing Γ(Y, ⊤)
      ((pullbackCohomologyModule d p g G₀ : Type u)) :=
    ⟨fun x a m ↦ by
      rw [Algebra.smul_def]
      exact mul_smul _ a m⟩
  have key : Module.FinitePresentation Γ(Y, ⊤)
      ((pullbackCohomologyModule d p g G₀ : Type u)) :=
    Stacks.EilenbergWatts.finitePresentation_of_compatible_smul
      (F := (situation g₀ d hvan).topDegreeFunctor ⟨G₀, hqc⟩)
      (A := Γ(Y, ⊤)) (N := (pullbackCohomologyModule d p g G₀ : Type u))
      (e := (topDegreeFunctorObjCohomologyIso g₀ d hvan G₀ hqc hsq).toLinearEquiv)
      (topDegreeFunctorObjCohomologyIso_smul g₀ d hvan G₀ hqc hsq)
      (finitePresentation_topDegreeFunctor_obj_self g₀ d hvan G₀)
  exact isFinitePresentation_rightDerived_pullback_of_finitePresentation_cohomology g₀ d G₀ hqc
    hsq key

end Situation

end NoetherianStage

end Stacks.AlgebraicGeometry.AffineBaseChangeProjection

end
