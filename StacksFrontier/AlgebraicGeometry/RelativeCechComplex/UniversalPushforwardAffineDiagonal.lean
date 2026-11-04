module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.CechResolution
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChangeDerived
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.UniversalPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived

/-!
# A complex universally computing the direct images, for a source of affine diagonal

Let `f : X ⟶ S` be a morphism of schemes and let `𝓕` be a quasi-coherent `𝒪_X`-module.
[Stacks, Tag 01XN] asserts that there is a bounded below complex `𝓚⁼` of quasi-coherent
`𝒪_S`-modules such that for every `g : S' ⟶ S` the ordinary inverse image `g^*𝓚⁼` represents
`Rf'_*𝓕'`, with the notation of the cartesian square of [Stacks, Tag 02KF].

This file proves this when `X` has affine diagonal, and in particular when `f` is separated. The
complex is the relative Čech complex `Č ⁼(𝒰, f, 𝓕)` of a finite affine open cover `𝒰` of `X`: its
terms are quasi-coherent ([Stacks, Tag 01XL]) and its inverse image along an arbitrary `g`
represents `Rf'_*𝓕'` ([Stacks, Tag 01XM]).

## Main definitions

* `universalPushforwardComplexOfAffineDiagonal`: the complex `Č ⁼(𝒰, f, 𝓕)` with the two
  properties of [Stacks, Tag 01XN], for a quasi-compact `X` of affine diagonal over a base of
  affine diagonal.

## Main results

* `universalPushforwardComplexOfAffineDiagonal_complex`: the underlying complex is the relative
  Čech complex of the finite affine open cover.
* `nonempty_universalPushforwardComplex_of_isAffineHom_diagonal`: [Stacks, Tag 01XN] for a source
  of affine diagonal.
* `nonempty_universalPushforwardComplex_of_isSeparated`: [Stacks, Tag 01XN] for a separated
  morphism.

## References

* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01XM](https://stacks.math.columbia.edu/tag/01XM)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.UniversalPushforward

open Stacks.AlgebraicGeometry.ModuleBaseChange (finiteAffineOpenCover)
open Stacks.AlgebraicGeometry.RelativeCechComplex
open Stacks.AlgebraicGeometry.RelativeCechBaseChange

variable {X S : Scheme.{u}}

/-- The complex of [Stacks, Tag 01XN] for a quasi-compact source of affine diagonal: the relative
Čech complex of the finite affine open cover `𝒰` obtained as a finite subcover of the canonical
affine open cover of `X`, together with the two properties the tag asserts: its terms are
quasi-coherent, and its ordinary inverse image along an arbitrary `g : S' ⟶ S` represents
`Rf'_*𝓕'` in `D⁺(S')`. -/
def universalPushforwardComplexOfAffineDiagonal (f : X ⟶ S) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    UniversalPushforwardComplex f F where
  complex := (relativeCechComplex f (finiteAffineOpenCover X)).obj F
  isQuasicoherent := relativeCechComplex_obj_isQuasicoherent f (finiteAffineOpenCover X) F
  baseChangeIso := fun {S' : Scheme.{u}} (g : S' ⟶ S) =>
    have e := @DerivedCategory.Plus.qhQIso S'.Modules _ _ (HasDerivedCategory.standard _)
      ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj
        ((relativeCechComplex f (finiteAffineOpenCover X)).obj F))
    e.symm ≪≫ baseChangeRelativeCechIsoDerivedPushforward (IsPullback.of_hasPullback f g)
      (finiteAffineOpenCover X) F

/-- The complex `universalPushforwardComplexOfAffineDiagonal f F` is the relative Čech complex of
the finite affine open cover of `X`. -/
theorem universalPushforwardComplexOfAffineDiagonal_complex (f : X ⟶ S) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (universalPushforwardComplexOfAffineDiagonal f F).complex =
      (relativeCechComplex f (finiteAffineOpenCover X)).obj F :=
  rfl

/-- Let `f : X ⟶ S` be a quasi-compact, quasi-separated morphism of schemes, let `S` be
quasi-compact and separated and let `𝓕` be a quasi-coherent `𝒪_X`-module. If `X` has affine
diagonal then there is a bounded below complex `𝓚⁼` of quasi-coherent `𝒪_S`-modules such that
for every `g : S' ⟶ S` the ordinary inverse image `g^*𝓚⁼` represents `Rf'_*𝓕'` in `D⁺(S')`. -/
@[stacks 01XN "for a source of affine diagonal"]
theorem nonempty_universalPushforwardComplex_of_isAffineHom_diagonal (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] [S.IsSeparated]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Nonempty (UniversalPushforwardComplex f F) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨universalPushforwardComplexOfAffineDiagonal f F⟩

/-- Let `f : X ⟶ S` be a quasi-compact, separated morphism of schemes, let `S` be quasi-compact
and separated and let `𝓕` be a quasi-coherent `𝒪_X`-module. Then there is a bounded below
complex `𝓚⁼` of quasi-coherent `𝒪_S`-modules such that for every `g : S' ⟶ S` the ordinary
inverse image `g^*𝓚⁼` represents `Rf'_*𝓕'` in `D⁺(S')`. -/
@[stacks 01XN "for a separated morphism"]
theorem nonempty_universalPushforwardComplex_of_isSeparated (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [CompactSpace S] [S.IsSeparated]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    Nonempty (UniversalPushforwardComplex f F) :=
  have : IsSeparated (terminal.from X) := by
    rw [terminal.hom_ext (terminal.from X) (f ≫ terminal.from S)]; infer_instance
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  nonempty_universalPushforwardComplex_of_isAffineHom_diagonal f F

end Stacks.AlgebraicGeometry.UniversalPushforward

end
