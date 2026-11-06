module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceConormalAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage

/-!
# The difference of two morphisms of first-order thickenings is a derivation

Let `S` be a scheme in a big fppf site, `T` an algebraic space over `S`, `Z ⊆ X` and `W₀ ⊆ W`
two first-order thickenings of algebraic spaces over `T` (that is, `X` and `W` come with
morphisms `pX : X ⟶ T` and `pW : W ⟶ T`), with inclusions `i : Z ⟶ X` and `j : W₀ ⟶ W`, and let
`(f, c)` and `(f, c')` be two morphisms of thickenings over `T` with the same restriction
`f : Z ⟶ W₀`: so `i ≫ c = f ≫ j = i ≫ c'` and `c ≫ pW = pX = c' ≫ pW`.  Assume that the two
canonical maps `f^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] are equal.

[Stacks Project, Tag 0618] asserts that `c^♯ - c'^♯` factors as

`𝒪_W ⟶ 𝒪_{W₀} --D--> f_*𝒞_{Z/X} ⟶ f_*𝒪_X`

with `D` an `𝒪_T`-derivation.  This file proves it:
`AlgebraicGeometry.Space.exists_derivation_restrictedSharpThroughThickening_sub`.

## How the statement is read

Following the convention of the section of the source (a sheaf on a thickening is read as a
sheaf on the thickened space), everything is stated on the small étale site of `W₀`:

* `𝒪_W` is `j^{-1}𝒪_W` and `𝒪_W ⟶ 𝒪_{W₀}` is the inverse-image form
  `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}` of the structure map of [Stacks Project, Tag 03G8];
* `f_*𝒪_X` is `f_*(i^{-1}𝒪_X)`, and `c^♯` is the comorphism of `c` transported there,
  `AlgebraicGeometry.Space.restrictedSharpThroughThickening`;
* `f_*𝒞_{Z/X} ⟶ f_*𝒪_X` is the inclusion of the conormal module as the kernel of
  `i^{-1}𝒪_X ⟶ 𝒪_Z`, the field `ι` of `AlgebraicGeometry.Space.restrictedSquareZeroValues`;
* `D` is an `𝒪_T`-derivation of `𝒪_{W₀}` with values in `f_*𝒞_{Z/X}`: a
  `PresheafOfModulesOfCommRing.Derivation'` over the structure map
  `(j ≫ pW)^♯ : (j ≫ pW)^{-1}𝒪_T ⟶ 𝒪_{W₀}`, that is, a derivation killing the functions read
  from `T`.

## The proof

It is the one of the source.  The two comorphisms differ by a section of the square-zero ideal
`f_*𝒞_{Z/X}` and their difference is a derivation; that is
`AlgebraicGeometry.Space.restrictedLiftDifferenceData`, provided the two comorphisms agree on the
sections killed by `j^♯`, which is where hypothesis (2) enters:
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_conormalMap_eq`.  The
difference then descends along the locally surjective `j^♯`
(`AlgebraicGeometry.Space.descendedDerivation`), and it kills the functions read from `T`
because both morphisms are over `T`
(`inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'`),
those functions being read from `T` along `pW` and then restricted to `W₀`
(`AlgebraicGeometry.Space.structureSharpInverseImage_comp_app_eq`).

## Main results

* `AlgebraicGeometry.Space.structureSharpInverseImage_comp_app_eq`: the inverse-image form of
  the structure map of a composite `j ≫ p`, on sections, through the inverse image along `j` of
  the structure map of `p`.
* `AlgebraicGeometry.Space.exists_derivation_restrictedSharpThroughThickening_sub`:
  **[Stacks Project, Tag 0618]**.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A function read from the base along a composite is read from the base along the second
factor and then restricted.**  For `j : Y₀ ⟶ Y` and `p : Y ⟶ T`, the inverse-image form of the
structure map of `j ≫ p` takes a section to the inverse-image form of the structure map of `j`
applied to the inverse image along `j` of the structure map of `p`, applied to the section read
through the composition comparison of inverse images of [Stacks Project, Tag 03G8]. -/
theorem structureSharpInverseImage_comp_app_eq {Y₀ Y T : AlgebraicSpaces B S hS} (j : Y₀ ⟶ Y)
    (p : Y ⟶ T) (V : (SmallEtale B S hS Y₀.1)ᵒᵖ)
    (σ : ToType ((inverseImageStructureSheaf B S hS (j ≫ p)).obj.obj V)) :
    (structureSharpInverseImage B S hS (j ≫ p)).hom.app V σ =
      (structureSharpRingInverseImage B S hS j).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS j)).map
          (structureSharpRingInverseImage B S hS p)).hom.app V
          (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS j p).inv.app
            (smallEtaleRingedTopos B S hS T).O).hom.app V σ)) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
    (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS j p)) V)
    (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS j p).inv.app
            (smallEtaleRingedTopos B S hS T).O).hom.app V σ)
  have h2 : ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS j p).hom.app
          (smallEtaleRingedTopos B S hS T).O).hom.app V
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS j p).inv.app
            (smallEtaleRingedTopos B S hS T).O).hom.app V σ) = σ :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS j p).inv_hom_id_app
        (smallEtaleRingedTopos B S hS T).O)) V) σ
  exact (congrArg (fun y => (structureSharpInverseImage B S hS (j ≫ p)).hom.app V y) h2).symm.trans
    (h1.trans ((congrArg (fun y => (structureSharpInverseImage B S hS j).hom.app V y)
      (app_inverseImage_structureSharpRingInverseImage B S hS j p V _).symm).trans
      (structureSharpRingInverseImage_app B S hS j V _).symm))

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))

/-- **[Stacks Project, Tag 0618].**  Let `Z ⊆ X` and `W₀ ⊆ W` be first-order thickenings of
algebraic spaces over an algebraic space `T`, and let `(f, c)` and `(f, c')` be two morphisms of
thickenings over `T` with the same restriction `f : Z ⟶ W₀` and equal canonical maps
`f^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP].  Then there is an `𝒪_T`-derivation `D`
of `𝒪_{W₀}` with values in `f_*𝒞_{Z/X}` through which `c^♯ - c'^♯` factors: for every local
section `x` of `𝒪_W`, read on `W₀`, the difference of the two comorphisms at `x` is the
inclusion `f_*𝒞_{Z/X} ⟶ f_*𝒪_X` applied to `D` of the image of `x` in `𝒪_{W₀}`.

The reading of `𝒪_W`, `f_*𝒪_X` and the comorphisms on the small étale site of `W₀` is the one
of the module documentation. -/
@[stacks 0618 "the full statement: for two morphisms of first order thickenings over T with \
equal restriction f and equal maps f^*C ⟶ C of 04CP, c^♯ - c'^♯, read on the small étale site \
of the reduced target, factors as j^♯ : j^{-1}O_W ⟶ O_{W₀} followed by an O_T-derivation D \
into f_*C_{Z/X} and the inclusion f_*C_{Z/X} ⟶ f_*(i^{-1}O_X)"]
theorem exists_derivation_restrictedSharpThroughThickening_sub
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hW₀ : IsFirstOrderThickening B S hS W W₀.1) (c' : X ⟶ W)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (hsq' : subspaceInclusion B S hS X Z ≫ c' = f ≫ subspaceInclusion B S hS W W₀)
    {T : AlgebraicSpaces B S hS} (pX : X ⟶ T) (pW : W ⟶ T) (hc : c ≫ pW = pX)
    (hc' : c' ≫ pW = pX)
    (hC : conormalMap B S hS Z W₀ c f hsq = conormalMap B S hS Z W₀ c' f hsq') :
    ∃ D : PresheafOfModulesOfCommRing.Derivation'
        ((modulePushforward B S hS f).obj (conormalModule B S hS X Z)).val
        (structureSharpInverseImage B S hS (subspaceInclusion B S hS W W₀ ≫ pW)).hom,
      ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ f hZ).ι
            (D.d ((structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS W W₀)).hom.app V x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c f hsq).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ c' f hsq').hom.app V x := by
  have := isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W W₀) W₀.2.2
  let L := restrictedLiftDifferenceData B S hS Z W₀ f hZ c c' hsq hsq'
    (restrictedSharpThroughThickening_app_eq_of_conormalMap_eq B S hS Z W₀ c f hZ hW₀ c' hsq hsq'
      hC)
  refine ⟨descendedDerivation B S hS (subspaceInclusion B S hS W W₀ ≫ pW) L.toQuotientDerivation
    (fun V σ => ?_), fun V x => ?_⟩
  · rw [structureSharpInverseImage_comp_app_eq]
    exact L.descend_eq_zero_of_comp_eq _ _ rfl
      (inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'
        B S hS Z W₀ c c' pW f hsq hsq' (hc.trans hc'.symm)) _
  · rw [descendedDerivation_d]
    exact (congrArg (restrictedSquareZeroValues B S hS Z W₀ f hZ).ι
      (L.toQuotientDerivation.descend_app x)).trans (L.ι_diff x)

end AlgebraicGeometry.Space

end
