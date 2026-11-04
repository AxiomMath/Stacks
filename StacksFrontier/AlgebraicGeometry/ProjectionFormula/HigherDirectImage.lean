module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparison
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# The projection formula for the higher direct images along an invertible module

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module and `𝒢` an **invertible**
`𝒪_Y`-module. This file proves the higher-degree clause of [Stacks, Tag 01E8],

`R^n f_*(ℱ ⊗_{𝒪_X} f^*𝒢) ≅ (R^n f_*ℱ) ⊗_{𝒪_Y} 𝒢` for every `n`,

naturally in `ℱ`, with no hypothesis on `f` or on `ℱ` and no hypothesis on `n`, together with
its iterated form for a finite family of invertible modules and an integer exponent vector.

## Main definitions

* `Stacks.ProjectionFormula.tensorRightInvertible`: tensoring on the right by an invertible
  module, as an endofunctor of `X.Modules`.
* `Stacks.ProjectionFormula.pushforwardTensorRightNatIso`: the projection formula of
  [Stacks, Tag 0FZE] in degree zero, read as a natural isomorphism of functors
  `(- ⊗ f^*𝒢) ⋙ f_* ≅ f_* ⋙ (- ⊗ 𝒢)`.
* `Stacks.ProjectionFormula.derivedPushforwardTensorRightPlusIso`: the `D⁺` clause of
  [Stacks, Tag 01E8] for an invertible module, `D(- ⊗ f^*𝒢) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗ 𝒢)` as
  functors `D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`.
* `Stacks.ProjectionFormula.higherDirectImageFunctor`: the higher direct image `R^q f_*`.

## Main results

* `Stacks.ProjectionFormula.higherDirectImageTensorRightIso`: **the projection formula in every
  degree, as a natural isomorphism of functors** `(- ⊗ f^*𝒢) ⋙ R^n f_* ≅ R^n f_* ⋙ (- ⊗ 𝒢)`.
* `Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso`: the same isomorphism read at
  a module, `R^n f_*(ℱ ⊗ f^*𝒢) ≅ (R^n f_*ℱ) ⊗ 𝒢`.
* `Stacks.ProjectionFormula.higherDirectImageTwistListIso` and
  `Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso`: **the same in the iterated form
  the Euler-characteristic induction of [Stacks, Tag 0BEM] consumes**,
  `R^q f_*(ℱ ⊗ (f^*𝓛_1)^{⊗ n_1} ⊗ ⋯) ≅ (R^q f_*ℱ) ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯`, for the twist
  `AlgebraicGeometry.twistedSheaf`.

## The route

Write `T_X` for `- ⊗_{𝒪_X} f^*𝒢` and `T_Y` for `- ⊗_{𝒪_Y} 𝒢`. Invertibility of `𝒢` means
exactly that `T_Y` is an equivalence ([Stacks, Tag 01CS]), and `f^*𝒢` is invertible by
[Stacks, Tag 0B8L], so `T_X` is an equivalence too. An equivalence is exact and carries
injective objects to injective objects, which are right acyclic for every additive functor; and
in degree zero `T_X ⋙ f_* ≅ f_* ⋙ T_Y` is the projection formula of
`Stacks.ProjectionFormula.isIso_projectionFormulaMap`, unconditional for an invertible module.

Those are precisely the hypotheses of
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`, which upgrades the
degree-zero isomorphism to `DT_X ⋙ Rf_* ≅ Rf_* ⋙ DT_Y` on bounded below derived categories.
Since `R^n f_* = (·[0]) ⋙ Rf_* ⋙ H^n`, the degreewise statement follows from that by the two
comparisons an exact functor satisfies on `D⁺`:
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle`, `DT_X(ℱ[0]) ≅ (T_Xℱ)[0]`, and
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`, `H^n(DT_Y K) ≅ T_Y(H^n K)`.

No injective resolution is chosen and no spectral sequence is used; in particular
[Stacks, Tag 01E7] is not needed, because an equivalence preserves injectives for free. That
saving is special to the invertible case: the same two clauses for a general **finite locally
free** `𝒢` — the hypothesis [Stacks, Tag 01E8] actually makes — are proved in
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/HigherDirectImageFiniteLocallyFree.lean`, where
tensoring is no longer an equivalence and Tag 01E7 is used.

## Implementation notes

*The two spellings of a sheaf of modules on a scheme.* `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)` are definitionally
equal, but instance synthesis does not cross between them. `tensorRightInvertible` is therefore
introduced with its type ascribed at the *scheme* spelling, which is the spelling the right
derived functors of `AlgebraicGeometry.Scheme.Modules.pushforward` are formed in, and the five
instances it needs are proved once for it.

*The two classes realising [Stacks, Tag 01CS].* The projection formula of
`StacksFrontier/AlgebraicGeometry/ProjectionFormulaInvertible/Basic.lean` is stated for
`Stacks.SheafOfModules.IsInvertible`, while `AlgebraicGeometry.twistedSheaf` and the tensor
powers it folds take `AlgebraicGeometry.SheafOfModules.IsInvertible`. The two agree by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; `isInvertible_tensorPowerOfFamily`
is where the iterated statement crosses between them.

*The degree is an arbitrary integer.* `CategoryTheory.Functor.rightDerivedPlus` is indexed by
`ℤ`, and nothing in the argument restricts the degree, so the statement is made for `n : ℤ`; the
`ℕ`-indexed form used by the canonicity condition of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap` is the case
`n = (q : ℤ)`.

*What is not claimed.* The isomorphism is not identified with the canonical map characterised by
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap`: no canonical map in
positive degree is constructed anywhere in this development — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparison.lean` — so there is nothing
to compare with. In degree zero the comparison is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMapZero`.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard

-- As in `StacksFrontier/Algebra/Homology/DerivedCategory/BaseChangeBoundedBelow.lean`: instance
-- search reaches for `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective`,
-- which applies at an arbitrary object, before the instance deducing the same conclusion from
-- `EnoughInjectives`, and then tries to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Tensoring on the right by an invertible module on a scheme -/

/-- **Tensoring an `𝒪_Z`-module on the right by `H`**, as an endofunctor of `Z.Modules`. This is
`Stacks.ProjectionFormula.tensorRightOf` for the tensor-product bifunctor of a ringed space,
with its type ascribed at the scheme spelling of the category of modules. -/
def tensorRightInvertible (Z : Scheme.{u}) (H : Z.Modules) : Z.Modules ⥤ Z.Modules :=
  tensorRightOf ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩))) H

/-- Tensoring on the right by `H` sends `A` to the tensor product `A ⊗_{𝒪_Z} H`. -/
theorem tensorRightInvertible_obj (Z : Scheme.{u}) (H A : Z.Modules) :
    (tensorRightInvertible Z H).obj A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(Z.toRingedSpace).presheaf, (Z.toRingedSpace).IsSheaf⟩).obj A).obj H := rfl

section Invertible

variable (Z : Scheme.{u}) (H : Z.Modules)
  [h : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 H]

/-- **Tensoring on the right by an invertible module is an equivalence**, [Stacks, Tag 01CS].
This is `Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` for
`(Tensor.sheafTensor _).flip.obj H`, with the invertibility hypothesis respelled at `Z.sheaf.obj`
rather than at `Z.presheaf`, transported to the uncurried bifunctor along
`CategoryTheory.Functor.tensorRightOfUncurryIso`. -/
instance isEquivalence_tensorRightInvertible : (tensorRightInvertible Z H).IsEquivalence :=
  haveI : Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.sheaf.obj
      (structureRingSheaf Z.toRingedSpace).property H := h
  @Functor.isEquivalence_of_iso _ _ _ _ _ _
    (Functor.tensorRightOfUncurryIso
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩) H).symm
    (Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
      Z.toRingedSpace.sheaf.obj (structureRingSheaf Z.toRingedSpace).property H)

/-- Tensoring on the right by an invertible module preserves finite limits, being an
equivalence. -/
instance preservesFiniteLimits_tensorRightInvertible :
    PreservesFiniteLimits (tensorRightInvertible Z H) :=
  inferInstance

/-- Tensoring on the right by an invertible module preserves finite colimits, being an
equivalence. -/
instance preservesFiniteColimits_tensorRightInvertible :
    PreservesFiniteColimits (tensorRightInvertible Z H) :=
  inferInstance

/-- Tensoring on the right by an invertible module is additive, preserving binary products and
the zero object. -/
instance additive_tensorRightInvertible : (tensorRightInvertible Z H).Additive :=
  (tensorRightInvertible Z H).additive_of_preserves_binary_products

/-- Tensoring on the right by an invertible module carries injective modules to injective
modules, being an equivalence. -/
instance preservesInjectiveObjects_tensorRightInvertible :
    (tensorRightInvertible Z H).PreservesInjectiveObjects :=
  inferInstance

end Invertible

/-! ### The projection formula in degree zero, as a natural isomorphism -/

section Zero

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
  [hG : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 G]

/-- Invertibility of an `𝒪_Y`-module read at `Y.sheaf.obj` and
`(Stacks.RingedSpace.structureRingSheaf Y).property`, the spelling the projection formula of
[Stacks, Tag 0FZE] is stated in. The two differ by no more than `exact`. -/
theorem isInvertible_structureRingSheaf :
    Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.sheaf.obj
      (structureRingSheaf Y.toRingedSpace).property G :=
  hG

attribute [local instance] isInvertible_structureRingSheaf

/-- **[Stacks, Tag 0B8L]**: the pullback of an invertible module is invertible, at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling, which instance search does not unfold to
reach `Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf`. -/
instance isInvertible_schemeModulesPullback :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj G) :=
  Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf f G

/-- **The projection formula morphism of [Stacks, Tag 0FZE] as a natural transformation**
`f_*(-) ⊗_{𝒪_Y} 𝒢 ⟶ f_*((-) ⊗_{𝒪_X} f^*𝒢)`, with no hypothesis on `𝒢`. -/
def pushforwardTensorRightNatTrans :
    Scheme.Modules.pushforward f ⋙ tensorRightInvertible Y G ⟶
      tensorRightInvertible X ((Scheme.Modules.pullback f).obj G) ⋙
        Scheme.Modules.pushforward f where
  app A := projectionFormulaMap' f.toLRSHom.toShHom A G
  naturality A B g := by
    have h := projectionFormulaMap'_natural f.toLRSHom.toShHom g (𝟙 G)
    have hid : (pullbackFunctor f.toLRSHom.toShHom).map (𝟙 G) = 𝟙 _ :=
      (pullbackFunctor f.toLRSHom.toShHom).map_id G
    rw [hid] at h
    exact h

/-- **The projection formula for an invertible module, in degree zero and naturally in the
module on the source**: `(- ⊗_{𝒪_X} f^*𝒢) ⋙ f_* ≅ f_* ⋙ (- ⊗_{𝒪_Y} 𝒢)`. Each component is
invertible by `Stacks.ProjectionFormula.isIso_projectionFormulaMap`. -/
def pushforwardTensorRightNatIso :
    tensorRightInvertible X ((Scheme.Modules.pullback f).obj G) ⋙
        Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f ⋙ tensorRightInvertible Y G :=
  haveI : ∀ A, IsIso ((pushforwardTensorRightNatTrans f G).app A) := fun A =>
    isIso_projectionFormulaMap f.toLRSHom.toShHom A G
  haveI := NatIso.isIso_of_isIso_app (pushforwardTensorRightNatTrans f G)
  (asIso (pushforwardTensorRightNatTrans f G)).symm

/-- **An injective module tensored by an invertible module is right acyclic for `f_*`**: the
tensor product is again injective, tensoring by an invertible module being an equivalence, and
an injective object is right acyclic for every additive functor ([Stacks, Tag 0157]). -/
theorem rightAcyclic_pushforward_tensorRightInvertible (I : X.Modules) (hI : Injective I) :
    (Scheme.Modules.pushforward f).rightAcyclic
      ((tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).obj I) :=
  Functor.rightAcyclic_obj_of_preservesInjectiveObjects
    (tensorRightInvertible X ((Scheme.Modules.pullback f).obj G))
    (Scheme.Modules.pushforward f) I hI

end Zero

/-! ### The projection formula in every degree -/

section Higher

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
  [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 G]

/-- **The projection formula in `D⁺` for an invertible module**: for a morphism of
schemes `f : X ⟶ Y` and an **invertible** `𝒪_Y`-module `𝒢`,

`D(- ⊗_{𝒪_X} f^*𝒢) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗_{𝒪_Y} 𝒢)`

as functors `D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`: the projection formula in the bounded below derived category,
for an arbitrary morphism of schemes and every object of `D⁺(𝒪_X)`.

Tensoring by an invertible module is an equivalence, hence exact, so it induces a functor on
bounded below derived categories and carries injectives to injectives; the degree-zero formula
`pushforwardTensorRightNatIso` is then upgraded to the derived categories by
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`. The degreewise statement
`higherDirectImageTensorRightIso` is read off from this one. -/
def derivedPushforwardTensorRightPlusIso :
    (tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).mapDerivedCategoryPlus ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (tensorRightInvertible Y G).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (tensorRightInvertible X ((Scheme.Modules.pullback f).obj G))
    (tensorRightInvertible Y G)
    (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f)
    (pushforwardTensorRightNatIso f G)
    (rightAcyclic_pushforward_tensorRightInvertible f G)

/-- **The projection formula for the higher direct images along an invertible module, as a
natural isomorphism of functors**: `(- ⊗_{𝒪_X} f^*𝒢) ⋙ R^n f_* ≅ R^n f_* ⋙ (- ⊗_{𝒪_Y} 𝒢)`,
for every integer `n`, for an arbitrary morphism of schemes and an invertible `𝒢`. -/
def higherDirectImageTensorRightIso (n : ℤ) :
    tensorRightInvertible X ((Scheme.Modules.pullback f).obj G) ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus n ≅
      (Scheme.Modules.pushforward f).rightDerivedPlus n ⋙ tensorRightInvertible Y G :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)) 0).symm
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor X.Modules 0)
      (Functor.isoWhiskerRight (derivedPushforwardTensorRightPlusIso f G)
        (DerivedCategory.Plus.homologyFunctor Y.Modules n)) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus)
      (Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (tensorRightInvertible Y G))
          (DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
        Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (tensorRightInvertible Y G) n)

/-- **The projection formula for higher direct images along an invertible module**: for a
morphism of schemes `f : X ⟶ Y`, an arbitrary `𝒪_X`-module `ℱ` and an **invertible**
`𝒪_Y`-module `𝒢`,

`R^n f_*(ℱ ⊗_{𝒪_X} f^*𝒢) ≅ (R^n f_*ℱ) ⊗_{𝒪_Y} 𝒢`

for every integer `n`. This is `higherDirectImageTensorRightIso` evaluated at `ℱ`. -/
def higherDirectImageProjectionFormulaIso (F : X.Modules) (n : ℤ) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F)).obj G :=
  (higherDirectImageTensorRightIso f G n).app F

end Higher

/-! ### The iterated projection formula, for a finite family of invertible modules -/

section Fold

/-- **The `q`-th higher direct image `R^q f_*`**, as a functor `X.Modules ⥤ Y.Modules`: the
`ℤ`-indexed right derived functor of the direct image. -/
abbrev higherDirectImageFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℤ) :
    X.Modules ⥤ Y.Modules :=
  (Scheme.Modules.pushforward f).rightDerivedPlus q

-- **[Stacks, Tag 0B8L]**, at the `AlgebraicGeometry.SheafOfModules.IsInvertible` spelling:
-- `AlgebraicGeometry.SheafOfModules.isInvertible_pullback`. It is a theorem rather than an
-- instance where it is proved, so it is made a local instance here; that discharges
-- invertibility of each `f^*𝓛_j`, which is why this section asks only for invertibility of the
-- `𝓛_j` themselves.
attribute [local instance] AlgebraicGeometry.SheafOfModules.isInvertible_pullback

variable {X Y : Scheme.{u}} {r : ℕ} (f : X ⟶ Y) (L : Fin r → Y.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L j)]

/-- **[Stacks, Tag 01CU]**: every integer tensor power of an invertible module is invertible, at
the `Stacks.SheafOfModules.IsInvertible` spelling the projection formula above asks for, from the
`AlgebraicGeometry.SheafOfModules.IsInvertible` spelling `AlgebraicGeometry.twistedSheaf` asks
for. -/
instance isInvertible_tensorPowerOfFamily (j : Fin r) (d : ℤ) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 (L j) d) :=
  haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L j) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.presheaf Y.ringCatSheaf.2
      (L j)).mpr inferInstance
  Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower Y.presheaf Y.ringCatSheaf.2 (L j) d

/-- **The projection formula for the higher direct images, folded over a list of twisting
indices**: `R^q f_*(ℳ ⊗ (f^*𝓛_{j_1})^{⊗ e_{j_1}} ⊗ ⋯) ≅ (R^q f_*ℳ) ⊗ 𝓛_{j_1}^{⊗ e_{j_1}} ⊗ ⋯`.

At the head of the list `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIntIso` rewrites
`(f^*𝓛_j)^{⊗ e_j}` as `f^*(𝓛_j^{⊗ e_j})`, `higherDirectImageProjectionFormulaIso` moves that
factor out of the higher direct image, and `AlgebraicGeometry.twistListIso` carries the
resulting isomorphism through the remaining factors, where the inductive hypothesis applies. -/
def higherDirectImageTwistListIso (q : ℤ) (e : Fin r → ℤ) :
    ∀ (l : List (Fin r)) (M : X.Modules),
      (higherDirectImageFunctor f q).obj
          (twistList (fun j => (Scheme.Modules.pullback f).obj (L j)) e l M) ≅
        twistList L e l ((higherDirectImageFunctor f q).obj M) := by
  intro l
  induction l with
  | nil => exact fun _ => Iso.refl _
  | cons j t ih =>
    exact fun M =>
      ih _ ≪≫
        twistListIso L e t
          ((higherDirectImageFunctor f q).mapIso
              (Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf X.ringCatSheaf.2
                (Iso.refl M)
                (Scheme.Modules.pullbackTensorPowerIntIso f (L j) (e j)).symm) ≪≫
            higherDirectImageProjectionFormulaIso f
              (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
                (L j) (e j)) M q)

/-- **The projection formula for higher direct images along an iterated twist**: for a
morphism of schemes `f : X ⟶ Y`, an arbitrary `𝒪_X`-module `ℱ`, a finite family `𝓛_1, …, 𝓛_r`
of **invertible** `𝒪_Y`-modules and an arbitrary integer exponent vector `n`,

`R^q f_*(ℱ ⊗ (f^*𝓛_1)^{⊗ n_1} ⊗ ⋯ ⊗ (f^*𝓛_r)^{⊗ n_r})
  ≅ (R^q f_*ℱ) ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}`

for every integer `q`. This is `higherDirectImageTwistListIso` at `List.finRange r`, the list
`AlgebraicGeometry.twistedSheaf` folds over. -/
def higherDirectImageTwistedSheafIso (F : X.Modules) (n : Fin r → ℤ) (q : ℤ) :
    (higherDirectImageFunctor f q).obj
        (twistedSheaf F (fun j => (Scheme.Modules.pullback f).obj (L j)) n) ≅
      twistedSheaf ((higherDirectImageFunctor f q).obj F) L n :=
  higherDirectImageTwistListIso f L q n (List.finRange r) F

end Fold

end Stacks.ProjectionFormula

end
