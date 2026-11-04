module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPushforwardBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Direct images with vanishing higher cohomology

Let `f : X ⟶ S` be a morphism of schemes of finite presentation and let `ℱ` be an `𝒪_X`-module
of finite presentation, flat over `S`, whose support is proper over `S`. If `R ⁱ f_* ℱ = 0` for
all `i > 0` then [Stacks, Tag 0D4E] asserts two things: that `f_* ℱ` is finite locally free, and
that its formation commutes with arbitrary base change.

The second conclusion means that for a cartesian diagram

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical comparison map `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the mate of the two
pullback-pushforward adjunctions, is an isomorphism at `ℱ`.

## Main definitions

* `FlatFinitePresentationOfSingleDirectImage`: if `Rf_* ℱ` is a module `N` placed in degree `0`,
  then `N` is flat and of finite presentation ([Stacks, Tag 0A1H] and [Stacks, Tag 0658]).
* `OrdinaryBaseChangeOfTensorFlatBaseChange`: invertibility of the derived base-change map of
  [Stacks, Tag 0A1D] implies invertibility of the ordinary comparison `g^* f_* ℱ ⟶ f'_* (g')^* ℱ`.

## Main results

* `nonempty_iso_plus_singleFunctor_of_isZero_homology`: an object of `D⁺(C)` whose cohomology
  vanishes outside one degree is its cohomology there, placed in that degree, [Stacks, Tag 0118].
* `nonempty_iso_singleFunctor_pushforward`: if `R ⁱ f_* ℱ = 0` for all `i > 0`, then `Rf_* ℱ` is
  isomorphic in `D⁺(𝒪_S)` to `f_* ℱ` placed in degree `0`.

## Implementation notes

**Higher direct images.** `R ⁱ f_*` is
`(AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerivedPlus i`, the convention of
`StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic`, computed in the bounded below
derived categories of the Grothendieck abelian categories `X.Modules` and `S.Modules` under
`CategoryTheory.HasDerivedCategory.standard`. The object `Rf_* ℱ` is accordingly
`(Scheme.Modules.pushforward f).rightDerivedFunctorPlus` evaluated at `ℱ` placed in degree `0`.

## References

* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace Stacks.AlgebraicGeometry.VanishingHigherDirectImages

attribute [local instance] HasDerivedCategory.standard

/-! ### The degeneration of the derived direct image -/

section Degeneration

/-- An object of `D⁺(C)` whose cohomology vanishes outside degree `n` is isomorphic to its
degree-`n` cohomology placed in degree `n`, [Stacks, Tag 0118]. -/
theorem nonempty_iso_plus_singleFunctor_of_isZero_homology {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] (K : DerivedCategory.Plus C) (n : ℤ)
    (h : ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj K)) :
    Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor C n).obj
      ((DerivedCategory.Plus.homologyFunctor C n).obj K)) := by
  have : K.IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    exact fun i hi => h i (by lia)
  have : K.IsLE n := by
    rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
    exact fun i hi => h i (by lia)
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  exact ⟨e ≪≫ (DerivedCategory.Plus.singleFunctor C n).mapIso
    (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) n).app M).symm ≪≫
      ((DerivedCategory.Plus.homologyFunctor C n).mapIso e).symm)⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- If `R ⁱ f_* ℱ = 0` for all `i > 0`, then `Rf_* ℱ` is isomorphic in `D⁺(𝒪_S)` to `f_* ℱ`
placed in degree `0`. -/
theorem nonempty_iso_singleFunctor_pushforward
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj F)) := by
  obtain ⟨e⟩ := nonempty_iso_plus_singleFunctor_of_isZero_homology
    ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F)) 0
    fun i hi => (lt_or_gt_of_ne hi).elim
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F i) (hvanish i)
  exact ⟨e ≪≫ (DerivedCategory.Plus.singleFunctor S.Modules 0).mapIso
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso f F)⟩

end Degeneration

/-! ### Flatness and base change of the direct image -/

/-- Let `f : X ⟶ S` be a morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`, with support proper over `S`. If `Rf_* ℱ` is isomorphic in
`D⁺(𝒪_S)` to a module `N` placed in degree `0`, then `N` is flat and of finite presentation
([Stacks, Tag 0A1H] and [Stacks, Tag 0658]). -/
public def FlatFinitePresentationOfSingleDirectImage : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f),
    letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
    ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
    (∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X)) →
    ∀ N : S.Modules,
      Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
        (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N) →
      _root_.AlgebraicGeometry.SheafOfModules.IsFlat (C := Opens S.toTopCat)
          (J := Opens.grothendieckTopology S.toTopCat) (O := S.sheaf) N ∧
        N.IsFinitePresentation

/-- Let `f : X ⟶ S` be a morphism of finite presentation, let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `S`, with support proper over `S`, and suppose `R ⁱ f_* ℱ = 0` for
`i > 0`. If the base-change map
`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)` of [Stacks, Tag 0A1D] is
invertible for every `E` with quasi-coherent cohomology and every `𝒢^•` satisfying the
hypotheses of [Stacks, Tag 0A1H], then the ordinary comparison `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is
invertible. -/
public def OrdinaryBaseChangeOfTensorFlatBaseChange : Prop :=
  ∀ {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
        f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom),
    ∀ hf : FinitePresentation f,
    letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
    ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
      (∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X)) →
      (∀ i : ℤ, 0 < i →
        IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) →
      (∀ (E : DerivedCategory X.Modules) (G : CochainComplex X.Modules ℤ),
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent) →
        FlatProperSupportFinitelyPresented f G →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj
            (DerivedCategory.Q.obj G))).IsQuasicoherent) →
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
          (((derivedTensorProductFunctor X'.sheaf).obj
              ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
            (DerivedCategory.Q.obj
              ((pullbackComplex g'.toLRSHom.toShHom).obj G)))).IsQuasicoherent) →
        IsIso (tensorFlatBaseChangeMap f g f' g' sq E G)) →
      IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F)

end Stacks.AlgebraicGeometry.VanishingHigherDirectImages

end
