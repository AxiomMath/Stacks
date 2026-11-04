module

public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesFlatness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct images with vanishing higher cohomology are locally free and commute with base change

Let `f : X ⟶ S` be a morphism of schemes of finite presentation and let `ℱ` be an `𝒪_X`-module
of finite presentation, flat over `S`, whose support is proper over `S`. If `R ⁱ f_* ℱ = 0` for
all `i > 0`, then [Stacks, Tag 0D4E] asserts that `f_* ℱ` is locally free and that its formation
commutes with arbitrary base change. The source's proof says what the second assertion means:
*commutation with base change means that `g^* f_* ℱ = f'_* (g')^* ℱ`* for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

that is, the canonical comparison `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` — the mate
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of the two pullback-pushforward
adjunctions — is an isomorphism at `ℱ`.

## Main results

* `isFiniteLocallyFree_pushforward_and_isIso_baseChange_of_isZero_higherDirectImage`:
  [Stacks, Tag 0D4E], both conclusions, with nothing granted.

## Implementation notes

The two conclusions are proved in
`StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImagesFlatness.lean`
(`isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage`: the perfection half of
[Stacks, Tag 0A1H], [More on Algebra, Tag 0658] and [Stacks, Tag 00NX]) and
`StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImagesBaseChange.lean`
(`isIso_baseChangeNatTrans_app_of_vanishing`: the base-change half of [Stacks, Tag 0A1H] read in
degree zero). The conditional statements of
`StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImages.lean` are superseded by the
theorem below, which carries no hypothesis beyond the source's.

"Locally free" is finite local freeness, `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`,
which is what the source's proof establishes (a finite projective module over each local ring,
[Stacks, Tag 00NX]). Proper support is read as containment of the support of `ℱ` in a closed
subset proper over `S`; the support of a module of finite presentation is closed, and a closed
subset of a closed subset proper over `S` is proper over `S`
(`AlgebraicGeometry.isProperOver_of_le`), so this is the source's condition.

## References

* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.VanishingHigherDirectImages

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0D4E].** Let `f : X ⟶ S` be a morphism of schemes of finite presentation and
let `ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`, whose support is proper over
`S`. If `R ⁱ f_* ℱ = 0` for all `i > 0`, then

1. `f_* ℱ` is a finite locally free `𝒪_S`-module, and
2. the formation of `f_* ℱ` commutes with arbitrary base change: for every cartesian square
   with `g' : X' ⟶ X`, `f' : X' ⟶ S'` and `g : S' ⟶ S`, the canonical comparison map
   `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` (`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`)
   is an isomorphism.

The first conclusion is `isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage`, the second
`isIso_baseChangeNatTrans_app_of_vanishing`. -/
@[stacks 0D4E "both conclusions: f_*F is finite locally free, and for every cartesian square the \
canonical comparison g^*f_*F --> f'_*(g')^*F (baseChangeNatTrans, the mate of the two \
pullback-pushforward adjunctions) is an isomorphism, which is the meaning the source's proof \
gives to `commutes with arbitrary base change`",
  ega "III 7.9.10" "partial",
  sga "6 III 5.7" "(iii), special case"]
public theorem isFiniteLocallyFree_pushforward_and_isIso_baseChange_of_isZero_higherDirectImage
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X))
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := S.ringCatSheaf) ((Scheme.Modules.pushforward f).obj F) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) :=
  ⟨isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage f hf F hflat hsupp hvanish,
    fun g f' g' hsq => isIso_baseChangeNatTrans_app_of_vanishing f g f' g' hsq hf F hflat hvanish⟩

end Stacks.AlgebraicGeometry.VanishingHigherDirectImages

end
