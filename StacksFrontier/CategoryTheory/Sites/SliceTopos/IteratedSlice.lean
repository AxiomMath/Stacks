module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import StacksCore.Tactic.EgaSgaAttribute

/-! # Relocalization of a topos: localizing `Sh(C)/F` at an object `G/F`

Let `E` be a topos (in this file: any category with pullbacks) and let `s : G ⟶ F` be a
morphism of `E`.  Stacks 04IR asserts that the localization `j` of the topos `E/F` at the
object `G/F` fits into a commutative triangle
```
  E/G --j--> E/F --j_F--> E ,     j_G = j_F ∘ j
```
that `j⁻¹` is base change along `s`, and that `j_!` is postcomposition with `s`.

The two localization morphisms are carried by `Over.forgetAdjStar`, so `j_{F!} = Over.forget F`
and `j_F⁻¹ = Over.star F`.  The triangle for the lower shrieks,
`Over.map s ⋙ Over.forget F = Over.forget G`, is `CategoryTheory.Over.mapForget_eq`, and
`j_! = Over.map s` (i.e. `j_!(E ⟶ G) = (E ⟶ G ⟶ F)`) is `comp_forget_eq_forget` together with
`map_eq_forget_iteratedSlice` of Stacks 03EH; nothing below repeats them.

## Main results

* `starIteratedSliceForwardIsoPullback`: the inverse image of the localization of `E/F` at the
  object `G/F` is base change along `s`, i.e. `j⁻¹(H ⟶ F) = (H ×_F G ⟶ G)`.  This is what
  identifies the abstract localization of the topos `E/F` at `G/F` with the concrete slice `E/G`.
* `pushforwardIsoCompPushforward`: `j_{G,*} = j_{F,*} ∘ j_*`, obtained from
  `Over.starPullbackIsoStar` (`j_G⁻¹ = j⁻¹ ∘ j_F⁻¹`) by uniqueness of right adjoints.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

-- `E/F` has binary products as soon as `E` has pullbacks; this is what makes `Over.star`
-- available on the slice, and hence what lets `E/F` be localized at one of its objects.
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {E : Type u} [Category.{v} E] {F G : E} (s : G ⟶ F)

/-- Let `s : G ⟶ F` be a morphism of a topos `E` and write `G/F` for the corresponding object of
the slice topos `E/F`.  Localizing `E/F` at `G/F` produces the morphism of topoi whose inverse
image is `Over.star (Over.mk s)`; transporting it along the iterated slice equivalence
`(E/F)/(G/F) ≌ E/G` identifies it with base change along `s`:
```
j⁻¹(H ⟶ F) = (H ×_F G ⟶ G).
```
Together with `map_eq_forget_iteratedSlice` (Stacks 03EH), which identifies the corresponding
lower shriek with `Over.map s`, this is the assertion that `j` is the localization of `E/F` at
`G/F`. -/
@[stacks 04IR "j = j_{G/F} and j^{-1}(H → F) = (H ×_F G → G)", sga "7 VII 2.0" "partial"]
noncomputable def starIteratedSliceForwardIsoPullback [HasPullbacks E] :
    Over.star (Over.mk s) ⋙ (Over.mk s).iteratedSliceForward ≅ Over.pullback s :=
  conjugateIsoEquiv
    ((Over.mk s).iteratedSliceEquiv.symm.toAdjunction.comp (Over.forgetAdjStar (Over.mk s)))
    (Over.mapPullbackAdj s)
    (eqToIso (Over.iteratedSliceBackward_forget (Over.mk s)).symm)

/-- The pushforwards of the localizations satisfy `j_{G,*} = j_{F,*} ∘ j_*`.

The inverse images satisfy `j_G⁻¹ = j⁻¹ ∘ j_F⁻¹`, which is `Over.starPullbackIsoStar`; passing
to right adjoints turns this into the stated identity between the pushforwards.  The three
pushforwards are given as data, since a general category with pullbacks and binary products
need not have them (in a topos they exist, by Stacks 04GZ). -/
@[stacks 04IR "j_{G,*} = j_{F,*} ∘ j_*"]
noncomputable def pushforwardIsoCompPushforward [HasPullbacks E] [HasBinaryProducts E]
    {pF : Over F ⥤ E} {pG : Over G ⥤ E} {p : Over G ⥤ Over F}
    (adjF : Over.star F ⊣ pF) (adjG : Over.star G ⊣ pG) (adj : Over.pullback s ⊣ p) :
    pG ≅ p ⋙ pF :=
  Adjunction.rightAdjointUniq adjG ((adjF.comp adj).ofNatIsoLeft (Over.starPullbackIsoStar s))

end CategoryTheory
