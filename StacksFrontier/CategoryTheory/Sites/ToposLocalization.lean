module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization of a topos at a sheaf: the morphism of topoi `j_F`

Let `(C, J)` be a site and `F` a sheaf on it. Stacks 04GZ asserts that the slice `Sh(C)/F` is a
topos, and that there is a canonical morphism of topoi

```
  j_F : Sh(C)/F ⟶ Sh(C)
```

which is a *localization* in the sense of Section 7.25 (tag 00XZ), i.e. whose inverse image
`j_F⁻¹` sits in a triple of adjoints `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}`, with

1. `j_F⁻¹` the functor `H ↦ (H × F ⟶ F)`, and
2. `j_{F!}` the forgetful functor `(G ⟶ F) ↦ G`.

Both descriptions come out on the nose: `j_F⁻¹` is Mathlib's `CategoryTheory.toOver F`, whose
value at `H` is literally `Over.mk (snd H F : H ⊗ F ⟶ F)`, and the adjunction
`Over.forget F ⊣ toOver F` is `CategoryTheory.forgetAdjToOver`. The left exactness of `j_F⁻¹` is
free: `toOver F` is a right adjoint, so it preserves all limits.

That `Sh(C)/F` is a topos is the equivalence `Sh(C)/F ≌ Sh(C/F)` with the category of sheaves on
the site `C/F` of pairs `(U, s)`, `s ∈ F(U)`, whose coverings are those of `C`: this is Stacks 0791,
`Stacks.Topos.Localized.sheafEquivalence`. It plays the role of the source's change of sites
(03CI) followed by 00Y1. The pushforward `j_{F,*}` is constructed through it: `j : C/F ⥤ C` is
continuous and cocontinuous, so restriction along `j` has the right adjoint `j^s` (Mathlib's
`Functor.sheafAdjunctionCocontinuous`), and restriction along `j`, read in `Sh(C)/F`, is
`toOver F` since both are right adjoint to `Over.forget F`.

The site is small (`SmallCategory C`), as Stacks requires of sites (Remark 00VI): this is what
makes the right Kan extensions defining `j_{F,*}` exist in `Type u`.

`toOver F` is Mathlib's computable form of `Over.star F`, the functor used for `j_F⁻¹` in
Stacks 04IP; it is also the functor `j_F⁻¹` used in Stacks 04H0 and 04H1.

## Main results

In `StacksFrontier.CategoryTheory.Sites.ToposLocalizationSheaf`:

* `CategoryTheory.Sheaf.exists_over_equiv_sheaf` (Stacks 04GZ): `Sh(C)/F` is a topos, i.e. is
  equivalent to the category of sheaves of sets on a small site; the equivalence is
  `MorphismOfTopoi.sheafOverEquivalence`.
* `MorphismOfTopoi.sheafOverLocalization` (Stacks 04GZ): the localization morphism
  `j_F : Sh(C)/F ⟶ Sh(C)`, with `j_F⁻¹ = toOver F` and `j_{F,*}` the constructed
  `MorphismOfTopoi.overLocalizationPushforward`.
* `MorphismOfTopoi.sheafOverLocalization_inverseImage_obj` (Stacks 04GZ (1)) and
  `MorphismOfTopoi.sheafOverLocalizationShriek` (Stacks 04GZ (2)).
* `MorphismOfTopoi.sheafOverLocalization_isLocalization` (Stacks 04GZ): the triple of adjoints
  `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}`.

In this file:

* `MorphismOfTopoi.overLocalization`: the same morphism for any category `E` with finite products
  and an object `F`, given a right adjoint of `toOver F` (which a general such `E` need not have),
  with `overLocalization_inverseImage_obj` and `overLocalizationShriek`.

The `@[stacks 04GZ]` registrations are in `StacksFrontier.CategoryTheory.Sites.ToposLocalizationSheaf`.
-/

@[expose] public section

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
universe v u
variable {E : Type u} [Category.{v} E] [CartesianMonoidalCategory E]

/-- The localization morphism `j_F : E/F ⟶ E` at an object `F` of a category `E` with finite
products, given a right adjoint `p` of `toOver F`: the morphism of topoi whose inverse image is
`j_F⁻¹ = toOver F`, i.e. `H ↦ (H × F ⟶ F)`, and whose pushforward is `p`. For `E = Sh(C)` the
right adjoint is constructed in `sheafOverLocalization` (Stacks 04GZ). -/
@[simps inverseImage pushforward,
  sga "4 IV 5.5" "Y = terminal object", sga "4 IV 5.2" "(5.2.1)", sga "4 IV 3.1.3" "special case"]
def overLocalization (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) : MorphismOfTopoi (Over F) E
    where
  pushforward := p
  inverseImage := toOver F
  adj := adj
  preservesFiniteLimits :=
    haveI := (forgetAdjToOver F).rightAdjoint_preservesLimits
    ⟨fun _ _ _ => inferInstance⟩

/-- The inverse image of the localization morphism `overLocalization F adj` is the functor
`H ↦ (H × F / F)`, the object of `E/F` given by the projection `H × F ⟶ F`. -/
@[sga "4 IV 5.5" "Y terminal (f^* formula)", sga "4 IV 5.2" "b)"]
lemma overLocalization_inverseImage_obj (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) (H : E) :
    (overLocalization F adj).inverseImage.obj H = Over.mk (snd H F) :=
  rfl

/-- For `overLocalization F adj`, the forgetful functor `(G ⟶ F) ↦ G` is left adjoint to `j_F⁻¹`,
so that `Over.forget F ⊣ j_F⁻¹ ⊣ p`. -/
@[sga "4 IV 5.5" "Y terminal (f_! ⊣ f^*)", sga "4 IV 5.2" "a)"]
def overLocalizationShriek (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) :
    Over.forget F ⊣ (overLocalization F adj).inverseImage :=
  forgetAdjToOver F

end MorphismOfTopoi
