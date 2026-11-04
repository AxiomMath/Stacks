module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization of a topos at a sheaf: the morphism of topoi `j_F`

Let `E` be a topos and `F` an object of `E` (in Stacks 04GZ, `E = Sh(C)` and `F` is a sheaf on the
site `C`).  The localization of `E` at `F` is the slice category `E/F`, and Stacks 04GZ asserts
that the canonical morphism of topoi

```
  j_F : E/F ⟶ E
```

is a *localization* in the sense of Section 7.25 (tag 00XZ), i.e. that its inverse image
`j_F⁻¹` sits in a triple of adjoints `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}`, together with the two
descriptions

1. `j_F⁻¹` is the functor `H ↦ (H × F ⟶ F)`, and
2. `j_{F!}` is the forgetful functor `(G ⟶ F) ↦ G`.

Both descriptions come out on the nose here: `j_F⁻¹` is Mathlib's `CategoryTheory.toOver F`,
whose value at `H` is literally `Over.mk (snd H F : H ⊗ F ⟶ F)`, and the adjunction
`Over.forget F ⊣ toOver F` making `Over.forget F` the lower shriek is
`CategoryTheory.forgetAdjToOver`.  The left exactness of `j_F⁻¹`, which is what makes the
adjoint pair `j_F⁻¹ ⊣ j_{F,*}` a morphism of topoi, is free: `toOver F` is a right adjoint, so
it preserves all limits.

`toOver F` is Mathlib's computable form of `Over.star F`, the functor used for `j_F⁻¹` in
Stacks 04IP; it is also the functor `j_F⁻¹` used in Stacks 04H0 and 04H1.

## Main results

* `MorphismOfTopoi.overLocalization` (Stacks 04GZ): the localization morphism
  `j_F : E/F ⟶ E`, as a morphism of topoi, with `j_F⁻¹ = toOver F`.
* `MorphismOfTopoi.overLocalization_inverseImage_obj` (Stacks 04GZ (1)): `j_F⁻¹` is
  `H ↦ (H × F ⟶ F)`.
* `MorphismOfTopoi.overLocalizationShriek` (Stacks 04GZ (2)): `j_{F!}` is the forgetful
  functor, i.e. `Over.forget F` is left adjoint to `j_F⁻¹`.

One assertion of Stacks 04GZ is *not* covered: that `E/F` is again a topos, i.e. that it is
equivalent to `Sh(D)` for some site `D`.  Stacks proves this by changing sites (Lemma 03CI) so
that `F` becomes a representable `h_U^#` and then invoking the equivalence
`Sh(C/U) ≌ Sh(C)/h_U^#` of Lemma 00Y1.

Of those two ingredients, 00Y1 is available as `CategoryTheory.OverShriek.sheafEquivalence`, but
03CI is not, and it is the one that does the work here: 00Y1 supplies exactly the *representable*
case `F = h_U^#`, while for general `F` there is no `Sh(C)/F ≌ Sh(D)` without the change of sites.
Independently, the library has no predicate "is a topos" against which the assertion could be
stated at all. The statements below are about a morphism of topoi out of the slice category
`E/F`.

The pushforward `j_{F,*}` is taken as data, as in Stacks 04H0 and 04IR: a general category with
finite products need not have a right adjoint to `toOver F` (in a topos it does, by local
cartesian closedness).

Tags covered: 04GZ.
-/

@[expose] public section

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
universe v u
variable {E : Type u} [Category.{v} E] [CartesianMonoidalCategory E]

/-- **Stacks 04GZ.** Let `E` be a topos and `F` an object of `E`.  The localization morphism
`j_F : E/F ⟶ E` is the morphism of topoi whose inverse image is `j_F⁻¹ = toOver F`, i.e.
`H ↦ (H × F ⟶ F)`, and whose pushforward `j_{F,*}` is a right adjoint of it. -/
@[stacks 04GZ "the morphism of topoi j_F, and its inverse image",
  simps inverseImage pushforward,
  sga "4 IV 5.5" "Y = terminal object", sga "4 IV 5.2" "(5.2.1)", sga "4 IV 3.1.3" "special case"]
def overLocalization (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) : MorphismOfTopoi (Over F) E
    where
  pushforward := p
  inverseImage := toOver F
  adj := adj
  preservesFiniteLimits :=
    haveI := (forgetAdjToOver F).rightAdjoint_preservesLimits
    ⟨fun _ _ _ => inferInstance⟩

/-- **Stacks 04GZ (1).** The inverse image of the localization morphism `j_F` is the functor
`H ↦ (H × F / F)`, the object of `E/F` given by the projection `H × F ⟶ F`. -/
@[stacks 04GZ "(1): the functor j_F^{-1} is H ↦ H × F / F",
  sga "4 IV 5.5" "Y terminal (f^* formula)", sga "4 IV 5.2" "b)"]
lemma overLocalization_inverseImage_obj (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) (H : E) :
    (overLocalization F adj).inverseImage.obj H = Over.mk (snd H F) :=
  rfl

/-- **Stacks 04GZ (2).** The functor `j_{F!}` is the forgetful functor `(G ⟶ F) ↦ G`: it is
left adjoint to `j_F⁻¹`, so that `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}` and `j_F` is a localization in the
sense of Section 7.25 (tag 00XZ). -/
@[stacks 04GZ "(2): the functor j_{F!} is the forgetful functor G/F ↦ G",
  sga "4 IV 5.5" "Y terminal (f_! ⊣ f^*)", sga "4 IV 5.2" "a)"]
def overLocalizationShriek (F : E) {p : Over F ⥤ E} (adj : toOver F ⊣ p) :
    Over.forget F ⊣ (overLocalization F adj).inverseImage :=
  forgetAdjToOver F

end MorphismOfTopoi
