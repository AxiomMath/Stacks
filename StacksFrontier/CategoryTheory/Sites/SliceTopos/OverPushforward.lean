module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localizing a morphism of topoi at a sheaf and its inverse image

Let `f : E ⟶ D` be a morphism of topoi, let `G` be an object of `D` and put `F = f⁻¹G`.  Stacks
04H1 produces a morphism of topoi `f' : E/F ⟶ D/G` fitting in a commutative square with the two
localization morphisms `j_F : E/F ⟶ E` and `j_G : D/G ⟶ D`, characterized by
`(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ F)`, and satisfying `f'_* ∘ j_F⁻¹ = j_G⁻¹ ∘ f_*`.

The characterizing property *is* Mathlib's `CategoryTheory.Over.post`, so `f'` is built by taking
`(f')⁻¹ = Over.post f⁻¹`; its right adjoint is then `Over.postAdjunctionLeft`, and it is left
exact because `Over.post` of a left exact functor is left exact.  The localization morphisms are
carried by `CategoryTheory.forgetAdjToOver`, so `j_{F!} = Over.forget F` and `j_F⁻¹ = toOver F`
(Mathlib's computable form of `Over.star F`, the functor used in Stacks 04IP).

The commutativity of the square is recorded twice, matching the two ways Stacks uses it: on
inverse images, where it is the statement that `f⁻¹` turns a product with `G` into a product with
`F`; and on the pushforwards, which is the displayed identity `f'_* j_F⁻¹ = j_G⁻¹ f_*`.  The third
face, `(f')⁻¹ ⋙ j_{F!} = j_{G!} ⋙ f⁻¹`, is Mathlib's `Over.post_forget_eq_forget_comp` and holds
on the nose.

## Main results

* `MorphismOfTopoi.over` (Stacks 04H1): the morphism of topoi `f' : E/F ⟶ D/G`, with
  `(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ F)` by construction.
* `MorphismOfTopoi.inverseImageCompToOverIso` (Stacks 04H1): `j_F⁻¹ ∘ f⁻¹ = (f')⁻¹ ∘ j_G⁻¹`, the
  commutativity of the square on inverse images.
* `MorphismOfTopoi.toOverCompPushforwardIso` (Stacks 04H1): `f'_* ∘ j_F⁻¹ = j_G⁻¹ ∘ f_*`.

Tags covered: 04H1.
-/

@[expose] public section

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe v v' u u'

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]
  (f : MorphismOfTopoi E D) (G : D) [HasPullbacks D]

/-- **Stacks 04H1.** Let `f : E ⟶ D` be a morphism of topoi and `G` an object of `D`.  Localizing
`E` at `F = f⁻¹G` and `D` at `G` gives a morphism of topoi `f' : E/F ⟶ D/G` whose inverse image
is `Over.post f⁻¹`, i.e.
```
(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ f⁻¹G) ,
```
which is the property characterizing `f'`.  Its pushforward is
`(K ⟶ F) ↦ (f_*K ×_{f_*f⁻¹G} G ⟶ G)`, the right adjoint supplied by
`CategoryTheory.Over.postAdjunctionLeft`, and its inverse image is left exact because `f⁻¹` is. -/
@[simps inverseImage pushforward,
  stacks 04H1 "the morphism f' and the description of (f')⁻¹",
  sga "4 V 5.1"]
noncomputable def over : MorphismOfTopoi (Over (f.inverseImage.obj G)) (Over G) :=
  haveI := f.preservesFiniteLimits
  { inverseImage := Over.post f.inverseImage
    pushforward := Over.post f.pushforward ⋙ Over.pullback (f.adj.unit.app G)
    adj := Over.postAdjunctionLeft f.adj
    preservesFiniteLimits := inferInstance }

variable [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- **Stacks 04H1**, commutativity of the square on inverse images: `j_F⁻¹ ∘ f⁻¹ = (f')⁻¹ ∘ j_G⁻¹`,
where `j_G⁻¹ = toOver G` and `j_F⁻¹ = toOver (f⁻¹G)`.  Concretely, `f⁻¹` carries the product
`H ⊗ G` over `G` to the product `f⁻¹H ⊗ f⁻¹G` over `f⁻¹G`; this is where the left exactness of
`f⁻¹` enters. -/
@[stacks 04H1 "commutativity of the square, on inverse images"]
noncomputable def inverseImageCompToOverIso :
    f.inverseImage ⋙ toOver (f.inverseImage.obj G) ≅ toOver G ⋙ (f.over G).inverseImage :=
  haveI := f.preservesFiniteLimits
  letI : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f.inverseImage
  NatIso.ofComponents
    (fun H => Over.isoMk (Functor.Monoidal.μIso f.inverseImage H G)
      (Functor.Monoidal.μ_snd f.inverseImage H G))
    (fun g => Over.OverMorphism.ext
      (Functor.LaxMonoidal.μ_natural_left f.inverseImage g G))

/-- **Stacks 04H1**: `f'_* ∘ j_F⁻¹ = j_G⁻¹ ∘ f_*`.

Both sides are right adjoints — of `(f')⁻¹ ⋙ j_{F!}` and of `j_{G!} ⋙ f⁻¹` respectively — and
those two left adjoints are equal on the nose by `Over.post_forget_eq_forget_comp`, so the
identity follows from uniqueness of right adjoints. -/
@[stacks 04H1 "f'_* j_F^{-1} = j_G^{-1} f_*"]
noncomputable def toOverCompPushforwardIso :
    toOver (f.inverseImage.obj G) ⋙ (f.over G).pushforward ≅ f.pushforward ⋙ toOver G :=
  Adjunction.rightAdjointUniq
    (Over.post_forget_eq_forget_comp f.inverseImage G ▸
      (f.over G).adj.comp (forgetAdjToOver (f.inverseImage.obj G)))
    ((forgetAdjToOver G).comp f.adj)

end MorphismOfTopoi
