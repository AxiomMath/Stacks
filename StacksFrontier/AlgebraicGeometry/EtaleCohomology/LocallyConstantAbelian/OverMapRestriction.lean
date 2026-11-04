module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction of a constant sheaf along a morphism of the site

Let `J` be a Grothendieck topology on `C` and let `f : X ⟶ Y` be a morphism of `C`. Restriction of
sheaves along `Over.map f`, that is `CategoryTheory.GrothendieckTopology.overMapPullback`, is
pushforward along a functor which is both continuous and cocontinuous, so it commutes with
sheafification (`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`). Since
`Over.map f` pulls the constant presheaf on `Over Y` back to the constant presheaf on `Over X`,
restriction along `f` carries the constant sheaf with value `E` to the constant sheaf with the same
value `E`.

The consequence used downstream is that a *trivialization survives refinement*: if a sheaf on `C`
becomes constant with value `E` after restriction to `Y`, it becomes constant with the same value
`E` after restriction to any `X` lying over `Y`. Two sheaves which are individually locally
constant can therefore be trivialized over one and the same object, which is what Tag 093S needs.

Everything here is stated for an arbitrary coefficient category, the only hypothesis being the
existence of the pointwise right Kan extensions along `(Over.map f).op` which the cocontinuous
pushforward is built from. For `Ab.{w}` on a site `C : Type u` with `Category.{v} C` that holds as
soon as `UnivLE.{max u v, w}`.

## Main results

* `Stacks.ConstantSheaf.constantSheafOverMapIso` — restriction along `Over.map f` carries the
  constant sheaf with value `E` to the constant sheaf with value `E`.
* `Stacks.ConstantSheaf.constantSheafOverMapIso_unit` — the isomorphism is compatible with the
  constant section maps of the two constant sheaves.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{w'} A] [∀ U : C, HasWeakSheafify (J.over U) A]

/-- **Restriction of a constant sheaf along a morphism of the site is constant**, with the same
value. -/
def constantSheafOverMapIso {X Y : C} (f : X ⟶ Y)
    [∀ F : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F] (E : A) :
    (constantSheaf (J.over X) A).obj E ≅
      (J.overMapPullback A f).obj ((constantSheaf (J.over Y) A).obj E) :=
  ((Over.map f).pushforwardContinuousSheafificationCompatibility A (J.over X) (J.over Y)).app
    ((Functor.const (Over Y)ᵒᵖ).obj E)

/-- The isomorphism of `Stacks.ConstantSheaf.constantSheafOverMapIso` takes the constant section
map on `Over X` to the constant section map on `Over Y`, restricted along `Over.map f`. -/
lemma constantSheafOverMapIso_unit {X Y : C} (f : X ⟶ Y)
    [∀ F : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F] (E : A) :
    CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj E) ≫
        (constantSheafOverMapIso J A f E).hom.hom =
      Functor.whiskerLeft (Over.map f).op
        (CategoryTheory.toSheafify (J.over Y) ((Functor.const (Over Y)ᵒᵖ).obj E)) :=
  (Over.map f).toSheafify_pullbackSheafificationCompatibility A (J.over X) (J.over Y)
    ((Functor.const (Over Y)ᵒᵖ).obj E)

end Stacks.ConstantSheaf

end
