module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.AbsoluteAllModules
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.HypercoveringAllModules

/-!
# The absolute factor of the coefficient presheaf of [Stacks, Tag 01XN]

The coefficient presheaf `Stacks.AlgebraicGeometry.UniversalPushforward.pushforwardPresheafAll` of
the relative hypercovering complex sends an open `U` of `X` to the `𝒪_S`-module `(U.ι ≫ f)_* M|_U`.
Pushforward along a morphism of schemes is strictly functorial in this `Mathlib`, so that module is
`f_*` of the `𝒪_X`-module `(U.ι)_* M|_U`:  **the relative coefficient presheaf is the absolute one
followed by `f_*`**, on the nose.

This file records that factorisation and transports the identification of the absolute coefficient
presheaf with the Čech diagram of [Stacks, Tag 02FU] —
`Stacks.CechSiteChange.absOpensPresheafAllObjIso` — from the site of open sets of `X` to the opens
over the top open, which is the indexing category of the relative hypercovering complex.

## Main definitions

* `absCechPresheafAll`:  the absolute coefficient presheaf on the opens of `X` over the top open.
* `absCechPresheafAllObjIso`:  **the absolute coefficient presheaf is the Čech diagram of
  [Stacks, Tag 02FU]**, restricted along `CategoryTheory.Over.forget`.

## Main results

* `pushforwardPresheafAll_eq` and `pushforwardPresheafAll_obj_eq`:  **the coefficient presheaf of
  [Stacks, Tag 01XN] is the absolute one followed by `f_*`**, as an equality of functors and at a
  single module.
* `absCechPresheafAll_obj_eq`:  the absolute coefficient presheaf on the opens over the top open is
  the one on the opens of `X`, restricted along `CategoryTheory.Over.forget`.

## Implementation notes

`absCechPresheafAll` is defined with the single whiskering along `opensOverTop` rather than as
`absOpensPresheafAll` whiskered along `Over.forget`, because `pushforwardPresheafAll_eq` is then a
`rfl` that fits in the kernel's budget while with the other definition it is not.  The price is
`absCechPresheafAll_obj_eq`, which is in turn not a single affordable `rfl`; it is assembled from
`opensOverTop_op` and the generic `whiskeringLeft_obj_obj_comp`, both of which are `rfl`s between
functor categories with no module sheaves in them and therefore cost nothing.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.CechSiteChange

universe u

namespace Stacks.AlgebraicGeometry.UniversalPushforward

/-- **Precomposing a functor with a composite is precomposing twice.**  Stated generically so that
its `rfl` is checked away from the heavy categories it is used at. -/
theorem whiskeringLeft_obj_obj_comp {J J' J'' A : Type*} [Category J] [Category J']
    [Category J''] [Category A] (F : J ⥤ A) (H : J' ⥤ J) (H' : J'' ⥤ J') :
    ((Functor.whiskeringLeft J'' J A).obj (H' ⋙ H)).obj F =
      H' ⋙ ((Functor.whiskeringLeft J' J A).obj H).obj F :=
  rfl

variable {X S : Scheme.{u}}

/-- The opens of `X` over the top open sit over `X` through the opens of `X`. -/
theorem opensOverTop_op (X : Scheme.{u}) :
    (opensOverTop X).op = (Over.forget (⊤ : Opens X)).op ⋙ (opensOver X).op :=
  rfl

/-- **The absolute coefficient presheaf of [Stacks, Tag 01XL] on the opens of `X` over the top
open**:  an object `A` of `Over (⊤ : Opens X)` goes to the `𝒪_X`-module `(A.left.ι)_* M|_{A.left}`.
This is the absolute factor of
`Stacks.AlgebraicGeometry.UniversalPushforward.pushforwardPresheafAll`. -/
noncomputable def absCechPresheafAll (X : Scheme.{u}) :
    X.Modules ⥤ ((Over (⊤ : Opens X))ᵒᵖ ⥤ X.Modules) :=
  (relativeMonad X).flip ⋙
    (Functor.whiskeringLeft (Over (⊤ : Opens X))ᵒᵖ (Over X)ᵒᵖ X.Modules).obj
      (opensOverTop X).op

/-- The value of the absolute coefficient presheaf is the direct image of the inverse image along
the inclusion of the open set. -/
theorem absCechPresheafAll_obj_obj (M : X.Modules) (A : Over (⊤ : Opens X)) :
    ((absCechPresheafAll X).obj M).obj (op A) =
      (pushforward (Scheme.Opens.ι (X := X) A.left)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) A.left)).obj M) :=
  rfl

/-- **The absolute coefficient presheaf on the opens over the top open is the one on the opens of
`X`**, restricted along `CategoryTheory.Over.forget`. -/
theorem absCechPresheafAll_obj_eq (M : X.Modules) :
    (absCechPresheafAll X).obj M =
      (Over.forget (⊤ : Opens X)).op ⋙ (absOpensPresheafAll X).obj M :=
  (congrArg
      (fun H ↦ ((Functor.whiskeringLeft (Over (⊤ : Opens X))ᵒᵖ (Over X)ᵒᵖ X.Modules).obj H).obj
        ((relativeMonad X).flip.obj M))
      (opensOverTop_op X)).trans
    (whiskeringLeft_obj_obj_comp ((relativeMonad X).flip.obj M) (opensOver X).op
      (Over.forget (⊤ : Opens X)).op)

/-- **At an arbitrary `𝒪_X`-module, the absolute coefficient presheaf of [Stacks, Tag 01XL] on the
opens over the top open is the Čech diagram of [Stacks, Tag 02FU]**:
`(A.left.ι)_* (A.left.ι)^* M ≅ M(· ⊓ A.left)`, naturally in `A`. -/
noncomputable def absCechPresheafAllObjIso (X : Scheme.{u}) (M : X.Modules) :
    (absCechPresheafAll X).obj M ≅
      (Over.forget (⊤ : Opens X)).op ⋙ (cechDiagramOpens X).obj M :=
  eqToIso (absCechPresheafAll_obj_eq M) ≪≫
    Functor.isoWhiskerLeft (Over.forget (⊤ : Opens X)).op (absOpensPresheafAllObjIso X M)

/-- **The coefficient presheaf of [Stacks, Tag 01XN] is the absolute one followed by the direct
image along `f`.**  Pushforward is strictly functorial, so `(U.ι ≫ f)_* M|_U` is `f_*` of
`(U.ι)_* M|_U` on the nose. -/
theorem pushforwardPresheafAll_eq (f : X ⟶ S) :
    pushforwardPresheafAll f =
      absCechPresheafAll X ⋙
        (Functor.whiskeringRight (Over (⊤ : Opens X))ᵒᵖ X.Modules S.Modules).obj
          (pushforward f) :=
  rfl

/-- `pushforwardPresheafAll_eq` at a single module. -/
theorem pushforwardPresheafAll_obj_eq (f : X ⟶ S) (M : X.Modules) :
    (pushforwardPresheafAll f).obj M = (absCechPresheafAll X).obj M ⋙ pushforward f :=
  congrArg (fun F ↦ F.obj M) (pushforwardPresheafAll_eq f)

end Stacks.AlgebraicGeometry.UniversalPushforward

end
