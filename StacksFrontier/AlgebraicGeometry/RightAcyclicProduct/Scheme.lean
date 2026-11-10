module

public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic

/-!
# Acyclicity of the terms of the absolute Čech resolution for a pushforward

Let `f : X ⟶ S` be a morphism of schemes with `X` and `S` of affine diagonal, let `T` be a
finite affine open cover of `X`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.  This file proves
that every term of the absolute Čech resolution `𝔠 ⁿ(𝒰, ℱ)` is right acyclic for `f_*`.

This is the hypothesis `∀ n, F.rightAcyclic (K.X n)` of Leray's acyclicity lemma
([Stacks, Tag 015E], `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`),
and it is the last of the three steps of the fourth label of [Stacks, Tag 01XL] that was a
*product* obstruction rather than mathematics: what is available independently of this file is
acyclicity of each **factor**
(`Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_relativeCechFactor`), and 015E consumes
the **term**.

## Main results

* `Stacks.RightAcyclicProduct.rightAcyclic_cechMonadPresheaf_obj`: the value at `A : Over X` of
  the absolute coefficient presheaf `A ↦ A.hom_* A.hom ^* ℱ` is right acyclic for `f_*` when
  `A.left` is affine.  This is `rightAcyclic_relativeCechFactor` restated at the presheaf.
* `Stacks.RightAcyclicProduct.rightAcyclic_absoluteCechComplex_X`: therefore so is every term of
  the Čech complex of a finite affine open cover.

## Implementation notes

**The coefficient presheaf used here is the absolute one, `(relativeMonad X).flip.obj ℱ`, and
not `relativeCechPresheaf (𝟙 X)`.** Both are the presheaf `A ↦ A.hom_* A.hom ^* ℱ` on `Over X`,
but the value of the second at `A` is `(A.hom ≫ 𝟙 X)_* A.hom ^* ℱ`, whose structure morphism is
not syntactically `A.hom`; crossing that would need a transport along `Category.comp_id` that the
flip of `Stacks.AlgebraicGeometry.RelativeCech.relativeMonad` makes unnecessary.  This matters
for the *source* category too: 015E asks for acyclicity of a complex in `X.Modules`, the source
of `f_*`, whereas `relativeCechPresheaf f` is valued in `S.Modules` — `f_*` has already been
applied to it, so the relative Čech complex is not the complex 015E consumes.  (It is
`Č ⁿ(𝒰, f, ℱ)`; identifying `f_*` of the complex below with it is a separate step, the third
step of the label, and is not done here.)

The proof is the acyclicity analogue of
`Stacks.AlgebraicGeometry.RelativeCechComplex.isQuasicoherent_cechComplex_X`, and the shape
transfers line for line: write the term as the `∏ᶜ` it definitionally is, apply the finite
product closure, and discharge each factor at an affine source.  The three `have`s before
`isAffine_left_pi` are stated at the composite family for the reason recorded in that file's
implementation notes: at a composite, instance search does not reduce
`((fun j ↦ Over.mk (T.f j)) ∘ i) a` far enough to see the `Over.mk`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.RightAcyclicProduct

open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.RelativeCechComplex

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

/-- **The value of the absolute coefficient presheaf at an object with affine source is right
acyclic for `f_*`.**  The presheaf is `A ↦ A.hom_* A.hom ^* ℱ`, the flip of the presheaf of
monads of [Stacks, Tag 01XL]; its value at `A` is `rfl`-equal to the factor handled by
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_relativeCechFactor`. -/
public theorem rightAcyclic_cechMonadPresheaf_obj (f : X ⟶ S) (A : Over X) [IsAffine A.left]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((relativeMonad X).flip.obj F.obj).obj (op A)) :=
  Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_relativeCechFactor f A F

/-- **Every term of the absolute Čech resolution of a finite affine open cover is right acyclic
for `f_*`.**  The degree `n` term is the product, over the `(n + 1)`-tuples
`i : Fin (n + 1) → T.I₀`, of the value of the absolute coefficient presheaf at the product `A` of
the `Over.mk (T.f (i a))` in `Over X`; that `A` has affine source because `X` has affine
diagonal, so each factor is acyclic by `rightAcyclic_cechMonadPresheaf_obj`, and
`rightAcyclic_pi` carries the conclusion across the product.

Together with the quasi-coherence of the same terms
(`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechComplex_obj_isQuasicoherent`, which
carries the quasi-coherence label of [Stacks, Tag 01XL]) this is the full input that Leray's
acyclicity lemma [Stacks, Tag 015E] asks of the complex.

No hypothesis is placed on `f`; as in the quasi-coherent analogue it is `S`, not `f`, that must
have affine diagonal, because the terms have affine source. -/
public theorem rightAcyclic_absoluteCechComplex_X (f : X ⟶ S) (T : X.AffineOpenCover)
    [Finite T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℕ) :
    (Scheme.Modules.pushforward f).rightAcyclic
      (((CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (T.f i) : Over X))).obj
        ((relativeMonad X).flip.obj F.obj)).X n) := by
  have key : (Scheme.Modules.pushforward f).rightAcyclic
      (∏ᶜ (fun (i : Fin (n + 1) → T.I₀) ↦
        ((relativeMonad X).flip.obj F.obj).obj
          (op (∏ᶜ (fun a ↦ (Over.mk (T.f (i a)) : Over X)))))) := by
    refine rightAcyclic_pi _ _ (fun i ↦ ?_)
    have hoi : ∀ a : Fin (n + 1), IsOpenImmersion (Over.mk (T.f (i a)) : Over X).hom :=
      fun a ↦ inferInstanceAs (IsOpenImmersion (T.f (i a)))
    have hfa : ∀ a : Fin (n + 1), IsAffine (Over.mk (T.f (i a)) : Over X).left :=
      fun a ↦ inferInstanceAs (IsAffine (Spec (T.X (i a))))
    have hA : IsAffine (∏ᶜ (fun a ↦ (Over.mk (T.f (i a)) : Over X))).left :=
      isAffine_left_pi _
    exact rightAcyclic_cechMonadPresheaf_obj f _ F
  exact key

end Stacks.RightAcyclicProduct

end
