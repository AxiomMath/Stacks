module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the terms of the relative Čech complex

Let `f : X ⟶ S` be a morphism of schemes with `X` and `S` of affine diagonal, and let `T` be a
finite affine open cover of `X`.  This file proves the last assertion of Stacks Tag 01XL: every
term of the relative Čech complex of `T` is a quasi-coherent `𝒪_S`-module.

The degree `p` term is, for `p = n ≥ 0`, the product over the `(n + 1)`-tuples
`i : Fin (n + 1) → T.I₀` of `(a ≫ f)_* a^* F`, where `a` is the structure morphism of the
product `A` of the `Over.mk (T.f (i b))` in `Over X`; for `p < 0` it is a zero object.  Three
closure properties give the result:

* `a^* F` is quasi-coherent for an arbitrary morphism `a`, by Stacks 01BG;
* `A` is affine and hence `a ≫ f` is an affine morphism — this is where both affine-diagonal
  hypotheses enter, through `isAffine_left_pi` and `isAffineHom_of_isAffine_source` — so the
  direct image is quasi-coherent by Stacks 02KG;
* a finite product of quasi-coherent modules is quasi-coherent, and a zero module is
  quasi-coherent.

Note that no hypothesis whatsoever is placed on `f`: it is `S`, not `f`, that must have affine
diagonal, because the terms have *affine source*, and a morphism out of an affine scheme to a
scheme of affine diagonal is automatically affine.

## Main results

* `relativeCechComplex_obj_isQuasicoherent` is the assertion of the tag.
* `isQuasicoherent_presheaf_obj` is the affine-source case: the value of the coefficient
  presheaf at an object of `Over X` with affine source is quasi-coherent.
* `isQuasicoherent_cechComplex_X` is the `ℕ`-indexed statement, before the extension to `ℤ`.

## Implementation notes

The identification of the degree `n` term with a product is `cechComplex_X`, which holds by
`rfl`; so is the identification of the value of the coefficient presheaf with `(a ≫ f)_* a^* F`
(`RelativeCech.relativeCechPresheaf_obj_obj`).  Both are therefore used by `exact` rather than
by `rw`, which cannot cross the two spellings.

The instance arguments of `isAffine_left_pi` (open immersion and affineness of each member of
the family) are supplied by `have`s stated at the composite family `V ∘ i`: at the composite,
instance search does not reduce `((fun j ↦ Over.mk (T.f j)) ∘ i) a` far enough to see the
`Over.mk`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechComplex

open Stacks.AlgebraicGeometry.RelativeCech

variable {X S : Scheme.{u}}

/-- **The value of the coefficient presheaf at an object with affine source is
quasi-coherent.**  Pullback preserves quasi-coherence with no hypothesis (Stacks 01BG), and the
composite `A.hom ≫ f` is an affine morphism because its source is affine and `S` has affine
diagonal, so the direct image preserves quasi-coherence (Stacks 02KG). -/
public theorem isQuasicoherent_presheaf_obj (f : X ⟶ S) (A : Over X) [IsAffine A.left]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (((relativeCechPresheaf f).obj F).obj (op A)).IsQuasicoherent := by
  have haff : IsAffineHom (A.hom ≫ f) := isAffineHom_of_isAffine_source _
  have hpb : ((Scheme.Modules.pullback A.hom).obj F.obj).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback A.hom F.obj F.property
  exact AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom (A.hom ≫ f)
    ((Scheme.Modules.pullback A.hom).obj F.obj)

/-- **Every term of the `ℕ`-indexed relative Čech complex is quasi-coherent.**  The term is a
finite product of values of the coefficient presheaf on the `(n + 1)`-fold intersections, each
of which is affine because `X` has affine diagonal. -/
public theorem isQuasicoherent_cechComplex_X (f : X ⟶ S) (T : X.AffineOpenCover)
    [Finite T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℕ) :
    ((((CategoryTheory.cechComplexFunctor (fun i ↦ (Over.mk (T.f i) : Over X))).obj
        ((relativeCechPresheaf f).obj F))).X n).IsQuasicoherent := by
  have key : (∏ᶜ (fun (i : Fin (n + 1) → T.I₀) ↦
      ((relativeCechPresheaf f).obj F).obj
        (op (∏ᶜ (fun a ↦ (Over.mk (T.f (i a)) : Over X)))))).IsQuasicoherent := by
    refine MeromorphicQuasicoherent.isQuasicoherent_pi _ (fun i ↦ ?_)
    have hoi : ∀ a : Fin (n + 1), IsOpenImmersion (Over.mk (T.f (i a)) : Over X).hom :=
      fun a ↦ inferInstanceAs (IsOpenImmersion (T.f (i a)))
    have hfa : ∀ a : Fin (n + 1), IsAffine (Over.mk (T.f (i a)) : Over X).left :=
      fun a ↦ inferInstanceAs (IsAffine (Spec (T.X (i a))))
    have hA : IsAffine (∏ᶜ (fun a ↦ (Over.mk (T.f (i a)) : Over X))).left :=
      isAffine_left_pi _
    exact isQuasicoherent_presheaf_obj f _ F
  exact key

/-- **Stacks Project, Tag 01XL:** every term of the relative Čech complex of a finite affine
open cover is a quasi-coherent `𝒪_S`-module. -/
@[stacks 01XL "quasi-coherence of the terms", ega "III 1.4.9" "affine diagonal"]
public theorem relativeCechComplex_obj_isQuasicoherent (f : X ⟶ S) (T : X.AffineOpenCover)
    [Fintype T.I₀]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (p : ℤ) :
    (((relativeCechComplex f T).obj F).obj.X p).IsQuasicoherent := by
  rcases le_or_gt 0 p with hp | hp
  · lift p to ℕ using hp with n
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
        (i := n) (i' := (n : ℤ)) (by simp)).symm
      (isQuasicoherent_cechComplex_X f T F n)
  · exact HigherDirectImage.isQuasicoherent_of_isZero (R := S.ringCatSheaf)
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
        (fun i ↦ by simp only [ComplexShape.embeddingUpNat_f]; omega))

end Stacks.AlgebraicGeometry.RelativeCechComplex
