module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic

/-!
# The relative Čech complex of a finite affine open cover

Let `f : X ⟶ S` be a morphism of schemes and let `T` be a finite affine open cover of `X`.
Tag 01XL forms the alternating Čech complex of the coefficient presheaf
`Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf` of `f` with respect to the
family `Over.mk (T.f i)` in `Over X`, and regards it as a bounded-below complex of
`𝒪_S`-modules.  Its degree `p` term is the product, over the `(p + 1)`-tuples `i : Fin (p + 1) →
T.I₀`, of the value of the coefficient presheaf on the product of the `Over.mk (T.f (i a))`,
i.e. of `f_{i₀ … i_p *} F|_{U_{i₀ … i_p}}`.

## Main definitions

* `relativeCechComplex`: the relative Čech complex of `T`, as a functor from quasi-coherent
  `𝒪_X`-modules to bounded-below cochain complexes of `𝒪_S`-modules.

## Main results

* `relativeCechComplex_obj_obj`: the underlying `ℤ`-indexed complex is the extension, along
  `ComplexShape.embeddingUpNat`, of Mathlib's `ℕ`-indexed Čech complex.
* `cechComplex_X`: the degree `n` term of that `ℕ`-indexed complex is the product over
  `(n + 1)`-tuples of indices of the values of the presheaf on the intersections.

## Implementation notes

Mathlib's `CategoryTheory.cechComplexFunctor` already supplies the alternating differential, and
needs `HasFiniteProducts (Over X)`, which holds because `Scheme` has finite limits; the
intersections `U_{i₀ … i_p}` are literally the products of the `Over.mk (T.f i)` in `Over X`.
`CochainComplex.plus` membership is witnessed at `0` by Mathlib's instance for the extension of
an `ℕ`-indexed complex, which is why the bound is produced by `infer_instance` after a `change`
that spells the extension out.

The index type `T.I₀` is forced into `Type u` by the elaborator: `cechComplexFunctor` demands
`HasProducts.{w} S.Modules` for `w` the universe of the index type, and `S.Modules` has products
of size `u` only.  So this definition, like the tagged statement it realises, is about covers
indexed in `Type u`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechComplex

open Stacks.AlgebraicGeometry.RelativeCech

variable {X S : Scheme.{u}}

/-- **The bounded-below relative Čech complex of a finite affine open cover (Stacks 01XL).**
The alternating Čech complex, for the family `Over.mk (T.f i)` in `Over X`, of the coefficient
presheaf of `f`, extended from `ℕ`-indexing to `ℤ`-indexing and regarded as a bounded-below
complex. -/
@[stacks 01XL "the complex"]
public noncomputable def relativeCechComplex (f : X ⟶ S) (T : X.AffineOpenCover)
    [Fintype T.I₀] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      CochainComplex.Plus S.Modules :=
  ObjectProperty.lift _
    (relativeCechPresheaf f ⋙
      CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ⋙
      ComplexShape.embeddingUpNat.extendFunctor S.Modules)
    (fun F ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE
        (((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj
          ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat) 0
      infer_instance⟩)

/-- The underlying `ℤ`-indexed complex of the relative Čech complex is the extension of
Mathlib's `ℕ`-indexed Čech complex along `ComplexShape.embeddingUpNat`. -/
public theorem relativeCechComplex_obj_obj (f : X ⟶ S) (T : X.AffineOpenCover) [Fintype T.I₀]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((relativeCechComplex f T).obj F).obj
      = ((CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))).obj
          ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat := rfl

/-- The degree `n` term of Mathlib's Čech complex of a presheaf on `Over X` is the product,
over the `(n + 1)`-tuples of indices, of the values of the presheaf on the products of the
corresponding members of the family. -/
public theorem cechComplex_X {ι : Type u} (U : ι → Over X) (P : (Over X)ᵒᵖ ⥤ S.Modules)
    (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj P).X n
      = ∏ᶜ (fun (i : Fin (n + 1) → ι) ↦ P.obj (op (∏ᶜ (U ∘ i)))) := rfl

end Stacks.AlgebraicGeometry.RelativeCechComplex
