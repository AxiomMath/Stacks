module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Finite products of affine open subschemes, and affineness over a semi-separated base

This file supplies the two geometric inputs needed by the relative Čech complex of Stacks
Tag 01XL: the degree `p` term of that complex is indexed by `(p + 1)`-tuples of members of a
finite affine open cover, and the object attached to such a tuple is the product, in `Over X`,
of the corresponding `Over.mk (T.f i)`.  To know that the term is quasi-coherent one needs

* that the product is again affine, which is the hypothesis `IsAffineHom (pullback.diagonal
  (terminal.from X))` — affineness of the diagonal of `X`, equivalently affineness of
  intersections of affine opens of `X` (Mathlib's `AlgebraicGeometry.IsAffineOpen.iInf`); and
* that the structure morphism of that product, composed with `f : X ⟶ S`, is an *affine*
  morphism, which needs no hypothesis on `f` at all but only affineness of the diagonal of `S`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeCechComplex.isLimitOpenImmersionFan`: a finite family of
  objects of `Over X` whose structure morphisms are open immersions has a product, namely the
  intersection of their ranges with its inclusion.
* `Stacks.AlgebraicGeometry.RelativeCechComplex.isAffine_left_pi`: if moreover each member is
  affine, the family is nonempty and `X` has affine diagonal, then the underlying scheme of the
  product is affine.
* `Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source`: every morphism
  from an affine scheme to a scheme with affine diagonal is an affine morphism.

## Implementation notes

An object `A : Over X` whose structure morphism is a monomorphism is subterminal, so there is at
most one morphism into it from any object; `over_hom_unique` records this.  Taking the product's
vertex to be an *open subscheme* therefore discharges both the `fac` and the `uniq` field of
`Fan.IsLimit.mk` with no computation, which is why the fan is built at the intersection rather
than transported from an abstract product.

The lift of a fan into that vertex is factored out as `fanLift` with its type written out.  This
is not cosmetic: `Scheme.Opens` is a `def`, and inside the `Fan.IsLimit.mk` application the
instance `IsOpenImmersion (commonOpen V).ι` is *not* found, although the same instance is found
immediately when the expected type is stated.  Giving `fanLift` a signature supplies that
expected type.

`isAffineHom_of_isAffine_source` is the cancellation
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal` at `P = Q = @IsAffineHom`, applied to
the factorisation `g ≫ terminal.from S = terminal.from W`; `RespectsIso` and the stability of
`P.diagonal` under base change have to be named explicitly, because instance search does not
find them for the bare `@IsAffineHom`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechComplex

variable {X : Scheme.{u}}

/-! ### Subterminal objects of `Over X` -/

/-- An object of `Over X` whose structure morphism is a monomorphism is subterminal: any two
morphisms into it from the same object agree.  The monomorphism is an explicit hypothesis
rather than an instance argument, because at the vertex `Over.mk (commonOpen V).ι` below
instance search does not find it. -/
public theorem over_hom_unique {A Z : Over X} (hm : Mono A.hom) (h₁ h₂ : Z ⟶ A) : h₁ = h₂ := by
  have := hm
  exact Over.OverMorphism.ext ((cancel_mono A.hom).mp ((Over.w h₁).trans (Over.w h₂).symm))

/-- The range of the structure morphism of an object of `Over X` is contained in the range of
the structure morphism of any object it maps to. -/
public theorem range_comp_subset {Z A : Over X} (h : Z ⟶ A) :
    Set.range Z.hom ⊆ Set.range A.hom := by
  have e : ⇑Z.hom = ⇑A.hom ∘ ⇑h.left := by
    rw [← Over.w h, Scheme.Hom.comp_base]; rfl
  rw [e, Set.range_comp]
  exact Set.image_subset_range _ _

/-! ### The product of finitely many open subschemes -/

variable {α : Type} [Finite α] (V : α → Over X) [∀ a, IsOpenImmersion (V a).hom]

/-- The intersection of the ranges of the structure morphisms of a family of objects of
`Over X` whose structure morphisms are open immersions. -/
public abbrev commonOpen : X.Opens := ⨅ a, (V a).hom.opensRange

/-- The intersection of the ranges is contained in each of them. -/
public theorem commonOpen_range_subset (a : α) :
    Set.range (commonOpen V).ι ⊆ Set.range (V a).hom := by
  rw [Scheme.Opens.range_ι, commonOpen, TopologicalSpace.Opens.coe_iInf]
  exact Set.iInter_subset _ a

/-- The structure morphism of the vertex of a fan over the family has range inside the
intersection of the ranges. -/
public theorem subset_commonOpen_range (s : Fan V) :
    Set.range s.pt.hom ⊆ Set.range (commonOpen V).ι := by
  rw [Scheme.Opens.range_ι, commonOpen, TopologicalSpace.Opens.coe_iInf]
  exact Set.subset_iInter fun b ↦ range_comp_subset (s.proj b)

/-- The fan over the family with vertex the intersection of the ranges, the projections being
the factorisations of the inclusion through each member. -/
public noncomputable def openImmersionFan : Fan V :=
  Fan.mk (Over.mk (commonOpen V).ι) fun a ↦
    Over.homMk (IsOpenImmersion.lift (V a).hom _ (commonOpen_range_subset V a))
      (IsOpenImmersion.lift_fac _ _ _)

/-- The morphism from the vertex of an arbitrary fan to the vertex of `openImmersionFan`. -/
public noncomputable def fanLift (s : Fan V) : s.pt ⟶ Over.mk (commonOpen V).ι :=
  Over.homMk (IsOpenImmersion.lift (commonOpen V).ι s.pt.hom (subset_commonOpen_range V s))
    (IsOpenImmersion.lift_fac _ _ _)

/-- **The product in `Over X` of finitely many open subschemes is their intersection.**  Both
the factorisation and the uniqueness are instances of `over_hom_unique`, since every object
involved has a monomorphism as structure morphism. -/
public noncomputable def isLimitOpenImmersionFan : IsLimit (openImmersionFan V) :=
  Fan.IsLimit.mk _ (fanLift V) (fun _ _ ↦ over_hom_unique inferInstance _ _)
    (fun _ _ _ ↦ over_hom_unique (A := Over.mk (commonOpen V).ι)
      (inferInstanceAs (Mono (commonOpen V).ι)) _ _)

/-! ### Affineness of the product -/

/-- Over a scheme with affine diagonal, the intersection of the ranges of a nonempty finite
family of affine open immersions is affine. -/
public theorem isAffine_commonOpen [Nonempty α] [∀ a, IsAffine (V a).left]
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    IsAffine (commonOpen V).toScheme :=
  IsAffineOpen.iInf (fun a ↦ isAffineOpen_opensRange (V a).hom)

/-- **The underlying scheme of a finite product in `Over X` of affine open subschemes is
affine**, provided the family is nonempty and `X` has affine diagonal. -/
public theorem isAffine_left_pi [Nonempty α] [∀ a, IsAffine (V a).left]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [HasProduct V] :
    IsAffine (∏ᶜ V).left := by
  have e : (∏ᶜ V : Over X) ≅ Over.mk (commonOpen V).ι :=
    (limit.isLimit _).conePointUniqueUpToIso (isLimitOpenImmersionFan V)
  have h : IsAffine ((Over.forget X).obj (Over.mk (commonOpen V).ι)) :=
    isAffine_commonOpen V
  exact IsAffine.of_isIso ((Over.forget X).mapIso e).hom

/-! ### Affineness of a morphism out of an affine scheme -/

/-- **Every morphism from an affine scheme to a scheme with affine diagonal is affine.**  This
is the cancellation property of `@IsAffineHom` with respect to its own diagonal, applied to the
factorisation of `terminal.from W` through `g`. -/
public theorem isAffineHom_of_isAffine_source {W S : Scheme.{u}} [IsAffine W] (g : W ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from S))] : IsAffineHom g := by
  have hri : MorphismProperty.RespectsIso (@IsAffineHom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hdg : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.diagonal @IsAffineHom) :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  have hpost : MorphismProperty.HasOfPostcompProperty (@IsAffineHom)
      (MorphismProperty.diagonal @IsAffineHom) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  refine MorphismProperty.of_postcomp (W := @IsAffineHom)
    (W' := MorphismProperty.diagonal @IsAffineHom) g (terminal.from S) ‹_› ?_
  have h : g ≫ terminal.from S = terminal.from W := terminal.hom_ext _ _
  rw [h]
  infer_instance

end Stacks.AlgebraicGeometry.RelativeCechComplex
