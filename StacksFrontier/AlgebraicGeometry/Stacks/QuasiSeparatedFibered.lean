module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Quasi-separated 1-morphisms of categories fibred in groupoids

Definition 04YW of the Stacks project calls a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
*quasi-separated* when its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is quasi-compact and
quasi-separated, and `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated` formalises it in
that generality. The two conditions on `Δ_f` are conditions of Stacks 04XB on a 1-morphism which is
representable by algebraic spaces, and for algebraic stacks the representability of `Δ_f` is
automatic (Stacks 04XS). Read with the representability made explicit, the definition makes sense
for an arbitrary 1-morphism of categories fibred in groupoids over the big fppf site of `S`, with
no algebraicity anywhere: `Δ_f` is representable by algebraic spaces, and every algebraic space
representing its base change along a scheme-valued point of the target is quasi-compact and
quasi-separated over that scheme.

This file states the definition in that generality and shows it agrees with Stacks 04YW for
1-morphisms of algebraic stacks. A 1-morphism of categories fibred in groupoids which is affine in
the sense of Stacks 04XB is quasi-compact and quasi-separated in that sense, so a 1-morphism whose
relative diagonal is representable by algebraic spaces and affine is quasi-separated.

## Main definitions

* `AlgebraicGeometry.Stack.IsFiberedQuasiSeparated`: a 1-morphism of categories fibred in groupoids
  is quasi-separated: its relative diagonal is representable by algebraic spaces, quasi-compact
  and quasi-separated.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompact_of_isAffineHom`,
  `AlgebraicGeometry.Stack.isQuasiSeparated_of_isAffineHom`: a 1-morphism of categories fibred in
  groupoids which is affine in the sense of Stacks 04XB is quasi-compact and quasi-separated in
  that sense.
* `AlgebraicGeometry.Stack.IsFiberedQuasiSeparated.of_isAffineHom_relativeDiagonal`: a 1-morphism
  whose relative diagonal is representable by algebraic spaces and affine is quasi-separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isFiberedQuasiSeparated`: for a
  1-morphism of algebraic stacks the two notions agree.

## Implementation notes

The categories fibred in groupoids are taken at the universes at which
`AlgebraicGeometry.Stack.relativeDiagonal` is formed, which include those of the stack of coherent
sheaves `Coh_{X/B}` of Stacks 08KB: its hom-sets live one universe above those of the site, so it
is not an object of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0DLZ](https://stacks.math.columbia.edu/tag/0DLZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Affine

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids which is affine in the sense of Stacks 04XB is
quasi-compact in that sense: an affine morphism of algebraic spaces is quasi-compact. -/
theorem isQuasiCompact_of_isAffineHom {f : 𝒳 ⟶ 𝒴} (hf : IsAffineHom B S hS f) :
    IsQuasiCompact B S hS f := fun U y hy F hF hrep =>
  Space.isQuasiCompact_of_isAffineHom' B S hS _ (ObjectProperty.FullSubcategory.property _)
    (ObjectProperty.FullSubcategory.property _) (hf U y hy F hF hrep)

/-- A 1-morphism of categories fibred in groupoids which is affine in the sense of Stacks 04XB is
quasi-separated in that sense: an affine morphism of algebraic spaces is quasi-separated. -/
theorem isQuasiSeparated_of_isAffineHom {f : 𝒳 ⟶ 𝒴} (hf : IsAffineHom B S hS f) :
    IsQuasiSeparated B S hS f := fun U y hy F hF hrep =>
  Space.isQuasiSeparated_of_isAffineHom B S hS _ (ObjectProperty.FullSubcategory.property _)
    (ObjectProperty.FullSubcategory.property _) (hf U y hy F hF hrep)

end Affine

section Fibered

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS)}

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` is
*quasi-separated* when its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is representable by
algebraic spaces and is quasi-compact and quasi-separated in the sense of Stacks 04XB. For a
1-morphism of algebraic stacks the first condition is automatic and this is Stacks 04YW, by
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isFiberedQuasiSeparated`. -/
def IsFiberedQuasiSeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom) ∧
    IsQuasiCompact B S hS (relativeDiagonal B S hS 𝒳 𝒴 f) ∧
    IsQuasiSeparated B S hS (relativeDiagonal B S hS 𝒳 𝒴 f)

variable {B S hS}

namespace IsFiberedQuasiSeparated

variable {f : 𝒳 ⟶ 𝒴}

/-- The relative diagonal of a quasi-separated 1-morphism is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces (hf : IsFiberedQuasiSeparated B S hS f) :
    IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom) :=
  hf.1

/-- The relative diagonal of a quasi-separated 1-morphism is quasi-compact. -/
theorem isQuasiCompact_relativeDiagonal (hf : IsFiberedQuasiSeparated B S hS f) :
    IsQuasiCompact B S hS (relativeDiagonal B S hS 𝒳 𝒴 f) :=
  hf.2.1

/-- The relative diagonal of a quasi-separated 1-morphism is quasi-separated. -/
theorem isQuasiSeparated_relativeDiagonal (hf : IsFiberedQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS (relativeDiagonal B S hS 𝒳 𝒴 f) :=
  hf.2.2

/-- A 1-morphism whose relative diagonal is representable by algebraic spaces, quasi-compact and
quasi-separated is quasi-separated. -/
theorem mk (hrep : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (hqc : IsQuasiCompact B S hS (relativeDiagonal B S hS 𝒳 𝒴 f))
    (hqs : IsQuasiSeparated B S hS (relativeDiagonal B S hS 𝒳 𝒴 f)) :
    IsFiberedQuasiSeparated B S hS f :=
  ⟨hrep, hqc, hqs⟩

/-- A 1-morphism whose relative diagonal is representable by algebraic spaces and affine in the
sense of Stacks 04XB is quasi-separated. -/
theorem of_isAffineHom_relativeDiagonal
    (hrep : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (haff : IsAffineHom B S hS (relativeDiagonal B S hS 𝒳 𝒴 f)) :
    IsFiberedQuasiSeparated B S hS f :=
  ⟨hrep, isQuasiCompact_of_isAffineHom B S hS haff, isQuasiSeparated_of_isAffineHom B S hS haff⟩

end IsFiberedQuasiSeparated

end Fibered

namespace AlgebraicStacks

variable {B S hS}

/-- For a 1-morphism of algebraic stacks, quasi-separatedness in the sense of Stacks 04YW is
quasi-separatedness of the underlying 1-morphism of categories fibred in groupoids: the relative
diagonal of a 1-morphism of algebraic stacks is representable by algebraic spaces (Stacks 04XS). -/
theorem isQuasiSeparated_iff_isFiberedQuasiSeparated {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S hS f ↔ IsFiberedQuasiSeparated.{u, u, u + 1} B S hS f.hom :=
  ⟨fun h => ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, h⟩,
    fun h => h.2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
