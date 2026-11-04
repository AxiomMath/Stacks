module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Composition of the separation axioms for morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Both separation axioms of Stacks 0ARN are
conditions on the relative diagonal — that it be a closed immersion, respectively that it be
quasi-compact — and both are stable under composition, because the relative diagonal of `f ≫ g`
factors as the relative diagonal of `f` followed by the comparison `X ×_Y X ⟶ X ×_Z X` of the
two relative self-products, and that comparison is a base change of the relative diagonal
of `g`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasRelativeDiagonal_comp`: **Stacks 0ARR** in the uniform
  shape of the two axioms of Stacks 0ARN, for a property `P` of morphisms of schemes which is
  stable under composition: a relative diagonal condition for `P` is stable under composition
  of morphisms of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_comp`: **Stacks 0ARR** for the
  separatedness axiom, a composite of separated morphisms is separated.
* `AlgebraicGeometry.FormalSpace.hasRelativeDiagonal_quasiCompact_comp`: **Stacks 0ARR** for
  the quasi-separatedness axiom, read as the relative diagonal condition for quasi-compact
  morphisms of schemes.

## Implementation notes

The factorisation of the relative diagonal of a composite is pure category theory and is
recorded here for an arbitrary category with fibre products; the comparison is Mathlib's
`CategoryTheory.Limits.pullback.mapDesc`. That the comparison is a base change of
the relative diagonal of the second morphism is the magic diagram
`AlgebraicGeometry.FormalSpace.isPullback_mapDesc`, so the second factor inherits the relative
diagonal condition from `g` with no hypothesis on `f`; this is the content of Stacks 0ARQ.

The separatedness clause is proved directly from the library's own notions rather than through
the uniform form: the second factor is a closed immersion by **Stacks 0ARQ, part (2)**, which
is `AlgebraicGeometry.FormalSpace.isClosedImmersion_mapDesc`, and closed immersions of formal
algebraic spaces compose by **Stacks 0GHW**, which is
`AlgebraicGeometry.FormalSpace.isClosedImmersion_comp`. This keeps the clause stated for
`AlgebraicGeometry.FormalSpace.IsSeparatedMorphism`, the definition carrying the tag of
Stacks 0ARN, part (1).

The quasi-separatedness clause is stated for the relative diagonal condition attached to
quasi-compactness of morphisms of schemes, which is the second of the two cases that the
implementation notes of `StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism` identify
as the axioms of Stacks 0ARN in uniform form. It is *not* stated for
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism`, whose quasi-compactness is
`AlgebraicGeometry.Space.IsQuasiCompactULift`, tested against quasi-compact algebraic spaces
rather than against schemes of the site: the composition law for that condition,
`AlgebraicGeometry.Space.isQuasiCompactULift_comp`, needs its middle and final objects to be
algebraic spaces, and here they are the relative self-products `X ×_Y X` and `X ×_Z X`, which
are only formal algebraic spaces. The other half of the argument is available for that
condition, as `AlgebraicGeometry.FormalSpace.isQuasiCompactULift_mapDesc`.

## References

* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARQ](https://stacks.math.columbia.edu/tag/0ARQ)
* [Stacks Project, Tag 0ARR](https://stacks.math.columbia.edu/tag/0ARR)
* [Stacks Project, Tag 0GHW](https://stacks.math.columbia.edu/tag/0GHW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- In a category with fibre products the relative diagonal of a composite `f ≫ g` factors as
the relative diagonal of `f` followed by the canonical comparison `X ×_Y X ⟶ X ×_Z X` of the
two relative self-products. -/
theorem diagonal_comp_eq_mapDesc {C : Type*} [Category* C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback.diagonal (f ≫ g) = pullback.diagonal f ≫ pullback.mapDesc f f g := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.mapDesc, pullback.map, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ARR** for a relative diagonal condition, which is the uniform shape of the two
separation axioms of Stacks 0ARN: if `P` is a property of morphisms of schemes stable under
composition, then a composite of two morphisms of fppf sheaves on the big fppf site of `S`
whose relative diagonals have `P` again has relative diagonal `P`. The relative diagonal of
the composite factors through the comparison of the two relative self-products, which has `P`
because it is a base change of the relative diagonal of the second morphism.

No hypothesis that the sheaves involved are formal algebraic spaces is needed, as the relative
diagonal condition itself needs none. -/
theorem hasRelativeDiagonal_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasRelativeDiagonal B S hS P f) (hg : HasRelativeDiagonal B S hS P g) :
    HasRelativeDiagonal B S hS P (f ≫ g) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : (fppfYoneda B S hS).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : (fppfYoneda B S hS).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  let Q := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)
  let R := Q.relative (fppfYoneda B S hS)
  let _ : R.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  show R (pullback.diagonal (f ≫ g))
  rw [diagonal_comp_eq_mapDesc f g]
  exact R.comp_mem _ _ hf <| (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
    (isPullback_mapDesc B S hS f f g) hg

/-- **Stacks 0ARR for the separatedness axiom of Stacks 0ARN.** A composite of two separated
morphisms of fppf sheaves on the big fppf site of `S` is separated: the relative diagonal of
`f ≫ g` factors as the relative diagonal of `f`, a closed immersion since `f` is separated,
followed by the comparison `X ×_Y X ⟶ X ×_Z X`, a closed immersion since `g` is separated by
Stacks 0ARQ, part (2); and closed immersions of formal algebraic spaces compose by
Stacks 0GHW. -/
@[stacks 0ARR "part (1): separated, separatedness read in the sense of Stacks 0ARN; the \
comparison of the two relative self-products is a closed immersion by Stacks 0ARQ, part (2), \
and closed immersions compose by Stacks 0GHW"]
theorem isSeparatedMorphism_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSeparatedMorphism B S hS f) (hg : IsSeparatedMorphism B S hS g) :
    IsSeparatedMorphism B S hS (f ≫ g) := by
  show IsClosedImmersion B S hS (pullback.diagonal (f ≫ g))
  rw [diagonal_comp_eq_mapDesc f g]
  exact isClosedImmersion_comp B S hS _ _ hf (isClosedImmersion_mapDesc B S hS f f g hg)

/-- **Stacks 0ARR for the quasi-separatedness axiom of Stacks 0ARN**, with quasi-compactness of
the relative diagonal read as the relative diagonal condition for quasi-compact morphisms of
schemes: if the relative diagonals of `f` and of `g` are quasi-compact in that sense, then so
is the relative diagonal of `f ≫ g`. Quasi-compact morphisms of schemes are stable under
composition, so this is the case `P = AlgebraicGeometry.QuasiCompact` of
`AlgebraicGeometry.FormalSpace.hasRelativeDiagonal_comp`. -/
@[stacks 0ARR "part (2): quasi-separated, with quasi-compactness of the relative diagonal read \
as the relative diagonal condition for quasi-compact morphisms of schemes, which is the second \
of the two cases of Stacks 0ARN in the uniform shape of Stacks 0ARS; stability under \
composition of quasi-compact morphisms of schemes is taken from Mathlib"]
theorem hasRelativeDiagonal_quasiCompact_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (hf : HasRelativeDiagonal B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) f)
    (hg : HasRelativeDiagonal B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) g) :
    HasRelativeDiagonal B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) (f ≫ g) :=
  hasRelativeDiagonal_comp B S hS _ f g hf hg

end AlgebraicGeometry.FormalSpace

end
