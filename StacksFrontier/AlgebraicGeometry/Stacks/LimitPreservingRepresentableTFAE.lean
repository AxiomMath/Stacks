module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingDiagonalObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphismObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableFull
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullbackConverse

/-!
# Stacks 0CMV: the three finiteness conditions on a 1-morphism representable by algebraic spaces

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S` which is representable by algebraic spaces. **Stacks 0CMV** says that the following are
equivalent:

1. `f` is limit preserving (Stacks 0CMR): at every directed limit `U = lim Uᵢ` of affine schemes
   over `S` the square of filtered colimits of fibre categories is 2-cartesian;
2. `f` is limit preserving on objects (Stacks 06CU);
3. `f` is locally of finite presentation in the sense of Stacks 03YK: every algebraic space
   representing a base change of `f` along a scheme-valued point of `𝒴` has locally finitely
   presented structural morphism.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreserving_of_isLimitPreservingOnObjects`: the implication
  (2) ⟹ (1), the substantial direction.
* `AlgebraicGeometry.Stack.isLimitPreserving_tfae`: **Stacks 0CMV**, the three-part equivalence.

## Implementation notes

The implication (1) ⟹ (2) is Stacks 0CMS
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isLimitPreserving`) and holds without the
representability hypothesis; the equivalence of (2) and (3) is Stacks 06CX
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`). What is
proved here is (2) ⟹ (1), which asks for the comparison functor

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}`

out of `AlgebraicGeometry.Stack.canonicalSquare` to be an equivalence. Its three properties are
assembled from three known facts: it is faithful because `f` is faithful on fibre categories,
which Stacks 02ZY reads off representability
(`AlgebraicGeometry.Stack.faithful_toCategoricalPullbackFunctor_canonicalSquare`); it is
essentially surjective directly by (2)
(`AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare`); and it is full
because the *relative diagonal* of `f` also satisfies (2)
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_twoFibreProductDiagonal`), which through the
criterion of Stacks 0CMW gives fullness
(`AlgebraicGeometry.Stack.full_toCategoricalPullbackFunctor_canonicalSquare`). Stacks 003Q then
turns the equivalence into 2-cartesianness of the square.

**Universes.** All three conditions are stated for index categories in the universe of the
schemes. This is the faithful reading of the directed limits of the source, and not merely the
size at which Stacks 06CX is available: for an index category in a larger universe, a cone of
affine schemes which is limiting among schemes of the universe `u` need not be the limit among
all schemes, and the implication (3) ⟹ (2) fails against such a cone. Index by `Ordinal.{u}` the
rings `Aₐ = k × k(x_β : β < α)` with the evident inclusions. A cocone from them to a ring `R` of
the universe `u` sends `(0, 1)` to one idempotent `e` and embeds the field
`k(x_β : β ∈ Ordinal.{u})` into `R e` unless `R e = 0`, and that field is too large to embed; so
the colimit among rings of the universe `u` is `k`, and `Spec k` is the limit of the `Spec Aₐ`
among schemes of the universe `u`, while their limit among all schemes is
`Spec k ⊔ Spec k(x_β : β ∈ Ordinal.{u})`. The open and closed immersion of `Spec k` into
`Spec A₀` is locally of finite presentation, yet the identity point of `Spec k`, lying over the
first component of `Spec A₀`, does not descend to any `Spec Aₐ`, whose second component maps
to the second component of `Spec A₀`. For index categories in the universe of the schemes the
colimit of the stage rings is computed in that universe, and a limiting cone is the limit among
all schemes.

## References

* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

add_to_stacks 0CMV "the equivalence of (2) and (3), which is Stacks 06CX"
  AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 0CMV, the implication (2) ⟹ (1).** A 1-morphism of categories fibred in groupoids
over the big fppf category of `S` which is representable by algebraic spaces and limit preserving
on objects is limit preserving.

The comparison functor out of `AlgebraicGeometry.Stack.canonicalSquare` is faithful because `f`
is, essentially surjective by the hypothesis, and full because the relative diagonal of `f` is
again limit preserving on objects; Stacks 003Q turns the resulting equivalence into
2-cartesianness of the square. -/
theorem isLimitPreserving_of_isLimitPreservingOnObjects
    (hp : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳 𝒴 f) :
    IsLimitPreserving.{u, u, u, u + 1, u} B S hS f := by
  have hfaith := faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hp
  have hdiag := isLimitPreservingOnObjects_twoFibreProductDiagonal B S hS 𝒳 𝒴 f hp hlim
  refine isLimitPreserving_of_canonicalSquare B S hS f fun J _ _ D cc hcc => ?_
  let := faithful_toCategoricalPullbackFunctor_canonicalSquare B S hS f hfaith
    (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone cc)
  let := essSurj_toCategoricalPullbackFunctor_canonicalSquare B S hS f
    (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone cc)
    (relativeDescentObj_of_isLimitPreservingOnObjects B S hS f D cc hcc hlim)
  let := full_toCategoricalPullbackFunctor_canonicalSquare B S hS 𝒳 𝒴 f
    (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone cc)
    (relativeDescentObj_of_isLimitPreservingOnObjects B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳 𝒴 f) D cc hcc hdiag)
  refine Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor.{u + 1, u + 1}
    _ ?_
  exact { full := inferInstance, faithful := inferInstance, essSurj := inferInstance }

/-- **Stacks 0CMV.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf category of `S` which is representable by algebraic spaces the following are equivalent:
`f` is limit preserving (Stacks 0CMR); `f` is limit preserving on objects (Stacks 06CU); and `f`
is locally of finite presentation in the sense of Stacks 03YK, that is, every algebraic space
representing a base change of `f` along a scheme-valued point of `𝒴` has locally finitely
presented structural morphism.

All three conditions are read for index categories in the universe of the schemes; see the
implementation notes. -/
@[stacks 0CMV "index categories in the universe of the schemes"]
theorem isLimitPreserving_tfae (hp : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    List.TFAE
      [IsLimitPreserving.{u, u, u, u + 1, u} B S hS f,
       BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳 𝒴 f,
       ∀ (U : BigFppfOver B S hS)
         (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
         (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
         (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
         (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
         Nonempty (StacksRepresentableCFG.EquivalenceOver
           (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
             (CatFiberedInGroupoids.homFunctor f))
           (presheafOfCategories (F ⋙ typeToCat)).p) →
         Space.IsLocallyOfFinitePresentation B S hS
           (algebraicSpaceMap B S hS U
             ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
               ⟨F, hF⟩)).hom] := by
  tfae_have 1 → 2 := fun h =>
    isLimitPreservingOnObjects_of_isLimitPreserving B S hS f h
  tfae_have 2 → 1 := isLimitPreserving_of_isLimitPreservingOnObjects B S hS 𝒳 𝒴 f hp
  tfae_have 2 ↔ 3 :=
    isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 f hp
  tfae_finish

end AlgebraicGeometry.Stack

end
