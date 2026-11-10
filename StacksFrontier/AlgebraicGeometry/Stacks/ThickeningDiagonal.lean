module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningUniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSelfProductDiagonal

/-!
# The diagonal comparison of a morphism of thickenings of algebraic stacks (Stacks 0BPU)

Stacks 0BPU reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> `𝒳 ×_𝒴 𝒳 → 𝒳' ×_{𝒴'} 𝒳'` is a thickening and the canonical diagram
> ```
>   𝒳  --Δ-->  𝒳 ×_𝒴 𝒳
>   |              |
>   v              v
>   𝒳' --Δ'--> 𝒳' ×_{𝒴'} 𝒳'
> ```
> is cartesian.

This file proves **both** assertions, for an arbitrary morphism of thickenings, at the canonical
2-fibre products of Stacks 04T2, and both of them *of the same comparison 1-morphism*,
`selfProductDiagonalMap` — the comparison with an explicit body, which is what the cartesian
assertion needs; see the implementation notes for why that rebuild is needed. The part key
*first assertion* is carried by `isThickening_selfProductDiagonalMap` and the part key *cartesian
diagonal square* by `isTwoFibreProduct_selfProductDiagonalSquare`.

The first assertion is registered a second time, on `isThickening_diagonalComparison`, which is
the same assertion for the other canonical comparison `diagonalComparison`; the 2-isomorphism
identifying the two comparisons is still open, so neither registration subsumes the other.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalComparison`: the comparison 1-morphism
  `c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` of a morphism of thickenings.
* `AlgebraicGeometry.Stack.diagonalComparison_comp_fst` and
  `AlgebraicGeometry.Stack.diagonalComparison_comp_snd`: the comparison is the canonical one —
  it carries each projection of `𝒳 ×_𝒴 𝒳` to the corresponding projection of
  `𝒳' ×_{𝒴'} 𝒳'` followed by `i`, up to 2-isomorphism. These are data, being 2-isomorphisms.

## Main results

* `AlgebraicGeometry.Stack.isThickening_snd_of_isTwoFibreProduct`: **Stacks 0BPR** for the
  *second* projection of a 2-fibre-product square, the mirror of
  `AlgebraicGeometry.Stack.isThickening_fst_of_isTwoFibreProduct`.
* `AlgebraicGeometry.Stack.isEquivalence_homFunctor_preHom`: the comparison 1-morphism between
  two 2-fibre products of one cospan of algebraic stacks is an equivalence of the underlying
  categories.
* `AlgebraicGeometry.Stack.isThickening_comp_of_isEquivalence`: a thickening precomposed with a
  1-morphism which is an equivalence of the underlying categories is a thickening.
* `AlgebraicGeometry.Stack.isThickening_diagonalComparison`: **the first assertion of Stacks
  0BPU**, that the comparison is a thickening, for `AlgebraicGeometry.Stack.diagonalComparison`.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductSndSquare`: the strict lift through which
  `AlgebraicGeometry.Stack.selfProductDiagonalMap` factors is itself a base change of `i`.
* `AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`: **the first assertion of Stacks
  0BPU** for `AlgebraicGeometry.Stack.selfProductDiagonalMap`, the comparison the cartesian
  assertion is also proved of.
* `AlgebraicGeometry.Stack.diagonalThickeningMorphism`: the two relative diagonals of a morphism
  of thickenings are themselves a morphism of thickenings — the opening step of the source's
  proof of **Stacks 0BPV**. It takes as a parameter the proof that the comparison
  `AlgebraicGeometry.Stack.selfProductDiagonalMap` is a thickening, which every call site can now
  supply from `AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`.
* `AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_iff`: **Stacks 0BPV** at the
  surjectivity property, on the same parameter.

## Implementation notes

The source factors the comparison as

`𝒳 ×_𝒴 𝒳 = 𝒳 ×_{𝒴'} 𝒳 ⟶ 𝒳 ×_{𝒴'} 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'`,

the two arrows being base changes of the thickening `i : 𝒳 ⟶ 𝒳'` in one factor at a time. Here
each of those two arrows is produced *as* a projection of a 2-fibre-product square rather than
as a functor to be recognised afterwards: pasting
(`CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd` and
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`) presents

`𝒳' ×_{𝒴'} 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'`  and  `𝒳 ×_{𝒴'} 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳`

as the first, respectively the second, projection of a square over a cospan whose other leg is
`i`, so **Stacks 0BPR** applies to each with no identification of functors to make; and the
apex of the twice-pasted square is then a 2-fibre product of the cospan `(i ≫ f', i ≫ f')`,
which after reindexing along the restriction 2-isomorphism of the morphism of thickenings
(**Stacks 003O**, `CategoryTheory.Bicategory.TwoCommSq.reindexFst` and `.reindexSnd`) is the
cospan `(f ≫ j, f ≫ j)`. The first equality of the display — the source's step "since
`𝒳 → 𝒴'` factors through the closed substack `𝒴`" — is
`AlgebraicGeometry.Stack.enlargeTargetComparison`, an equivalence because a closed immersion is
fully faithful (**Stacks 04ZZ** (1) ⟹ (2)).

Two transfers are therefore needed, and both are along a 1-morphism which is an equivalence of
the underlying categories rather than a base change: the enlargement of the target, and the
comparison of the twice-pasted model of the cospan `(f ≫ j, f ≫ j)` with the canonical one.
`AlgebraicGeometry.Stack.isThickening_comp_of_isEquivalence` does both at once. Its
closed-immersion half is **Stacks 0457**
(`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`) and its
surjectivity half is `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_of_isEquivalence`.

The composition of the two base-change thickenings is **Stacks 0BPS**,
`AlgebraicGeometry.Stack.isThickening_comp`. Its closed-immersion half rests on
fppf-target-locality of the closed-immersion property of morphisms of algebraic spaces —
**Stacks 0420** — which the library now has at that precoverage as the instance
`AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf`, so Stacks 0BPS no longer
carries it. The declarations here still take it as an instance *hypothesis*, which that instance
discharges at every call site.

**The second assertion of Stacks 0BPU is not proved for
`AlgebraicGeometry.Stack.diagonalComparison`, and the obstruction is this 1-morphism rather than
any missing mathematics.** The assertion is the over-the-base form of Stacks 0CBB applied to
`𝒳 ⟶ 𝒳' ⟶ 𝒴'`, and that form is now available, fully proved, as
`CategoryTheory.TwoFibreProductOver.isEquivalence_selfProductDiagonalComparison` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverSelfProductDiagonal`, in the generality the
growing target needs: `i` fully faithful (**Stacks 05UK**, `i` being a monomorphism) and `j`
faithful. The permanence property this needs — the
transport of `CategoryTheory.Bicategory.IsTwoFibreProduct` along an equivalence of the *apex* —
is also present, as `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` and
`…_from` in `StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence`, and
`AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare` already consumes it.

What blocks the assertion here is that `AlgebraicGeometry.Stack.diagonalComparison` has no
computable body to reason with. Its middle factor is
`AlgebraicGeometry.Stack.selfProductComparison`, i.e.
`CategoryTheory.Bicategory.twoFibreProductPreHom`, which is a `Quotient.out` of the terminality
witness; so neither the cartesian filler `Δ ≫ c ≅ i ≫ Δ'` nor the three halves of an
equivalence can be computed for it, and the universal property supplies the filler only as an
*existence* statement, while `IsTwoFibreProduct` is data. Carrying the second assertion
therefore needs the comparison to be rebuilt with an explicit body — the functor
`CategoryTheory.TwoFibreProductOver.selfProductMap`, which applies `i` to both factors and reads
the comparison isomorphism of an object through `j` and the restriction 2-isomorphism of the
morphism of thickenings. For that 1-morphism the filler is the identity on both components, and
the cartesian assertion is the statement cited above.

**Stacks 0BPV is carried here at two of its seventeen properties only.** The source lists
representability by schemes, affineness, surjectivity, quasi-compactness, universal closedness,
integrality, quasi-separatedness, separatedness, universal injectivity, universal openness, local
quasi-finiteness, finiteness, unramifiedness, being a monomorphism, being an immersion, being a
closed immersion and properness, and asserts for each that it holds for `Δ` exactly when it holds
for `Δ'`. Each such equivalence is the corresponding part of **Stacks 0CJ9** applied to the
morphism of thickenings `(Δ, Δ')` of `AlgebraicGeometry.Stack.diagonalThickeningMorphism`, and
this library carries exactly two parts of 0CJ9 — part (2), surjectivity
(`AlgebraicGeometry.Stack.isSurjective_inner_iff_outer`), and part (6), universal injectivity
(`AlgebraicGeometry.Stack.universallyInjective_inner_iff_outer`). The other fifteen need the
invariance of their property under a cartesian morphism of thickenings of algebraic *spaces*,
**Stacks 09ZY** and **Stacks 0BPJ**, of which
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms` carries only the surjectivity clause
and `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties` only
local quasi-finiteness and the vanishing of the relative differentials, in a shape stated for the
two horizontal morphisms of the square rather than for the §04XB point test that the stack-level
statement needs.

Both properties carried here take the hypothesis of
`AlgebraicGeometry.Stack.diagonalThickeningMorphism` as a parameter. That hypothesis — the first
assertion of Stacks 0BPU for `AlgebraicGeometry.Stack.selfProductDiagonalMap` rather than for
`AlgebraicGeometry.Stack.diagonalComparison` — is now proved, by
`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`, so every call site can discharge
it; it is left as a parameter here rather than inlined, which would change three signatures for
no mathematical gain.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0BPS](https://stacks.math.columbia.edu/tag/0BPS)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section BaseChange

variable {𝒴 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0BPR for the second projection.** In a 2-fibre-product square over the cospan
`j : 𝒴 ⟶ 𝒴'`, `g : 𝒳' ⟶ 𝒴'` of algebraic stacks over `S`, the projection to the source of `g`
is a thickening as soon as `j` is.

This is `AlgebraicGeometry.Stack.isThickening_fst_of_isTwoFibreProduct` with the two legs of the
cospan exchanged (`CategoryTheory.Bicategory.isTwoFibreProduct_swap`); both are the statement
that a base change of a thickening is a thickening. -/
theorem isThickening_snd_of_isTwoFibreProduct {j : 𝒴 ⟶ 𝒴'} {g : 𝒳' ⟶ 𝒴'}
    (hj : IsThickening j)
    (P : Bicategory.TwoCommSq j g) (hP : Bicategory.IsTwoFibreProduct P) :
    IsThickening P.snd :=
  isThickening_fst_of_isTwoFibreProduct B S hS hj P.swap (Bicategory.isTwoFibreProduct_swap hP)

end BaseChange

section Equivalences

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **The comparison 1-morphism of two 2-fibre products of one cospan of algebraic stacks is an
equivalence of the underlying categories.**

The two squares of algebraic stacks are 2-fibre products of categories fibred in groupoids as
well (`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`), the
pre-morphism descends to one of those squares
(`CategoryTheory.Bicategory.TwoCommSq.PreHom.underlying`), and
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` applies there. -/
theorem isEquivalence_homFunctor_preHom {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    {P Q : Bicategory.TwoCommSq g f}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (c : Bicategory.TwoCommSq.PreHom P Q) :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor c.hom.hom) :=
  Bicategory.isEquivalence_of_isTwoFibreProduct
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP)
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS Q hQ)
    (Bicategory.TwoCommSq.PreHom.underlying c)

/-- The identity based functor of an algebraic stack is an equivalence of categories. -/
private theorem isEquivalence_basedFunctor_id (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor := by
  dsimp [BasedFunctor.id]
  infer_instance

/-- Thickenings transfer along a 2-commutative square of based functors whose two horizontal
legs are equivalences of categories, provided surjectivity on points does. -/
private theorem isThickening_of_equivalences {𝒳₁ 𝒴₁ 𝒳₂ 𝒴₂ : AlgebraicStacks.{u, w} B S hS}
    (f' : 𝒳₂ ⟶ 𝒴₂) (f : 𝒳₁ ⟶ 𝒴₁) (a : 𝒳₂.val.val ⥤ᵇ 𝒳₁.val.val)
    (b : 𝒴₂.val.val ⥤ᵇ 𝒴₁.val.val)
    (α : BasedFunctor.comp a f.hom.hom ≅ BasedFunctor.comp f'.hom.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hf : IsThickening f) (hs : Function.Surjective (AlgebraicStacks.pointsMap B S hS f')) :
    IsThickening f' :=
  ⟨⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f'.hom.hom f.hom.hom a b α).1
      hf.1.1,
    relativeProperty_of_equivalences B S hS (fun _ _ m => Space.IsClosedImmersion B S hS m.hom)
      f'.hom.hom f.hom.hom a b α hf.1.2⟩, hs⟩

/-- **A thickening of algebraic stacks precomposed with an equivalence is a thickening.** If the
underlying functor of `u : 𝒳 ⟶ 𝒴` is an equivalence of categories and `ψ : 𝒴 ⟶ 𝒵` is a
thickening, then `u ≫ ψ` is a thickening.

Representability by algebraic spaces and the closed-immersion condition of Stacks 04XB both
transfer along `u` by **Stacks 0457**, with the identity on the target; surjectivity on points
transfers because `u` is bijective on points. -/
theorem isThickening_comp_of_isEquivalence (u : 𝒳 ⟶ 𝒴) (ψ : 𝒴 ⟶ 𝒵)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor u.hom)]
    (hψ : IsThickening ψ) : IsThickening (u ≫ ψ) := by
  have := isEquivalence_basedFunctor_id B S hS 𝒵
  refine isThickening_of_equivalences B S hS (u ≫ ψ) ψ u.hom.hom (BasedFunctor.id 𝒵.val.val)
    (Iso.refl _) hψ ?_
  rw [AlgebraicStacks.pointsMap_comp]
  exact hψ.2.comp (AlgebraicStacks.bijective_pointsMap_of_isEquivalence B S hS u).2

/-- **A thickening of algebraic stacks stays a thickening after a 2-isomorphism of the
1-morphism.** If `p : 𝒳 ⟶ 𝒴` is a thickening and `p ≅ q`, then `q` is a thickening; so being a
thickening is a property of the 2-isomorphism class of a 1-morphism, as it must be in a
2-category.

This is the case `a = b = 𝟙` of **Stacks 0457** for the two conditions of Stacks 04YL part (2),
the same specialisation that
`AlgebraicGeometry.Stack.isRelativelySmooth_congr_twoIso` makes at the smooth property: taking
both horizontal 1-morphisms of the 2-commutative square to be identities makes its two
composites the two 1-morphisms themselves, so the 2-isomorphism *is* the filler. Surjectivity on
points transports because the map on points does not see 2-morphisms
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`).

It is the companion of `AlgebraicGeometry.Stack.isThickening_comp_of_isEquivalence`, which moves
a thickening along an equivalence of the source, and it is the permanence property a
consolidation of the two assertions of Stacks 0BPU onto a single comparison 1-morphism would
consume — see the implementation note on
`AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductDiagonalSquare` for what such a
consolidation still lacks. -/
theorem isThickening_congr_twoIso {p q : 𝒳 ⟶ 𝒴} (e : p ≅ q) (hp : IsThickening p) :
    IsThickening q := by
  have := isEquivalence_basedFunctor_id B S hS 𝒳
  have := isEquivalence_basedFunctor_id B S hS 𝒴
  refine isThickening_of_equivalences B S hS q p (BasedFunctor.id 𝒳.val.val)
    (BasedFunctor.id 𝒴.val.val)
    (twoIsoHomIso B S hS (Bicategory.InducedBicategory.isoHom (f := p) (g := q) e)) hp ?_
  rw [← AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS e.hom]
  exact hp.2

end Equivalences

section EnlargeTarget

variable {𝒳 𝒴 𝒴' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **Enlarging the target of a cospan is strictly over the second projection as well.** The
companion of `AlgebraicGeometry.Stack.enlargeTargetComparison_comp_fst`: the comparison keeps
both components of an object of the 2-fibre product and only applies `j` to its comparison
isomorphism, so it commutes with either projection on the nose. -/
theorem enlargeTargetComparison_comp_snd (d : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (j : 𝒴 ⟶ 𝒴') :
    enlargeTargetComparison B S hS d f j ≫
        (AlgebraicStacks.twoFibreProductSquare B S hS (d ≫ j) (f ≫ j)).snd =
      (AlgebraicStacks.twoFibreProductSquare B S hS d f).snd :=
  rfl

end EnlargeTarget

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- The canonical 2-fibre product `𝒳' ×_{𝒴'} 𝒳'` of the ambient 1-morphism of a morphism of
thickenings of algebraic stacks with itself. -/
abbrev ambientSelfProduct : Bicategory.TwoCommSq m.outer m.outer :=
  AlgebraicStacks.twoFibreProductSquare B S hS m.outer m.outer

/-- The canonical 2-fibre product `𝒳' ×_{𝒴'} 𝒳` of the ambient 1-morphism with the thickening
`i` of its source, i.e. the base change of `i` along the second projection of
`𝒳' ×_{𝒴'} 𝒳'`. -/
abbrev secondFactorRestriction :
    Bicategory.TwoCommSq (ambientSelfProduct B S hS m).snd i :=
  AlgebraicStacks.twoFibreProductSquare B S hS (ambientSelfProduct B S hS m).snd i

/-- `𝒳' ×_{𝒴'} 𝒳`, presented as a 2-fibre product of the cospan `(f', i ≫ f')` by pasting the
base change of `i` onto the second projection of `𝒳' ×_{𝒴'} 𝒳'`. -/
abbrev secondFactorSquare :
    Bicategory.TwoCommSq m.outer (i ≫ m.outer) :=
  (ambientSelfProduct B S hS m).pasteSnd (secondFactorRestriction B S hS m)

/-- The canonical 2-fibre product `𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳)`, i.e. the base change of `i` along
the first projection of `𝒳' ×_{𝒴'} 𝒳`. -/
abbrev firstFactorRestriction :
    Bicategory.TwoCommSq i (secondFactorSquare B S hS m).fst :=
  AlgebraicStacks.twoFibreProductSquare B S hS i (secondFactorSquare B S hS m).fst

/-- `𝒳 ×_{𝒴'} 𝒳`, presented as a 2-fibre product of the cospan `(i ≫ f', i ≫ f')` by pasting
the base change of `i` onto the first projection of `𝒳' ×_{𝒴'} 𝒳`. -/
abbrev pastedSelfProduct :
    Bicategory.TwoCommSq (i ≫ m.outer) (i ≫ m.outer) :=
  (secondFactorSquare B S hS m).pasteFst (firstFactorRestriction B S hS m)

/-- `𝒳 ×_{𝒴'} 𝒳` as a 2-fibre product of the cospan `(f ≫ j, f ≫ j)`: the twice-pasted square
reindexed along the restriction 2-isomorphism of the morphism of thickenings, in both legs. -/
abbrev reindexedSelfProduct :
    Bicategory.TwoCommSq (m.inner ≫ j) (m.inner ≫ j) :=
  ((pastedSelfProduct B S hS m).reindexFst m.comm.symm).reindexSnd m.comm.symm

/-- The twice-pasted square is a 2-fibre product of the cospan `(i ≫ f', i ≫ f')`: both pasted
pieces are canonical 2-fibre products, so `CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`
and `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst` apply in turn. -/
def isTwoFibreProduct_pastedSelfProduct :
    Bicategory.IsTwoFibreProduct (pastedSelfProduct B S hS m) :=
  Bicategory.isTwoFibreProduct_pasteFst _
    (Bicategory.isTwoFibreProduct_pasteSnd _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS m.outer m.outer) _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS _ i)) _
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS i _)

/-- The reindexed twice-pasted square is a 2-fibre product of the cospan `(f ≫ j, f ≫ j)`. -/
def isTwoFibreProduct_reindexedSelfProduct :
    Bicategory.IsTwoFibreProduct (reindexedSelfProduct B S hS m) :=
  Bicategory.isTwoFibreProduct_reindexSnd _
    (Bicategory.isTwoFibreProduct_reindexFst _ (isTwoFibreProduct_pastedSelfProduct B S hS m))

/-- The comparison pre-morphism from the canonical 2-fibre product of the cospan
`(f ≫ j, f ≫ j)` to the reindexed twice-pasted model of it. -/
def selfProductComparison :
    Bicategory.TwoCommSq.PreHom
      (AlgebraicStacks.twoFibreProductSquare B S hS (m.inner ≫ j) (m.inner ≫ j))
      (reindexedSelfProduct B S hS m) :=
  Bicategory.twoFibreProductPreHom (isTwoFibreProduct_reindexedSelfProduct B S hS m) _

/-- **The comparison 1-morphism `c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` of a morphism of thickenings of
algebraic stacks over `S`**, at the canonical 2-fibre products of Stacks 04T2.

It is the composite of the source's three steps: the enlargement of the target along `j`, which
identifies `𝒳 ×_𝒴 𝒳` with `𝒳 ×_{𝒴'} 𝒳`; the comparison with the twice-pasted model of
`𝒳 ×_{𝒴'} 𝒳`; and the two base changes of `i`, one factor at a time. -/
def diagonalComparison :
    (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).pt ⟶
      (ambientSelfProduct B S hS m).pt :=
  enlargeTargetComparison B S hS m.inner m.inner j ≫
    (selfProductComparison B S hS m).hom ≫
      (firstFactorRestriction B S hS m).snd ≫ (secondFactorRestriction B S hS m).fst

/-- **The comparison 1-morphism lies over the first projection**: following it with the first
projection of `𝒳' ×_{𝒴'} 𝒳'` is the first projection of `𝒳 ×_𝒴 𝒳` followed by `i`, up to
2-isomorphism. Together with
`AlgebraicGeometry.Stack.diagonalComparison_comp_snd` this says that
`AlgebraicGeometry.Stack.diagonalComparison` is the *canonical* comparison of Stacks 0BPU.

The two 2-isomorphisms used are the filler of the base change of `i` along the first projection
of `𝒳' ×_{𝒴'} 𝒳` and the first comparison 2-cell of the pre-morphism comparing the two models
of the cospan `(f ≫ j, f ≫ j)`; the enlargement of the target contributes nothing, being
strictly over the first projection. -/
def diagonalComparison_comp_fst :
    diagonalComparison B S hS m ≫ (ambientSelfProduct B S hS m).fst ≅
      (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).fst ≫ i :=
  Bicategory.whiskerLeftIso
      (enlargeTargetComparison B S hS m.inner m.inner j ≫ (selfProductComparison B S hS m).hom)
      (firstFactorRestriction B S hS m).iso.symm ≪≫
    Bicategory.whiskerLeftIso (enlargeTargetComparison B S hS m.inner m.inner j)
      (Bicategory.whiskerRightIso (selfProductComparison B S hS m).isoFst.symm i)

/-- **The comparison 1-morphism lies over the second projection**: following it with the second
projection of `𝒳' ×_{𝒴'} 𝒳'` is the second projection of `𝒳 ×_𝒴 𝒳` followed by `i`, up to
2-isomorphism. See `AlgebraicGeometry.Stack.diagonalComparison_comp_fst`. -/
def diagonalComparison_comp_snd :
    diagonalComparison B S hS m ≫ (ambientSelfProduct B S hS m).snd ≅
      (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).snd ≫ i :=
  Bicategory.whiskerLeftIso
      (enlargeTargetComparison B S hS m.inner m.inner j ≫
        (selfProductComparison B S hS m).hom ≫ (firstFactorRestriction B S hS m).snd)
      (secondFactorRestriction B S hS m).iso ≪≫
    Bicategory.whiskerLeftIso (enlargeTargetComparison B S hS m.inner m.inner j)
      (Bicategory.whiskerRightIso (selfProductComparison B S hS m).isoSnd.symm i)

/-- The two base changes of `i`, composed: `𝒳 ×_{𝒴'} 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` is a thickening by
**Stacks 0BPR** twice and **Stacks 0BPS** once. -/
theorem isThickening_firstFactorRestriction_snd_comp
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)] :
    IsThickening ((firstFactorRestriction B S hS m).snd ≫
      (secondFactorRestriction B S hS m).fst) :=
  isThickening_comp _ _
    (isThickening_snd_of_isTwoFibreProduct B S hS hi _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS i _))
    (isThickening_fst_of_isTwoFibreProduct B S hS hi _
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS _ i))

/-- **Stacks 0BPU, the first assertion.** In a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the comparison 1-morphism
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` is a thickening.

Since `𝒳 → 𝒴'` factors through the closed substack `𝒴`, the enlargement of the target
identifies `𝒳 ×_𝒴 𝒳` with `𝒳 ×_{𝒴'} 𝒳` (**Stacks 04ZZ** (1) ⟹ (2) makes `j` fully faithful);
the latter maps to `𝒳' ×_{𝒴'} 𝒳'` by two base changes of the thickening `i`, one factor at a
time, each a thickening by **Stacks 0BPR**, so their composite is one by **Stacks 0BPS**.

This carries the part key *first assertion* of Stacks 0BPU for *this* comparison 1-morphism. The
other assertion of that tag, that the diagonal square is cartesian, is not proved for it — see
the implementation notes, which name the obstruction. Both assertions are proved for the rebuilt
comparison with an explicit body: the first by `isThickening_selfProductDiagonalMap` below, which
carries the same part key, and the cartesian one by
`isTwoFibreProduct_selfProductDiagonalSquare`. The 2-isomorphism between the two comparisons is
still open, which is why the first assertion is registered twice rather than once.

The fppf-target-locality instance is Stacks 0420. The library proves it at the fpqc precoverage,
`isClosedImmersion_isLocalAtTarget_fpqc`, and restricts it to the fppf precoverage asked for
here in `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf`, which is an instance;
the hypothesis below is therefore discharged automatically. -/
@[stacks 0BPU "first assertion"]
theorem isThickening_diagonalComparison
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)] :
    IsThickening (diagonalComparison B S hS m) := by
  have hjff := AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  have hEn := isEquivalence_enlargeTargetComparison B S hS m.inner m.inner hjff
  have hcmp := isEquivalence_homFunctor_preHom B S hS
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (m.inner ≫ j) (m.inner ≫ j))
    (isTwoFibreProduct_reindexedSelfProduct B S hS m) (selfProductComparison B S hS m)
  have : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (enlargeTargetComparison B S hS m.inner m.inner j ≫
        (selfProductComparison B S hS m).hom).hom) := by
    change Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (enlargeTargetComparison B S hS m.inner m.inner j).hom ⋙
        CatFiberedInGroupoids.homFunctor (selfProductComparison B S hS m).hom.hom)
    infer_instance
  exact isThickening_comp_of_isEquivalence B S hS
    (enlargeTargetComparison B S hS m.inner m.inner j ≫ (selfProductComparison B S hS m).hom)
    ((firstFactorRestriction B S hS m).snd ≫ (secondFactorRestriction B S hS m).fst)
    (isThickening_firstFactorRestriction_snd_comp B S hS m)

/-- **The restriction 2-isomorphism of a morphism of thickenings, as a natural isomorphism of the
underlying functors.** The 2-cell `m.comm : f ≫ j ≅ i ≫ f'` of the restriction square, read first
in the 2-category of categories fibred in groupoids
(`CategoryTheory.Bicategory.InducedBicategory.isoHom`) and then on the underlying functors
(`CategoryTheory.CatFiberedInGroupoids.underlyingIso`).

This is the isomorphism `E` that `CategoryTheory.TwoFibreProductOver.selfProductMap` transports a
comparison isomorphism along. -/
def restrictionNatIso :
    CatFiberedInGroupoids.homFunctor m.inner.hom ⋙ CatFiberedInGroupoids.homFunctor j.hom ≅
      CatFiberedInGroupoids.homFunctor i.hom ⋙ CatFiberedInGroupoids.homFunctor m.outer.hom :=
  CatFiberedInGroupoids.underlyingIso
    (Bicategory.InducedBicategory.isoHom (f := m.inner ≫ j) (g := i ≫ m.outer) m.comm)

/-- Every component of `AlgebraicGeometry.Stack.restrictionNatIso` lies over an identity of the
big fppf site: it is a component of a 2-morphism of the 2-category of algebraic stacks, and
verticality of those components is clause (3) of Stacks 02XS. -/
theorem isHomLift_restrictionNatIso (x : 𝒳.val.val.obj) :
    𝒴'.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x)) ((restrictionNatIso B S hS m).hom.app x) :=
  m.comm.hom.hom.hom.isHomLift' x

/-- **The comparison 1-morphism `𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` of a morphism of thickenings of
algebraic stacks, with an explicit body.** It applies `i` to both factors and reads the comparison
isomorphism `φ : f x ≅ f y` of an object as an isomorphism `f' (i x) ≅ f' (i y)` through `j` and
the restriction 2-isomorphism: it is
`CategoryTheory.TwoFibreProductOver.selfProductMap` read in the 2-category of algebraic stacks.

It has the same source and target as
`AlgebraicGeometry.Stack.diagonalComparison` and is canonical in the same sense — indeed
strictly so, by `AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_fst` and
`AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_snd`, which hold on the nose rather than up
to a 2-isomorphism. Unlike `AlgebraicGeometry.Stack.diagonalComparison` it has a body one can
compute with, which is what the second assertion of Stacks 0BPU needs; see the implementation
notes. -/
def selfProductDiagonalMap :
    (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).pt ⟶
      (ambientSelfProduct B S hS m).pt :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.selfProductMap
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m)
      w := TwoFibreProductOver.selfProductMap_comp_structureFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m) })

/-- **The comparison 1-morphism lies strictly over the first projection**: following it with the
first projection of `𝒳' ×_{𝒴'} 𝒳'` *is* the first projection of `𝒳 ×_𝒴 𝒳` followed by `i`, with
no 2-isomorphism to insert. This and
`AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_snd` are what make
`AlgebraicGeometry.Stack.selfProductDiagonalMap` the canonical comparison of Stacks 0BPU; they are
the strict form of `AlgebraicGeometry.Stack.diagonalComparison_comp_fst` and `…_comp_snd`. -/
theorem selfProductDiagonalMap_comp_fst :
    selfProductDiagonalMap B S hS m ≫ (ambientSelfProduct B S hS m).fst =
      (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).fst ≫ i :=
  rfl

/-- **The comparison 1-morphism lies strictly over the second projection.** See
`AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_fst`. -/
theorem selfProductDiagonalMap_comp_snd :
    selfProductDiagonalMap B S hS m ≫ (ambientSelfProduct B S hS m).snd =
      (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).snd ≫ i :=
  rfl

/-! ### The comparison as a composite of two base changes of `i` -/

/-- The square whose two legs are the first projection of `𝒳 ×_𝒴 𝒳` and the comparison
1-morphism, over the cospan `(i, Δ'-free first projection of 𝒳' ×_{𝒴'} 𝒳')`. It 2-commutes
*strictly*, by `AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_fst`. -/
def selfProductFstSquare :
    Bicategory.TwoCommSq i (ambientSelfProduct B S hS m).fst where
  pt := (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).pt
  fst := (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).fst
  snd := selfProductDiagonalMap B S hS m
  iso := Iso.refl _

/-- The canonical 2-fibre product `𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳')`, i.e. the base change of the
thickening `i` along the first projection of `𝒳' ×_{𝒴'} 𝒳'`. -/
abbrev ambientFstRestriction :
    Bicategory.TwoCommSq i (ambientSelfProduct B S hS m).fst :=
  twoFibreProductSquareAlgebraicStacks B S hS i (ambientSelfProduct B S hS m).fst

/-- **The second of the two base changes of `i`** that the comparison 1-morphism is composed of:
the base change of `i` along the first projection of `𝒳' ×_{𝒴'} 𝒳'`, which is a thickening by
**Stacks 0BPR**. -/
theorem isThickening_ambientFstRestriction_snd :
    IsThickening (ambientFstRestriction B S hS m).snd :=
  isThickening_baseChange B S hS i (ambientSelfProduct B S hS m).fst _
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS i
      (ambientSelfProduct B S hS m).fst) hi

/-- **The first of the two base changes of `i`**: the strict comparison of
`AlgebraicGeometry.Stack.selfProductFstSquare` with the canonical 2-fibre product
`𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳')`. It is the canonical lift of Stacks 0040, so its composite with the
second projection is the comparison 1-morphism on the nose
(`AlgebraicGeometry.Stack.selfProductFstLift_comp_snd`). -/
def selfProductFstLift :
    (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).pt ⟶
      (ambientFstRestriction B S hS m).pt :=
  (canonicalPreHomAlgebraicStacks B S hS i (ambientSelfProduct B S hS m).fst
    (selfProductFstSquare B S hS m)).hom

/-- The comparison 1-morphism factors as the strict lift followed by the base change of `i` along
the first projection of `𝒳' ×_{𝒴'} 𝒳'`, on the nose. -/
theorem selfProductFstLift_comp_snd :
    selfProductFstLift B S hS m ≫ (ambientFstRestriction B S hS m).snd =
      selfProductDiagonalMap B S hS m :=
  canonicalPreHomAlgebraicStacks_hom_comp_snd B S hS i (ambientSelfProduct B S hS m).fst
    (selfProductFstSquare B S hS m)

/-- The square exhibiting the strict lift of
`AlgebraicGeometry.Stack.selfProductFstLift` as a base change of `i`: its legs are the *second*
projection of `𝒳 ×_𝒴 𝒳` and the lift, over the cospan
`(i, 𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳') ⟶ 𝒳' )`, the second leg being the composite of the base change of
`i` with the second projection of `𝒳' ×_{𝒴'} 𝒳'`. It 2-commutes strictly, by
`AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_snd`. -/
def selfProductSndSquare :
    Bicategory.TwoCommSq i
      ((ambientFstRestriction B S hS m).snd ≫ (ambientSelfProduct B S hS m).snd) where
  pt := (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).pt
  fst := (AlgebraicStacks.twoFibreProductSquare B S hS m.inner m.inner).snd
  snd := selfProductFstLift B S hS m
  iso := Iso.refl _

/-- **The strict lift is itself a base change of `i`**: the square
`AlgebraicGeometry.Stack.selfProductSndSquare`, whose legs are the second projection of
`𝒳 ×_𝒴 𝒳` and `AlgebraicGeometry.Stack.selfProductFstLift`, is a 2-fibre product of the cospan
`(i, 𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳') ⟶ 𝒳')`.

It is recognised through its own strict comparison with the canonical 2-fibre product of that
cospan, `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`, which is an equivalence of the
underlying categories by
`CategoryTheory.CatFiberedInGroupoids.isEquivalence_canonicalPreHom`. That result's three
hypotheses all hold here. The square's second leg is the mediating 1-morphism of Stacks 0040 and
is full and faithful because `AlgebraicGeometry.Stack.selfProductDiagonalMap` is
(`CategoryTheory.TwoFibreProductOver.full_lift` and `…faithful_lift`, fed by
`CategoryTheory.TwoFibreProductOver.full_selfProductMap` and `…faithful_selfProductMap`); the
cospan's first leg `i` is faithful; and both of those rest on full faithfulness of the closed
immersions `i` and `j`, **Stacks 04ZZ** (1) ⟹ (2).

The third hypothesis, that objects lift, is the content. An object of the canonical apex is a
quadruple `(U, x, (x₁, (y₁, y₂, ψ), χ), ω)` — a point `x` of `𝒳`, a point of
`𝒳 ×_{𝒳'} (𝒳' ×_{𝒴'} 𝒳')` consisting of a point `x₁` of `𝒳`, a point `(y₁, y₂, ψ)` of
`𝒳' ×_{𝒴'} 𝒳'` and `χ : i x₁ ≅ y₁`, and `ω : i x ≅ y₂`. The object of `𝒳 ×_𝒴 𝒳` lying over it is
`(U, x₁, x, φ)`, where `φ : f x₁ ≅ f x` is the preimage under the fully faithful `j` of
`E_{x₁} ≫ f' χ ≫ ψ ≫ f' ω⁻¹ ≫ E_x⁻¹` — the restriction 2-isomorphism `E` of the morphism of
thickenings is what carries the comparison isomorphism between `𝒴` and `𝒴'`. It is vertical
because all five of its factors are. The intertwining the lifting criterion asks for then holds
because `E` and `f' ω` cancel against their own inverses; that cancellation is carried out on
abstract morphisms, the composite it concerns being type-correct only once the projections of the
2-fibre product are unfolded, which puts it out of reach of `simp` and `rw`.

With `AlgebraicGeometry.Stack.isThickening_baseChange` this makes the lift a thickening, which is
the step the first assertion of Stacks 0BPU needed for this comparison; see
`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`. -/
noncomputable def isTwoFibreProduct_selfProductSndSquare :
    Bicategory.IsTwoFibreProduct (selfProductSndSquare B S hS m) := by
  obtain ⟨hifull, hifaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS i hi.1
  obtain ⟨hjfull, hjfaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  haveI hKf : (selfProductDiagonalMap B S hS m).hom.hom.toFunctor.Faithful :=
    TwoFibreProductOver.faithful_selfProductMap
      (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
      (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m)
  haveI hKF : (selfProductDiagonalMap B S hS m).hom.hom.toFunctor.Full :=
    TwoFibreProductOver.full_selfProductMap
      (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
      (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m)
  haveI hTf : (AlgebraicStacks.toCatFiberedInGroupoids B S hS
      (selfProductSndSquare B S hS m)).snd.hom.toFunctor.Faithful :=
    TwoFibreProductOver.faithful_lift _ _ _ _ _ _ _
      (selfProductDiagonalMap B S hS m).hom.hom.toFunctor
      (selfProductFstSquare B S hS m).underlying.fst.hom.w
      (selfProductFstSquare B S hS m).underlying.snd.hom.w _ _
  haveI hTF : (AlgebraicStacks.toCatFiberedInGroupoids B S hS
      (selfProductSndSquare B S hS m)).snd.hom.toFunctor.Full :=
    TwoFibreProductOver.full_lift _ _ _ _ _ _ _
      (selfProductDiagonalMap B S hS m).hom.hom.toFunctor
      (selfProductFstSquare B S hS m).underlying.fst.hom.w
      (selfProductFstSquare B S hS m).underlying.snd.hom.w _ _
  refine AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        i.hom ((ambientFstRestriction B S hS m).snd ≫ (ambientSelfProduct B S hS m).snd).hom)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} _ _ _)
      (CatFiberedInGroupoids.isEquivalence_canonicalPreHom.{u, u, u + 1, u + 1} _ _ _ ?_))
  intro P
  have hb0 : P.y.base = P.base := P.hy
  have hb1 : 𝒳.val.val.p.obj P.y.x = P.base := P.y.hx.trans hb0
  have hb2 : P.y.y.base = P.base := P.y.hy.trans hb0
  have v0 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
      ((restrictionNatIso B S hS m).app P.x).hom := by
    rw [← P.hx]
    exact isHomLift_restrictionNatIso B S hS m P.x
  have v1 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
      ((restrictionNatIso B S hS m).hom.app P.y.x) := by
    rw [← hb1]
    exact isHomLift_restrictionNatIso B S hS m P.y.x
  have vx : 𝒳'.val.val.p.IsHomLift (𝟙 P.base) P.y.iso.hom := by
    rw [← hb0]
    exact P.y.vertical
  have v2 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
      ((CatFiberedInGroupoids.homFunctor m.outer.hom).map P.y.iso.hom) :=
    Functor.isHomLift_map_of_comp_eq
      (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom) (𝟙 P.base) P.y.iso.hom
  have v3 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base) P.y.y.iso.hom := by
    rw [← hb2]
    exact P.y.y.vertical
  have v4 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
      ((CatFiberedInGroupoids.homFunctor m.outer.hom).map P.iso.inv) :=
    have := P.vertical
    have := IsHomLift.lift_id_inv 𝒳'.val.val.p P.base P.iso
    Functor.isHomLift_map_of_comp_eq
      (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom) (𝟙 P.base) P.iso.inv
  have v5 : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
      ((restrictionNatIso B S hS m).inv.app P.x) :=
    have := v0
    IsHomLift.lift_id_inv 𝒴'.val.val.p P.base ((restrictionNatIso B S hS m).app P.x)
  have vid1 : 𝒳.val.val.p.IsHomLift (𝟙 P.base) (𝟙 P.y.x) := by
    rw [← hb1]
    infer_instance
  have vid2 : 𝒳.val.val.p.IsHomLift (𝟙 P.base) (𝟙 P.x) := by
    rw [← P.hx]
    infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ : (CatFiberedInGroupoids.homFunctor m.inner.hom).obj P.y.x ≅
      (CatFiberedInGroupoids.homFunctor m.inner.hom).obj P.x,
      (CatFiberedInGroupoids.homFunctor j.hom).map φ.hom =
        (restrictionNatIso B S hS m).hom.app P.y.x ≫
          (CatFiberedInGroupoids.homFunctor m.outer.hom).map P.y.iso.hom ≫
            P.y.y.iso.hom ≫
              (CatFiberedInGroupoids.homFunctor m.outer.hom).map P.iso.inv ≫
                (restrictionNatIso B S hS m).inv.app P.x :=
    ⟨(CatFiberedInGroupoids.homFunctor j.hom).preimageIso
      ((restrictionNatIso B S hS m).app P.y.x ≪≫
        (CatFiberedInGroupoids.homFunctor m.outer.hom).mapIso P.y.iso ≪≫
          P.y.y.iso ≪≫
            (CatFiberedInGroupoids.homFunctor m.outer.hom).mapIso P.iso.symm ≪≫
              ((restrictionNatIso B S hS m).app P.x).symm),
      (CatFiberedInGroupoids.homFunctor j.hom).map_preimage _⟩
  have hφv : 𝒴.val.val.p.IsHomLift (𝟙 P.base) φ.hom := by
    have hmap : 𝒴'.val.val.p.IsHomLift (𝟙 P.base)
        ((CatFiberedInGroupoids.homFunctor j.hom).map φ.hom) := by
      rw [hφ]
      exact @IsHomLift.comp_of_lift_id _ _ _ _ _ P.base _ _ _ _ _ v1
        (@IsHomLift.comp_of_lift_id _ _ _ _ _ P.base _ _ _ _ _ v2
          (@IsHomLift.comp_of_lift_id _ _ _ _ _ P.base _ _ _ _ _ v3
            (@IsHomLift.comp_of_lift_id _ _ _ _ _ P.base _ _ _ _ _ v4 v5)))
    exact Functor.isHomLift_of_isHomLift_map (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
      (𝟙 P.base) φ.hom
  refine ⟨{ base := P.base, x := P.y.x, y := P.x, hx := hb1, hy := P.hx, iso := φ
            vertical := hφv }, Iso.refl _,
    TwoFibreProductOver.isoMkVertical (U := P.base) (Iso.refl _)
      (TwoFibreProductOver.isoMkVertical (U := P.base) P.y.iso P.iso vx P.vertical ?_) vid1
      (TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 P.base) vx) ?_, vid2,
    TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 P.base) vid1, ?_⟩
  · change (CatFiberedInGroupoids.homFunctor m.outer.hom).map P.y.iso.hom ≫ P.y.y.iso.hom =
        ((restrictionNatIso B S hS m).inv.app P.y.x ≫
          (CatFiberedInGroupoids.homFunctor j.hom).map φ.hom ≫
            (restrictionNatIso B S hS m).hom.app P.x) ≫
          (CatFiberedInGroupoids.homFunctor m.outer.hom).map P.iso.hom
    -- `Iso.inv_hom_id_app_assoc` cancels the first pair of components of `E`, but no rewriting
    -- tactic can reach the second: the junction between `P.y.y.iso.hom` and the image of
    -- `P.iso.inv` is spelled through the projections of the 2-fibre product on one side and
    -- through the fields of the object on the other, so the composite is type-correct only once
    -- those projections are unfolded, and `Category.assoc` itself fails to match there. The
    -- cancellation is therefore done on abstract morphisms, where `simp` and `rw` do apply, and
    -- transported by an application, which is checked at default transparency.
    have key : ∀ {A₀ A₁ X Y Z W : 𝒴'.val.val.obj} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₀) (u : A₀ ⟶ X)
        (v : X ⟶ Y) (r : Y ⟶ Z) (s : Z ⟶ W) (s' : W ⟶ Z) (r' : Z ⟶ Y),
        a ≫ b = 𝟙 A₀ → s ≫ s' = 𝟙 Z → r ≫ r' = 𝟙 Y →
          (a ≫ (b ≫ u ≫ v ≫ r ≫ s) ≫ s') ≫ r' = u ≫ v := by
      intro A₀ A₁ X Y Z W a b u v r s s' r' ha hs hr
      simp only [Category.assoc]
      rw [← Category.assoc s s' r', hs, Category.id_comp, hr, Category.comp_id,
        ← Category.assoc a b (u ≫ v), ha, Category.id_comp]
    rw [hφ]
    exact (key ((restrictionNatIso B S hS m).inv.app P.y.x)
      ((restrictionNatIso B S hS m).hom.app P.y.x)
      ((CatFiberedInGroupoids.homFunctor m.outer.hom).map P.y.iso.hom) P.y.y.iso.hom
      ((CatFiberedInGroupoids.homFunctor m.outer.hom).map P.iso.inv)
      ((restrictionNatIso B S hS m).inv.app P.x)
      ((restrictionNatIso B S hS m).hom.app P.x)
      ((CatFiberedInGroupoids.homFunctor m.outer.hom).map P.iso.hom)
      (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_map _ _)).symm
  · change (CatFiberedInGroupoids.homFunctor i.hom).map (𝟙 P.y.x) ≫ P.y.iso.hom =
        𝟙 _ ≫ P.y.iso.hom
    simp
  · change (CatFiberedInGroupoids.homFunctor i.hom).map (𝟙 P.x) ≫ P.iso.hom = 𝟙 _ ≫ P.iso.hom
    simp

/-- **Stacks 0BPU, the first assertion, for the comparison with an explicit body.** For a morphism
of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the canonical
comparison 1-morphism `AlgebraicGeometry.Stack.selfProductDiagonalMap : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'`
is a thickening.

The source's factorisation of the comparison into two base changes of `i`, one factor at a time,
is carried here *strictly*: the comparison is `AlgebraicGeometry.Stack.selfProductFstLift`
followed by the base change of `i` along the first projection of `𝒳' ×_{𝒴'} 𝒳'`, on the nose
(`AlgebraicGeometry.Stack.selfProductFstLift_comp_snd`, which holds by `rfl`). The second factor
is a thickening by **Stacks 0BPR**
(`AlgebraicGeometry.Stack.isThickening_ambientFstRestriction_snd`); the first is one because
`AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductSndSquare` exhibits it too as a base change
of `i`, so **Stacks 0BPR** applies again; and their composite is a thickening by **Stacks 0BPS**,
`AlgebraicGeometry.Stack.isThickening_comp`.

This carries the part key *first assertion* of Stacks 0BPU, and together with
`AlgebraicGeometry.Stack.isTwoFibreProduct_selfProductDiagonalSquare` — which carries the part key
*cartesian diagonal square* — it puts **both** assertions of the tag on this one comparison
1-morphism. The part key *first assertion* is also carried by
`AlgebraicGeometry.Stack.isThickening_diagonalComparison`, the same assertion for the other
canonical comparison `AlgebraicGeometry.Stack.diagonalComparison`; that registration is kept, the
two comparisons being 2-isomorphic but not yet identified in the library.

The fppf-target-locality instance is Stacks 0420 and is discharged automatically, exactly as in
`AlgebraicGeometry.Stack.isThickening_diagonalComparison`. -/
@[stacks 0BPU "first assertion"]
theorem isThickening_selfProductDiagonalMap
    [(Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)] :
    IsThickening (selfProductDiagonalMap B S hS m) := by
  rw [← selfProductFstLift_comp_snd B S hS m]
  exact isThickening_comp _ _
    (isThickening_baseChange B S hS i
      ((ambientFstRestriction B S hS m).snd ≫ (ambientSelfProduct B S hS m).snd)
      (selfProductSndSquare B S hS m) (isTwoFibreProduct_selfProductSndSquare B S hS m) hi)
    (isThickening_ambientFstRestriction_snd B S hS m)
/-- **The diagonal square of a morphism of thickenings of algebraic stacks.** The 2-commutative
square

```text
  𝒳  --Δ-->  𝒳 ×_𝒴 𝒳
  |              |
 i|              | c
  v              v
  𝒳' --Δ'--> 𝒳' ×_{𝒴'} 𝒳'
```

over the cospan `(c, Δ')`, where `c` is
`AlgebraicGeometry.Stack.selfProductDiagonalMap` and the two relative diagonals are taken at the
canonical 2-fibre products of Stacks 04T2. Its filler is
`CategoryTheory.TwoFibreProductOver.selfProductDiagonalFiller`, both components of every
component of which are identities, and every component of which is vertical. -/
def selfProductDiagonalSquare :
    Bicategory.TwoCommSq (selfProductDiagonalMap B S hS m)
      (AlgebraicStacks.relativeDiagonal B S hS m.outer) where
  pt := 𝒳
  fst := AlgebraicStacks.relativeDiagonal B S hS m.inner
  snd := i
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (TwoFibreProductOver.selfProductDiagonalFiller
        (CatFiberedInGroupoids.homFunctor_comp_p m.inner.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m))
      (TwoFibreProductOver.isHomLift_selfProductDiagonalFiller
        (CatFiberedInGroupoids.homFunctor_comp_p m.inner.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m))))

/-- The canonical pre-morphism of 2-commutative squares (**Stacks 003O**) from the square of
categories fibred in groupoids underlying
`AlgebraicGeometry.Stack.selfProductDiagonalSquare` to the canonical 2-fibre product square of
its cospan. Its 1-morphism is
`CategoryTheory.TwoFibreProductOver.selfProductDiagonalComparison`, and both of its comparison
2-cells are identities, that functor being strictly compatible with the two projections; the
compatibility square of Stacks 003O then reduces to
`CategoryTheory.CatFiberedInGroupoids.map_id_comp_id_eq`, exactly as it does in
`AlgebraicGeometry.Stack.diagonalBaseChangePreHom`. -/
def selfProductDiagonalPreHom :
    Bicategory.TwoCommSq.PreHom
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS (selfProductDiagonalSquare B S hS m))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (selfProductDiagonalMap B S hS m).hom
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom) where
  hom := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.selfProductDiagonalComparison
        (CatFiberedInGroupoids.homFunctor_comp_p m.inner.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m)
      w := TwoFibreProductOver.selfProductDiagonalComparison_comp_structureFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p m.inner.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m) }
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    change (AlgebraicStacks.toCatFiberedInGroupoids B S hS
          (selfProductDiagonalSquare B S hS m)).iso.hom.hom.toNatTrans.app x ≫
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ =
      (selfProductDiagonalMap B S hS m).hom.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (AlgebraicStacks.toCatFiberedInGroupoids B S hS
          (selfProductDiagonalSquare B S hS m)).iso.hom.hom.toNatTrans.app x
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (selfProductDiagonalMap B S hS m).hom.hom.toFunctor
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom.hom.toFunctor
      ((AlgebraicStacks.toCatFiberedInGroupoids B S hS
        (selfProductDiagonalSquare B S hS m)).iso.hom.hom.toNatTrans.app x)

/-- **Stacks 0BPU, the second assertion: the diagonal square of a morphism of thickenings of
algebraic stacks is cartesian.** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the square

```text
  𝒳  --Δ-->  𝒳 ×_𝒴 𝒳
  |              |
  v              v
  𝒳' --Δ'--> 𝒳' ×_{𝒴'} 𝒳'
```

is a 2-fibre product in the 2-category of algebraic stacks over `(Sch/S)_fppf`, the right-hand
leg being the canonical comparison
`AlgebraicGeometry.Stack.selfProductDiagonalMap` — canonical strictly, by
`AlgebraicGeometry.Stack.selfProductDiagonalMap_comp_fst` and `…_comp_snd`.

The source proves this by applying **Stacks 0CBB** to `𝒳 ⟶ 𝒳' ⟶ 𝒴'`, using that the thickening
`i : 𝒳 ⟶ 𝒳'` is a monomorphism. Here it is the over-the-base form of 0CBB with a growing target,
`CategoryTheory.TwoFibreProductOver.isEquivalence_selfProductDiagonalComparison`, whose three
hypotheses are met because a closed immersion of algebraic stacks is fully faithful
(**Stacks 04ZZ** (1) ⟹ (2),
`AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion`),
applied to `i` for fullness and faithfulness and to `j` for the faithfulness the growing target
costs. The passage from an equivalence of underlying categories to the universal property is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` against the canonical 2-fibre
product square of the cospan, and the passage from the 2-category of categories fibred in
groupoids down to the full sub-2-category of algebraic stacks is
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids`.

This carries the part key *cartesian diagonal square* of Stacks 0BPU; the other assertion, that
the comparison is a thickening, is
`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`, for **this same** comparison
1-morphism, so the two assertions of the tag are both statements about
`AlgebraicGeometry.Stack.selfProductDiagonalMap`. The first assertion is registered a second time
on `AlgebraicGeometry.Stack.isThickening_diagonalComparison`, which asserts it of the other
canonical comparison `AlgebraicGeometry.Stack.diagonalComparison`; the implementation note above
says why the cartesian assertion cannot be carried by that one.

**What identifying the two comparisons still lacks.** The two 1-morphisms are 2-isomorphic, being
two canonical comparisons into a 2-fibre product, and
`AlgebraicGeometry.Stack.isThickening_congr_twoIso` would then make either of the two
first-assertion registrations redundant. The 2-isomorphism is *not* available from
`CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_legs`, however: that result needs the two
comparison 2-cells to be compatible with the filler of `𝒳' ×_{𝒴'} 𝒳'`, and that compatibility
mentions the filler whiskered by `AlgebraicGeometry.Stack.diagonalComparison`, which is the very
thing the `Quotient.out` in `AlgebraicGeometry.Stack.selfProductComparison` makes uncomputable.
It would instead have to come from
`CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_preHom`, i.e. by exhibiting
`AlgebraicGeometry.Stack.diagonalComparison` as the 1-morphism of a pre-morphism of
2-commutative squares assembled by `CategoryTheory.Bicategory.TwoCommSq.PreHom.comp` from its
four stages — the enlargement of the target, the comparison of the two models of the cospan
`(f ≫ j, f ≫ j)`, and the two base changes of `i` — which is a chase through two cospan
reindexings that the library does not currently assemble. -/
@[stacks 0BPU "cartesian diagonal square"]
def isTwoFibreProduct_selfProductDiagonalSquare :
    Bicategory.IsTwoFibreProduct (selfProductDiagonalSquare B S hS m) := by
  obtain ⟨hifull, hifaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS i hi.1
  obtain ⟨-, hjfaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion B S hS j hj.1
  have _ := hifull
  have _ := hifaith
  have _ := hjfaith
  exact AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (selfProductDiagonalMap B S hS m).hom
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom)
      (selfProductDiagonalPreHom B S hS m)
      (TwoFibreProductOver.isEquivalence_selfProductDiagonalComparison
        (CatFiberedInGroupoids.homFunctor_comp_p m.inner.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p m.outer.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p i.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p j.hom)
        (restrictionNatIso B S hS m) (isHomLift_restrictionNatIso B S hS m)))

/-! ### The two diagonals as a morphism of thickenings (Stacks 0BPV) -/

/-- **The two relative diagonals of a morphism of thickenings of algebraic stacks form a morphism
of thickenings.** For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` the pair
`(Δ, Δ')` of relative diagonals is a morphism of thickenings
`(𝒳 ⊂ 𝒳') → (𝒳 ×_𝒴 𝒳 ⊂ 𝒳' ×_{𝒴'} 𝒳')`: the restriction square is the diagonal square of
**Stacks 0BPU**, which 2-commutes by its filler, and the target thickening is the comparison
1-morphism `AlgebraicGeometry.Stack.selfProductDiagonalMap`.

This is the step with which the source's proof of **Stacks 0BPV** opens. The hypothesis `hk` is
the first assertion of Stacks 0BPU *for this comparison*, which is
`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`: every call site can supply it from
there. It stays a parameter so that the shape of this definition and of its two consumers is
unchanged. -/
def diagonalThickeningMorphism (hk : IsThickening (selfProductDiagonalMap B S hS m)) :
    ThickeningMorphism i (selfProductDiagonalMap B S hS m) hi hk where
  outer := AlgebraicStacks.relativeDiagonal B S hS m.outer
  inner := AlgebraicStacks.relativeDiagonal B S hS m.inner
  comm := (selfProductDiagonalSquare B S hS m).iso

/-- **Stacks 0BPV at the surjectivity property.** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective (**Stacks 04ZS**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is.

The two diagonals are a morphism of thickenings
(`AlgebraicGeometry.Stack.diagonalThickeningMorphism`), and surjectivity passes between the two
1-morphisms of a morphism of thickenings by **Stacks 0CJ9** part (2).

*Parameter*: `hk`, that the comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` of
`AlgebraicGeometry.Stack.selfProductDiagonalMap` is a thickening. That is the first assertion of
**Stacks 0BPU**, proved in `AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`; see
`AlgebraicGeometry.Stack.diagonalThickeningMorphism`. -/
@[stacks 0BPV "surjective (granted: the diagonal comparison is a thickening)"]
theorem isSurjective_relativeDiagonal_iff
    (hk : IsThickening (selfProductDiagonalMap B S hS m)) :
    IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner) ↔
      IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer) :=
  isSurjective_inner_iff_outer (diagonalThickeningMorphism B S hS m hk)

end Diagonal

end AlgebraicGeometry.Stack

end
