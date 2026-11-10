module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubmersiveComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyOpenSubmersiveBaseChange

/-!
# Universal homeomorphisms of algebraic stacks (Stacks 0CI7, 0CI9)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a *universal homeomorphism*
(**Stacks 0CI7**) when for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S` the map
`|𝒵 ×_𝒴 𝒳| → |𝒵|` on the points of Stacks 04XG, for the topology of Stacks 04XL, is a
homeomorphism. **Stacks 0CI9** says the notion is stable under composition.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsHomeomorphOnPoints`: the non-universal condition.
* `AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`: **Stacks 0CI7**.

## Main results

* `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_of_isEquivalence`: an equivalence over the site
  is a homeomorphism on points.
* `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_fst_congr`: being a homeomorphism on points is a
  property of the first projection of a cospan, not of the chosen 2-fibre product.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isHomeomorphOnPoints_comp`: the non-universal
  composition statement.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universalHomeomorphism_comp`: **Stacks 0CI9**.

## Implementation notes

For a 1-morphism representable by algebraic spaces the notion is the relative one of
Properties of Stacks, Section 04XB; **Stacks 0CI6** identifies that notion with the condition
above, which Stacks 0CI7 then takes as the definition for an arbitrary 1-morphism. It is the
latter, absolute notion that is defined here, in the shape the library already uses for universal
closedness (**Stacks 0513**, part (2)) and universal openness (**Stacks 06U2**, part (2)): the
quantifier ranges over the canonical 2-fibre product square of Stacks 04T2 for the cospan
`(g, f)`, and `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_fst_congr` shows that any other
2-fibre product of that cospan would give the same condition.

The source's proof of Stacks 0CI9 reads *"Omitted."* The argument is the pasting law for 2-fibre
products, exactly as for `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_comp`
(**Stacks 0515**): for `k : 𝒲 ⟶ 𝒵` the base change of `f ≫ g` along `k` is the outer rectangle
of a base change of `g` along `k` followed by a base change of `f` along the resulting
projection, so its first leg is a composite of two maps on points that are homeomorphisms by
hypothesis.

A homeomorphism on points transports along an equivalence over the site in both directions, so
unlike the closed case no `iff` form of the transport is needed: the composite route of
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` applies verbatim, with
`IsHomeomorph.comp` in place of `IsOpenMap.comp`.

The leaf names match `AlgebraicGeometry.Space` and `AlgebraicGeometry.Scheme` siblings for
morphisms of algebraic spaces and of schemes; those are different notions about different
objects, distinguished by namespace as elsewhere in this library.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CI6](https://stacks.math.columbia.edu/tag/0CI6)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
* [Stacks Project, Tag 0CI9](https://stacks.math.columbia.edu/tag/0CI9)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points of a based functor whose underlying functor is an equivalence of categories
is a homeomorphism for the topology of Tag 04XL. -/
theorem isHomeomorph_pointsMap_of_isEquivalence
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : 𝒜.val ⥤ᵇ 𝒞.val) (hF : F.toFunctor.IsEquivalence) :
    @IsHomeomorph (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property F) := by
  let _ := pointTopology B S hS 𝒜
  let _ := pointTopology B S hS 𝒞
  obtain ⟨e, he⟩ := exists_basedEquivalence_functor_eq B S hS 𝒜 𝒞 F hF
  rw [← he]
  exact Homeomorph.isHomeomorph (pointsHomeomorphOfBasedEquivalence B S hS 𝒜 𝒞 e)

/-- **Being a homeomorphism on points is a property of the cospan.** Any two 2-fibre products of
one cospan of categories fibred in groupoids over the big fppf site of `S` have first projections
which are homeomorphisms on points together: the comparison 1-morphism has an underlying
equivalence of categories, so its map on points is a homeomorphism, and it identifies the two
projections. -/
theorem isHomeomorph_pointsMap_fst_congr
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @IsHomeomorph _ _ (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)) :
    @IsHomeomorph _ _ (pointTopology B S hS Q.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom) := by
  let _ := pointTopology B S hS P.pt
  let _ := pointTopology B S hS Q.pt
  let _ := pointTopology B S hS 𝒵
  let a := Quotient.out (hP.from Q)
  rw [pointsMap_fst_comp_eq B S hS a]
  exact h.comp (isHomeomorph_pointsMap_of_isEquivalence B S hS Q.pt P.pt a.hom.hom
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hP a))

namespace AlgebraicStacks

universe w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks over `S` *is a homeomorphism on points* when the map
`|𝒳| → |𝒴|` it induces on the topological spaces of points of Stacks 04XG and 04XL is a
homeomorphism. -/
abbrev IsHomeomorphOnPoints {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  letI := Stack.pointTopology B S hS 𝒴.val
  IsHomeomorph (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)

/-- **Stacks 0CI7.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a *universal
homeomorphism* when, for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S`, the base
change `𝒵 ×_{g, 𝒴, f} 𝒳 ⟶ 𝒵` of `f` by `g` induces a homeomorphism `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the
points of Stacks 04XG for the topology of Stacks 04XL.

For a 1-morphism representable by algebraic spaces this agrees with the relative notion of
Stacks 04XB, by **Stacks 0CI6**. -/
@[stacks 0CI7]
abbrev UniversalHomeomorphism {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
    IsHomeomorphOnPoints B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst

/-- The composite of two 1-morphisms of algebraic stacks over `S` which are homeomorphisms on
points is a homeomorphism on points, since the map on points of Stacks 04XG takes a composite of
1-morphisms to the composite of the maps. -/
theorem isHomeomorphOnPoints_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsHomeomorphOnPoints B S hS f)
    (hg : IsHomeomorphOnPoints B S hS g) : IsHomeomorphOnPoints B S hS (f ≫ g) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  change IsHomeomorph
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒵.val.property (f ≫ g).hom.hom)
  rw [pointsMap_comp' B S hS f g]
  exact hg.comp hf

/-- **Stacks 0CI9.** The composite of two universal homeomorphisms of algebraic stacks over `S`
is a universal homeomorphism.

A base change of `f ≫ g` along `k` is the outer rectangle of a base change of `g` along `k`
followed by a base change of `f` along the resulting projection, by the pasting law for 2-fibre
products; the two legs of that rectangle are homeomorphisms on points by hypothesis, so the
rectangle's own first leg is one too, and that condition depends only on the cospan. -/
@[stacks 0CI9]
theorem universalHomeomorphism_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : UniversalHomeomorphism B S hS f) (hg : UniversalHomeomorphism B S hS g) :
    UniversalHomeomorphism B S hS (f ≫ g) := by
  intro 𝒲 k
  have hA := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k g
  set A := Stack.twoFibreProductSquareAlgebraicStacks B S hS k g
  have hC := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS A.snd f
  set C := Stack.twoFibreProductSquareAlgebraicStacks B S hS A.snd f
  exact Stack.isHomeomorph_pointsMap_fst_congr B S hS
    (A.paste C).underlying
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Bicategory.isTwoFibreProduct_paste hA hC))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)))
    (isHomeomorphOnPoints_comp B S hS C.fst A.fst (hf A.pt A.snd) (hg 𝒲 k))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
