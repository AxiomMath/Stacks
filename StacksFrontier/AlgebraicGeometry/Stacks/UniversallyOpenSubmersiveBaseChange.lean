module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsEquivalenceHomeomorph
public import StacksFrontier.AlgebraicGeometry.Stacks.SubmersiveAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Universal openness and universal submersiveness are stable under base change (Stacks 06U3, 0CHY)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *universally open*
(`AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen`, **Stacks 06U2** part (2)) when every
base change of it is open on the topological spaces of points of Stacks 04XG and 04XL, and
*universally submersive* (`...IsUniversallySubmersive`, **Stacks 06U6** part (2)) when every base
change of it is a quotient map on those spaces. This file proves **Stacks 06U3** and **Stacks
0CHY**: both properties are inherited by a base change, so that if `f` has one of them and `R` is
*any* 2-fibre product square of a cospan `(g, f)`, then the first projection `R.fst` — the base
change of `f` along `g` — has it too.

The content is the pasting law for 2-fibre products,
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`, and nothing else. A base change of
`R.fst` along `h : 𝒵 ⟶ 𝒴'` is the outer rectangle of

```text
             R.fst
  𝒵 ×_𝒴' R.pt ---> R.pt ---> 𝒳
      |              |        |
   h' |              |        | f
      v              v        v
      𝒵 -----h----> 𝒴' ---g--> 𝒴
```

so it is *also* a 2-fibre product of the cospan `(h ≫ g, f)`; and a base change of `f` along
`h ≫ g` is open (resp. submersive) because `f` is universally open (resp. universally
submersive), by definition and with no further argument. The point-topological property then
transfers between the two 2-fibre products of that one cospan by
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` resp.
`...isQuotientMap_pointsMap_fst_congr`.

So each statement is the quantifier in the definition reindexed along `h ↦ h ≫ g`, and the
pasting law is what licenses the reindexing. This is the open and submersive mirror of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_baseChange_of_isTwoFibreProduct`
(**Stacks 0514**), and the two obvious alternative routes are unavailable for the same reasons
there: there is no stability theorem for `...IsOpen` or `...IsSubmersive` to invoke, and the
canonical iterated apex of Stacks 02XD
(`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks`) recognises one
*particular* apex rather than an arbitrary pair of squares, so it cannot see `R`.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_fst_comp_eq`: the map on points of one 2-fibre product's
  first projection factors through another's.
* `AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` and
  `...isQuotientMap_pointsMap_fst_congr`: openness resp. the quotient-map condition on points of
  the first projection is a property of the cospan.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyOpen_baseChange_of_isTwoFibreProduct`:
  **Stacks 06U3**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isUniversallySubmersive_baseChange_of_isTwoFibreProduct`
  (**Stacks 0CHY**).

## Implementation notes

The two congruence lemmas are the open and quotient-map siblings of the already available
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr`, and they are proved here from public
material rather than by reusing that lemma's own route: the comparison 1-morphism between two
2-fibre products of one cospan has an underlying equivalence of categories by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, whose map on points is therefore
open and a quotient map by `AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_isEquivalence` and
`...isQuotientMap_pointsMap_of_isEquivalence`, and the comparison identifies the two first
projections up to a vertical 2-isomorphism, which
`AlgebraicGeometry.Stack.pointsMap_eq_of_basedNatTrans` says leaves the map on points unchanged.
Each property is then closed under composition. No homeomorphism is constructed, because neither
property needs one.

Both statements are made at an **arbitrary** 2-fibre product square rather than at the canonical
one of Stacks 04T2, following Stacks 0514 and its siblings: the canonical form is the one-term
instantiation `R := AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks B S hS g f`, and
stating it at an arbitrary square costs nothing because
`CategoryTheory.Bicategory.TwoCommSq.pasteFst` already takes an arbitrary outer square.

The `@[stacks 06U3]` and `@[stacks 0CHY]` attributes each sit on a single theorem, which is that
tag's whole covering set. Stacks 06U2 part (2) and Stacks 06U6 part (2) are the *definitions* of
the two universal properties and their covering sets are carried separately by
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen` and `...IsUniversallySubmersive`;
base-change stability is the assertion of the lemmas that follow those definitions, whose proofs
the source gives as *"this is immediate from the definition"*.

The topology of Stacks 04XL takes no algebraicity hypothesis, so the three lemmas in the
`AlgebraicGeometry.Stack` namespace are stated for arbitrary categories fibred in groupoids.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0514](https://stacks.math.columbia.edu/tag/0514)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 06U3](https://stacks.math.columbia.edu/tag/06U3)
* [Stacks Project, Tag 06U6](https://stacks.math.columbia.edu/tag/06U6)
* [Stacks Project, Tag 0CHY](https://stacks.math.columbia.edu/tag/0CHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The map on points of one 2-fibre product's first projection factors through another's.**
A comparison 1-morphism `a : Q ⟶ P` between two 2-commutative squares over one cospan identifies
`Q.fst` with `a.hom ≫ P.fst` up to a vertical 2-isomorphism, and 2-isomorphic 1-morphisms induce
the same map on points of Stacks 04XG. -/
theorem pointsMap_fst_comp_eq
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {P Q : Bicategory.TwoCommSq g f}
    (a : Bicategory.TwoCommSq.PreHom Q P) :
    pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom =
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom) ∘
        (pointsMap B S hS Q.pt.val Q.pt.property P.pt.property a.hom.hom) := by
  funext x
  exact (congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property 𝒵.property
      a.isoFst.hom.hom) x).trans
    (pointsMap_comp B S hS Q.pt.val Q.pt.property P.pt.property 𝒵.property
      a.hom.hom P.fst.hom x).symm

/-- **Openness on points of the first projection is a property of the cospan.** Any two 2-fibre
products of one cospan of categories fibred in groupoids over the big fppf site of `S` have first
projections which are open on points together: the comparison 1-morphism has an underlying
equivalence of categories, so its map on points is open, and it identifies the two projections. -/
theorem isOpenMap_pointsMap_fst_congr
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @IsOpenMap _ _ (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)) :
    @IsOpenMap _ _ (pointTopology B S hS Q.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom) := by
  let _ := pointTopology B S hS P.pt
  let _ := pointTopology B S hS Q.pt
  let _ := pointTopology B S hS 𝒵
  let a := Quotient.out (hP.from Q)
  rw [pointsMap_fst_comp_eq B S hS a]
  exact h.comp (isOpenMap_pointsMap_of_isEquivalence B S hS Q.pt P.pt a.hom.hom
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hP a))

/-- **The quotient-map condition on points of the first projection is a property of the cospan.**
Any two 2-fibre products of one cospan of categories fibred in groupoids over the big fppf site
of `S` have first projections which are quotient maps on points together, i.e. submersive in the
sense of Stacks 0406. -/
theorem isQuotientMap_pointsMap_fst_congr
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @Topology.IsQuotientMap _ _ (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)) :
    @Topology.IsQuotientMap _ _ (pointTopology B S hS Q.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom) := by
  let _ := pointTopology B S hS P.pt
  let _ := pointTopology B S hS Q.pt
  let _ := pointTopology B S hS 𝒵
  let a := Quotient.out (hP.from Q)
  rw [pointsMap_fst_comp_eq B S hS a]
  exact h.comp (isQuotientMap_pointsMap_of_isEquivalence B S hS Q.pt P.pt a.hom.hom
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hP a))

namespace AlgebraicStacks

universe w

/-- The underlying square of the outer rectangle of a base change of `R.fst` is a 2-fibre
product. -/
private noncomputable def isTwoFibreProduct_underlying_pasteFst
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (h : 𝒵 ⟶ 𝒴') :
    Bicategory.IsTwoFibreProduct
      (R.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)).underlying :=
  Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
    (Bicategory.isTwoFibreProduct_pasteFst R hR
      (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h R.fst))

/-- **Stacks 06U3.** Universal openness is stable under base change: let `f : 𝒳 ⟶ 𝒴` be a
universally open 1-morphism of algebraic stacks over `S` and let `R` be a 2-fibre product square
of the cospan `(g, f)` for some `g : 𝒴' ⟶ 𝒴`. Then the base change `R.fst : R.pt ⟶ 𝒴'` of `f`
along `g` is universally open.

The square is arbitrary, so this applies to any square a consumer has already exhibited as a
2-fibre product rather than only to the canonical one of Stacks 04T2. -/
@[stacks 06U3]
theorem universallyOpen_baseChange_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : UniversallyOpen B S hS f) :
    UniversallyOpen B S hS R.fst := fun 𝒵 h =>
  Stack.isOpenMap_pointsMap_fst_congr B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f).underlying
    (R.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f))
    (isTwoFibreProduct_underlying_pasteFst B S hS R hR 𝒵 h)
    (hf 𝒵 (h ≫ g))

/-- **Stacks 0CHY.** Universal submersiveness is stable under base change: let `f : 𝒳 ⟶ 𝒴` be a
universally submersive 1-morphism of algebraic stacks over `S` and let `R` be a 2-fibre product
square of the cospan `(g, f)` for some `g : 𝒴' ⟶ 𝒴`. Then the base change `R.fst : R.pt ⟶ 𝒴'` of
`f` along `g` is universally submersive.

The square is arbitrary, so this applies to any square a consumer has already exhibited as a
2-fibre product rather than only to the canonical one of Stacks 04T2. -/
@[stacks 0CHY]
theorem isUniversallySubmersive_baseChange_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsUniversallySubmersive B S hS f) :
    IsUniversallySubmersive B S hS R.fst := fun 𝒵 h =>
  Stack.isQuotientMap_pointsMap_fst_congr B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f).underlying
    (R.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f))
    (isTwoFibreProduct_underlying_pasteFst B S hS R hR 𝒵 h)
    (hf 𝒵 (h ≫ g))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
