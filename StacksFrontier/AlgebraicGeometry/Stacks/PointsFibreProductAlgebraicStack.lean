module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Points of a 2-fibre product of algebraic stacks (Stacks 04XH)

Let `g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴` be 1-morphisms of algebraic stacks over the big fppf site of
`S`, and let `P` be a 2-fibre product of that cospan *in the 2-category of algebraic stacks*.
The canonical map

```text
|P| ⟶ |𝒵| ×_{|𝒴|} |𝒳|
```

is surjective. This is **Stacks 04XH** as the source states it: the source's lemma is about a
fibre product of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.exists_point_of_isTwoFibreProduct_algebraicStacks`: **Stacks 04XH**.
* `AlgebraicGeometry.Stack.exists_point_of_comparison`: the transport of a lifted point along a
  comparison 1-morphism between two 2-commutative squares over one cospan.

## Implementation notes

The companion `AlgebraicGeometry.Stack.exists_point_of_isTwoFibreProduct` proves the same
elementwise conclusion for a 2-fibre product in the 2-category of **categories fibred in
groupoids**, and it does *not* specialise to the statement here. The 2-category of algebraic
stacks is a `CategoryTheory.Bicategory.InducedBicategory` over the subtype of the algebraic
stacks, so a 2-commutative square there has its apex — and, through terminality, its test
objects — ranging over algebraic stacks only, whereas the hypothesis
`CategoryTheory.Bicategory.IsTwoFibreProduct` at the level of categories fibred in groupoids
quantifies over *every* category fibred in groupoids. The latter hypothesis is therefore
strictly stronger and cannot be produced from the former: the implication runs the wrong way.

What bridges the two levels is that the universal property is only ever applied to *one* test
square, the canonical one, which is an object of the category of 2-commutative squares of
algebraic stacks by `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`. Terminality
of `P` there supplies a comparison 1-morphism out of it, and `exists_point_of_comparison`
carries along that comparison the point which the companion theorem constructs on the canonical
apex.

`exists_point_of_comparison` is stated for the underlying based categories, functors and natural
transformations rather than for a `CategoryTheory.Bicategory.TwoCommSq.PreHom`, so that it
applies verbatim at both levels of the tower: the comparison data of a pre-morphism of squares
of algebraic stacks is reached by one more `.hom` projection than at the level of categories
fibred in groupoids, and the two agree after those projections.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport of a lifted point along a comparison 1-morphism of 2-commutative squares.**
Let `Tfst`, `Tsnd` and `Qfst`, `Qsnd` be the legs of two 2-commutative squares over one cospan,
and let `H` be a comparison 1-morphism from the first apex to the second, with 2-morphisms
identifying each leg of the first square with `H` followed by the corresponding leg of the
second. Then a point of the first apex over a given pair of points of the two factors induces
one of the second apex.

The data is taken as based functors and based natural transformations rather than as a
`CategoryTheory.Bicategory.TwoCommSq.PreHom`, so that the lemma applies to a pre-morphism of
squares of categories fibred in groupoids and to one of squares of algebraic stacks alike. -/
theorem exists_point_of_comparison
    {𝒵 𝒳 T Q : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (hZ : 𝒵.p.IsFiberedInGroupoids) (hX : 𝒳.p.IsFiberedInGroupoids)
    (hT : T.p.IsFiberedInGroupoids) (hQ : Q.p.IsFiberedInGroupoids)
    {Tfst : T ⥤ᵇ 𝒵} {Tsnd : T ⥤ᵇ 𝒳} {Qfst : Q ⥤ᵇ 𝒵} {Qsnd : Q ⥤ᵇ 𝒳}
    (H : T ⥤ᵇ Q)
    (ηfst : BasedNatTrans Tfst (H.comp Qfst)) (ηsnd : BasedNatTrans Tsnd (H.comp Qsnd))
    {z : points B S hS 𝒵 hZ} {x : points B S hS 𝒳 hX} {q : points B S hS T hT}
    (hq₁ : pointsMap B S hS T hT hZ Tfst q = z)
    (hq₂ : pointsMap B S hS T hT hX Tsnd q = x) :
    ∃ p : points B S hS Q hQ,
      pointsMap B S hS Q hQ hZ Qfst p = z ∧ pointsMap B S hS Q hQ hX Qsnd p = x :=
  ⟨pointsMap B S hS T hT hQ H q,
    (pointsMap_comp B S hS T hT hQ hZ H Qfst q).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS T hT hZ ηfst) q).symm.trans hq₁),
    (pointsMap_comp B S hS T hT hQ hX H Qsnd q).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS T hT hX ηsnd) q).symm.trans hq₂)⟩

/-- **Stacks 04XH.** Let `g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴` be 1-morphisms of algebraic stacks over
`S` and let `P` be a 2-fibre product of that cospan in the 2-category of algebraic stacks. A
point of `𝒵` and a point of `𝒳` with the same image in `|𝒴|` lift to a point of `P`; that is,
the canonical map `|P| ⟶ |𝒵| ×_{|𝒴|} |𝒳|` is surjective. -/
@[stacks 04XH]
theorem exists_point_of_isTwoFibreProduct_algebraicStacks
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (z : points B S hS 𝒵.val.val (Classical.choose 𝒵.property))
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (h : pointsMap B S hS 𝒵.val.val (Classical.choose 𝒵.property)
          (Classical.choose 𝒴.property) g.hom.hom z =
        pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
          (Classical.choose 𝒴.property) f.hom.hom x) :
    ∃ p : points B S hS P.pt.val.val (Classical.choose P.pt.property),
      pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
          (Classical.choose 𝒵.property) P.fst.hom.hom p = z ∧
        pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
          (Classical.choose 𝒳.property) P.snd.hom.hom p = x := by
  classical
  obtain ⟨q, hq₁, hq₂⟩ := exists_point_of_isTwoFibreProduct B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom f.hom) z x h
  obtain ⟨α, -⟩ :=
    Quotient.exists_rep (hP.from (twoFibreProductSquareAlgebraicStacks B S hS g f))
  exact exists_point_of_comparison B S hS _ _ _ _ α.hom.hom.hom
    α.isoFst.hom.hom.hom α.isoSnd.hom.hom.hom hq₁ hq₂

end AlgebraicGeometry.Stack

end
