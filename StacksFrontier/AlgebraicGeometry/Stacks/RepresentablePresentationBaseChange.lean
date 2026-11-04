module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Base change of a presentation along a morphism representable by algebraic spaces

Let `g : 𝒳' ⟶ 𝒳` be a morphism of algebraic stacks, let `f : 𝒰 ⟶ 𝒳` be an atlas and let
`R = 𝒰 ×_𝒳 𝒰` be its relation, so that `[U/R] ⟶ 𝒳` is a presentation. Stacks 04Y6 base changes
that presentation along `g`: it sets `U' = 𝒰 ×_𝒳 𝒳'` and `R' = R ×_𝒳 𝒳'`, and produces a
groupoid in algebraic spaces `(U', R', s', t', c')`, a presentation `[U'/R'] ⟶ 𝒳'` and a
morphism of groupoids `pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)` inducing a 2-commutative
square of quotient stacks.

This file carries the step of its proof that the rest rests on, the displayed chain

    R ×_𝒳 𝒳' = 𝒰 ×_𝒳 𝒰 ×_𝒳 𝒳' = (𝒰 ×_𝒳 𝒳') ×_{𝒳'} (𝒰 ×_𝒳 𝒳'),

that is: the base change of the relation is the self-intersection of the base-changed atlas, so
that `R' = U' ×_{𝒳'} U'` and the hypothesis of Stacks 04T5 is met. The middle term is the triple
product, and both outer terms are exhibited as 2-fibre products of the one cospan
`(f, pr_𝒰 ≫ f)` that names it; being terminal in one and the same category of 2-commutative
squares, they agree together with their two projections.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.baseChangedSelfIntersection`: the self-intersection of
  the base-changed atlas, read as a square over the cospan naming the triple product.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_baseChangedSelfIntersection`: that square is a
  2-fibre product, i.e. `U' ×_{𝒳'} U' = 𝒰 ×_𝒳 U'`.
* `CategoryTheory.Bicategory.isTwoFibreProduct_relationBaseChange`: the base change of `R` along
  the atlas of `𝒳'` is a base change of `R` along `g`, i.e. `R ×_{s, 𝒰} U' = R ×_𝒳 𝒳'`.
* `CategoryTheory.Bicategory.isTwoFibreProduct_relationBaseChangeTriple`: the same object is
  `𝒰 ×_𝒳 U'`.
* `CategoryTheory.Bicategory.nonempty_iso_baseChangedSelfIntersection`: the two therefore agree.
* In `CategoryTheory.CatFiberedInGroupoids.RepresentablePresentation`, the two theorems
  `isTwoFibreProduct_relationBaseChangeSquare` and `nonempty_iso_baseChangedRelationSquare`:
  **Stacks 04Y6**, the same two statements for the canonical 2-fibre products of a cospan of
  categories fibred in groupoids, where every object in sight is constructed and no hypothesis
  is carried.

## Implementation notes

The source cites Categories, Lemmas 02XC and 02XD for the chain. Neither is used here: both
identifications are instances of the pasting law for 2-fibre products,
`CategoryTheory.Bicategory.isTwoFibreProduct_paste` and `...isTwoFibreProduct_pasteFst`, which
is the form in which the library has the content of those lemmas for an arbitrary bicategory.
The two routes to the triple product land on cospans whose second leg is `pr_𝒰 ≫ f` on one side
and `p' ≫ g` on the other; the filler of the square defining `U'` is a 2-isomorphism between
them, and `CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` moves one to the other.

Nothing beyond the universal property of the four squares is used, so the abstract statements
hold in an arbitrary bicategory: neither the algebraicity of `𝒳` and `𝒳'` nor the
representability of `g` by algebraic spaces plays any part in this step. Those hypotheses enter
Stacks 04Y6 elsewhere — in knowing that `U'` and `R'` are algebraic spaces, that `U' ⟶ 𝒳'` is
smooth and surjective (Stacks 04X0), and hence in building the groupoid and the presentation
through Stacks 04T4 and 04T5 and the induced morphism of quotient stacks through Stacks 046Q.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XC](https://stacks.math.columbia.edu/tag/02XC)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A] {𝒳 𝒳' 𝒰 : A} {g : 𝒳' ⟶ 𝒳} {f : 𝒰 ⟶ 𝒳}

/-- **The self-intersection of a base-changed atlas, read over the triple product.** Let `SU` be
a square over `(f, g)`, thought of as `U' = 𝒰 ×_𝒳 𝒳'`, and let `SRel` be a square over
`(SU.snd, SU.snd)`, thought of as `U' ×_{𝒳'} U'`. Pasting the two and reindexing the resulting
cospan leg `p' ≫ g` along the filler of `SU` presents `SRel` as a square over `(f, pr_𝒰 ≫ f)`,
the cospan naming the triple product `𝒰 ×_𝒳 𝒰 ×_𝒳 𝒳'`. -/
@[reducible]
def TwoCommSq.baseChangedSelfIntersection (SU : TwoCommSq f g)
    (SRel : TwoCommSq SU.snd SU.snd) : TwoCommSq f (SU.fst ≫ f) :=
  (SU.paste SRel).reindexSnd SU.iso.symm

/-- **The self-intersection of a base-changed atlas is the triple product.** If `U' = 𝒰 ×_𝒳 𝒳'`
and `R' = U' ×_{𝒳'} U'`, then `R' = 𝒰 ×_𝒳 U'`, the apex of a 2-fibre product of the cospan
`(f, pr_𝒰 ≫ f)`. -/
noncomputable def isTwoFibreProduct_baseChangedSelfIntersection {SU : TwoCommSq f g}
    (hSU : IsTwoFibreProduct SU) {SRel : TwoCommSq SU.snd SU.snd}
    (hSRel : IsTwoFibreProduct SRel) :
    IsTwoFibreProduct (SU.baseChangedSelfIntersection SRel) :=
  isTwoFibreProduct_reindexSnd SU.iso.symm (isTwoFibreProduct_paste hSU hSRel)

/-- **The base change of the relation along `g`.** If `U' = 𝒰 ×_𝒳 𝒳'` and `SBC` is a square over
`(SR.snd, SU.fst)`, thought of as `R ×_{s, 𝒰} U'`, then its apex is a base change of `R` along
`g`: it is the apex of a 2-fibre product of the cospan `(s ≫ f, g)`. -/
noncomputable def isTwoFibreProduct_relationBaseChange (SU : TwoCommSq f g)
    (hSU : IsTwoFibreProduct SU) {SR : TwoCommSq f f} (SBC : TwoCommSq SR.snd SU.fst)
    (hSBC : IsTwoFibreProduct SBC) :
    IsTwoFibreProduct (SU.pasteFst SBC) :=
  isTwoFibreProduct_pasteFst SU hSU SBC hSBC

/-- **The base change of the relation is the triple product.** With `R = 𝒰 ×_𝒳 𝒰` and
`R ×_{s, 𝒰} U'` as above, that apex is also `𝒰 ×_𝒳 U'`, a 2-fibre product of the cospan
`(f, pr_𝒰 ≫ f)`. -/
noncomputable def isTwoFibreProduct_relationBaseChangeTriple {SR : TwoCommSq f f}
    (hSR : IsTwoFibreProduct SR) {SU : TwoCommSq f g} {SBC : TwoCommSq SR.snd SU.fst}
    (hSBC : IsTwoFibreProduct SBC) :
    IsTwoFibreProduct (SR.paste SBC) :=
  isTwoFibreProduct_paste hSR hSBC

/-- **The base change of the relation is the self-intersection of the base-changed atlas.** Let
`U' = 𝒰 ×_𝒳 𝒳'`, `R = 𝒰 ×_𝒳 𝒰`, `R' = U' ×_{𝒳'} U'` and `R ×_{s, 𝒰} U' = R ×_𝒳 𝒳'`. Both are
2-fibre products of the cospan `(f, pr_𝒰 ≫ f)` naming the triple product `𝒰 ×_𝒳 𝒰 ×_𝒳 𝒳'`, so
they are isomorphic in the category of 2-commutative squares over it: the comparison is
compatible with the projections to `𝒰` and to `U'`. -/
theorem nonempty_iso_baseChangedSelfIntersection {SU : TwoCommSq f g}
    (hSU : IsTwoFibreProduct SU) {SRel : TwoCommSq SU.snd SU.snd}
    (hSRel : IsTwoFibreProduct SRel) {SR : TwoCommSq f f} (hSR : IsTwoFibreProduct SR)
    {SBC : TwoCommSq SR.snd SU.fst} (hSBC : IsTwoFibreProduct SBC) :
    Nonempty (SU.baseChangedSelfIntersection SRel ≅ SR.paste SBC) :=
  twoFibreProduct_uniqueUpToIso
    (isTwoFibreProduct_baseChangedSelfIntersection hSU hSRel)
    (isTwoFibreProduct_relationBaseChangeTriple hSR hSBC)

end CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids.RepresentablePresentation

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]
  {𝒳 𝒳' 𝒰 : CatFiberedInGroupoids.{v₁, v₁, u₁, max u₁ v₁} C} (f : 𝒰 ⟶ 𝒳) (g : 𝒳' ⟶ 𝒳)

/-- The canonical square presenting the base-changed atlas `U' = 𝒰 ×_𝒳 𝒳'`. -/
abbrev atlasBaseChangeSquare : Bicategory.TwoCommSq f g :=
  twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} f g

/-- The canonical square presenting the relation `R = 𝒰 ×_𝒳 𝒰` of the atlas `f`. -/
abbrev relationSquare : Bicategory.TwoCommSq f f :=
  twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} f f

/-- The canonical square presenting the self-intersection `R' = U' ×_{𝒳'} U'` of the
base-changed atlas. -/
abbrev baseChangedRelationSquare :
    Bicategory.TwoCommSq (atlasBaseChangeSquare f g).snd (atlasBaseChangeSquare f g).snd :=
  twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} _ _

/-- The canonical square presenting `R ×_{s, 𝒰} U'`, the base change of the relation along the
atlas of `𝒳'`. -/
abbrev relationBaseChangeSquare :
    Bicategory.TwoCommSq (relationSquare f).snd (atlasBaseChangeSquare f g).fst :=
  twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} _ _

/-- **Stacks 04Y6.** The canonical `R ×_{s, 𝒰} U'` is a base change of the relation `R` along
`g`: pasted onto the square of `U' = 𝒰 ×_𝒳 𝒳'`, it is a 2-fibre product of the cospan
`(s ≫ f, g)`. This is the `R' = R ×_𝒳 𝒳'` of the statement of the lemma. -/
@[stacks 04Y6 "R' = R ×_𝒳 𝒳' for the canonical squares; no hypothesis carried"]
noncomputable def isTwoFibreProduct_relationBaseChangeSquare :
    Bicategory.IsTwoFibreProduct
      ((atlasBaseChangeSquare f g).pasteFst (relationBaseChangeSquare f g)) :=
  Bicategory.isTwoFibreProduct_relationBaseChange _
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} f g) _
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} _ _)

/-- **Stacks 04Y6.** The displayed chain of the proof, for the canonical 2-fibre products:
`R ×_𝒳 𝒳' = 𝒰 ×_𝒳 𝒰 ×_𝒳 𝒳' = (𝒰 ×_𝒳 𝒳') ×_{𝒳'} (𝒰 ×_𝒳 𝒳')`. The base change of the relation
and the self-intersection of the base-changed atlas are isomorphic as 2-commutative squares over
the triple product, hence compatibly with the projections `pr_R` and `s'`. -/
@[stacks 04Y6 "R ×_𝒳 𝒳' = U' ×_{𝒳'} U' for the canonical squares; nothing carried"]
theorem nonempty_iso_baseChangedRelationSquare :
    Nonempty ((atlasBaseChangeSquare f g).baseChangedSelfIntersection
        (baseChangedRelationSquare f g) ≅
      (relationSquare f).paste (relationBaseChangeSquare f g)) :=
  Bicategory.nonempty_iso_baseChangedSelfIntersection
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} f g)
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} _ _)
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} f f)
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₁, u₁, max u₁ v₁} _ _)

end CategoryTheory.CatFiberedInGroupoids.RepresentablePresentation

end
