module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory

/-!
# From a 2-fibre product of categories fibred in groupoids to one of stacks in groupoids

The 2-category of stacks in groupoids over a site `(𝒞, J)` (`CategoryTheory.StackInGroupoids`,
Stacks 02ZK) and the 2-category of categories fibred in groupoids over `𝒞`
(`CategoryTheory.CatFiberedInGroupoids`, Stacks 02XS) are both full sub-2-categories of the
2-category of categories over `𝒞` (Stacks 003Y): each is a
`CategoryTheory.Bicategory.InducedBicategory` of `CategoryTheory.BasedCategory`, with all of its
1-morphisms and 2-morphisms between the images. A stack in groupoids is in particular fibred in
groupoids, so the first is a full sub-2-category of the second as well.

A 2-commutative square of stacks in groupoids whose reading as a square of categories fibred in
groupoids is a 2-fibre product (Stacks 003Q, or its 1-truncated form) is a 2-fibre product of
stacks in groupoids.

## Main definitions

* `CategoryTheory.StackInGroupoids.toFibred`, `CategoryTheory.StackInGroupoids.toFibredHom` and
  `CategoryTheory.StackInGroupoids.toFibredSquare`: a stack in groupoids, a 1-morphism of them
  and a 2-commutative square of them, read as a category fibred in groupoids, a 1-morphism of
  them and a 2-commutative square of them.

## Main results

* `CategoryTheory.StackInGroupoids.underlying_toFibredSquare`: the square of categories over `𝒞`
  underlying a 2-commutative square of stacks in groupoids and the one underlying its reading as
  a square of categories fibred in groupoids are equal.
* `CategoryTheory.StackInGroupoids.isTwoFibreProduct_of_toFibred`: a 2-commutative square of
  stacks in groupoids whose reading as a square of categories fibred in groupoids is a 2-fibre
  product is a 2-fibre product of stacks in groupoids, for the 1-truncated notion
  `CategoryTheory.Bicategory.IsTwoFibreProduct`.
* `CategoryTheory.StackInGroupoids.isFinalTwoCommSq_of_toFibred`: the same for 2-fibre products in
  the sense of Stacks 003Q (`CategoryTheory.Bicategory.IsFinalTwoCommSq`).

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Y](https://stacks.math.columbia.edu/tag/003Y)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 02ZK](https://stacks.math.columbia.edu/tag/02ZK)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.StackInGroupoids

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {J : GrothendieckTopology 𝒞}

attribute [local implicit_reducible] StackInGroupoids.bicategory
  Bicategory.InducedBicategory Bicategory.InducedBicategory.bicategory
  Bicategory.InducedBicategory.isoMk Bicategory.InducedBicategory.isoHom
  Bicategory.TwoCommSq.underlying

/-- A stack in groupoids over `(𝒞, J)` (Stacks 02ZK), read as a category fibred in groupoids over
`𝒞` (Stacks 02XS): the same category over `𝒞`, carrying the fibred-in-groupoids half of its
being a stack in groupoids. -/
abbrev toFibred (𝒳 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J) :
    CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.mk 𝒳.toBasedCategory 𝒳.isStackInGroupoids.isFiberedInGroupoids

/-- A 1-morphism of stacks in groupoids, read as a 1-morphism of categories fibred in groupoids:
the same functor over `𝒞`. -/
abbrev toFibredHom {𝒳 𝒴 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J} (f : 𝒳 ⟶ 𝒴) :
    toFibred 𝒳 ⟶ toFibred 𝒴 :=
  Bicategory.InducedBicategory.mkHom f.hom

variable {X Y Z : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A 2-commutative square of stacks in groupoids (Stacks 003O), read as a 2-commutative square
of categories fibred in groupoids over the cospan read the same way, with the same apex, legs and
filler. -/
def toFibredSquare (P : Bicategory.TwoCommSq f g) :
    Bicategory.TwoCommSq (toFibredHom f) (toFibredHom g) where
  pt := toFibred P.pt
  fst := toFibredHom P.fst
  snd := toFibredHom P.snd
  iso := Bicategory.InducedBicategory.isoMk
    (Bicategory.InducedBicategory.isoHom (f := P.fst ≫ f) (g := P.snd ≫ g) P.iso)

/-- A 2-commutative square of stacks in groupoids and its reading as a square of categories
fibred in groupoids have the same underlying square of categories over `𝒞`. -/
theorem underlying_toFibredSquare (P : Bicategory.TwoCommSq f g) :
    (toFibredSquare P).underlying = P.underlying := rfl

/-- A 2-commutative square of stacks in groupoids whose reading as a square of categories fibred
in groupoids is a 1-truncated 2-fibre product (terminal in the quotient category of 2-commutative
squares, `CategoryTheory.Bicategory.IsTwoFibreProduct`) is one of stacks in groupoids. The
version for 2-fibre products in the sense of Stacks 003Q is
`CategoryTheory.StackInGroupoids.isFinalTwoCommSq_of_toFibred`. -/
noncomputable def isTwoFibreProduct_of_toFibred {P : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct (toFibredSquare P)) :
    Bicategory.IsTwoFibreProduct P := by
  refine IsTerminal.ofUniqueHom
    (fun T => Bicategory.TwoCommSq.homOfUnderlying (T := T) (S := P)
      (Bicategory.TwoCommSq.homUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
        (hP.from (toFibredSquare T)))) (fun T m => ?_)
  have hround : Bicategory.TwoCommSq.homUnderlying (T := toFibredSquare T)
      (S := toFibredSquare P)
      (Bicategory.TwoCommSq.homOfUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
        (Bicategory.TwoCommSq.homUnderlying (T := T) (S := P) m))
      = Bicategory.TwoCommSq.homUnderlying (T := T) (S := P) m :=
    Bicategory.TwoCommSq.homUnderlying_homOfUnderlying _
  have h := congrArg
    (Bicategory.TwoCommSq.homUnderlying (T := toFibredSquare T) (S := toFibredSquare P))
    (hP.hom_ext
      (Bicategory.TwoCommSq.homOfUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
        (Bicategory.TwoCommSq.homUnderlying (T := T) (S := P) m))
      (hP.from (toFibredSquare T)))
  rw [← Bicategory.TwoCommSq.homOfUnderlying_homUnderlying m]
  exact congrArg (Bicategory.TwoCommSq.homOfUnderlying (T := T) (S := P)) (hround.symm.trans h)

/-- A 2-commutative square of stacks in groupoids whose reading as a square of categories fibred
in groupoids is a 2-fibre product in the sense of Stacks 003Q (a final object of the 2-category of
2-commutative diagrams) is a 2-fibre product of stacks in groupoids in the same sense. Both
2-categories are full on 1-morphisms and 2-morphisms over the 2-category of categories over `𝒞`,
so the 1-morphisms and the 2-morphisms of Stacks 003O into `P` are those into its reading. -/
noncomputable def isFinalTwoCommSq_of_toFibred {P : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsFinalTwoCommSq (toFibredSquare P)) : Bicategory.IsFinalTwoCommSq P where
  preHom T := Bicategory.TwoCommSq.PreHom.ofUnderlying (T := T) (S := P)
    (hP.preHom (toFibredSquare T)).underlying
  uniqueHom₂ {T} a b :=
    letI := hP.uniqueHom₂
      (Bicategory.TwoCommSq.PreHom.ofUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
        a.underlying)
      (Bicategory.TwoCommSq.PreHom.ofUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
        b.underlying)
    ((Bicategory.TwoCommSq.PreHom.hom₂UnderlyingEquiv a b).trans
      (Bicategory.TwoCommSq.PreHom.hom₂UnderlyingEquiv
        (Bicategory.TwoCommSq.PreHom.ofUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
          a.underlying)
        (Bicategory.TwoCommSq.PreHom.ofUnderlying (T := toFibredSquare T) (S := toFibredSquare P)
          b.underlying)).symm).unique

end CategoryTheory.StackInGroupoids

end
