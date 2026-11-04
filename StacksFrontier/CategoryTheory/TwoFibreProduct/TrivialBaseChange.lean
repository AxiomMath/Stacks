module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Base change along an identity changes nothing (Stacks 003Q)

Fix a 1-morphism `f : x ⟶ z` in a bicategory. Among the 2-commutative squares of **Stacks 003O**
over the cospan `(f, 𝟙 z)` there is an evident one, `trivialBaseChangeSquare f`, whose apex is
`x` itself and whose legs are `𝟙 x` and `f`:

```text
          𝟙 x
    x ----------> x
    |             |
  f |             | f
    v     𝟙 z     v
    z ----------> z
```

This square is a 2-fibre product: *the base change of `f` along the identity of its target is
`f` itself*.

## Main definitions

* `CategoryTheory.Bicategory.trivialBaseChangeSquare`: the square above.
* `CategoryTheory.Bicategory.preHomToTrivialBaseChangeSquare`: the pre-morphism into it from an
  arbitrary 2-commutative square over the same cospan.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_trivialBaseChangeSquare`: the square is a 2-fibre
  product.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- **The square exhibiting `f` as its own base change along the identity of its target.** Its
apex is the source of `f`, its first leg is the identity and its second leg is `f`; the filler is
the pair of unitors. -/
def trivialBaseChangeSquare {x z : B} (f : x ⟶ z) : TwoCommSq f (𝟙 z) where
  pt := x
  fst := 𝟙 x
  snd := f
  iso := λ_ f ≪≫ (ρ_ f).symm

/-- **Every 2-commutative square over the cospan `(f, 𝟙 z)` maps to
`CategoryTheory.Bicategory.trivialBaseChangeSquare`**, on its own first leg. The comparison with
the identity leg is a unitor; the comparison with `f` is a unitor followed by the inverse of the
filler of the square. -/
def preHomToTrivialBaseChangeSquare {x z : B} (f : x ⟶ z) (Q : TwoCommSq f (𝟙 z)) :
    TwoCommSq.PreHom Q (trivialBaseChangeSquare f) where
  hom := Q.fst
  isoFst := (ρ_ Q.fst).symm
  isoSnd := (ρ_ Q.snd).symm ≪≫ Q.iso.symm
  compat := by simp [trivialBaseChangeSquare]

/-- **The base change of a 1-morphism along the identity of its target is the 1-morphism itself**
(**Stacks 003Q**): `CategoryTheory.Bicategory.trivialBaseChangeSquare` is a 2-fibre product of
the cospan `(f, 𝟙 z)`, as soon as that cospan has some 2-fibre product `Q`. -/
noncomputable def isTwoFibreProduct_trivialBaseChangeSquare {x z : B} (f : x ⟶ z)
    {Q : TwoCommSq f (𝟙 z)} (hQ : IsTwoFibreProduct Q) :
    IsTwoFibreProduct (trivialBaseChangeSquare f) :=
  isTwoFibreProduct_of_section hQ (preHomToTrivialBaseChangeSquare f Q)
    (_root_.Quotient.out (hQ.from (trivialBaseChangeSquare f))).hom
    (_root_.Quotient.out (hQ.from (trivialBaseChangeSquare f))).isoFst.symm

end CategoryTheory.Bicategory

end
