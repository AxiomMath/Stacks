module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The chart comparison behind the dimension formula of Stacks 0DS4

Let `f : 𝒯 ⟶ 𝒵` be a 1-morphism locally of finite type of locally Noetherian algebraic stacks
over `S`, let `a : 𝒱 ⟶ 𝒵` be a smooth 1-morphism locally of finite type, let `P` be a 2-fibre
product of the cospan `(a, f)` and let `s : 𝒲 ⟶ P.pt` be smooth and locally of finite type. The
resulting square

```text
         s ≫ P.fst
  𝒲 ----------------> 𝒱
  |                   |
  | s ≫ P.snd         | a
  v         f         v
  𝒯 ----------------> 𝒵
```

has smooth left-hand and right-hand legs. **The dimension formula at a point of `𝒲` descends to
`𝒯`**: if at `w ∈ |𝒲|` the dimension of `𝒲` splits as the dimension of `𝒱` at the image of `w`
plus the relative dimension of `s ≫ P.fst` at `w`, then the dimension of `𝒯` at the image `t` of
`w` splits as the dimension of `𝒵` at `f(t)` plus the relative dimension of `f` at `t`.

This is the step by which the proof of **Stacks 0DS4** passes from a dimension formula proved for
a morphism of schemes to the dimension of `𝒯` relative to its scheme theoretic image: the four
corners of the square are compared through a single chart of the 2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.eq_of_add_intCast_eq_add_intCast`: an equality of extended integers
  may be cancelled by a finite summand.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_add_relativeStackDimensionAt_of_chartComparison`:
  the descent of the dimension formula along the square above.

## Implementation notes

Every input is proved elsewhere; the proof is their composition, and no geometry is created here.

* **Stacks 0DRP**,
  `AlgebraicGeometry.Stack.dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth`,
  is applied three times: to `s`, to `P.snd` and to `a`. It is what makes the two smooth legs
  of the square into dimension formulas.
* **Stacks 0DRN**,
  `AlgebraicGeometry.Stack.relativeStackDimensionAt_fst_eq_relativeStackDimensionAt`, is applied
  twice, once to `P` and once to its swap
  (`CategoryTheory.Bicategory.TwoCommSq.swap`, whose 2-cartesianness is
  `CategoryTheory.Bicategory.isTwoFibreProduct_swap`): the relative dimension of `P.fst` at a
  point of `|P.pt|` is that of `f` below it, and the relative dimension of `P.snd` there is that
  of `a`. The swap is what makes the second instance available, the statement of Stacks 0DRN
  fixing the order of the cospan.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isSmooth` splits the relative
  dimension of each of the two composites `s ≫ P.fst` and `s ≫ P.snd` at `w` as the relative
  dimension of the second factor at `s(w)` plus that of `s` at `w`; only the first is needed,
  the second being absorbed by two applications of Stacks 0DRP instead.

Both of the two quantities that are cancelled — the relative dimension of `a` at the image of
`w` in `|𝒱|` and the relative dimension of `s` at `w` — are *integers*, by
`AlgebraicGeometry.Stack.exists_relativeStackDimensionAt_eq_intCast`, so the cancellation is
legitimate even though `EInt` is not a group. They are cancelled one at a time, which avoids
having to add the two integers inside `EInt`.

The 2-commutativity of the square is used once, to see that the image of `w` in `|𝒵|` is the
same computed along either leg; that is `AlgebraicGeometry.Stack.pointsMap_eq_of_basedNatTrans`
at the filler `P.iso` together with `AlgebraicGeometry.Stack.pointsMap_comp`.

The hypotheses on the two projections of `P` and on `P.pt` are *derived*: local finite type of
`P.fst` and of `P.snd` is **Stacks 06FU**, smoothness of `P.snd` is **Stacks 075W**, and local
Noetherianity of `P.pt` is **Stacks 06R6** along `P.snd`. Only the local finite type of
`s ≫ P.fst` is carried, because it appears in the statement as an argument of the relative
dimension of Stacks 0DRL.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- An equality of extended integers may be cancelled by a finite summand: if `A + c = B + c`
for an integer `c`, then `A = B`. This is the equality form of
`AlgebraicGeometry.Stack.le_of_add_intCast_le_add_intCast`. -/
theorem eq_of_add_intCast_eq_add_intCast {A B : EInt} {c : ℤ}
    (h : A + ((c : ℤ) : EInt) = B + ((c : ℤ) : EInt)) : A = B :=
  le_antisymm (le_of_add_intCast_le_add_intCast h.le)
    (le_of_add_intCast_le_add_intCast h.ge)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart comparison of Stacks 0DS4.** Let `f : 𝒯 ⟶ 𝒵` be locally of finite type, let
`a : 𝒱 ⟶ 𝒵` be smooth and locally of finite type, let `P` be a 2-fibre product of the cospan
`(a, f)` and let `s : 𝒲 ⟶ P.pt` be smooth and locally of finite type, all of locally Noetherian
algebraic stacks over `S`. If at `w ∈ |𝒲|` the dimension of `𝒲` is the dimension of `𝒱` at the
image `v` of `w` plus the relative dimension of `s ≫ P.fst` at `w`, then the dimension of `𝒯` at
the image `t` of `w` is the dimension of `𝒵` at `f(t)` plus the relative dimension of `f` at `t`.

The two smooth legs `s` and `P.snd` of the square turn the left-hand side into
`dim_t(𝒯) + dim_v(𝒱_{f(t)}) + dim_w(𝒲_{s(w)})` by Stacks 0DRP and Stacks 0DRN, while the
hypothesis turns it into `dim_{f(t)}(𝒵) + dim_v(𝒱_{f(t)}) + dim_t(𝒯_{f(t)}) + dim_w(𝒲_{s(w)})`;
the two relative dimensions of the smooth 1-morphisms `a` and `s` are integers, so they cancel. -/
theorem dimensionAtPoint_eq_add_relativeStackDimensionAt_of_chartComparison
    {𝒯 𝒵 𝒱 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒵) (a : 𝒱 ⟶ 𝒵)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS 𝒱)
    (h𝒲 : IsLocallyNoetherianStack.{u, w} B S hS 𝒲)
    (P : Bicategory.TwoCommSq a f) (hP : Bicategory.IsTwoFibreProduct P)
    (s : 𝒲 ⟶ P.pt)
    (hs : AlgebraicStacks.IsLocallyOfFiniteType B S hS s)
    (hssm : AlgebraicStacks.IsSmooth B S hS s)
    (hsfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS (s ≫ P.fst))
    (w : points B S hS 𝒲.val.val 𝒲.val.property)
    (hchart : dimensionAtPoint B S hS 𝒲 h𝒲 w =
      dimensionAtPoint B S hS 𝒱 h𝒱
          (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒱.val.property P.fst.hom.hom
            (pointsMap B S hS 𝒲.val.val 𝒲.val.property P.pt.val.property s.hom.hom w)) +
        relativeStackDimensionAt.{u, w} B S hS (s ≫ P.fst) hsfst h𝒲 h𝒱 w) :
    dimensionAtPoint B S hS 𝒯 h𝒯
        (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom
          (pointsMap B S hS 𝒲.val.val 𝒲.val.property P.pt.val.property s.hom.hom w)) =
      dimensionAtPoint B S hS 𝒵 h𝒵
          (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒵.val.property f.hom.hom
            (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom
              (pointsMap B S hS 𝒲.val.val 𝒲.val.property P.pt.val.property s.hom.hom w))) +
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒵
          (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom
            (pointsMap B S hS 𝒲.val.val 𝒲.val.property P.pt.val.property s.hom.hom w)) := by
  classical
  -- the swapped square, which is what makes Stacks 0DRN available at the second projection
  have hPsw := Bicategory.isTwoFibreProduct_swap hP
  have hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.fst :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a P hP hf
  have hsnd : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS a f P.swap hPsw ha
  have hsndsm : AlgebraicStacks.IsSmooth B S hS P.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS a f P.swap hPsw hasm
  have h𝒫 : IsLocallyNoetherianStack.{u, w} B S hS P.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS P.snd hsnd h𝒯
  set p := pointsMap B S hS 𝒲.val.val 𝒲.val.property P.pt.val.property s.hom.hom w with hp
  set v := pointsMap B S hS P.pt.val.val P.pt.val.property 𝒱.val.property P.fst.hom.hom p with hv
  set t := pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom p with ht
  -- Stacks 0DRP at the three smooth 1-morphisms `s`, `P.snd` and `a`
  have e1 := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} B S hS s hssm hs
    h𝒲 h𝒫 w
  have e2 := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} B S hS P.snd
    hsndsm hsnd h𝒫 h𝒯 p
  have e5 := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} B S hS a hasm ha
    h𝒱 h𝒵 v
  -- Stacks 0DRN at the two projections
  have e3 : relativeStackDimensionAt.{u, w} B S hS P.snd hsnd h𝒫 h𝒯 p =
      relativeStackDimensionAt.{u, w} B S hS a ha h𝒱 h𝒵 v :=
    relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS f a P.swap hPsw ha
      hsnd h𝒫 h𝒱 h𝒯 h𝒵 p
  have e4 : relativeStackDimensionAt.{u, w} B S hS P.fst hfst h𝒫 h𝒱 p =
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒵 t :=
    relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS a f P hP hf hfst h𝒫
      h𝒯 h𝒱 h𝒵 p
  -- additivity along `s ≫ P.fst`
  have e6 := relativeStackDimensionAt_comp_of_isSmooth.{u, w} B S hS s P.fst hssm hs hfst hsfst
    h𝒲 h𝒫 h𝒱 w
  -- the square commutes on points
  have e7 : pointsMap B S hS 𝒱.val.val 𝒱.val.property 𝒵.val.property a.hom.hom v =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒵.val.property f.hom.hom t :=
    (pointsMap_comp B S hS P.pt.val.val P.pt.val.property 𝒱.val.property 𝒵.val.property
        P.fst.hom.hom a.hom.hom p).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS P.pt.val.val P.pt.val.property
          𝒵.val.property P.iso.hom.hom.hom) p).trans
        (pointsMap_comp B S hS P.pt.val.val P.pt.val.property 𝒯.val.property 𝒵.val.property
          P.snd.hom.hom f.hom.hom p).symm)
  -- both cancelled summands are integers
  obtain ⟨c₁, hc₁⟩ := exists_relativeStackDimensionAt_eq_intCast.{u, w} B S hS a ha h𝒱 h𝒵 v
  obtain ⟨c₂, hc₂⟩ := exists_relativeStackDimensionAt_eq_intCast.{u, w} B S hS s hs h𝒲 h𝒫 w
  refine eq_of_add_intCast_eq_add_intCast (c := c₁)
    (eq_of_add_intCast_eq_add_intCast (c := c₂) ?_)
  calc dimensionAtPoint B S hS 𝒯 h𝒯 t + ((c₁ : ℤ) : EInt) + ((c₂ : ℤ) : EInt)
      = dimensionAtPoint B S hS 𝒲 h𝒲 w := by
        rw [e1, e2, e3, hc₁, hc₂]
    _ = dimensionAtPoint B S hS 𝒵 h𝒵
            (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒵.val.property f.hom.hom t) +
          relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒵 t +
          ((c₁ : ℤ) : EInt) + ((c₂ : ℤ) : EInt) := by
        rw [hchart, e5, e6, e4, e7, hc₁, hc₂]
        abel

end AlgebraicGeometry.Stack

end
