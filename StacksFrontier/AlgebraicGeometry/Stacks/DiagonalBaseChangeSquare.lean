module

public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange

/-!
# The diagonal of a base change is a base change of the diagonal, over the site (Stacks 04YR)

Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S`, write
`𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'` for the 2-fibre product of Stacks 04T2, and let `r : 𝒰 ⟶ 𝒳` and
`f' : 𝒰 ⟶ 𝒴'` be its two projections, so that `f'` is the base change of `f` by `g`. This file
exhibits the 2-commutative square

```text
            Δ_{f'}
    𝒰  ------------->  𝒰 ×_{𝒴'} 𝒰
    |                       |
  r |                       | r × r
    v                       v
    𝒳  --Δ_f-------->  𝒳 ×_𝒴 𝒳
```

in the 2-category of categories fibred in groupoids over the big fppf site of `S`, and proves
that it is a 2-fibre product in the sense of `CategoryTheory.Bicategory.IsTwoFibreProduct`
(Stacks 003O, 003Q). This is Stacks 04YR read over the site; for categories over an arbitrary
base it is `CategoryTheory.TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison`. In
the square the relative diagonal of the base change is a base change of the relative diagonal of
`f`, which is the step of Stacks 050F.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.diagonalBaseChangeFiller`: the 2-cell of the square, over
  an arbitrary base.
* `AlgebraicGeometry.Stack.diagonalMapDiag`: the right-hand leg `r × r`.
* `AlgebraicGeometry.Stack.diagonalBaseChangeSquare`: the square.
* `AlgebraicGeometry.Stack.diagonalBaseChangePreHom`: the comparison into the canonical 2-fibre
  product of the cospan.

## Main results

* `CategoryTheory.TwoFibreProductOver.isHomLift_diagonalBaseChangeFiller`: every component of
  the 2-cell is vertical.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare`: Stacks 04YR over the big
  fppf site, the square is 2-cartesian.

## Implementation notes

No declaration here carries a `@[stacks]` attribute. Stacks 04YR is a lemma of the Categories
chapter, about the (2,1)-category of categories, and its tag is on the absolute form
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_baseChangeDiagonalComparison`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒱 : Type u₃} [Category.{v₃} 𝒱] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒱 : 𝒱 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {h : 𝒳 ⥤ 𝒴} {s : 𝒱 ⥤ 𝒴}
variable (hh : h ⋙ p𝒴 = p𝒳) (hs : s ⋙ p𝒴 = p𝒱)

/-- The 2-cell `Δ_{𝒰/𝒱} ⋙ (r × r) ≅ r ⋙ Δ_{𝒳/𝒴}` filling the base-change square for the
diagonal over `𝒞`, whose component at `u` is `CategoryTheory.TwoFibreProductOver.comparisonIso`. -/
noncomputable def diagonalBaseChangeFiller :
    (diagonal (snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒱) (p𝒮 := p𝒴) (F := h) (G := s)) ⋙
        mapDiag hs) ≅ (fst p𝒳 p𝒱 p𝒴 h s ⋙ diagonal hh) :=
  NatIso.ofComponents (comparisonIso hh hs) (by
    intro u u' k
    apply Hom.ext' <;> (change k.a ≫ 𝟙 _ = 𝟙 _ ≫ k.a; simp))

/-- Every component of `CategoryTheory.TwoFibreProductOver.diagonalBaseChangeFiller` lies over
an identity of `𝒞`. -/
theorem isHomLift_diagonalBaseChangeFiller (u : TwoFibreProductOver p𝒳 p𝒱 p𝒴 h s) :
    (structureFunctor p𝒳 p𝒳 p𝒴 h h).IsHomLift
      (𝟙 ((structureFunctor p𝒳 p𝒱 p𝒴 h s).obj u))
      ((diagonalBaseChangeFiller hh hs).hom.app u) :=
  structureFunctor_isHomLift (comparisonIso hh hs u).hom (𝟙 u.base) (by
    rw [comparisonIso_hom_a]
    exact IsHomLift.id u.hx)

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- The right-hand leg `r × r : 𝒰 ×_{𝒴'} 𝒰 ⟶ 𝒳 ×_𝒴 𝒳` of the base-change square for the
diagonal, where `𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'` and `r : 𝒰 ⟶ 𝒳` is its first projection: it applies `r`
to both factors, with the comparison isomorphism `h u₁ ≅ s u₁' ≅ s u₂' ≅ h u₂` assembled from the
two structural isomorphisms and the image of the given one. -/
noncomputable def diagonalMapDiag (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    twoFibreProduct B S hS 𝒴'.val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom ⟶
      twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.mapDiag
        (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
        (h := f.hom.hom.toFunctor) (s := g.hom.hom.toFunctor)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      w := by rfl }

/-- The base-change square for the diagonal, over the big fppf site. With
`𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'`, `r : 𝒰 ⟶ 𝒳` its first projection and `f' : 𝒰 ⟶ 𝒴'` its second, the base
change of `f` by `g`, this is the 2-commutative square whose apex is `𝒰`, whose first leg is the
relative diagonal `Δ_{f'}`, whose second leg is `r`, and whose cospan is `(r × r, Δ_f)`. -/
noncomputable def diagonalBaseChangeSquare (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.TwoCommSq (diagonalMapDiag B S hS f g)
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) where
  pt := (twoFibreProductAlgebraicStack B S hS f g).val
  fst := relativeDiagonal.{u, u, u + 1} B S hS
    (twoFibreProductAlgebraicStack B S hS f g).val 𝒴'.val
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom
  snd := (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom
  iso := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.diagonalBaseChangeFiller
      (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom))
    (TwoFibreProductOver.isHomLift_diagonalBaseChangeFiller
      (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)))

/-- The canonical pre-morphism of 2-commutative squares from
`AlgebraicGeometry.Stack.diagonalBaseChangeSquare` to the canonical 2-fibre product square of its
cospan. Its 1-morphism is the comparison functor of Stacks 04YR over the big fppf site, and both
of its comparison 2-cells are identities. -/
noncomputable def diagonalBaseChangePreHom (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.TwoCommSq.PreHom (diagonalBaseChangeSquare B S hS f g)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (diagonalMapDiag B S hS f g)
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) where
  hom := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.diagonalBaseChangeComparison
        (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      w := TwoFibreProductOver.diagonalBaseChangeComparison_comp_structureFunctor
        (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom) }
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    change (diagonalBaseChangeSquare B S hS f g).iso.hom.hom.toNatTrans.app x ≫
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val
          f.hom).hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ =
      (diagonalMapDiag B S hS f g).hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (diagonalBaseChangeSquare B S hS f g).iso.hom.hom.toNatTrans.app x
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (diagonalMapDiag B S hS f g).hom.toFunctor
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom).hom.toFunctor
      ((diagonalBaseChangeSquare B S hS f g).iso.hom.hom.toNatTrans.app x)

/-- Stacks 04YR over the big fppf site: the base-change square for the diagonal is
2-cartesian. -/
noncomputable def isTwoFibreProduct_diagonalBaseChangeSquare (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.IsTwoFibreProduct (diagonalBaseChangeSquare B S hS f g) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (diagonalMapDiag B S hS f g)
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (diagonalBaseChangePreHom B S hS f g)
    (TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison
      (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom))

end AlgebraicGeometry.Stack

end
