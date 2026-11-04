module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverAsPullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PrecomposeLegs

/-!
# The relative diagonal along a fully faithful 1-morphism

Let `j : 𝒳 ⟶ 𝒴` and `π : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in groupoids over the big
fppf site of a scheme `S`, and assume that the functor underlying `j` is fully faithful. Then the
2-commutative square

```text
  𝒳  --Δ_{j ≫ π}-->  𝒳 ×_𝒵 𝒳
  |                     |
 j|                     | j × j
  v                     v
  𝒴  ----Δ_π----->  𝒴 ×_𝒵 𝒴
```

is a 2-fibre product. This is the argument of Stacks 0CBB, which states it for a monomorphism of
algebraic stacks: `𝒳 = 𝒳 ×_𝒴 𝒳` because the relative diagonal of a fully faithful 1-morphism is
an equivalence (Stacks 04ZZ), and the square is then the 2-cartesian square of Stacks 04Z1
precomposed with that equivalence. Nothing in the argument uses that the three categories are
algebraic stacks, and the universes of the three total categories are those of
`AlgebraicGeometry.Stack.relativeDiagonal`, so that it applies to categories whose morphisms live
one universe above the schemes, such as the Picard stack and the stack of coherent sheaves.

Consequently the relative diagonal of `j ≫ π` is a base change of the relative diagonal of `π`,
so it inherits representability by algebraic spaces (Stacks 0302 for 2-fibre products,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) and every condition of
Properties of Stacks, Section 04XB (Stacks 045C,
`AlgebraicGeometry.Stack.relativeProperty_baseChange`); in particular quasi-compactness and
quasi-separatedness. This is the step of the proof of Stacks 0DMB which deduces the
quasi-separatedness of `Pic_{X/B} ⟶ B` from that of `Coh_{X/B} ⟶ B`, the first being an open
substack of the second (Stacks 0D03).

## Main definitions

* `AlgebraicGeometry.Stack.relativeDiagonalMapBase`: the comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` of
  Stacks 050H, at the universes of the relative diagonal.
* `AlgebraicGeometry.Stack.relativeDiagonalMapBoth`: the 1-morphism `j × j`.
* `AlgebraicGeometry.Stack.relativeDiagonalComparisonSquare`: the square of Stacks 04Z1.
* `AlgebraicGeometry.Stack.relativeDiagonalCompSquare`: the square displayed above.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_relativeDiagonalComparisonSquare`: Stacks 04Z1.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_relativeDiagonalCompSquare`: the square above is a
  2-fibre product when `j` is fully faithful.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_comp`,
  `AlgebraicGeometry.Stack.relativeProperty_relativeDiagonal_comp`,
  `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_comp` and
  `AlgebraicGeometry.Stack.isQuasiSeparated_relativeDiagonal_comp`: the transfer of
  representability and of the conditions of Section 04XB from `Δ_π` to `Δ_{j ≫ π}`.

## References

* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
-/

@[expose] public noncomputable section

open CategoryTheory Bicategory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS)}

/-- **The comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` of Stacks 050H** for `j : 𝒳 ⟶ 𝒴` and `π : 𝒴 ⟶ 𝒵`:
it is the identity on both factors and applies `π` to the comparison isomorphism. -/
def relativeDiagonalMapBase (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    twoFibreProduct B S hS 𝒴 𝒳 𝒳 j.hom j.hom ⟶
      twoFibreProduct B S hS 𝒵 𝒳 𝒳 (j ≫ π).hom (j ≫ π).hom :=
  InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.mapBaseOver 𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
        j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p π)
      w := rfl }

/-- **The 1-morphism `j × j : 𝒳 ×_𝒵 𝒳 ⟶ 𝒴 ×_𝒵 𝒴`**, which applies `j` to both factors; it is the
right-hand leg of the square of Stacks 04Z1. -/
def relativeDiagonalMapBoth (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    twoFibreProduct B S hS 𝒵 𝒳 𝒳 (j ≫ π).hom (j ≫ π).hom ⟶
      twoFibreProduct B S hS 𝒵 𝒴 𝒴 π.hom π.hom :=
  InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.mapBothOver 𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
        j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p j) (CatFiberedInGroupoids.homFunctor_comp_p j)
      w := rfl }

/-- The first projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳`. -/
def relativeDiagonalFst (j : 𝒳 ⟶ 𝒴) : twoFibreProduct B S hS 𝒴 𝒳 𝒳 j.hom j.hom ⟶ 𝒳 :=
  InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.fst _ _ _ _ _
      w := TwoFibreProductOver.fst_comp_eq }

/-- **The square of Stacks 04Z1** for `j`, `j` and `π`:

```text
                   Θ
  𝒳 ×_𝒴 𝒳  ------------>  𝒳 ×_𝒵 𝒳
    |                         |
    |                         | j × j
    v                         v
    𝒴  -------Δ_π------>  𝒴 ×_𝒵 𝒴
```

whose left leg is the first projection followed by `j`. The filler is
`CategoryTheory.TwoFibreProductOver.relativeDiagonalSquareIsoOver`. -/
def relativeDiagonalComparisonSquare (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    TwoCommSq (relativeDiagonalMapBoth B S hS j π) (relativeDiagonal B S hS 𝒴 𝒵 π) where
  pt := twoFibreProduct B S hS 𝒴 𝒳 𝒳 j.hom j.hom
  fst := relativeDiagonalMapBase B S hS j π
  snd := relativeDiagonalFst B S hS j ≫ j
  iso := InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.relativeDiagonalSquareIsoOver
      𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
      j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p π))
    (TwoFibreProductOver.isHomLift_relativeDiagonalSquareIsoOver
      𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
      j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p π)))

/-- The canonical pre-morphism from the square of Stacks 04Z1 to the canonical 2-fibre product
square of its cospan; its 1-morphism is the comparison functor of Stacks 04Z1. -/
def relativeDiagonalComparisonPreHom (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    TwoCommSq.PreHom (relativeDiagonalComparisonSquare B S hS j π)
      (CatFiberedInGroupoids.twoFibreProductSquare (relativeDiagonalMapBoth B S hS j π)
        (relativeDiagonal B S hS 𝒴 𝒵 π)) where
  hom := InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.toRelativeDiagonalPullbackOver
        𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
        j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p j)
        (CatFiberedInGroupoids.homFunctor_comp_p j)
        (CatFiberedInGroupoids.homFunctor_comp_p π)
      w := TwoFibreProductOver.toRelativeDiagonalPullbackOver_comp_structureFunctor
        𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
        j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p j)
        (CatFiberedInGroupoids.homFunctor_comp_p j)
        (CatFiberedInGroupoids.homFunctor_comp_p π) }
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (relativeDiagonalMapBoth B S hS j π).hom.toFunctor
      (relativeDiagonal B S hS 𝒴 𝒵 π).hom.toFunctor
      ((relativeDiagonalComparisonSquare B S hS j π).iso.hom.hom.toNatTrans.app x)

/-- **Stacks 04Z1.** The square `AlgebraicGeometry.Stack.relativeDiagonalComparisonSquare` is a
2-fibre product: the comparison functor into the canonical 2-fibre product of its cospan is an
equivalence (`CategoryTheory.TwoFibreProductOver.isEquivalence_toRelativeDiagonalPullbackOver`). -/
def isTwoFibreProduct_relativeDiagonalComparisonSquare (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    IsTwoFibreProduct (relativeDiagonalComparisonSquare B S hS j π) :=
  isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare
      (relativeDiagonalMapBoth B S hS j π) (relativeDiagonal B S hS 𝒴 𝒵 π))
    (relativeDiagonalComparisonPreHom B S hS j π)
    (TwoFibreProductOver.isEquivalence_toRelativeDiagonalPullbackOver
      𝒳.val.p 𝒳.val.p 𝒴.val.p 𝒵.val.p
      j.hom.toFunctor j.hom.toFunctor π.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p π))

/-- **The relative diagonal of a composite factors through the diagonal of the first factor**:
`Δ_{j ≫ π} = Δ_j ≫ Θ`, where `Θ` is `AlgebraicGeometry.Stack.relativeDiagonalMapBase`. -/
theorem relativeDiagonal_comp_eq (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π) =
      relativeDiagonal B S hS 𝒳 𝒴 j ≫ relativeDiagonalMapBase B S hS j π :=
  InducedBicategory.hom_ext <| BasedCategory.BasedFunctor.ext' <|
    TwoFibreProductOver.diagonal_comp_mapBaseOver
      𝒳.val.p 𝒴.val.p 𝒵.val.p
      j.hom.toFunctor π.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p j)
      (CatFiberedInGroupoids.homFunctor_comp_p π)
      (CatFiberedInGroupoids.homFunctor_comp_p (j ≫ π))

/-- **The square of Stacks 0CBB** for `j : 𝒳 ⟶ 𝒴` and `π : 𝒴 ⟶ 𝒵`:

```text
  𝒳  --Δ_{j ≫ π}-->  𝒳 ×_𝒵 𝒳
  |                     |
 j|                     | j × j
  v                     v
  𝒴  ----Δ_π----->  𝒴 ×_𝒵 𝒴
```

It is the square of Stacks 04Z1 precomposed with `Δ_j`, along the factorization
`AlgebraicGeometry.Stack.relativeDiagonal_comp_eq`. -/
def relativeDiagonalCompSquare (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    TwoCommSq (relativeDiagonalMapBoth B S hS j π) (relativeDiagonal B S hS 𝒴 𝒵 π) :=
  (relativeDiagonalComparisonSquare B S hS j π).precomposeLegs
    (relativeDiagonal B S hS 𝒳 𝒴 j) (relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π)) j
    (eqToIso (relativeDiagonal_comp_eq B S hS j π)) (Iso.refl _)

/-- The first leg of the square of Stacks 0CBB is the relative diagonal of the composite. -/
@[simp]
theorem relativeDiagonalCompSquare_fst (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵) :
    (relativeDiagonalCompSquare B S hS j π).fst = relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π) :=
  rfl

/-- **Stacks 0CBB, for a fully faithful 1-morphism of categories fibred in groupoids.** If the
functor underlying `j : 𝒳 ⟶ 𝒴` is full and faithful, the square
`AlgebraicGeometry.Stack.relativeDiagonalCompSquare` is a 2-fibre product: `Δ_j` is an equivalence
(Stacks 04ZZ, `CategoryTheory.TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal`),
and the square is the 2-fibre product of Stacks 04Z1 precomposed with it. -/
def isTwoFibreProduct_relativeDiagonalCompSquare (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵)
    (hj : (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful) :
    IsTwoFibreProduct (relativeDiagonalCompSquare B S hS j π) :=
  isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_relativeDiagonalComparisonSquare B S hS j π)
    (TwoCommSq.PreHom.ofPrecomposeLegs _ _ _ _ _ _)
    ((TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p j)).mp hj)

/-- **The relative diagonal of `j ≫ π` is representable by algebraic spaces when that of `π` is
and `j` is fully faithful**: by Stacks 0CBB it is a base change of `Δ_π`. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_comp (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵)
    (hj : (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonal B S hS 𝒴 𝒵 π).hom) :
    IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π)).hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒴 _ _
    (relativeDiagonal B S hS 𝒴 𝒵 π) (relativeDiagonalMapBoth B S hS j π)
    (relativeDiagonalCompSquare B S hS j π)
    (isTwoFibreProduct_relativeDiagonalCompSquare B S hS j π hj) hΔ

/-- **A condition of Properties of Stacks, Section 04XB on `Δ_π` is inherited by `Δ_{j ≫ π}`**
when `j` is fully faithful, for any property `P` of morphisms of algebraic spaces: by Stacks 0CBB
the relative diagonal of `j ≫ π` is a base change of that of `π`, and Stacks 045C applies
(`AlgebraicGeometry.Stack.relativeProperty_baseChange`). -/
theorem relativeProperty_relativeDiagonal_comp (P : MorphismProperty (AlgebraicSpaces B S hS))
    (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵)
    (hj : (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful)
    (hΔ : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS 𝒵 𝒴 𝒴 π.hom π.hom).val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS 𝒵 𝒴 𝒴 π.hom π.hom).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p
          (twoFibreProduct B S hS 𝒵 𝒴 𝒴 π.hom π.hom).val.p y
          (CatFiberedInGroupoids.homFunctor (relativeDiagonal B S hS 𝒴 𝒵 π)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS 𝒵 𝒳 𝒳 (j ≫ π).hom (j ≫ π).hom).val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS 𝒵 𝒳 𝒳 (j ≫ π).hom (j ≫ π).hom).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p
          (twoFibreProduct B S hS 𝒵 𝒳 𝒳 (j ≫ π).hom (j ≫ π).hom).val.p z
          (CatFiberedInGroupoids.homFunctor (relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π))))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  relativeProperty_baseChange.{u, v, w} B S hS P 𝒴 _ _
    (relativeDiagonal B S hS 𝒴 𝒵 π) (relativeDiagonalMapBoth B S hS j π)
    (relativeDiagonalCompSquare B S hS j π)
    (isTwoFibreProduct_relativeDiagonalCompSquare B S hS j π hj) hΔ

/-- **`Δ_{j ≫ π}` is quasi-compact when `Δ_π` is and `j` is fully faithful**, in the sense of
Properties of Stacks, Section 04XB. -/
theorem isQuasiCompact_relativeDiagonal_comp (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵)
    (hj : (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful)
    (hΔ : IsQuasiCompact B S hS (relativeDiagonal B S hS 𝒴 𝒵 π)) :
    IsQuasiCompact B S hS (relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π)) :=
  relativeProperty_relativeDiagonal_comp B S hS
    (fun _ _ g => Space.IsQuasiCompact B S hS g.hom) j π hj hΔ

/-- **`Δ_{j ≫ π}` is quasi-separated when `Δ_π` is and `j` is fully faithful**, in the sense of
Properties of Stacks, Section 04XB. -/
theorem isQuasiSeparated_relativeDiagonal_comp (j : 𝒳 ⟶ 𝒴) (π : 𝒴 ⟶ 𝒵)
    (hj : (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful)
    (hΔ : IsQuasiSeparated B S hS (relativeDiagonal B S hS 𝒴 𝒵 π)) :
    IsQuasiSeparated B S hS (relativeDiagonal B S hS 𝒳 𝒵 (j ≫ π)) :=
  relativeProperty_relativeDiagonal_comp B S hS
    (fun _ _ g => Space.IsQuasiSeparated B S hS g.hom) j π hj hΔ

end AlgebraicGeometry.Stack

end
