module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverAsPullback
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The comparison of two fibre products of algebraic stacks

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over `S`, and
consider the induced 1-morphism

    i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴.

The square

```text
                   i
  𝒳 ×_𝒵 𝒴  ------------>  𝒳 ×_𝒯 𝒴
    |                         |
    |                         |
    v                         v
    𝒵  --Δ_{𝒵/𝒯}-->       𝒵 ×_𝒯 𝒵
```

is 2-cartesian, so `i` is a base change of the relative diagonal `Δ_{𝒵/𝒯}`. Hence `i` is
representable by algebraic spaces, and it is unramified when `h` is Deligne–Mumford. The
relative diagonal of a composite `f ≫ g` factors as `Δ_{𝒳/𝒵} = Δ_{𝒳/𝒴} ≫ i`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`: the relative diagonal, as a
  1-morphism in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.comparison`: the 1-morphism `i`.
* `AlgebraicGeometry.Stack.comparisonCospanRight`: the right-hand leg `𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`.
* `AlgebraicGeometry.Stack.comparisonSquare`: the square above.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_comparisonSquare`: the square is 2-cartesian.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comparison`: `i` is representable by
  algebraic spaces.
* `AlgebraicGeometry.Stack.isUnramified_comparison`: `i` is unramified when `h` is
  Deligne–Mumford.
* `AlgebraicGeometry.Stack.relativeDiagonal_comp`: the factorization of the diagonal of a
  composite.

## Implementation notes

`AlgebraicGeometry.Stack.relativeDiagonal` is a 1-morphism in the 2-category of categories fibred
in groupoids; `AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks` is the same 1-morphism in
the 2-category of algebraic stacks. The two agree on underlying 1-morphisms by definition.

## References

* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism `f` of algebraic stacks,
as a 1-morphism in the 2-category of algebraic stacks, whose target is the algebraic stack
`AlgebraicGeometry.Stack.twoFibreProductAlgebraicStack`. Its underlying 1-morphism of categories
fibred in groupoids is `AlgebraicGeometry.Stack.relativeDiagonal`. -/
noncomputable def relativeDiagonalAlgebraicStacks
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    𝒳 ⟶ twoFibreProductAlgebraicStack B S hS f f :=
  Bicategory.InducedBicategory.mkHom (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

variable {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- The comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`. It is the identity on both factors and
applies `h` to the comparison isomorphism, i.e. `CategoryTheory.TwoFibreProductOver.mapBaseOver`
in the 2-category of algebraic stacks. -/
noncomputable def comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    twoFibreProductAlgebraicStack B S hS f g ⟶
      twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      ({ toFunctor := TwoFibreProductOver.mapBaseOver
          𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
          f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
          (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
         w := by rfl } :
        (twoFibreProductAlgebraicStack B S hS f g).val.val ⥤ᵇ
          (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val.val))

/-- The 1-morphism `𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵` of algebraic stacks applying `f` to the first factor and
`g` to the second. -/
noncomputable def comparisonCospanRight (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h) ⟶
      twoFibreProductAlgebraicStack B S hS h h :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      ({ toFunctor := TwoFibreProductOver.mapBothOver
          𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
          f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
         w := by rfl } :
        (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val.val ⥤ᵇ
        (twoFibreProductAlgebraicStack B S hS h h).val.val))

/-- The 2-commutative square

```text
                   i
  𝒳 ×_𝒵 𝒴  ------------>  𝒳 ×_𝒯 𝒴
    |                         |
    |                         |
    v                         v
    𝒵  --Δ_{𝒵/𝒯}-->       𝒵 ×_𝒯 𝒵
```

whose apex is `𝒳 ×_𝒵 𝒴`, whose first leg is the comparison `i` and whose second leg is the first
projection followed by `f`. The filler is
`CategoryTheory.TwoFibreProductOver.relativeDiagonalSquareIsoOver`. -/
noncomputable def comparisonSquare (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.TwoCommSq (comparisonCospanRight B S hS f g h).hom
      (relativeDiagonalAlgebraicStacks B S hS h).hom where
  pt := (twoFibreProductAlgebraicStack B S hS f g).val
  fst := (comparison B S hS f g h).hom
  snd := ((twoFibreProductSquareAlgebraicStacks B S hS f g).fst ≫ f).hom
  iso := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.relativeDiagonalSquareIsoOver
      𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
      f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p h.hom))
    (TwoFibreProductOver.isHomLift_relativeDiagonalSquareIsoOver
      𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
      f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p h.hom)))

/-- The canonical pre-morphism of 2-commutative squares from
`AlgebraicGeometry.Stack.comparisonSquare` to the canonical 2-fibre product square of its cospan.
Its 1-morphism is `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver`, and both
of its comparison 2-cells are identities. -/
noncomputable def comparisonPreHom (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.TwoCommSq.PreHom (comparisonSquare B S hS f g h)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (comparisonCospanRight B S hS f g h).hom
        (relativeDiagonalAlgebraicStacks B S hS h).hom) where
  hom := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.toRelativeDiagonalPullbackOver
        𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
        f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
      w := TwoFibreProductOver.toRelativeDiagonalPullbackOver_comp_structureFunctor
        𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
        f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p h.hom) }
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    change (comparisonSquare B S hS f g h).iso.hom.hom.toNatTrans.app x ≫
        (relativeDiagonalAlgebraicStacks B S hS h).hom.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ =
      (comparisonCospanRight B S hS f g h).hom.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (comparisonSquare B S hS f g h).iso.hom.hom.toNatTrans.app x
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (comparisonCospanRight B S hS f g h).hom.hom.toFunctor
      (relativeDiagonalAlgebraicStacks B S hS h).hom.hom.toFunctor
      ((comparisonSquare B S hS f g h).iso.hom.hom.toNatTrans.app x)

/-- The square `AlgebraicGeometry.Stack.comparisonSquare` is a 2-fibre product. -/
noncomputable def isTwoFibreProduct_comparisonSquare
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.IsTwoFibreProduct (comparisonSquare B S hS f g h) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (comparisonCospanRight B S hS f g h).hom
      (relativeDiagonalAlgebraicStacks B S hS h).hom)
    (comparisonPreHom B S hS f g h)
    (TwoFibreProductOver.isEquivalence_toRelativeDiagonalPullbackOver
      𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
      f.hom.hom.toFunctor g.hom.hom.toFunctor h.hom.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p h.hom))

/-- The comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is representable by algebraic spaces. -/
@[stacks 050H "part (1): representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_comparison
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    IsRepresentableByAlgebraicSpaces B S hS (comparison B S hS f g h).hom.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
    𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
    (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonalAlgebraicStacks B S hS h).hom
    (comparisonCospanRight B S hS f g h).hom
    (comparisonSquare B S hS f g h) (isTwoFibreProduct_comparisonSquare B S hS f g h)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS h)

/-- If `h : 𝒵 ⟶ 𝒯` is Deligne–Mumford then the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is unramified, in the sense of `HasRelativeProperty`. The statement
supplies, as local instances, the stability of unramifiedness of morphisms of algebraic spaces
under base change and its locality on the target for the fppf precoverage. -/
@[stacks 050H "dm_unramified"]
theorem isUnramified_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : IsDM B S hS h) :
    letI : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom) :=
      Space.isUnramified_isStableUnderBaseChange B S hS
    letI : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    HasRelativeProperty B S hS
      (fun _ _ k => Space.IsUnramified B S hS k.hom)
      (comparison B S hS f g h).hom
      (isRepresentableByAlgebraicSpaces_comparison B S hS f g h) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _⦄ k => Space.IsUnramified B S hS k.hom
  let _ : P.IsStableUnderBaseChange := Space.isUnramified_isStableUnderBaseChange B S hS
  let _ : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  obtain ⟨hΔrep, hΔP⟩ := hh
  exact hasRelativeProperty_baseChange.{u, u, u + 1} B S hS P
    𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
    (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonalAlgebraicStacks B S hS h).hom
    (comparisonCospanRight B S hS f g h).hom
    (comparisonSquare B S hS f g h) (isTwoFibreProduct_comparisonSquare B S hS f g h)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS h) hΔP

/-- For 1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks over `S`, the relative
diagonal of the composite factors as

    Δ_{𝒳/𝒵} = Δ_{𝒳/𝒴} ≫ i,

where `i = AlgebraicGeometry.Stack.comparison` is the comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`. -/
theorem relativeDiagonal_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    relativeDiagonalAlgebraicStacks B S hS (f ≫ g) =
      relativeDiagonalAlgebraicStacks B S hS f ≫ comparison B S hS f f g := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  exact BasedCategory.BasedFunctor.ext' (TwoFibreProductOver.diagonal_comp_mapBaseOver
    𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
    f.hom.hom.toFunctor g.hom.hom.toFunctor
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (f ≫ g).hom))

end AlgebraicGeometry.Stack

end
