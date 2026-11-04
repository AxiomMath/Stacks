module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Cancelling the product projection off the 2-fibre product projection

Let `f : 𝒲 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, representable by algebraic spaces, with `𝒲` represented by an algebraic space. The
square `AlgebraicGeometry.Stack.relativeDiagonalSquare` at the cospan `(f, f)` has apex
`𝒲 ×_𝒳 𝒲` and first projection

```text
  pr : 𝒲 ×_𝒳 𝒲 ⟶ 𝒲 × 𝒲,
```

and composing `pr` with the first projection of the product gives back the first projection
`𝒲 ×_𝒳 𝒲 ⟶ 𝒲`, which is a base change of `f`. So if `P` is a property of morphisms of algebraic
spaces over `S` that is inherited by the first factor of a composite that has it, a relative
property `P` of the projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲` gives `P` for the morphism of representing
algebraic spaces induced by `pr`.

The cancellation happens on the *global* morphisms of representing algebraic spaces and not
fibrewise: over a scheme-valued point of `𝒲 × 𝒲` the base change of `pr` maps into the base
change of `pr` composed with the product projection, which is the wrong direction for
cancellation. The passage between the two levels is the bridge of Stacks 04XB for represented
source and target, `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`,
together with the functoriality of `AlgebraicGeometry.Stack.representingMap`.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_relativeDiagonalSquare_fst`: the cancellation,
  for an arbitrary property of morphisms of algebraic spaces inherited by first factors.
* `AlgebraicGeometry.Stack.prop_representingMap_relativeDiagonalSquare_fst_of_hasRelativeProperty`:
  the same from the relative property of `f` itself, by Stacks 045C.
* `AlgebraicGeometry.Stack.isUnramified_representingMap_relativeDiagonalSquare_fst` and
  `AlgebraicGeometry.Stack.isLocallyQuasiFinite_representingMap_relativeDiagonalSquare_fst`: the
  same at unramifiedness (Stacks 06G6) and at local quasi-finiteness (Stacks 03XN).

## Implementation notes

The conclusion is stated for representing algebraic spaces `V` of `𝒲 ×_𝒳 𝒲` and `W` of `𝒲 × 𝒲`
taken as arguments, which is the shape
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_fppf` consumes; the
representing algebraic space of `𝒲` occurs in no part of the statement and is extracted from the
representability hypothesis inside the proof.

Every universe is pinned by hand. The bridge of Stacks 04XB and the functoriality of
`AlgebraicGeometry.Stack.representingMap` are stated at
`CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, and the index universe of the fppf precoverage is
not determined by the instance binders, so it is written out as well.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The first projection of a product of two categories fibred in groupoids over the big fppf
site of `S`, as a 1-morphism of the 2-category: the product is the 2-fibre product over the
final object, and this is its first projection. -/
def productFstHom (𝒵 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    CatFiberedInGroupoids.product 𝒵 𝒴 ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.fst 𝒵.val.p 𝒴.val.p (𝟭 (BigFppfOver B S hS))
        𝒵.val.p 𝒴.val.p
      w := TwoFibreProductOver.fst_comp_eq }

variable (P : MorphismProperty (AlgebraicSpaces B S hS))
  [P.IsStableUnderBaseChange]
  [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
  (𝒲 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒲 ⟶ 𝒳)

/-- **Cancelling the product projection.** Let `P` be a property of morphisms of algebraic spaces
over `S` which is stable under base change, local on the target for the fppf precoverage, and
inherited by the first factor of a composite that has it. Let `f : 𝒲 ⟶ 𝒳` be representable by
algebraic spaces with `𝒲` represented by an algebraic space, and let `V` and `W` be algebraic
spaces representing `𝒲 ×_𝒳 𝒲` and `𝒲 × 𝒲`. If the first projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲` has the
relative property `P` of Stacks 03YK, then the morphism `V ⟶ W` induced by the projection
`𝒲 ×_𝒳 𝒲 ⟶ 𝒲 × 𝒲` of `AlgebraicGeometry.Stack.relativeDiagonalSquare` has `P`.

Composing that projection with the first projection of `𝒲 × 𝒲` is the first projection
`𝒲 ×_𝒳 𝒲 ⟶ 𝒲`, so on representing algebraic spaces the induced morphism `V ⟶ W` is a first
factor of a composite with `P`. -/
theorem prop_representingMap_relativeDiagonalSquare_fst
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (hcancel : ∀ ⦃X Y Z : AlgebraicSpaces B S hS⦄ (a : X ⟶ Y) (b : Y ⟶ Z), P (a ≫ b) → P a)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (Bicategory.InducedBicategory.mkHom (twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom))
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf)) :
    P (ObjectProperty.homMk
        (representingMap B S hS (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt
          (CatFiberedInGroupoids.product 𝒲 𝒲) V W eV eW
          (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst) :
      (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) := by
  obtain ⟨W₁, hW₁, ⟨eW₁⟩⟩ := h𝒲
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      ((relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst ≫
        productFstHom B S hS 𝒲 𝒲).hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf
  have hcomposite := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P
    ((relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst ≫ productFstHom B S hS 𝒲 𝒲)
    hrep V W₁ hV hW₁ eV eW₁).1 hP
  rw [representingMap_comp B S hS V W W₁ eV eW eW₁] at hcomposite
  exact hcancel _ _ hcomposite

/-- **Cancelling the product projection, from a relative property of `f` itself.** The
hypothesis of `AlgebraicGeometry.Stack.prop_representingMap_relativeDiagonalSquare_fst` on the
first projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲` is supplied by Stacks 045C from the relative property `P` of
`f`: that projection is a base change of `f` along `f`. -/
theorem prop_representingMap_relativeDiagonalSquare_fst_of_hasRelativeProperty
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (hcancel : ∀ ⦃X Y Z : AlgebraicSpaces B S hS⦄ (a : X ⟶ Y) (b : Y ⟶ Z), P (a ≫ b) → P a)
    (hPf : HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf) :
    P (ObjectProperty.homMk
        (representingMap B S hS (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt
          (CatFiberedInGroupoids.product 𝒲 𝒲) V W eV eW
          (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst) :
      (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) :=
  prop_representingMap_relativeDiagonalSquare_fst B S hS P 𝒲 𝒳 f hf h𝒲 V W hV hW eV eW hcancel
    (hasRelativeProperty_baseChange.{u, u, u, u} B S hS P 𝒲 𝒳 𝒲 f f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f)
      hf hPf)

/-- **Cancelling the product projection, at unramifiedness.** Let `f : 𝒲 ⟶ 𝒳` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` representable by algebraic spaces,
with `𝒲` represented by an algebraic space, and let `V` and `W` be algebraic spaces representing
`𝒲 ×_𝒳 𝒲` and `𝒲 × 𝒲`. If the first projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲` is unramified in the relative
sense of Stacks 03YK, then the morphism `V ⟶ W` induced by the projection `𝒲 ×_𝒳 𝒲 ⟶ 𝒲 × 𝒲` is
unramified.

The cancellation on morphisms of algebraic spaces is Stacks 06G6. -/
theorem isUnramified_representingMap_relativeDiagonalSquare_fst
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (hP : haveI : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
        Space.isUnramified_isStableUnderBaseChange B S hS
      haveI : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
        (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
          (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.unramifiedMorphismProperty B S hS)
        (Bicategory.InducedBicategory.mkHom (twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom))
        (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf)) :
    Space.IsUnramified B S hS
      (representingMap B S hS (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt
        (CatFiberedInGroupoids.product 𝒲 𝒲) V W eV eW
        (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst) := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact prop_representingMap_relativeDiagonalSquare_fst B S hS
    (Space.unramifiedMorphismProperty B S hS) 𝒲 𝒳 f hf h𝒲 V W hV hW eV eW
    (fun {X Y Z} a b h => Space.isUnramified_of_comp B S hS X.property Y.property Z.property
      a.hom b.hom h) hP

/-- **Cancelling the product projection, at local quasi-finiteness.** The statement of
`AlgebraicGeometry.Stack.isUnramified_representingMap_relativeDiagonalSquare_fst` with
unramifiedness replaced by local quasi-finiteness of morphisms of algebraic spaces over `S`.

The cancellation on morphisms of algebraic spaces is Stacks 03XN. -/
theorem isLocallyQuasiFinite_representingMap_relativeDiagonalSquare_fst
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.product 𝒲 𝒲).val.p
      (presheafOfCategories (W ⋙ typeToCat)).p)
    (hP : haveI : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
        Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.locallyQuasiFiniteProperty B S hS)
        (Bicategory.InducedBicategory.mkHom (twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom))
        (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 𝒲 𝒲 f.hom f.hom hf)) :
    Space.IsLocallyQuasiFinite B S hS
      (representingMap B S hS (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).pt
        (CatFiberedInGroupoids.product 𝒲 𝒲) V W eV eW
        (relativeDiagonalSquare.{u, u, u} B S hS 𝒲 𝒲 𝒳 f f).fst) := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
    Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
  exact prop_representingMap_relativeDiagonalSquare_fst B S hS
    (Space.locallyQuasiFiniteProperty B S hS) 𝒲 𝒳 f hf h𝒲 V W hV hW eV eW
    (fun {X Y Z} a b h => Space.isLocallyQuasiFinite_of_comp B S hS X.property Y.property
      Z.property a.hom b.hom h) hP

end AlgebraicGeometry.Stack

end
