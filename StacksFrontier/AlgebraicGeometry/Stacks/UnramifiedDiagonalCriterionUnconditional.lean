module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedIsLocallyQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedLocallyQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleFlatUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalEtalePrecomposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalCriterion

/-!
# Unramified 1-morphisms of algebraic stacks and their diagonal, without a supplied chart

**Stacks 0CJ0**: a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is unramified (**Stacks 0CIT**) if
and only if it is locally of finite type (**Stacks 06FS**) and its relative diagonal is étale
(**Stacks 0CIL**). The base registration
`AlgebraicStacks.isUnramified_iff_isLocallyOfFiniteType_and_isEtale_relativeDiagonal` takes
`AlgebraicGeometry.Stack.HasDiagonalDescentChart` as a hypothesis; this module removes it.

`HasDiagonalDescentChart f` itself is **not** a statement about an arbitrary `f`: its clause that
the left leg of the diagram factors étale through `𝒳 ×_𝒴 V` forces `f` to be Deligne–Mumford
(for `BG_m ⟶ Spec k` no algebraic space maps étale and surjectively onto `BG_m`). Both directions
of Stacks 0CJ0 do pass through Deligne–Mumford 1-morphisms, and the source's proof only ever uses
the chart for them; so the chart is not reconstructed here, the source's argument is carried out
directly.

## Main results

* `AlgebraicGeometry.Stack.isEtale_diagonal_of_etaleSmoothDiagram`: on *every* diagram of
  algebraic spaces over `f` with étale comparison to `𝒳 ×_𝒴 V`, étaleness of `Δ_f` makes the
  diagonal of the top morphism `U ⟶ V` étale. No surjectivity is needed.
* `AlgebraicGeometry.Stack.isRelativelyEtale_relativeDiagonal_of_isEtale_diagonal`: conversely,
  when `V ⟶ 𝒴` is surjective, flat and locally of finite presentation and the chart
  `U ⟶ 𝒳 ×_𝒴 V` is surjective étale, étaleness of the diagonal of `U ⟶ V` gives that of `Δ_f`.
* `AlgebraicStacks.isUnramified_of_isLocallyOfFiniteType_of_isEtale_relativeDiagonal`:
  **(2) ⇒ (1)** of Stacks 0CJ0, with no hypothesis beyond the source's.
* `isLocallyOfFiniteType_and_isEtale_relativeDiagonal_of_isUnramified_of_etalePresentation`:
  **(1) ⇒ (2)**, with the structure theorem of **Stacks 06N3** as the explicit argument through
  which **Stacks 0CIA** reaches this library.

## Implementation notes

The comparison of `Δ_f` with the diagonal of `U ⟶ V` goes through the relative diagonal of the
base change `𝒳 ×_𝒴 V ⟶ V`, which is a base change of `Δ_f` (**Stacks 04YR**,
`AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare`), and through
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalEtalePrecomposition` for the chart
`U ⟶ 𝒳 ×_𝒴 V`. The descent along `V ⟶ 𝒴` is **Stacks 045D** with the local essential
surjectivity `AlgebraicGeometry.Stack.localEssSurj_diagonalMapDiag`.

## References

* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06M2](https://stacks.math.columbia.edu/tag/06M2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Étaleness of `Δ_f` gives étaleness of the diagonal on a chart.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks, `b : 𝒮_V ⟶ 𝒴` a 1-morphism from an algebraic space, and
`k : 𝒮_U ⟶ 𝒳 ×_{f, 𝒴, b} V` a relatively étale 1-morphism from an algebraic space. If the relative
diagonal of `f` is relatively étale, then the diagonal of the morphism `U ⟶ V` induced by `k`
followed by the projection is étale.

The relative diagonal of `𝒳 ×_𝒴 V ⟶ V` is a base change of `Δ_f` (**Stacks 04YR**), so it is
relatively étale; precomposed with `k` it stays étale, and that composite is the relative
diagonal of `U ⟶ V` followed by the étale `k × k`. -/
theorem isEtale_diagonal_of_isRelativelyEtale_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (k : fibredCategory B S hS U ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt)
    (hk : IsRelativelyEtale B S hS k)
    (hΔ : IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    Space.IsEtale B S hS (pullback.diagonal
      (representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (k ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom b.hom).snd))) := by
  have hΔ' : IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS
      (twoFibreProductAlgebraicStack B S hS f b).val (algebraicSpaceStack.{u, w} B S hS V hV).val
      (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom) :=
    isRelativelyEtale_baseChange B S hS _ _ _ _ _ (diagonalBaseChangeSquare B S hS f b)
      (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f b) hΔ
  exact (isRelativelyEtale_relativeDiagonal_iff_isEtale_diagonal B S hS hU hV _).1
    ((isRelativelyEtale_comp_relativeDiagonal_iff B S hS k
      (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom hk).1
      (isRelativelyEtale_comp B S hS k _ hk hΔ'))

/-- Transport of étaleness of a diagonal along an equality of morphisms. -/
theorem isEtale_diagonal_of_eq {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g g' : U ⟶ V}
    (e : g = g') (h : Space.IsEtale B S hS (pullback.diagonal g)) :
    Space.IsEtale B S hS (pullback.diagonal g') :=
  e ▸ h

/-- **Étaleness of the diagonal on an étale chart gives étaleness of `Δ_f`.** Let `f : 𝒳 ⟶ 𝒴`
be a 1-morphism of algebraic stacks, `b : 𝒮_V ⟶ 𝒴` a surjective, flat, locally finitely presented
1-morphism from an algebraic space, and `k : 𝒮_U ⟶ 𝒳 ×_{f, 𝒴, b} V` a surjective relatively étale
1-morphism from an algebraic space. If the diagonal of the morphism `U ⟶ V` induced by `k`
followed by the projection is étale, then the relative diagonal of `f` is relatively étale.

This is the descent half of the source's proof: étaleness of the relative diagonal of
`𝒳 ×_𝒴 V ⟶ V` descends along the étale cover `k` (**Stacks 06M2**), and étaleness of `Δ_f`
descends along the base change of the cover `b` (**Stacks 04YR** and **Stacks 06TY**). -/
theorem isRelativelyEtale_relativeDiagonal_of_isEtale_diagonal (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (hbSurj : IsSurjective B S hS b) (hbFlat : AlgebraicStacks.IsFlat B S hS b)
    (hbLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS b)
    (k : fibredCategory B S hS U ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt)
    (hk : IsRelativelyEtale B S hS k)
    (hksurj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      k hk.1)
    (het : Space.IsEtale B S hS (pullback.diagonal
      (representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (k ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom b.hom).snd)))) :
    IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) := by
  have hΔ' := isRelativelyEtale_relativeDiagonal_of_comp B S hS k
    (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom hk hksurj
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f b).snd)
      ((isRelativelyEtale_relativeDiagonal_iff_isEtale_diagonal B S hS hU hV _).2 het)
  have hΔrep := isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  exact ⟨hΔrep, hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS 𝒳.val
    (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
    (Space.etaleMorphisms B S hS)
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
    (diagonalMapDiag B S hS f b) (diagonalBaseChangeSquare B S hS f b)
    (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f b) hΔrep
    (localEssSurj_diagonalMapDiag B S hS f b
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV) hbSurj hbFlat hbLfp) hΔ'.2⟩

/-- **On every étale-smooth diagram over `f`, étaleness of `Δ_f` gives étaleness of the diagonal
of the top morphism.** Let

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

be a 2-commutative square of algebraic spaces over `f` whose comparison 1-morphisms into the
2-fibre products of `(b, f)` are étale. If the relative diagonal of `f` is relatively étale, then
`U ⟶ U ×_V U` is étale. -/
theorem isEtale_diagonal_of_etaleSmoothDiagram (f : 𝒳 ⟶ 𝒴)
    (hΔ : IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom)
    (hk : ∀ (Q : Bicategory.TwoCommSq b.hom f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a.hom b.hom h η) Q),
        IsRelativelyEtale B S hS k.hom) :
    Space.IsEtale B S hS (pullback.diagonal h) := by
  have hJ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom b.hom)
  let k := Bicategory.twoFibreProductPreHom hJ (diagramCone B S hS f.hom a.hom b.hom h η)
  have heq : representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (k.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom b.hom).snd) = h :=
    (representingMap_congr_twoIso B S hS (𝒜 := fibredCategory B S hS U)
      (𝒞 := fibredCategory B S hS V) U V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) k.isoFst.symm).trans
      (representingMap_associatedMap B S hS U V h)
  exact isEtale_diagonal_of_eq B S hS heq
    (isEtale_diagonal_of_isRelativelyEtale_relativeDiagonal B S hS f hU hV b k.hom (hk _ hJ k) hΔ)

/-- Composites of 1-morphisms which are surjective on objects are surjective on objects. -/
private theorem isSurjectiveOnObjects_comp_hom
    {𝒰 𝒱 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (c : 𝒰 ⟶ 𝒱) (g : 𝒱 ⟶ 𝒲)
    (hc : IsSurjectiveOnObjects B S hS 𝒰.val.p 𝒱.val.p (CatFiberedInGroupoids.homFunctor c))
    (hg : IsSurjectiveOnObjects B S hS 𝒱.val.p 𝒲.val.p (CatFiberedInGroupoids.homFunctor g)) :
    IsSurjectiveOnObjects B S hS 𝒰.val.p 𝒲.val.p (CatFiberedInGroupoids.homFunctor (c ≫ g)) :=
  isSurjectiveOnObjects_comp B S hS 𝒰.val.p 𝒱.val.p 𝒲.val.p
    (CatFiberedInGroupoids.homFunctor c) (CatFiberedInGroupoids.homFunctor g)
    (CatFiberedInGroupoids.homFunctor_comp_p g) hc hg

/-- A Deligne–Mumford stack admits a relatively étale 1-morphism which is surjective on objects
from the fibred category of a representable presheaf. -/
private theorem exists_isRelativelyEtale_fibredCategory_yoneda_of_isDeligneMumfordStack
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒜 : IsDeligneMumfordStack.{u, w} B S hS 𝒜.val) :
    ∃ (W : BigFppfOver B S hS) (c : fibredCategory B S hS (yoneda.obj W) ⟶ 𝒜),
      IsRelativelyEtale B S hS c ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS (yoneda.obj W)).val.p 𝒜.val.p
        (CatFiberedInGroupoids.homFunctor c) := by
  obtain ⟨W, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS h𝒜
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver W
  let aInv : fibredCategory B S hS (yoneda.obj W) ⟶ schemeFibredCategory B S hS W :=
    equivalenceOverInvMap B S hS (yoneda.obj W) eU
  have haInv : Functor.IsEquivalence aInv.hom.toFunctor := by
    show Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  exact ⟨W, aInv ≫ pres, isRelativelyEtale_of_isEquivalence_comp B S hS aInv pres haInv hpreset,
    isSurjectiveOnObjects_comp_hom B S hS aInv pres
      (isSurjectiveOnObjects_equivalenceOverInvMap
        (𝒳 := schemeFibredCategory B S hS W) B S hS (yoneda.obj W) eU) hpressu⟩

/-- Let `R` be a 2-fibre product of `f` with a representable 1-morphism `g` which is surjective
on objects. If `c` into `R.pt` is surjective on objects, so is `c` followed by the first
projection. -/
private theorem isSurjectiveOnObjects_comp_fst
    {𝒰 𝒱 𝒲 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒱 ⟶ 𝒲) (f : 𝒵 ⟶ 𝒲) (R : Bicategory.TwoCommSq f g)
    (hR : Bicategory.IsTwoFibreProduct R) (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hgsu : IsSurjectiveOnObjects B S hS 𝒱.val.p 𝒲.val.p (CatFiberedInGroupoids.homFunctor g))
    (c : 𝒰 ⟶ R.pt)
    (hc : IsSurjectiveOnObjects B S hS 𝒰.val.p R.pt.val.p (CatFiberedInGroupoids.homFunctor c)) :
    IsSurjectiveOnObjects B S hS 𝒰.val.p 𝒵.val.p
      (CatFiberedInGroupoids.homFunctor (c ≫ R.fst)) :=
  isSurjectiveOnObjects_comp_hom B S hS c R.fst hc
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS R.fst
        (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ g f R hR hg)).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) _ _ _ g f R hR hg
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS g
          hg).1 hgsu)))

namespace AlgebraicStacks

/-- **Stacks 0CJ0, (2) ⇒ (1).** A 1-morphism of algebraic stacks over `S` which is locally of
finite type and has étale relative diagonal is unramified. No hypothesis beyond the source's. -/
theorem isUnramified_of_isLocallyOfFiniteType_of_isEtale_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hΔet : Stack.IsEtale B S hS (relativeDiagonal B S hS f)) :
    Stack.IsUnramified B S hS f := by
  have hΔ : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal B S hS f).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hΔrel : Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsEtale B S hS g.hom)
      (relativeDiagonal B S hS f).hom hΔ := by
    refine Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, u, w} B S hS _
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) _ hΔ ?_
    refine Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
      B S hS _ _ ?_ hΔet.2
    obtain ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp', -⟩ :=
      Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
        (⊤ : MorphismProperty (AlgebraicSpaces B S hS)) _ hΔ
        (fun _ _ _ _ _ _ => trivial)
    exact ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp'⟩
  refine ⟨⟨hΔ, fun U₀ y hy F hF he =>
    Space.isUnramified_of_isEtale B S hS (hΔrel U₀ y hy F hF he)⟩,
    fun U V hU hV a b h η hbsm hcomp => ?_⟩
  have hlfth : Space.IsLocallyOfFiniteType B S hS h :=
    hlft U V hU hV a.hom b.hom h η
      (Stack.isRelativelySmooth_of_etaleSmoothDiagram B S hS f hU hV a b h η hbsm hcomp) hbsm
      (fun Q hQ k => Stack.isRelativelySmooth_of_isRelativelyEtale B S hS _ (hcomp Q hQ k))
  exact Space.isUnramified_of_isOpenImmersion_diagonal B S hS h hlfth
    (Space.isOpenImmersion_diagonal_of_isEtale_diagonal B S hS hU hV h
      (Stack.isEtale_diagonal_of_etaleSmoothDiagram B S hS f ⟨hΔ, hΔrel⟩ hU hV a b h η hcomp))

/-- An algebraic stack admits a smooth 1-morphism from an algebraic space which is surjective on
objects; it is surjective, flat and locally of finite presentation. -/
private theorem exists_isRelativelySmooth_isSurjective_isFlat_isLocallyOfFinitePresentation
    (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (b : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴),
      Stack.IsRelativelySmooth B S hS b.hom ∧
      IsSurjectiveOnObjects B S hS (Stack.fibredCategory B S hS V).val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor b.hom) ∧
      Stack.IsSurjective B S hS b ∧ IsFlat B S hS b ∧ IsLocallyOfFinitePresentation B S hS b := by
  obtain ⟨V, hV, b₀, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒴.property
  let b : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom b₀
  have hbsm' : Stack.IsRelativelySmooth B S hS b.hom := hbsm
  have hsmooth : Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) b.hom :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) b.hom V hV
      (StacksRepresentableCFG.EquivalenceOver.refl _) hbsm' (Space.isSmooth_id B S hS hV)
  exact ⟨V, hV, b, hbsm', hbsu, Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS b hbsu,
    isFlat_of_isSmooth B S hS b hsmooth, isLocallyOfFinitePresentation_of_isSmooth B S hS b hsmooth⟩

/-- **Stacks 0CJ0, (1) ⇒ (2), with the structure theorem of Stacks 06N3 as an explicit
argument.** An unramified 1-morphism of algebraic stacks over `S` is locally of finite type and
has étale relative diagonal.

The source's proof: `f` is Deligne–Mumford, so for a smooth surjective `V ⟶ 𝒴` from an algebraic
space there is a surjective étale `U ⟶ 𝒳 ×_𝒴 V` from a scheme (**Stacks 0CIA**). Then `U ⟶ V` is
unramified, hence locally of finite type and with open immersion as diagonal (**Stacks 05W1**);
the first gives local finite type of `f`, the second étaleness of `Δ_f` by descent along the two
covers (`AlgebraicGeometry.Stack.isRelativelyEtale_relativeDiagonal_of_isEtale_diagonal`).

`hForward` is the substantial direction of Stacks 06N3, through which Stacks 0CIA is available in
this library (`isDeligneMumfordStack_twoFibreProduct_algebraicSpace`); it is the only input not
proved here. -/
theorem isLocallyOfFiniteType_and_isEtale_relativeDiagonal_of_isUnramified_of_etalePresentation
    (hForward : Stack.ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    (f : 𝒳 ⟶ 𝒴) (hf : Stack.IsUnramified B S hS f) :
    IsLocallyOfFiniteType B S hS f ∧ Stack.IsEtale B S hS (relativeDiagonal B S hS f) := by
  -- a smooth chart of `𝒴`, surjective on objects, by an algebraic space
  obtain ⟨V, hV, b, hbsm, hbsu, hbSurj, hbFlat, hbLfp⟩ :=
    exists_isRelativelySmooth_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS 𝒴
  -- Stacks 0CIA, part (2): an étale chart of `𝒳 ×_𝒴 V` by a scheme
  set J₀ : Bicategory.TwoCommSq f.hom b.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom
  have hJ₀ : Bicategory.IsTwoFibreProduct J₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom b.hom
  have hDM : Stack.IsDeligneMumfordStack.{u, w} B S hS J₀.pt.val :=
    isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w} B S hS B.contains_terminal
      hForward f hf.1 V hV b
  obtain ⟨W, cc, hccet, hccsu⟩ :=
    Stack.exists_isRelativelyEtale_fibredCategory_yoneda_of_isDeligneMumfordStack B S hS hDM
  have hU : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  -- the top horizontal morphism of the diagram, from Stacks 04SW
  let h : yoneda.obj W ⟶ V :=
    Stack.representingMap B S hS (Stack.fibredCategory B S hS (yoneda.obj W))
      (Stack.fibredCategory B S hS V) (yoneda.obj W) V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ J₀.snd)
  obtain ⟨e₀, hee, -⟩ := Stack.existsUnique_twoIso_of_representingMap_eq B S hS
    (Stack.fibredCategory B S hS (yoneda.obj W)) (Stack.fibredCategory B S hS V)
    (yoneda.obj W) V (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (Stack.representingMap_associatedMap B S hS (yoneda.obj W) V h)
  let e : (Stack.associatedMap B S hS h).1 ≅ cc ≫ J₀.snd :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e₀ hee)
  let a : Stack.algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) hU ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (cc ≫ J₀.fst)
  let η : (Stack.associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom :=
    Bicategory.whiskerRightIso e b.hom ≪≫ Bicategory.whiskerLeftIso cc J₀.swap.iso
  have hcomp : ∀ (Q : Bicategory.TwoCommSq b.hom f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom
        (Stack.diagramCone B S hS f.hom a.hom b.hom h η) Q),
      Stack.IsRelativelyEtale B S hS k.hom :=
    fun Q hQ k => Stack.isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b.hom
      J₀.swap (Bicategory.isTwoFibreProduct_swap hJ₀) cc hccet h e Q hQ k
  refine ⟨?_, ?_⟩
  · -- local finite type, through the existential smooth-diagram test of Stacks 06FM
    exact (isLocallyQuasiFinite_of_isUnramified B S hS f hf).2.1
  · -- étaleness of the relative diagonal, by descent along the two covers
    exact isEtale_of_isRelativelyEtale B S hS _
      (Stack.isRelativelyEtale_relativeDiagonal_of_isEtale_diagonal B S hS f hU hV b hbSurj
        hbFlat hbLfp cc hccet
        ((Stack.isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS cc
          hccet.1).1 hccsu)
        (Space.isEtale_of_isOpenImmersion B S hS
          (Space.isOpenImmersion_diagonal_of_isUnramified B S hS hU hV h
            -- the top horizontal morphism is unramified
            (hf.2 _ V hU hV a b h η hbsm hcomp))))

/-- **Stacks 0CJ0, with the structure theorem of Stacks 06N3 as an explicit argument.** A
1-morphism of algebraic stacks over `S` is unramified if and only if it is locally of finite type
and its relative diagonal is étale. `hForward` enters only the forward implication. -/
theorem isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal_of_etalePresentation
    (hForward : Stack.ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    (f : 𝒳 ⟶ 𝒴) :
    Stack.IsUnramified B S hS f ↔
      (IsLocallyOfFiniteType B S hS f ∧ Stack.IsEtale B S hS (relativeDiagonal B S hS f)) :=
  ⟨isLocallyOfFiniteType_and_isEtale_relativeDiagonal_of_isUnramified_of_etalePresentation
      B S hS hForward f,
    fun h => isUnramified_of_isLocallyOfFiniteType_of_isEtale_relativeDiagonal B S hS f h.1 h.2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
