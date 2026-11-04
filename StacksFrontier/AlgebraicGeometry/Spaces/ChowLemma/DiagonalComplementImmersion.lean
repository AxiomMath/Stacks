module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdOverBase

/-!
# The complement of the diagonals is an immersion into the fibre power over the base

The proof of Stacks 089J cuts its cover out of the scheme-theoretic image of the complement of
the diagonals `V` inside a finite fibre power over the base of a projective compactification of
an étale chart. For Stacks 01RG to apply — so that `V` sits inside that image as a *dense open*
subscheme, which is what the gluing and the properness argument both use — the morphism from `V`
into the fibre power has to be an **immersion of schemes**. That is what this file proves.

Three facts compose. The complement of the diagonals is an open subspace of the `d`-fold
self-product of the chart *over the algebraic space*
(`AlgebraicGeometry.Space.SpacesEtale.isOpenImmersion_diagonalComplementObjι`); that
self-product sits in the `d`-fold product of the chart *over the base* as an immersion, by
`AlgebraicGeometry.Space.SpacesEtale.exists_isImmersion_selfProdOverBase`, which is where
separatedness of the algebraic space over the base is used; and the chart sits in the
compactification as an immersion, which is carried along by that same statement. The composite
is a morphism of presheaves between two represented presheaves, and it is the one represented by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementToOverProdObj` because the two have the
same components in the product.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isImmersion_diagonalComplementToOverProdObj`: **the
  morphism from the complement of the diagonals into the finite fibre power over the base is an
  immersion of schemes**, provided the algebraic space is separated over the base and the chart
  is an immersion into each factor.

## What is and is not proved

Nothing here carries a Stacks attribute. Stacks 02YU is carried by
`AlgebraicGeometry.Space.IsImmersion`, Stacks 02YV by
`AlgebraicGeometry.Space.isImmersion_comp`, and the content of the induction over the number of
factors sits in `StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/SelfProdOverBase.lean`.

Separatedness of the algebraic space over the base is an explicit hypothesis, stated as
separatedness of its morphism to a presheaf which is assumed terminal; it is not derived, and it
is exactly the hypothesis of Stacks 089J. Nothing is claimed about the morphism being
quasi-compact, which is the other input of Stacks 01RG; that is
`AlgebraicGeometry.Space.SpacesEtale.compactSpace_of_iso_underlying_diagonalComplement` together
with quasi-compactness of the fibre power.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The morphism from the complement of the diagonals into the finite fibre power over the
base is an immersion of schemes.**

Here `c : W ⟶ X` is an étale chart of an algebraic space `X` over `S` which is separated as a
morphism, `V` is an object of the big fppf category over `S` identified with the complement of
the diagonals in the `(n+1)`-fold self-product of the chart over `X`, and `j i : W ⟶ Y i` are
morphisms of the site which are immersions of schemes — in Stacks 089J the open immersion of the
chart into a projective compactification of it. The hypothesis `hXsep` is separatedness of the
structure morphism of `X` to the base, which is what Stacks 089J assumes about `X`.

This is the hypothesis `himm` of
`AlgebraicGeometry.Space.isOpenImmersion_toSchemeImageObj`, so with it Stacks 01RG puts `V` into
its scheme-theoretic image as an open subscheme. -/
theorem isImmersion_diagonalComplementToOverProdObj (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsTerminal T)
    (hXsep : IsSeparated B S hS (hT.from X.obj)) (n : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (n + 1) hsep)).obj)
    (Y : Fin (n + 1) → BigFppfOver B S hS) (j : ∀ i, W ⟶ Y i)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (j i))) :
    _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map
      (diagonalComplementToOverProdObj B S hS X W c hc hsep (n + 1) V e Y j)) := by
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) _).1 ?_
  have hj' : ∀ i, IsImmersion B S hS (yoneda.map (j i)) := fun i ↦
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) (j i)).2 (hj i)
  obtain ⟨Φ, hΦ, hΦc⟩ := exists_isImmersion_selfProdOverBase B S hS X hT hXsep
    (chartObj B S hS X W c hc) n (fun i ↦ yoneda.obj (Y i)) (fun i ↦ yoneda.map (j i)) hj'
  have hι := isOpenImmersion_diagonalComplementObjι B S hS X W c hc hsep (n + 1) V e
  have hΨ : IsImmersion B S hS ((e.hom ≫ ((toSpaces B S hS X).map
      (diagonalComplementι B S hS X (chartObj B S hS X W c hc) (n + 1) hsep)).hom) ≫
      Φ ≫ (yonedaOverProdObjIso B S hS Y).hom) :=
    isImmersion_comp B S hS _ _ (isImmersion_of_isOpenImmersion B S hS hι)
      (isImmersion_comp B S hS _ _ hΦ
        (isImmersion_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _)))
  have hcomps : ∀ i, ((e.hom ≫ ((toSpaces B S hS X).map
        (diagonalComplementι B S hS X (chartObj B S hS X W c hc) (n + 1) hsep)).hom) ≫
        Φ ≫ (yonedaOverProdObjIso B S hS Y).hom) ≫
          yoneda.map (overProdObjπ B S hS Y i) =
      yoneda.map (diagonalComplementProj B S hS X W c hc hsep (n + 1) V e i ≫ j i) := by
    intro i
    have hπ : ((toSpaces B S hS X).map (diagonalComplementπ B S hS X
          (chartObj B S hS X W c hc) (n + 1) hsep i)).hom =
        ((toSpaces B S hS X).map (diagonalComplementι B S hS X
          (chartObj B S hS X W c hc) (n + 1) hsep)).hom ≫
        ((toSpaces B S hS X).map
          (Pi.π (fun _ : Fin (n + 1) ↦ chartObj B S hS X W c hc) i)).hom :=
      hom_toSpaces_map_comp B S hS X _ _
    rw [Category.assoc, Category.assoc, Category.assoc, yonedaOverProdObjIso_hom_comp_π,
      hΦc i, Functor.map_comp, yoneda_map_diagonalComplementProj, hπ]
    cat_disch
  have hpre : yoneda.preimage ((e.hom ≫ ((toSpaces B S hS X).map
        (diagonalComplementι B S hS X (chartObj B S hS X W c hc) (n + 1) hsep)).hom) ≫
        Φ ≫ (yonedaOverProdObjIso B S hS Y).hom) =
      diagonalComplementToOverProdObj B S hS X W c hc hsep (n + 1) V e Y j := by
    refine overProdObj_hom_ext B S hS Y fun i ↦ yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, hcomps i,
      diagonalComplementToOverProdObj_comp_π]
  rw [← hpre, Functor.map_preimage]
  exact hΨ

end AlgebraicGeometry.Space.SpacesEtale

end
