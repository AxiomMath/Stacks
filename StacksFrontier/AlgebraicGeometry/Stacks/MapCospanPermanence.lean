module

public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelPostcomposeRoutes

/-!
# Surjectivity, flatness and local finite presentation pass to `f × g` (Stacks 04ZU, 06PY, 06Q4)

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over `S`. The
1-morphism

    f × g : 𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵

of **Stacks 050H** (`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan`) is surjective, flat, or
locally of finite presentation as soon as `f` and `g` are. This is the permanence statement the
source uses without comment whenever it forms `f × f` over a cospan — in the proof of
**Stacks 0CPQ**, for instance — and it is proved here once, for several tags to use.

## The route

`f × g` factors through `𝒵 ×_𝒯 𝒴`, one factor at a time:

```text
  𝒳 ×_𝒯 𝒴  --- f × 1 --->  𝒵 ×_𝒯 𝒴  --- 1 × g --->  𝒵 ×_𝒯 𝒵
```

and each leg is a base change of the factor it applies: `1 × g` is the projection of the iterated
2-fibre product `(𝒵 ×_𝒯 𝒵) ×_{snd, 𝒵, g} 𝒴` and `f × 1` that of
`(𝒵 ×_𝒯 𝒴) ×_{fst, 𝒵, f} 𝒳`. So **Stacks 04ZU**, **Stacks 06PY** and **Stacks 06Q4** give the
three properties of each leg and **Stacks 04ZT**, **Stacks 06PX** and **Stacks 06Q3** compose
them.

The two apexes above are *iterated* 2-fibre products, so they are not the canonical 2-fibre
products of the cospans `(h, g ≫ h)` and `(f ≫ h, g ≫ h)` that `f × g` is written on; the
cancellations of **Stacks 02XD** recognise them as 2-fibre products of those cospans, and the
comparison 1-morphisms with the canonical ones are equivalences of the underlying categories. The
composite of the four 1-morphisms is `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanRoute`, and
`AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_twoIso_mapCospanRoute` identifies it with
`f × g`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanMiddleComparison` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanSourceComparison`: the two comparisons of a
  canonical 2-fibre product with an iterated one.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanRoute`: the factorisation of `f × g` into two
  base changes and those two comparisons.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanPreHom`: `f × g` itself, as a pre-morphism of
  2-commutative squares (**Stacks 003O**) with identity comparison 2-cells.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_mapCospanMiddleComparison` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_mapCospanSourceComparison`: the two
  comparisons are equivalences of the underlying categories.
* `AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_twoIso_mapCospanRoute`: that factorisation is
  2-isomorphic to `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_mapCospan`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_mapCospan` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_mapCospan`: the three
  permanence statements.

## Implementation notes

Each cancellation of Stacks 02XD is applied to a *canonical* inner square, which is what
`CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` and
`CategoryTheory.CatFiberedInGroupoids.cancelFstSquare` are stated for; that is why the route
alternates canonical and iterated 2-fibre products and carries two comparison 1-morphisms rather
than one.

The identification with `f × g` is a comparison of two 1-morphisms into the canonical 2-fibre
product `𝒵 ×_𝒯 𝒵`, so it is `CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_preHom`: the
route is assembled as a composite of pre-morphisms of 2-commutative squares (Stacks 003O), which
is what makes every compatibility square of Stacks 003O free except the one belonging to `f × g`
itself. That one is free too, up to the identities a strict 2-category's unitors and associators
leave behind: `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan` composed with either projection
of `𝒵 ×_𝒯 𝒵` is the corresponding projection of `𝒳 ×_𝒯 𝒴` followed by `f` or `g` *on the nose*
(`CategoryTheory.TwoFibreProductOver.mapCospan_comp_fst` and `..._comp_snd`), and the filler of
the source square is the filler of the canonical square `𝒳 ×_𝒯 𝒴` sandwiched between four
identity 2-cells.

The three properties do not transport across that 2-isomorphism uniformly. Surjectivity is a
property of the map on points, which only depends on the 2-isomorphism class
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`); flatness is an existential
smooth-diagram predicate, and local finite presentation a universal one, so the latter has to be
moved across the equivalence of conditions (1) and (2) of Stacks 06FM. Those two transports are
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_of_twoIso` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- Cancelling the four identity morphisms a strict 2-category's unitors and associators leave in
a sandwiched composite. Stated for an abstract category, where the bracketing of the identities is
free, and then applied; `rw` and `simp` cannot act inside such a composite of whiskerings, as
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstPostcompose` records. -/
theorem id_sandwich_eq {D : Type*} [Category D] {A B' : D} (u : A ⟶ B') :
    ((𝟙 A ≫ 𝟙 A) ≫ u) ≫ (𝟙 B' ≫ 𝟙 B') = u := by simp

section Route

variable (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)

/-- **The comparison of `𝒵 ×_𝒯 𝒴` with the iterated 2-fibre product `(𝒵 ×_𝒯 𝒵) ×_𝒵 𝒴`.** The
second-factor cancellation of **Stacks 02XD** exhibits the iterated apex as a 2-fibre product of
the cospan `(h, g ≫ h)`, and this is the mediating 1-morphism out of the canonical one. -/
noncomputable def mapCospanMiddleComparison :
    twoFibreProduct B S hS h (g ≫ h) ⟶
      twoFibreProduct B S hS (twoFibreProductSquare B S hS h h).snd g :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.twoFibreProductPreHom
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
        h.hom h.hom g.hom (g.hom ≫ h.hom) (Iso.refl _))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        h.hom (g.hom ≫ h.hom))).hom

/-- **The comparison of `𝒳 ×_𝒯 𝒴` with the iterated 2-fibre product `(𝒵 ×_𝒯 𝒴) ×_𝒵 𝒳`.** The
first-factor cancellation of **Stacks 02XD** exhibits the iterated apex as a 2-fibre product of
the cospan `(g ≫ h, f ≫ h)`, and this is the mediating 1-morphism out of the canonical square of
`(f ≫ h, g ≫ h)` with its two legs exchanged. -/
noncomputable def mapCospanSourceComparison :
    twoFibreProduct B S hS (f ≫ h) (g ≫ h) ⟶
      twoFibreProduct B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.twoFibreProductPreHom
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
        h.hom (g.hom ≫ h.hom) f.hom (f.hom ≫ h.hom) (Iso.refl _))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (f.hom ≫ h.hom) (g.hom ≫ h.hom)).swap).hom

/-- **`f × g` factored into two base changes and two comparison equivalences.** Reading
`𝒳 ×_𝒯 𝒴` as `(𝒵 ×_𝒯 𝒴) ×_𝒵 𝒳` and `𝒵 ×_𝒯 𝒴` as `(𝒵 ×_𝒯 𝒵) ×_𝒵 𝒴`, the two projections of
those iterated 2-fibre products are base changes of `f` and of `g`, and their composite is
`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan` up to a 2-isomorphism
(`AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_twoIso_mapCospanRoute`). -/
noncomputable def mapCospanRoute :
    twoFibreProduct B S hS (f ≫ h) (g ≫ h) ⟶ twoFibreProduct B S hS h h :=
  mapCospanSourceComparison B S hS f g h ≫
    ((twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f).fst ≫
      (mapCospanMiddleComparison B S hS g h ≫
        (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h h).snd g).fst))

/-- **`f × g` as a pre-morphism of 2-commutative squares (Stacks 003O).** The canonical square
of the cospan `(f ≫ h, g ≫ h)`, read over the cospan `(h, h)` by composing its two legs with `f`
and with `g`, maps to the canonical 2-fibre product `𝒵 ×_𝒯 𝒵` by `f × g`, with both comparison
2-cells of Stacks 003O identities: `f × g` composed with either projection of `𝒵 ×_𝒯 𝒵` is the
corresponding projection of `𝒳 ×_𝒯 𝒴` followed by `f` or `g` on the nose. -/
noncomputable def mapCospanPreHom :
    Bicategory.TwoCommSq.PreHom
      (((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (f.hom ≫ h.hom) (g.hom ≫ h.hom)).swap.postcomposeSnd f.hom
          (Iso.refl _)).swap.postcomposeSnd g.hom (Iso.refl _))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom h.hom) where
  hom := (mapCospan B S hS f g h).hom
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext P
    refine CatFiberedInGroupoids.map_id_comp_id_eq_of_eq h.hom.hom.toFunctor
      h.hom.hom.toFunctor ?_
    exact id_sandwich_eq _

/-- **The factorisation is `f × g`.** Both are 1-morphisms into the canonical 2-fibre product
`𝒵 ×_𝒯 𝒵`, presented as pre-morphisms of 2-commutative squares (**Stacks 003O**) out of one and
the same square with apex `𝒳 ×_𝒯 𝒴` over the cospan `(h, h)`, so the uniqueness half of the
universal property of **Stacks 003Q** identifies them up to a 2-isomorphism. -/
theorem nonempty_twoIso_mapCospanRoute :
    Nonempty (mapCospanRoute B S hS f g h ≅ mapCospan B S hS f g h) := by
  classical
  -- the canonical squares of the three cospans, and the two cancellations
  set J := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom h.hom
  set M := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    h.hom (g.hom ≫ h.hom)
  set C := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (f.hom ≫ h.hom) (g.hom ≫ h.hom)
  have hJ : Bicategory.IsTwoFibreProduct J :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      h.hom h.hom
  -- the four legs of the route, each a pre-morphism of 2-commutative squares
  set w₀ := CatFiberedInGroupoids.cancelSndPostcomposeSndPreHom.{u, u, u + 1, u + 1} h.hom h.hom
    g.hom (g.hom ≫ h.hom) (Iso.refl _)
  set w₁ := (Bicategory.twoFibreProductPreHom
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
        h.hom h.hom g.hom (g.hom ≫ h.hom) (Iso.refl _))
      M).postcomposeSnd g.hom (Iso.refl _)
  set w₂ := (CatFiberedInGroupoids.cancelFstPostcomposeSndPreHom.{u, u, u + 1, u + 1} h.hom
      (g.hom ≫ h.hom) f.hom (f.hom ≫ h.hom) (Iso.refl _)).postcomposeSnd g.hom (Iso.refl _)
  set w₃ := (((Bicategory.twoFibreProductPreHom
        (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
          h.hom (g.hom ≫ h.hom) f.hom (f.hom ≫ h.hom) (Iso.refl _))
        C.swap).postcomposeSnd f.hom (Iso.refl _)).swap).postcomposeSnd g.hom (Iso.refl _)
  set route := w₃.comp (w₂.comp (w₁.comp w₀))
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProduct_twoIso_of_preHom hJ route
    (mapCospanPreHom B S hS f g h)
  refine ⟨Bicategory.InducedBicategory.isoMk ?_⟩
  exact θ

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanMiddleComparison` is an equivalence of the
underlying categories: it compares two 2-fibre products of the cospan `(h, g ≫ h)`, the canonical
one and the second-factor cancellation of **Stacks 02XD**. -/
theorem isEquivalence_mapCospanMiddleComparison :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (mapCospanMiddleComparison B S hS g h).hom) :=
  Bicategory.isEquivalence_of_isTwoFibreProduct
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      h.hom (g.hom ≫ h.hom))
    (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
      h.hom h.hom g.hom (g.hom ≫ h.hom) (Iso.refl _))
    _

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanSourceComparison` is an equivalence of the
underlying categories: it compares two 2-fibre products of the cospan `(g ≫ h, f ≫ h)`. -/
theorem isEquivalence_mapCospanSourceComparison :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (mapCospanSourceComparison B S hS f g h).hom) :=
  Bicategory.isEquivalence_of_isTwoFibreProduct
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (f.hom ≫ h.hom) (g.hom ≫ h.hom)))
    (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
      h.hom (g.hom ≫ h.hom) f.hom (f.hom ≫ h.hom) (Iso.refl _))
    _

/-- **Stacks 04ZU for `f × g`.** If `f` and `g` are surjective then so is
`f × g : 𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`: each leg of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanRoute` is either a base change of `f` or of `g`,
surjective by Stacks 04ZU, or a comparison equivalence, surjective on points; the composite is
surjective by **Stacks 04ZT**, and surjectivity only depends on the 2-isomorphism class. -/
theorem isSurjective_mapCospan (hf : Stack.IsSurjective B S hS f)
    (hg : Stack.IsSurjective B S hS g) :
    Stack.IsSurjective B S hS (mapCospan B S hS f g h) := by
  have h₁ : Stack.IsSurjective B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h h).snd g).fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h h).snd g).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquare B S hS
          (twoFibreProductSquare B S hS h h).snd g)) hg
  have h₂ : Stack.IsSurjective B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f).fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquare B S hS
          (twoFibreProductSquare B S hS h (g ≫ h)).fst f)) hf
  have hroute : Stack.IsSurjective B S hS (mapCospanRoute B S hS f g h) :=
    Stack.isSurjective_comp_of_isEquivalence B S hS _ _
      (isEquivalence_mapCospanSourceComparison B S hS f g h)
      (Stack.isSurjective_comp B S hS _ _ h₂
        (Stack.isSurjective_comp_of_isEquivalence B S hS _ _
          (isEquivalence_mapCospanMiddleComparison B S hS g h) h₁))
  obtain ⟨Θ⟩ := nonempty_twoIso_mapCospanRoute B S hS f g h
  show Function.Surjective (pointsMap B S hS (mapCospan B S hS f g h))
  rw [← pointsMap_eq_of_hom₂ B S hS Θ.hom]
  exact hroute

/-- **Stacks 06PY for `f × g`.** If `f` and `g` are flat then so is
`f × g : 𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`: each leg of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanRoute` is a base change of `f` or of `g`, flat by
Stacks 06PY, or a comparison equivalence; the composite is flat by **Stacks 06PX**, and flatness
only depends on the 2-isomorphism class. -/
theorem isFlat_mapCospan (hf : IsFlat B S hS f) (hg : IsFlat B S hS g) :
    IsFlat B S hS (mapCospan B S hS f g h) := by
  have h₁ : IsFlat B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h h).snd g).fst :=
    isFlat_baseChange B S hS g (twoFibreProductSquare B S hS h h).snd _
      (isTwoFibreProduct_twoFibreProductSquare B S hS
        (twoFibreProductSquare B S hS h h).snd g) hg
  have h₂ : IsFlat B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f).fst :=
    isFlat_baseChange B S hS f (twoFibreProductSquare B S hS h (g ≫ h)).fst _
      (isTwoFibreProduct_twoFibreProductSquare B S hS
        (twoFibreProductSquare B S hS h (g ≫ h)).fst f) hf
  have hroute : IsFlat B S hS (mapCospanRoute B S hS f g h) :=
    isFlat_comp_of_isEquivalence B S hS _ _
      (isEquivalence_mapCospanSourceComparison B S hS f g h)
      (isFlat_comp B S hS _ _ h₂
        (isFlat_comp_of_isEquivalence B S hS _ _
          (isEquivalence_mapCospanMiddleComparison B S hS g h) h₁))
  obtain ⟨Θ⟩ := nonempty_twoIso_mapCospanRoute B S hS f g h
  exact (isFlat_iff_of_twoIso B S hS (mapCospanRoute B S hS f g h) (mapCospan B S hS f g h)
    (Bicategory.InducedBicategory.isoHom (f := mapCospanRoute B S hS f g h)
      (g := mapCospan B S hS f g h) Θ)).1 hroute

/-- **Stacks 06Q4 for `f × g`.** If `f` and `g` are locally of finite presentation then so is
`f × g : 𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`: each leg of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapCospanRoute` is a base change of `f` or of `g`, locally
of finite presentation by Stacks 06Q4, or a comparison equivalence; the composite is locally of
finite presentation by **Stacks 06Q3**, and the property only depends on the 2-isomorphism
class. -/
theorem isLocallyOfFinitePresentation_mapCospan
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS (mapCospan B S hS f g h) := by
  have h₁ : IsLocallyOfFinitePresentation B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h h).snd g).fst :=
    isLocallyOfFinitePresentation_baseChange B S hS g
      (twoFibreProductSquare B S hS h h).snd _
      (isTwoFibreProduct_twoFibreProductSquare B S hS
        (twoFibreProductSquare B S hS h h).snd g) hg
  have h₂ : IsLocallyOfFinitePresentation B S hS
      (twoFibreProductSquare B S hS (twoFibreProductSquare B S hS h (g ≫ h)).fst f).fst :=
    isLocallyOfFinitePresentation_baseChange B S hS f
      (twoFibreProductSquare B S hS h (g ≫ h)).fst _
      (isTwoFibreProduct_twoFibreProductSquare B S hS
        (twoFibreProductSquare B S hS h (g ≫ h)).fst f) hf
  have hroute : IsLocallyOfFinitePresentation B S hS (mapCospanRoute B S hS f g h) :=
    isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS _ _
      (isEquivalence_mapCospanSourceComparison B S hS f g h)
      (isLocallyOfFinitePresentation_comp B S hS _ _ h₂
        (isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS _ _
          (isEquivalence_mapCospanMiddleComparison B S hS g h) h₁))
  obtain ⟨Θ⟩ := nonempty_twoIso_mapCospanRoute B S hS f g h
  exact (isLocallyOfFinitePresentation_iff_of_twoIso B S hS (mapCospanRoute B S hS f g h)
    (mapCospan B S hS f g h)
    (Bicategory.InducedBicategory.isoHom (f := mapCospanRoute B S hS f g h)
      (g := mapCospan B S hS f g h) Θ)).1 hroute

end Route

end AlgebraicGeometry.Stack.AlgebraicStacks

end
