module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CompactificationSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The construction datum of Stacks 089J

Every step of the construction of the Chow cover of [Stacks, Tag 089J] in this directory is
stated for a fixed tuple of data: an affine étale chart `c : W ⟶ X` of the algebraic space which
is *separated* as a morphism, an open immersion `j : W ⟶ Y` of that chart into a scheme `Y`
which is H-projective over the base, and the complement `V` of the diagonals in the
`(n+1)`-fold self-product of the chart over `X`, met as an object of the big fppf category
together with an *identification* `e` of the presheaf it represents with that complement. The
principal consumer is
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom`.

Nothing in this directory produced that tuple from `X`. Each ingredient fell just short: the
chart of `AlgebraicGeometry.Space.exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact`
comes without separatedness, the compactification of
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec` is a scheme
rather than an object of the site, and
`AlgebraicGeometry.Space.SpacesEtale.exists_diagonalComplementObj` discards the iso `e` which
the cover needs. This file closes that gap.

The three steps are: separatedness of the chart is Stacks 03FZ applied to the affine chart,
because an affine scheme is separated; the compactification is placed in the site by
`AlgebraicGeometry.Space.contains_of_isProjectiveMorphism` and its structure morphism and the
open immersion are lifted through fullness of the site's inclusion into schemes; and `e` is
simply retained rather than discarded.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.toScheme_map_from_mkIdTerminal`: the morphism of schemes underlying
  the unique morphism of the site to its terminal object is the structure morphism.
* `AlgebraicGeometry.Space.locallyOfFiniteType_hom_of_isEtale`: an étale chart of an algebraic
  space locally of finite type over the base has structure morphism locally of finite type as a
  morphism of schemes.
* `AlgebraicGeometry.Space.exists_compactificationObj_of_isAffine`: **the compactification of
  the chart as an object of the big fppf category over `Spec A`**, together with the open
  immersion of the chart into it and H-projectivity of its structure morphism.
* `AlgebraicGeometry.Space.exists_chowConstructionDatum`: **the construction datum of
  [Stacks, Tag 089J], produced from the algebraic space alone.** For an algebraic space over
  `Spec A` whose structure morphism is of finite type, and for every `n`, there is an affine
  chart which is étale, surjective and separated, a compactification of it H-projective over
  the base, and the complement of the diagonals in the `(n+1)`-fold self-product with the
  identifying isomorphism retained.

## Implementation notes

`AlgebraicGeometry.Space.locallyOfFiniteType_hom_of_isEtale` rests on a bridge between the
étale-chart-local formulation of `AlgebraicGeometry.Space.IsLocallyOfFiniteType` and the
scheme-level `AlgebraicGeometry.LocallyOfFiniteType` for a morphism of the site. The same
bridge is `private` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/CoverSeparated.lean` and in two further
modules; under the Lean module system a `private` declaration may not occur in the exposed body
of a public one, so it is re-derived here under a different name rather than reused. No existing
declaration is touched.

The number `n` of factors of the self-product is an argument, not an output: the datum exists
for every `n`, and the proof of [Stacks, Tag 089J] instantiates it at the minimal fibre degree
of the chart, which is
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_of_minimal_degree`.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute. Separatedness of the chart is Stacks 03FZ, carried by
`AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated`; the existence of the
affine étale chart is Stacks 03H6, carried by
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`; the
compactification is Stacks 01WA, carried by
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`; the size
estimate placing the compactification in the site is Stacks 000R (5), carried by
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`. What is added is
their combination into the tuple the construction consumes.

Only the data listed in the statement is produced. In particular nothing is said here about
compactness of `V`, about quasi-compactness of the morphism of `V` into the fibre power, or
about quasi-separatedness of the cover; those are further hypotheses of
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom` and they are not
discharged. Nor is the minimal fibre degree chosen here, nor the induction on it performed.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite type of the chart as a morphism of schemes -/

/-- **The morphism of schemes underlying the unique morphism of the site to its terminal object
is the structure morphism of the scheme.** The terminal object of the big fppf category over
`S` is the identity of `S`, so the unique morphism to it has the structure morphism as its
underlying morphism in the site; applying the inclusion into schemes gives the claim. -/
theorem toScheme_map_from_mkIdTerminal (W : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from W) =
      B.inclusion.map W.hom :=
  congrArg B.inclusion.map
    (show (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 (B.obj hS))).left = W.hom by simp)

/-- **An étale chart of an algebraic space locally of finite type over the base has structure
morphism locally of finite type as a morphism of schemes.**

The composite of the chart with the structure morphism of the algebraic space is the structure
morphism of the chart, and both factors are locally of finite type — the chart because it is
étale, by Stacks 06LT. Read on the site, that composite is the Yoneda image of the unique
morphism to the terminal object, whose underlying morphism of schemes is
`AlgebraicGeometry.Space.toScheme_map_from_mkIdTerminal`; the étale-chart-local formulation of
locally-of-finite-type and the scheme-level one agree for such a morphism because
`AlgebraicGeometry.LocallyOfFiniteType` is étale local on source and target. -/
theorem locallyOfFiniteType_hom_of_isEtale
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X) (hc : IsEtale B S hS c)
    (hlft : IsLocallyOfFiniteType B S hS ((isTerminal_yoneda_obj_base B S hS).from X)) :
    LocallyOfFiniteType (B.inclusion.map W.hom) := by
  have hcomp : IsLocallyOfFiniteType B S hS
      (c ≫ (isTerminal_yoneda_obj_base B S hS).from X) :=
    isLocallyOfFiniteType_comp' B S hS c _ hX
      (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))
      (isLocallyOfFiniteType_of_isEtale' B S hS c hc) hlft
  rw [show c ≫ (isTerminal_yoneda_obj_base B S hS).from X =
      yoneda.map (Over.mkIdTerminal.from W) from
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _] at hcomp
  have h := (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (Over.mkIdTerminal.from W)).1 hcomp
  rwa [toScheme_map_from_mkIdTerminal B S hS W] at h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (A : CommRingCat.{u}) (hA : B.Contains (Spec A))

/-! ### The compactification of the chart as an object of the site -/

/-- **The compactification of an affine chart, as an object of the big fppf category over
`Spec A`.** An affine scheme locally of finite type over `Spec A` is an open subscheme of a
scheme `Y` which is H-projective over `Spec A`, by
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec`. That `Y`
satisfies the site's size cutoff by
`AlgebraicGeometry.Space.contains_of_isProjectiveMorphism`, so both its structure morphism and
the open immersion of the chart into it are morphisms of schemes between objects of the site,
and therefore lift through fullness of the site's inclusion. The lifted structure morphism
makes `Y` an object of the big fppf category over `Spec A` whose structure morphism is the
original one, and the lifted immersion is a morphism of that category over the base.

This is the choice of `Y` with which the proof of [Stacks, Tag 089J] forms the fibre power in
which the cover is cut out, met in the site in which that fibre power is taken. -/
theorem exists_compactificationObj_of_isAffine (Wch : BigFppfOver B (Spec A) hA)
    (hW : IsAffine ((BigFppfOver.toScheme B (Spec A) hA).obj Wch))
    (hlft : LocallyOfFiniteType (B.inclusion.map Wch.hom)) :
    ∃ (Yo : BigFppfOver B (Spec A) hA) (j : Wch ⟶ Yo),
      _root_.AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B (Spec A) hA).map j) ∧
        IsProjectiveMorphism (B.inclusion.map Yo.hom) := by
  obtain ⟨Y, jsch, p, hj, hp, htri⟩ :=
    @exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec A
      ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) hW (B.inclusion.map Wch.hom) hlft
  have hYsite : B.Contains Y :=
    contains_of_isProjectiveMorphism B (Spec A) hA
      (D := Over.mk (𝟙 (B.obj hA))) p hp
  let Yo : BigFppfOver B (Spec A) hA :=
    Over.mk (B.inclusion.preimage (X := B.obj hYsite) (Y := B.obj hA) p)
  have hYohom : B.inclusion.map Yo.hom = p := B.inclusion.map_preimage _
  have hjs := B.inclusion.map_preimage (X := Wch.left) (Y := B.obj hYsite) jsch
  refine ⟨Yo, Over.homMk (B.inclusion.preimage (X := Wch.left) (Y := B.obj hYsite) jsch)
    (B.inclusion.map_injective ?_), hjs ▸ hj, hYohom ▸ hp⟩
  rw [Functor.map_comp, hjs, hYohom, htri]

/-! ### The construction datum -/

/-- **The construction datum of [Stacks, Tag 089J], produced from the algebraic space alone.**

Let `X` be an algebraic space over `Spec A` whose structure morphism is of finite type, and let
`n` be a natural number. Then there are

* an object `Wch` of the big fppf category over `Spec A` with *affine*, hence compact,
  underlying scheme, and a morphism `c : h_{Wch} ⟶ X` which is étale, surjective and
  **separated**;
* an object `Yo` of the site whose structure morphism to `Spec A` is H-projective, and a
  morphism `j : Wch ⟶ Yo` whose underlying morphism of schemes is an open immersion;
* an object `V` of the site **together with** an isomorphism `e` of the presheaf it represents
  with the complement of the diagonals in the `(n+1)`-fold self-product of the chart over `X`.

This is exactly the tuple on which the construction of the cover in this directory is
parametrised, in the shape
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom` takes it; the isomorphism
`e` is retained rather than existentially discarded, because the cover
`AlgebraicGeometry.Space.chowCoverObj` is a function of it. The binder is written `_e` only
because no later conjunct of the statement mentions it; a consumer destructures it like any
other component of the tuple.

Separatedness of `c` is Stacks 03FZ: the chart is affine, hence a separated scheme, and an
étale morphism to an algebraic space out of a separated scheme is separated. It is **not**
obtained from separatedness of `X` over the base, which is therefore not assumed; of the two
hypotheses of [Stacks, Tag 089J] only finite type is used here, and of it only
quasi-compactness — for the chart — and locally-of-finite-type — for the compactification. -/
theorem exists_chowConstructionDatum (X : AlgebraicSpaces B (Spec A) hA)
    (hft : IsFiniteType B (Spec A) hA
      ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj)) (n : ℕ) :
    ∃ (Wch : BigFppfOver B (Spec A) hA) (c : yoneda.obj Wch ⟶ X.obj)
      (hc : IsEtale B (Spec A) hA c) (hsep : IsSeparated B (Spec A) hA c)
      (Yo : BigFppfOver B (Spec A) hA) (j : Wch ⟶ Yo) (V : BigFppfOver B (Spec A) hA)
      (_e : yoneda.obj V ≅ (SpacesEtale.underlying B (Spec A) hA X
        (SpacesEtale.diagonalComplement B (Spec A) hA X
          (SpacesEtale.chartObj B (Spec A) hA X Wch c hc) (n + 1) hsep)).obj),
      IsAffine ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) ∧
        CompactSpace ((BigFppfOver.toScheme B (Spec A) hA).obj Wch) ∧
        IsSurjective B (Spec A) hA c ∧
        _root_.AlgebraicGeometry.IsOpenImmersion
            ((BigFppfOver.toScheme B (Spec A) hA).map j) ∧
          IsProjectiveMorphism (B.inclusion.map Yo.hom) := by
  obtain ⟨Wch, c, hW, hcsurj, hc⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec A) hA X.property
      ((isTerminal_yoneda_obj_base B (Spec A) hA).from X.obj) hft.2
  have := hW
  have hsep : IsSeparated B (Spec A) hA c :=
    isSeparated_of_isEtale_of_scheme_isSeparated B (Spec A) hA X.obj X.property Wch
      inferInstance c hc
  obtain ⟨Yo, j, hj, hYo⟩ :=
    exists_compactificationObj_of_isAffine B A hA Wch hW
      (locallyOfFiniteType_hom_of_isEtale B (Spec A) hA X.property Wch c hc hft.1)
  obtain ⟨V, ⟨e⟩⟩ :=
    SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement B (Spec A) hA X
      (SpacesEtale.chartObj B (Spec A) hA X Wch c hc)
      (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj Wch))) n hsep
  exact ⟨Wch, c, hc, hsep, Yo, j, V, e, hW, inferInstance,
    isSurjective_of_presheafSurjective B (Spec A) hA c hcsurj, hj, hYo⟩

end AlgebraicGeometry.Space

end
