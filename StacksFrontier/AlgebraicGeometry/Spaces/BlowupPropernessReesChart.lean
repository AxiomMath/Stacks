module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupReesProjContains
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Properness of a blowup of an algebraic space, read off a scheme chart

Stacks 085Z: the blowup `b : X' ⟶ X` of an algebraic space in a closed subspace of finite
presentation is proper.  Properness is étale local on the target (Stacks 083R); over a
surjective étale scheme chart the base change of `b` is the blowup of the chart (Stacks 085S),
which is the relative `Proj` of the Rees algebra of the chart ideal (Stacks 085R); that ideal is
finitely generated on affine opens by Stacks 084Q, so the scheme-level blowup is proper.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_exists_isProper`: properness of a
  blowup depends only on its centre.
* `AlgebraicGeometry.Space.fg_ideal_reesChartIdeal_preimage`: the chart ideal of a finitely
  presented centre is finitely generated over every affine open (Stacks 084Q on the chart).
* `AlgebraicGeometry.Space.hasReesProjChartInSite_of_isFinitePresentation`: the site-size
  condition `AlgebraicGeometry.Space.HasReesProjChartInSite` holds at every finitely presented
  centre, on the chart of an étale presentation of `X` (Stacks 0263 for the presentation, and
  the containment of the three relative `Proj`s of Stacks 085Q in the site).
* `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_hasReesProjChartInSite`: properness of
  the blowup, read off a chart on which the site-size condition is known.
* `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`: **Stacks 085Z**,
  the blowup of an algebraic space in a closed subspace of finite presentation is proper.
* `AlgebraicGeometry.Space.IsAdmissibleBlowup.isProper`: a `U`-admissible blowup of Stacks 086B
  is proper.

## References

* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Properness

variable {X X' : AlgebraicSpaces B S hS}

/-- A morphism which is a proper morphism precomposed with an isomorphism is proper. -/
private theorem isProper_of_iso_comp_eq {W W' Y : AlgebraicSpaces B S hS} (e : W ≅ W')
    {f : W' ⟶ Y} {g : W ⟶ Y} (hf : IsProper B S hS f.hom) (he : e.hom ≫ f = g) :
    IsProper B S hS g.hom := by
  have h : properProperty B S hS (e.hom ≫ f) :=
    MorphismProperty.RespectsIso.precomp (properProperty B S hS) e.hom f hf
  rw [he] at h
  exact h

/-- **Properness of a blowup depends only on its centre.**  If some blowup of `X` in `Z` is
proper then every blowup of `X` in `Z` is proper.

Being the blowup of `X` in `Z` is `AlgebraicGeometry.Space.IsBlowupAlong`, finality in the
category of Stacks 085U, so any two blowups of `X` in `Z` are isomorphic over `X` by
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`; properness is invariant under precomposition
with an isomorphism because `AlgebraicGeometry.Space.properProperty` is stable under base change,
hence respects isomorphisms. -/
theorem isProper_of_isBlowupAlong_of_exists_isProper (Z : ClosedSubspaces B S hS X.1)
    (b : X' ⟶ X) (hb : IsBlowupAlong B S hS Z b)
    (hsome : ∃ (X'' : AlgebraicSpaces B S hS) (b'' : X'' ⟶ X),
      IsBlowupAlong B S hS Z b'' ∧ IsProper B S hS b''.hom) :
    IsProper B S hS b.hom := by
  obtain ⟨X'', b'', hb'', hproper⟩ := hsome
  obtain ⟨e, he⟩ := hb.exists_iso hb''
  exact isProper_of_iso_comp_eq B S hS e hproper he

section Construction

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The relative `Proj`s which the construction of Stacks 085Q forms over some surjective
étale scheme chart of `X` are objects of the site.**  Spelled out: there is a scheme `V` of the
site and a surjective étale morphism `a : V ⟶ X` such that the three relative `Proj`s which
`AlgebraicGeometry.Space.blowUpAlong'` builds from the self-presentation of `V` and the inverse
image of `Z` in `V` — the one on the chart, the one on the relation and the one on the double
relation — lie below the site's size cutoff.

This is a condition on the big fppf site, not a mathematical hypothesis: it asserts only
membership in `AlgebraicGeometry.BigFppfSite.Contains`, which is the size bound
`Scheme.size · < B.cutoff`, and it is exactly the side condition that the construction of
Stacks 085Q (`AlgebraicGeometry.Space.blowUpAlong'`), its universal property, Stacks 085U
(`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`) and Stacks 085R
(`AlgebraicGeometry.Space.exists_iso_proj_reesGrading_affineChart`) already take.  No part of
any tag's statement enters it.  At a finitely presented centre it always holds, by
`AlgebraicGeometry.Space.hasReesProjChartInSite_of_isFinitePresentation`. -/
abbrev HasReesProjChartInSite (Z : ClosedSubspaces B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (a : schemeSpace V ⟶ X),
    IsEtale B S hS a.hom ∧ IsSurjective B S hS a.hom ∧
    B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj ∧
    B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj ∧
    B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The site-size condition holds at every finitely presented centre.**  If the inclusion of
the closed subspace `Z` of `X` is of finite presentation, take the chart `a : V ⟶ X` of the étale
presentation of `X` that `AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace` builds
(Stacks 0263); it is étale and surjective.  The inverse image of `Z` in `V` is again finitely
presented (`AlgebraicGeometry.Space.isFinitePresentation_ι_preimage`, Stacks 083Q), so the three
relative `Proj`s which the construction of Stacks 085Q forms from the self-presentation of `V`
lie in the site by `AlgebraicGeometry.Space.contains_reesProj_of_isFinitePresentation`: the
ideal they blow up is finitely generated over every affine open, so the blowup is proper, hence
quasi-compact and locally of finite type, over a scheme of the site. -/
theorem hasReesProjChartInSite_of_isFinitePresentation (Z : ClosedSubspaces B S hS X.1)
    (hfp : IsFinitePresentation B S hS Z.1.ι) : HasReesProjChartInSite B S hS Z := by
  let P := presentationOfIsAlgebraicSpace B S hS X.1 X.2
  let a : schemeSpace P.U ⟶ X := ObjectProperty.homMk P.toSpace
  obtain ⟨hcU, hcR, hcRR⟩ := contains_reesProj_of_isFinitePresentation
    (preimageClosedSubspace a Z) (isFinitePresentation_ι_preimage a Z hfp)
    (selfPresentation B S hS P.U)
  exact ⟨P.U, a, (isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).2 P.etale,
    isSurjective_of_presheafSurjective B S hS P.toSpace P.surjective, hcU, hcR, hcRR⟩

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The ideal which the inverse image of a finitely presented centre cuts out on a scheme
chart is finitely generated over every affine open of that chart.**

This is Stacks 084Q,
`AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart`, at the
self-presentation of the chart, whose atlas is the identity and so is trivially
surjective and étale; the inverse image of a finitely presented closed subspace is again
finitely presented by `AlgebraicGeometry.Space.isFinitePresentation_ι_preimage` (Stacks 083Q),
and the ideal the criterion produces is the Rees chart ideal by
`AlgebraicGeometry.Space.ker_rep_snd_eq_reesChartIdeal`. -/
theorem fg_ideal_reesChartIdeal_preimage (Z : ClosedSubspaces B S hS X.1)
    (hfp : IsFinitePresentation B S hS Z.1.ι) (V : BigFppfOver B S hS)
    (a : schemeSpace V ⟶ X)
    (A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens) :
    ((reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).ideal A).FG := by
  rw [← ker_rep_snd_eq_reesChartIdeal B S hS (schemeSpace V) (preimageClosedSubspace a Z)
    (selfPresentation B S hS V)]
  refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := ⟨(preimageClosedSubspace a Z).1.toFunctor, (preimageClosedSubspace a Z).2.1⟩)
    (X := schemeSpace V) (ObjectProperty.homMk (preimageClosedSubspace a Z).1.ι)
    (preimageClosedSubspace a Z).2.2 (selfPresentation B S hS V).etale
    (selfPresentation B S hS V).surjective).mp ?_ A
  exact isFinitePresentation_ι_preimage a Z hfp

/-- **Properness of a blowup, read off a chart in the site.**  A blowup `b : X' ⟶ X` of an
algebraic space `X` in a closed subspace `Z ⊆ X` whose closed immersion is of finite
presentation is proper, given a surjective étale scheme chart of `X` on which the three
relative `Proj`s of the construction of Stacks 085Q lie in the site.  Such a chart always
exists (`AlgebraicGeometry.Space.hasReesProjChartInSite_of_isFinitePresentation`), and the form
without it is `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`.

The source's proof is followed: properness is étale local on the target, Stacks 083R
(`AlgebraicGeometry.Space.isProper_tfae`), so it suffices to prove it for the base change of `b`
to a surjective étale scheme chart `a : V ⟶ X`.  An étale morphism is flat, so that base change
is the blowup of `V` in the inverse image of `Z`, Stacks 085S
(`AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat`), and over a scheme
chart a blowup is the relative `Proj` of the Rees algebra of the induced ideal, Stacks 085R
(`AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale`) — in particular a
scheme of the site.  The finite presentation of the centre says that the induced ideal is
finitely generated over every affine open of the chart
(`AlgebraicGeometry.Space.fg_ideal_reesChartIdeal_preimage`, Stacks 084Q), which is the
hypothesis under which the blowup of a scheme is proper over its base,
`Stacks.Blowup.isProper_blowUpToBase_of_fg`.  Properness of a morphism of schemes of the site
gives properness of its Yoneda image, `AlgebraicGeometry.Space.isProper_yoneda_map`, and
properness is invariant under precomposition with an isomorphism.

`hsite` supplies the chart; see `AlgebraicGeometry.Space.HasReesProjChartInSite`. -/
theorem isProper_of_isBlowupAlong_of_hasReesProjChartInSite (Z : ClosedSubspaces B S hS X.1)
    (b : X' ⟶ X)
    (hfp : IsFinitePresentation B S hS Z.1.ι)
    (hsite : HasReesProjChartInSite B S hS Z)
    (hb : IsBlowupAlong B S hS Z b) :
    IsProper B S hS b.hom := by
  obtain ⟨V, a, ha, hasurj, hcU, hcR, hcRR⟩ := hsite
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V ha hcU hcR hcRR
    (AlgebraicSpaces.isPullback_fiberProduct B S hS a b)
  have hscheme : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map
        (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU)) := by
    rw [toScheme_map_reesProjChartHom, ←
      Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase
        (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V))]
    exact MorphismProperty.RespectsIso.precomp
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (Stacks.Blowup.reesSituationBlowUpIso
        (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V))).hom _
      (_root_.AlgebraicGeometry.isProper_blowUpToBase_of_fg
        (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V))
        (fg_ideal_reesChartIdeal_preimage B S hS Z hfp V a))
  have h := isProper_of_iso_comp_eq B S hS e
    (isProper_yoneda_map B S hS
      (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) hscheme) he
  refine ((isProper_tfae B S hS X'.2 X.2 b.hom).out 4 1).mp ?_
  exact ⟨V, a.hom, hasurj, ha, h⟩

/-- **Stacks 085Z.**  Let `X` be an algebraic space over a scheme `S` and let `Z ⊆ X` be a
closed subspace whose closed immersion is of finite presentation — equivalently, whose
quasi-coherent sheaf of ideals `𝓘` is of finite type.  Then every blowup `b : X' ⟶ X` of `X` in
`Z` (in `𝓘`) is a proper morphism.

The source's proof: properness is étale local on the target (Stacks 083R), blowing up commutes
with flat base change (Stacks 085S), and over a scheme chart the blowup is proper because `𝓘`
is of finite type there (Stacks 02NS, 01WC).  That is
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_hasReesProjChartInSite`, applied on the
chart of an étale presentation of `X`, on which the relative `Proj`s the argument reads lie in
the site by `AlgebraicGeometry.Space.hasReesProjChartInSite_of_isFinitePresentation`.

The only argument beyond the source's is the instance `HasSheafify` for the big fppf topology:
the existence of sheafification of `Type u`-valued presheaves on the site, which this library's
construction of blowups of algebraic spaces (Stacks 085Q) and its chart description
(Stacks 085R) are stated with. -/
@[stacks 085Z "the blowup b : X' -> X of an algebraic space X in a closed subspace Z whose \
closed immersion is of finite presentation (equivalently, whose quasi-coherent ideal sheaf is of \
finite type) is a proper morphism, at the source's hypotheses: the relative Proj charts the \
proof reads are shown to lie in the site by hasReesProjChartInSite_of_isFinitePresentation"]
theorem isProper_of_isBlowupAlong_of_isFinitePresentation (Z : ClosedSubspaces B S hS X.1)
    (b : X' ⟶ X) (hfp : IsFinitePresentation B S hS Z.1.ι) (hb : IsBlowupAlong B S hS Z b) :
    IsProper B S hS b.hom :=
  isProper_of_isBlowupAlong_of_hasReesProjChartInSite B S hS Z b hfp
    (hasReesProjChartInSite_of_isFinitePresentation B S hS Z hfp) hb

/-- **Stacks 085Z for a `U`-admissible blowup.**  A `U`-admissible blowup of Stacks 086B is a
blowup of `X` in a closed subspace whose closed immersion is of finite presentation, so it is
proper.

The side condition `hsite` is the one of
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_hasReesProjChartInSite`,
quantified over the possible centres because admissibility leaves the centre existentially
bound. -/
theorem isProper_of_isAdmissibleBlowup_of_hasReesProjChartInSite (U : OpenSubspaces B S hS X.1)
    (b : X' ⟶ X) (hsite : ∀ Z : ClosedSubspaces B S hS X.1, HasReesProjChartInSite B S hS Z)
    (hb : IsAdmissibleBlowup B S hS U b) :
    IsProper B S hS b.hom := by
  obtain ⟨Z, hfp, -, hbl⟩ := hb
  exact isProper_of_isBlowupAlong_of_hasReesProjChartInSite B S hS Z b hfp (hsite Z) hbl

/-- **A `U`-admissible blowup is proper.**  A `U`-admissible blowup of Stacks 086B is a blowup
of `X` in a closed subspace whose closed immersion is of finite presentation, so it is proper by
Stacks 085Z, `AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`. -/
theorem IsAdmissibleBlowup.isProper {U : OpenSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsAdmissibleBlowup B S hS U b) : IsProper B S hS b.hom := by
  obtain ⟨Z, hfp, -, hbl⟩ := hb
  exact isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z b hfp hbl

end Construction

end Properness

end AlgebraicGeometry.Space

end
