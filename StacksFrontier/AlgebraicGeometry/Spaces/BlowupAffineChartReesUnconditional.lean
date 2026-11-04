module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.BlowupContains
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees

/-!
# The blowup of an algebraic space over an affine étale chart, without side conditions

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `Z ⊆ X` be a closed subspace
with quasi-coherent sheaf of ideals `ℐ`, and let `b : X' ⟶ X` be the blowup of `X` in `Z`.
**Stacks 085R** says that for an affine scheme `U = Spec A` étale over `X`, with `I ⊆ A` the
ideal corresponding to `ℐ|_U`, the fibre product `U ×_X X'` is canonically isomorphic over `U`
to `Proj(⨁_{d ≥ 0} Iᵈ)`, and is covered by the affine opens `Spec A[I/a]`, `a ∈ I`.

`StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees` proves both clauses with the three
set-theoretic conditions that the construction of Stacks 085Q carries as hypotheses: that the
relative `Proj`s of the Rees algebras on the presenting scheme, on the relation scheme and on the
scheme of composable pairs of the chart's own presentation belong to the big fppf site. This
file proves those three conditions for an arbitrary étale presentation, and so states both
clauses of Stacks 085R at the source's hypotheses alone.

## Main results

* `AlgebraicGeometry.Space.contains_relativeProj_reesChartSituation`,
  `AlgebraicGeometry.Space.contains_relativeProj_reesRelationSituation` and
  `AlgebraicGeometry.Space.contains_relativeProj_reesDoubleSituation`: the three size conditions.
* `AlgebraicGeometry.Space.exists_iso_proj_reesGrading_affineChart_unconditional`: **Stacks
  085R, the canonical isomorphism**.
* `AlgebraicGeometry.Space.exists_iSup_opensRange_specAffineBlowupι_affineChart_unconditional`:
  **Stacks 085R, the affine open covering**.

## Implementation notes

For the self-presentation of a chart all three bases are objects of the site already, and
`Stacks.Blowup.size_relativeProj_reesSituation_le` — the bound special to the Rees algebra,
whose every graded piece is a submodule of the structure sheaf — says each relative `Proj` is no
larger than its base. So `AlgebraicGeometry.BigFppfSite.contains_relativeProj_reesSituation`
discharges each one outright. The bound is false for a general graded algebra, so this route is
specific to the blowup. Neither statement carries a `HasSheafify` instance: sheafification of
`Type`-valued presheaves for a Grothendieck topology is unconditional.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The three relative Projs are objects of the site -/

/-- **`P_U` is an object of the site.**  The relative `Proj` of the Rees algebra of a
quasi-coherent sheaf of ideals on the presenting scheme `U` of an étale presentation is no
larger than `U` itself (`Stacks.Blowup.size_relativeProj_reesSituation_le`, the bound special to
the Rees algebra), and `U`, being an object of the big fppf site over `S`, already satisfies the
site's size cutoff.  So the size side condition of the construction of Stacks 085Q holds with no
hypothesis at all. -/
theorem contains_relativeProj_reesChartSituation {X : AlgebraicSpaces B S hS}
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesChartSituation N hN P).relativeProj :=
  B.contains_relativeProj_reesSituation P.U.left.property (reesChartIdeal N hN P)

/-- **`P_R` is an object of the site.**  As
`AlgebraicGeometry.Space.contains_relativeProj_reesChartSituation`, for the relation scheme `R`
of the presentation in place of the presenting scheme. -/
theorem contains_relativeProj_reesRelationSituation {X : AlgebraicSpaces B S hS}
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesRelationSituation N hN P).relativeProj :=
  B.contains_relativeProj_reesSituation P.R.left.property (reesRelationIdeal N hN P)

/-- **`P_{R ×_U R}` is an object of the site.**  As
`AlgebraicGeometry.Space.contains_relativeProj_reesChartSituation`, for the scheme of composable
pairs of the presentation in place of the presenting scheme. -/
theorem contains_relativeProj_reesDoubleSituation {X : AlgebraicSpaces B S hS}
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesDoubleSituation N hN P).relativeProj :=
  B.contains_relativeProj_reesSituation (presentationDouble P).left.property
    (reesDoubleIdeal N hN P)

/-- The size side condition on `P_U` for the self-presentation of an étale chart, in the form
the statements of Stacks 085R use it. -/
theorem contains_relativeProj_reesChartSituation_selfPresentation
    {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.obj)
    (V : BigFppfOver B S hS) (a : schemeSpace V ⟶ X) :
    B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj :=
  contains_relativeProj_reesChartSituation _ _ _

/-! ### Stacks 085R: the blowup over an affine étale chart -/

/-- **Stacks 085R, the canonical isomorphism.**  Let `S` be a scheme, let `X` be an algebraic
space over `S`, let `Z ⊆ X` be a closed subspace with quasi-coherent defining sheaf of ideals
`ℐ ⊆ 𝒪_X` and let `b : X' ⟶ X` be the blowup of `X` in `Z`.  Let `U = Spec A` be an affine
scheme of the site étale over `X` and let `I ⊆ A` be the ideal corresponding to `ℐ|_U`.  Then
`U ×_X X'` is a scheme, and it is canonically isomorphic over `U` to the homogeneous spectrum
`Proj(⨁_{d ≥ 0} Iᵈ)` of the Rees algebra of `I` in `A`.

The first isomorphism exhibits the fibre product as the algebraic space of a scheme of the
site, namely the relative `Proj` `P_U` of the Rees algebra of `ℐ|_U`, compatibly with the
projections to `U`; the second identifies that scheme over `U` with `Proj` of the Rees algebra
of `I`, where `I` is the ideal of sections of `ℐ|_U` over `A`, which is the defining ideal of
the centre on the chart by
`AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_eq_ofIdealTop`. -/
@[stacks 085R "the canonical isomorphism clause: for an affine scheme U = Spec A of the site \
étale over X, the fibre product U ×_X X' is the scheme Proj of the Rees algebra of the ideal \
I of A corresponding to the restriction of the centre's defining sheaf of ideals, by an \
isomorphism over U; the blowup b is named by the universal property of Stacks 085U; there are \
no side conditions, the three B.Contains conditions on the relative Projs of the chart's own \
presentation being proved here from the Rees size bound; the tag's affine open covering clause \
is a separate registration"]
theorem exists_iso_proj_reesGrading_affineChart_unconditional
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.obj}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (I : Ideal ↥Γ((BigFppfOver.toScheme B S hS).obj V,
      (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1))
    (hI : (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).ideal
        (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)) = I) :
    ∃ e : W ≅ schemeSpace (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
        (contains_relativeProj_reesChartSituation_selfPresentation Z V a)),
      e.hom ≫ schemeSpaceMap (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
          (contains_relativeProj_reesChartSituation_selfPresentation Z V a)) = q ∧
      ∃ f : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
          (BigFppfOver.toScheme B S hS).obj
            (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
              (contains_relativeProj_reesChartSituation_selfPresentation Z V a)),
        f.hom ≫ (BigFppfOver.toScheme B S hS).map
            (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
              (contains_relativeProj_reesChartSituation_selfPresentation Z V a)) =
          Stacks.Blowup.toSpec I ≫
            (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen
              ((BigFppfOver.toScheme B S hS).obj V))).isoSpec.inv ≫
              (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1.ι := by
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V ha
    (contains_relativeProj_reesChartSituation_selfPresentation Z V a)
    (contains_relativeProj_reesRelationSituation _ _ _)
    (contains_relativeProj_reesDoubleSituation _ _ _) sq
  exact ⟨e, he, Stacks.Blowup.exists_iso_proj_reesGrading_of_ideal_eq _ I hI⟩

/-- **Stacks 085R, the affine open covering.**  In the situation of
`AlgebraicGeometry.Space.exists_iso_proj_reesGrading_affineChart_unconditional`, the scheme
representing `U ×_X X'` has an affine open covering by the spectra of the affine blowup
algebras `A[I/a]`, `a ∈ I`: the morphisms `Spec A[I/a] ⟶ U ×_X X'` obtained by composing the
standard chart `Stacks.Blowup.specAffineBlowupι` with the identification of the previous
theorem -- the same isomorphism over `U`, whose compatibility with the projections to `U` is
restated here -- are open immersions whose images have supremum the whole space.

The sources of the covering morphisms are the spectra of the affine blowup algebras
`Stacks.Blowup.affineBlowup I a` by construction, so this is the tag's "Moreover" clause. -/
@[stacks 085R "the affine open covering clause: the scheme U ×_X X' is covered by the images \
of the open immersions Spec A[I/a] ⟶ U ×_X X', a ∈ I, out of the spectra of the affine blowup \
algebras; same hypotheses as the canonical-isomorphism clause and, like it, no side conditions"]
theorem exists_iSup_opensRange_specAffineBlowupι_affineChart_unconditional
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.obj}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (I : Ideal ↥Γ((BigFppfOver.toScheme B S hS).obj V,
      (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1))
    (hI : (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).ideal
        (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)) = I) :
    ∃ e : W ≅ schemeSpace (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
        (contains_relativeProj_reesChartSituation_selfPresentation Z V a)),
      e.hom ≫ schemeSpaceMap (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
          (contains_relativeProj_reesChartSituation_selfPresentation Z V a)) = q ∧
      ∃ f : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
          (BigFppfOver.toScheme B S hS).obj
            (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
              (contains_relativeProj_reesChartSituation_selfPresentation Z V a)),
        (f.hom ≫ (BigFppfOver.toScheme B S hS).map
            (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)
              (contains_relativeProj_reesChartSituation_selfPresentation Z V a)) =
          Stacks.Blowup.toSpec I ≫
            (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen
              ((BigFppfOver.toScheme B S hS).obj V))).isoSpec.inv ≫
              (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1.ι) ∧
        (∀ c : I, _root_.AlgebraicGeometry.IsOpenImmersion
            (Stacks.Blowup.specAffineBlowupι I (c : _) c.2 ≫ f.hom)) ∧
          ⨆ c : I, (Stacks.Blowup.specAffineBlowupι I (c : _) c.2 ≫ f.hom).opensRange = ⊤ := by
  obtain ⟨e, he, f, hf⟩ :=
    exists_iso_proj_reesGrading_affineChart_unconditional hb V ha sq I hI
  exact ⟨e, he, f, hf, fun c => Stacks.Blowup.isOpenImmersion_specAffineBlowupι_comp I c.2 f,
    Stacks.Blowup.iSup_opensRange_specAffineBlowupι_comp I f⟩


end AlgebraicGeometry.Space

end
