module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocusCharts
public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleOpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding

/-!
# Openness of the ample locus of the Picard stack of a family of curves

Let `X ⟶ T` be a family of curves and `A = (T', b, L)` an object of `Picardstack_{X/T}` over a
scheme `T'` of the site. Stacks 0D3D, applied to the base change `X_{T'} ⟶ T'` of the structure
morphism and to `L`, produces an open subspace of `T'` through which a test scheme factors exactly
when the pullback of `A` to it is in the ample locus. That open subspace is an open subscheme
`v : V ⟶ T'`, so the criterion becomes one about morphisms of the site.

`AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_factors_iff_isInAmpleLocus` is that
criterion, and `AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point` is
the consequence the Picard-chart argument uses: if the pullback of `A` along a field-valued point
`y` of `T'` is in the ample locus, then `y` factors through an open subscheme of `T'` to which the
pullback of `A` is in the ample locus.

Every input is a theorem of the library:

* Stacks 0D3D is
  `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`;
* an open subspace of a scheme is an open subscheme, in factorization form, by
  `AlgebraicGeometry.Space.exists_isOpenImmersion_factors_iff_of_isOpenSubspace`;
* properness of `X_{T'} ⟶ T'` is base change (Stacks 0CL4) of the properness carried by the
  family of curves.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_factors_iff_isInAmpleLocus`.
* `AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point`.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The ample locus of `Picardstack_{X/T}` is cut out by an open subscheme of the test
scheme.** For an object `A` of the Picard stack of a family of curves over a test scheme
`π : T' ⟶ T` there is an open subscheme `v : V ⟶ T'` through which a morphism `g : T'' ⟶ T'`
of the site factors if and only if the pullback of `A` along `g` is in the ample locus. -/
theorem exists_isOpenImmersion_factors_iff_isInAmpleLocus (X : CurveFamily B hZ)
    {T' : BigFppfOver B integerBase hZ} (π : T' ⟶ X.base)
    (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ T'),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map v) ∧
        ∀ {T'' : BigFppfOver B integerBase hZ} (g : T'' ⟶ T'),
          ((∃ k : T'' ⟶ V, k ≫ v = g) ↔
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap g π ≫ eqToHom hA.symm)).IsInAmpleLocus) := by
  obtain ⟨T, L, hLinv⟩ := A
  change T = X.picardTestScheme π at hA
  subst hA
  have hpA : Space.IsProper B integerBase hZ
      (Space.baseChangeInclusion X.picardSituation.f (X.picardTestScheme π)).hom :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.picardSituation.f
        ((Space.schemesOverToOver X.picardSituation.base).obj (X.picardTestScheme π)).hom) X.proper
  obtain ⟨W, hW, hfac⟩ :=
    Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B integerBase hZ hpA
      hLinv
  obtain ⟨V, v, hv, hvfac⟩ :=
    Space.exists_isOpenImmersion_factors_iff_of_isOpenSubspace B integerBase hZ W hW
  refine ⟨V, v, hv, fun {T''} g => (hvfac g).trans ?_⟩
  refine (hfac _ _ _
    (Space.isPullback_baseChangeMap X.picardSituation.f (X.picardTestSchemeMap g π))).trans ?_
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- **The ample locus of `Picardstack_{X/T}` is open at a field-valued point.** If the pullback
of an object `A` of `Picardstack_{X/T}` over a test scheme `π : T' ⟶ T` along a field-valued point
`y` of `T'` is in the ample locus, then there is an open subscheme `ι : V ⟶ T'` whose image
contains the image of `y` and to which the pullback of `A` is in the ample locus. -/
theorem exists_isOpenImmersion_isInAmpleLocus_of_point (X : CurveFamily B hZ)
    (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base)
    (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
    (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
    (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
    (hy : (Space.PicardSituation.pullbackObject A
      (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus) :
    ∃ (V : BigFppfOver B integerBase hZ) (ι : V ⟶ T'),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι) ∧
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map y) ⊆
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map ι) ∧
      (Space.PicardSituation.pullbackObject A
        (X.picardTestSchemeMap ι π ≫ eqToHom hA.symm)).IsInAmpleLocus := by
  obtain ⟨V, v, hv, hfac⟩ := exists_isOpenImmersion_factors_iff_isInAmpleLocus X π A hA
  obtain ⟨k, hk⟩ := (hfac y).mpr hy
  refine ⟨V, v, hv, ?_, (hfac v).mp ⟨𝟙 V, Category.id_comp v⟩⟩
  rintro - ⟨t, rfl⟩
  refine ⟨(BigFppfOver.toScheme B integerBase hZ).map k t, ?_⟩
  have h := congrArg (fun φ : (schemeOverIntegers B).obj (B.obj hK') ⟶ T' =>
    (BigFppfOver.toScheme B integerBase hZ).map φ t) hk
  simp only [Functor.map_comp] at h
  exact h

end AlgebraicGeometry.CurveFamily

end
