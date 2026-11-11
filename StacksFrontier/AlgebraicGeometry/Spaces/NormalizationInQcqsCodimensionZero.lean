module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfStalks

/-!
# Codimension-zero points of the normalization of an algebraic space in another

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`
and let `Y ⟶ X' ⟶ X` be the normalization of `X` in `Y` (Stacks 0822).  Stacks 0AYG says that
every point `x'` of `|X'|` of codimension `0` (Stacks 04NA) is the image of a point of `|Y|` of
codimension `0`.  This file proves it at exactly these hypotheses.

## Main results

* `AlgebraicGeometry.Space.closure_range_pointsMap_eq_univ_of_isRelativeNormalization`: the
  morphism to the normalization has dense image when it is quasi-compact.
* `AlgebraicGeometry.Space.exists_localRingDimension_eq_zero_pointsMap_toNormalizationInQcqs`:
  **Stacks 0AYG.**

## Implementation notes

The printed statement of Stacks 0AYG says "morphism of schemes", but the lemma sits in the
section on relative normalization of algebraic spaces, refers to `|X'|`, `|Y|` and to the
codimension of points of algebraic spaces (Stacks 04NA), and its proof uses an étale chart of
`Y`; the scheme case is Stacks 0AXP.  The word is read as "algebraic spaces", as recorded in
`errata.md`.

Codimension `0` is `AlgebraicGeometry.Space.localRingDimension B S hS x = 0`, the dimension of
the local ring of Stacks 04NA.

The source reduces to an affine `X` by Stacks 0ABP and argues with the minimal primes of the
integral closure `A'`.  The proof here works on an affine étale chart `W ⟶ X'` at `x'` instead.
The morphism `f' : Y ⟶ X'` is quasi-compact and its image is dense: the scheme-theoretic image
of `f'` is a closed subspace through which `f` factors integrally, so the universal property of
the normalization (Stacks 0823) makes it all of `X'`.  The preimage of a dense set under the open
map `|W| → |X'|` is dense, so for an affine étale surjective chart `V` of the quasi-compact space
`Y ×_{X'} W` the morphism of affine schemes `V ⟶ W` is dominant.  The point of `W` above `x'` is
the generic point of an irreducible component (Stacks 0BAQ), hence the image of a generic point
`v₀` of `V`, and the image `y` of `v₀` in `Y` has codimension `0`, `V ⟶ Y` being étale.

## References

* [Stacks Project, Tag 0AYG](https://stacks.math.columbia.edu/tag/0AYG)
* [Stacks Project, Tag 0AXP](https://stacks.math.columbia.edu/tag/0AXP)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact morphism to the normalization of `V` in `U` has dense image: its
scheme-theoretic image is a closed subspace through which `U ⟶ V` factors integrally, so the
characterization of Stacks 0823 retracts the normalization onto that image. -/
theorem closure_range_pointsMap_eq_univ_of_isRelativeNormalization
    {U V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : U ⟶ V} {ν : V' ⟶ V} {g' : U ⟶ V'}
    (h : IsRelativeNormalization B S hS g ν g') (hU : IsAlgebraicSpace B S hS U)
    (hV' : IsAlgebraicSpace B S hS V') (hqcg : IsQuasiCompact B S hS g') :
    closure (Set.range (pointsMap B S hS U g')) = Set.univ := by
  set Z := schemeTheoreticImageSubfunctor B S hS g'
  have hZcl : IsClosedSubspace B S hS Z :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS g' hV'
  have hfac : toSchemeTheoreticImage B S hS g' ≫ Z.ι = g' :=
    toSchemeTheoreticImage_ι B S hS g'
  have hZint : IsIntegralHom B S hS (Z.ι ≫ ν) :=
    isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS Z.ι hZcl.2) h.isIntegralHom
  obtain ⟨k, ⟨hkg, hkν⟩, -⟩ := h.existsUnique_lift hZcl.1 (Z.ι ≫ ν) hZint
    (toSchemeTheoreticImage B S hS g') (by rw [← Category.assoc, hfac, h.fac])
  have hsection : k ≫ Z.ι = 𝟙 V' := by
    refine (h.existsUnique_lift hV' ν h.isIntegralHom g' h.fac).unique ⟨?_, ?_⟩
      ⟨Category.comp_id g', Category.id_comp ν⟩
    · rw [← Category.assoc, hkg, hfac]
    · rw [Category.assoc]; exact hkν
  have hretract : Z.ι ≫ k = 𝟙 Z.toFunctor := by
    refine (cancel_mono Z.ι).1 ?_
    rw [Category.assoc, hsection, Category.comp_id, Category.id_comp]
  have : IsIso Z.ι := ⟨k, hretract, hsection⟩
  rw [← range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS g' hU hV'
    hqcg]
  exact Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS Z.ι)

/-- Let `f' : Y ⟶ N` be a quasi-compact morphism of algebraic spaces with dense image.  Every
point of `|N|` of codimension `0` is the image of a point of `|Y|` of codimension `0`.

On an affine étale chart `W ⟶ N` at the point, the point above it is generic (Stacks 0BAQ); an
affine étale surjective chart `V` of the quasi-compact space `Y ×_N W` maps dominantly to `W`,
so a generic point of `V` lies over it, and its image in `Y` has codimension `0`. -/
theorem exists_localRingDimension_eq_zero_pointsMap_eq_of_dense_range {Y N : AlgebraicSpaces B S hS}
    (f' : Y ⟶ N) (hqc : IsQuasiCompact B S hS f'.hom)
    (hD : Dense (Set.range (pointsMap B S hS Y.1 f'.hom))) (x' : points B S hS N.1)
    (hx' : localRingDimension B S hS x' = 0) :
    ∃ y : points B S hS Y.1, localRingDimension B S hS y = 0 ∧
      pointsMap B S hS Y.1 f'.hom y = x' := by
  let Tsch := BigFppfOver.toScheme B S hS
  -- an affine étale chart of `N` at `x'`, whose point above `x'` is generic
  obtain ⟨W, b, hWaff, hbet, w, rfl⟩ := exists_affine_etale_chart_at_point B S hS N.1 N.2 x'
  have hb : IsEtale B S hS b := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hbet
  have hWsp : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hwgen : pointsToScheme B S hS W w ∈ genericPoints (Tsch.obj W) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS N.2 _).1 hx' W b _ hb
      (chartPoint_pointsToScheme B S hS W b w)
  -- an affine étale surjective chart of `Y ×_N W`
  have hPqc : IsQuasiCompactSpace B S hS (pullback f'.hom b) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry b f'.hom)
      (hqc _ hWsp (isAffineSpace_yoneda B S hS W hWaff).isQuasiCompactSpace b)
  have hP : IsAlgebraicSpace B S hS (pullback f'.hom b) :=
    isAlgebraicSpace_pullback B S hS f'.hom b Y.2 hWsp N.2
  obtain ⟨V, c, hVaff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hP).1 hPqc
  have hcsurj' : Function.Surjective (pointsMap B S hS _ c) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hP V c).1 hcsurj
  obtain ⟨g, hg⟩ := yoneda.map_surjective (c ≫ pullback.snd f'.hom b)
  -- the morphism of affine schemes `V ⟶ W` is dominant
  have hrange : pointsMap B S hS _ b ⁻¹' Set.range (pointsMap B S hS Y.1 f'.hom) ⊆
      Set.range (pointsMap B S hS _ (yoneda.map g)) := by
    rintro w' ⟨y, hy⟩
    obtain ⟨p, -, hp2⟩ :=
      exists_point_of_isPullback_presheaf B S hS (IsPullback.of_hasPullback f'.hom b) y w' hy
    obtain ⟨v, rfl⟩ := hcsurj' p
    exact ⟨v, by rw [hg, pointsMap_comp_apply, hp2]⟩
  have hopen := isOpenMap_pointsMap_of_isEtale B S hS b hWsp N.2 hb
  have hpre : Dense (pointsMap B S hS _ b ⁻¹' Set.range (pointsMap B S hS Y.1 f'.hom)) := by
    refine dense_iff_inter_open.2 fun O hO hne => ?_
    obtain ⟨_, ⟨o, ho, rfl⟩, hy⟩ := hD.inter_open_nonempty _ (hopen O hO) (hne.image _)
    exact ⟨o, ho, hy⟩
  have hGdense : DenseRange (Tsch.map g).base := by
    have h1 : Dense (schemePointsHomeomorph B S hS W ''
        Set.range (pointsMap B S hS _ (yoneda.map g))) :=
      (schemePointsHomeomorph B S hS W).surjective.denseRange.dense_image
        (schemePointsHomeomorph B S hS W).continuous (hpre.mono hrange)
    refine h1.mono ?_
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨pointsToScheme B S hS V v, (pointsToScheme_pointsMap B S hS g v).symm⟩
  have : IsAffine (Tsch.obj V) := hVaff
  have : IsAffine (Tsch.obj W) := hWaff
  have : IsDominant (Tsch.map g) := (isDominant_iff _).2 hGdense
  obtain ⟨v₀, hv₀, hgv₀⟩ := exists_mem_genericPoints_eq_of_isDominant (Tsch.map g) hwgen
  obtain ⟨vp, rfl⟩ := (schemePointsHomeomorph B S hS V).surjective v₀
  -- the image of the generic point in `Y`
  have hfst : IsEtale B S hS (pullback.fst f'.hom b) :=
    isEtale_pullback_fst B S hS Y.2 N.2 hWsp f'.hom b hb
  have hcy : IsEtale B S hS (c ≫ pullback.fst f'.hom b) := isEtale_comp B S hS hcet hfst
  refine ⟨pointsMap B S hS _ (c ≫ pullback.fst f'.hom b) vp,
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS Y.2 _).2
      ⟨V, c ≫ pullback.fst f'.hom b, _, hcy, chartPoint_pointsToScheme B S hS V _ vp, hv₀⟩, ?_⟩
  have hgw : pointsMap B S hS _ (yoneda.map g) vp = w :=
    (schemePointsHomeomorph B S hS W).injective
      ((pointsToScheme_pointsMap B S hS g vp).trans hgv₀)
  rw [← pointsMap_comp_apply, Category.assoc, pullback.condition, ← Category.assoc, ← hg,
    pointsMap_comp_apply, hgw]

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **Stacks 0AYG.**  Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of
algebraic spaces over `S` and let `Y ⟶ X' ⟶ X` be the normalization of `X` in `Y`
(Stacks 0822).  Every point `x'` of `|X'|` of codimension `0` (Stacks 04NA) is the image under
`f' : Y ⟶ X'` of a point of `|Y|` of codimension `0`. -/
@[stacks 0AYG "the printed word schemes is read as algebraic spaces, as the section, the \
notation |X'|, |Y| and the reference to 04NA require; codimension 0 is localRingDimension = 0"]
theorem exists_localRingDimension_eq_zero_pointsMap_toNormalizationInQcqs
    (x' : points B S hS (normalizationInQcqs B S hS f hfqc hfqs).1)
    (hx' : localRingDimension B S hS x' = 0) :
    ∃ y : points B S hS Y.1, localRingDimension B S hS y = 0 ∧
      pointsMap B S hS Y.1 (toNormalizationInQcqs f hfqc hfqs).hom y = x' :=
  exists_localRingDimension_eq_zero_pointsMap_eq_of_dense_range B S hS
    (toNormalizationInQcqs f hfqc hfqs) (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
    (dense_iff_closure_eq.2 (closure_range_pointsMap_eq_univ_of_isRelativeNormalization B S hS
      (isRelativeNormalization_normalizationInQcqs f hfqc hfqs) Y.2
      (normalizationInQcqs B S hS f hfqc hfqs).2
      (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs))) x' hx'

end AlgebraicGeometry.Space

end
