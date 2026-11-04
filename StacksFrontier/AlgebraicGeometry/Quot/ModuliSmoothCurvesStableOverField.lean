module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable

/-!
# Smooth curves of genus `g ≥ 2` over a field are stable

Let `X` be a proper scheme of dimension at most one over a field `K`, and suppose its family of
curves lies in `𝓜_g` (Stacks 0E83): it is smooth of relative dimension one, `f_*𝒪_X = 𝒪`
universally, and `R¹f_*𝒪_X` is locally free of rank `g` on the small étale site of `Spec K`.
For `g ≥ 2` the family is then stable of genus `g`, that is, it lies in `𝓜̄_g` (Stacks 0E78).
This is the inclusion `𝓜_g ⊂ 𝓜̄_g` of Stacks 0E87, on points.

The rank of `R¹f_*𝒪_X` is the genus of `X` (Stacks 071N, read through the comparison of the étale
and Zariski direct images), and the fibre of the family over a field-valued point `Spec L ⟶ Spec K`
is the base change `X_L`, whose genus is that of `X` (Stacks 0BY9). The remaining conditions of
stability are those of `AlgebraicGeometry.isStableCurveFamilyOfGenus_of_isSmoothH0Family`.

## Main results

* `AlgebraicGeometry.genus_eq_of_isPullback_curveFamilyOfScheme`: the fibres of the family of
  curves of `X` over field-valued points have the genus of `X`.
* `AlgebraicGeometry.genus_eq_of_hasGenus_curveFamilyOfScheme`: if that family has genus `g`,
  so does `X`.
* `AlgebraicGeometry.isStableCurveFamilyOfGenus_curveFamilyOfScheme_of_isSmoothH0Family`: for
  `g ≥ 2`, a family over a field in `𝓜_g` is in `𝓜̄_g`.

## References

* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The genus of a fibre of the family of curves of a proper scheme over a field.** Let `X` be
a proper scheme over a field `K`. The fibre of its family of curves over a field-valued point
`Spec L ⟶ Spec K` of the base, formed as a fibre product of algebraic spaces, is the base change
`X_L`, so it has the genus of `X` (Stacks 0BY9). -/
theorem genus_eq_of_isPullback_curveFamilyOfScheme {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    {p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hK hdim).base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject}
    {q : schemeSpace V ⟶ (curveFamilyOfScheme X B hZ hK hdim).total}
    (hsq : IsPullback q (schemeSpaceMap v) (curveFamilyOfScheme X B hZ hK hdim).toBase
      (schemeSpaceMap p.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map v) = genus X.hom := by
  let hff := schemeSpaceFunctorFullyFaithful B (S := integerBase) hZ
  have := hff.full
  have := hff.faithful
  let q' := hff.preimage q
  have hq' : schemeSpaceMap q' = q := hff.map_preimage q
  let xs := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK)
    hK X.hom
  let pv : p.siteObject ⟶ integerSiteObject B hZ hK := p.value
  have hw : q' ≫ xs = v ≫ pv := by
    apply (schemeSpaceFunctor B integerBase hZ).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    show schemeSpaceMap q' ≫ schemeSpaceMap xs = schemeSpaceMap v ≫ schemeSpaceMap pv
    rw [hq']
    exact hsq.w
  have hsite : IsPullback q' v xs pv := by
    refine IsPullback.of_map (schemeSpaceFunctor B integerBase hZ) hw ?_
    show IsPullback (schemeSpaceMap q') (schemeSpaceMap v) (schemeSpaceMap xs)
      (schemeSpaceMap pv)
    rwa [hq']
  have hsch := hsite.map (BigFppfOver.toScheme B integerBase hZ)
  let L := p.carrier
  let φ : CommRingCat.of K ⟶ CommRingCat.of L :=
    Spec.preimage ((BigFppfOver.toScheme B integerBase hZ).map pv)
  let : Algebra K L := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      (BigFppfOver.toScheme B integerBase hZ).map pv :=
    Spec.map_preimage _
  have h' : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map q')
      ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rwa [hφ]
  exact genus_baseChange K L _ _ X.hom h'

/-- **The genus of a proper scheme over a field from its family of curves.** If the family of
curves of a proper scheme `X` of dimension at most one over a field has genus `g`, that is,
`R¹f_*𝒪_X` is locally free of rank `g` on the small étale site of the field, then `X` has
genus `g`: that module is locally free of rank the genus of `X` (Stacks 071N, through the
comparison of the étale and Zariski direct images), and the rank over a nonempty base is
unique. -/
theorem genus_eq_of_hasGenus_curveFamilyOfScheme {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {g : ℕ}
    (hgen : CurveFamily.HasGenus B hZ (curveFamilyOfScheme X B hZ hK hdim) g) :
    genus X.hom = g := by
  have h₁ := isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus
    (B := B) (hZ := hZ) K
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK) hK
      X.hom) rfl (inferInstanceAs (IsProper X.hom)) hdim
  have h₂ : CurveFamily.HasGenus B hZ (curveFamilyOfScheme X B hZ hK hdim)
      (genus (X.hom ≫ eqToHom rfl)) := h₁
  simpa using CurveFamily.hasGenus_unique B hZ h₂ hgen (IsLocalRing.closedPoint K)

/-- **A smooth proper curve of genus `g ≥ 2` over a field with `H⁰ = k` is stable.** Let `X` be
a proper scheme of dimension at most one over a field whose family of curves is smooth of
relative dimension one, with `f_*𝒪_X = 𝒪` universally and of genus `g ≥ 2`. Then the family is
stable of genus `g`: it is prestable, a smooth morphism of relative dimension one being
at-worst-nodal; every fibre over a field-valued point is smooth and proper with `H⁰ = k`, hence
irreducible, so it has neither a rational tail nor a rational bridge; and it is a base change of
`X`, so it has the genus `g` of `X`. -/
theorem isStableCurveFamilyOfGenus_curveFamilyOfScheme_of_isSmoothH0Family {K : Type u}
    [Field K] (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {g : ℕ} (hg : 2 ≤ g)
    (hF : IsSmoothH0Family B hZ (curveFamilyOfScheme X B hZ hK hdim))
    (hgen : CurveFamily.HasGenus B hZ (curveFamilyOfScheme X B hZ hK hdim) g) :
    IsStableCurveFamilyOfGenus B hZ g (curveFamilyOfScheme X B hZ hK hdim) := by
  have hpre : IsPrestableCurveFamily B hZ (curveFamilyOfScheme X B hZ hK hdim) :=
    ⟨Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth B integerBase hZ hF.1.1 hF.1.2, hF.2⟩
  refine ⟨⟨hpre, fun p => ?_⟩, hgen⟩
  obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ _ p
  have hsq' : IsPullback q.hom (yoneda.map v) (curveFamilyOfScheme X B hZ hK hdim).toBase.hom
      (yonedaEquiv.symm p.value) :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
  refine ⟨V, v, q.hom, hsq', ?_⟩
  have := CurveFamily.smooth_of_isPullback_fieldValuedPoint hF.1.1 hsq
  have := CurveFamily.isProper_of_isPullback_fieldValuedPoint hsq
  have := irreducibleSpace_of_smooth_of_isIso_appTop p.carrier
    ((BigFppfOver.toScheme B integerBase hZ).map v)
    (CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint hF.2 hsq)
  let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over (Spec (.of p.carrier)) :=
    ⟨(BigFppfOver.toScheme B integerBase hZ).map v⟩
  have hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).obj V ↘
    Spec (.of p.carrier)) := ‹IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)›
  refine ⟨?_, not_isRationalTail_of_irreducibleSpace p.carrier _, hproper,
    not_isRationalBridge_of_irreducibleSpace p.carrier _⟩
  rwa [genus_eq_of_isPullback_curveFamilyOfScheme hK X hdim hsq,
    genus_eq_of_hasGenus_curveFamilyOfScheme hK X hdim hgen]

end AlgebraicGeometry

end
