module

public import StacksFrontier.AlgebraicGeometry.Quot.BaseChangeSpaceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.DifferenceDivisorSheafFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierGenericFibreExtension

/-!
# Extending an invertible module from the generic fibre over a valuation ring

This is the geometric core of Stacks 0DNG. Let `f : X ⟶ B` be a proper, smooth morphism of
finite presentation of algebraic spaces over `S`, let `R` be a valuation ring with fraction field
`K`, and let `g : T_K ⟶ T_R` be a morphism of test schemes over `B` whose underlying morphism of
schemes is `Spec K ⟶ Spec R`. Every invertible module `L_K` on `X_{T_K}` is the inverse image of
an invertible module on `X_{T_R}`.

## Main results

* `AlgebraicGeometry.Space.exists_isInvertibleModule_modulePullback_iso_of_valuationRing`: every
  invertible module on `X_{T_K}` is the inverse image of an invertible module on `X_{T_R}`.

## The argument

`X_{T_K}` is separated, Noetherian and regular (Stacks 04ZL, 06M1), so
`L_K ≅ 𝒪(D_K - D'_K)` for effective Cartier divisors `D_K, D'_K` (Stacks 0DMM); both are
inverse images of effective Cartier divisors `D, D' ⊆ X_{T_R}` (Stacks 0DMC, in the form
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_preimage_eq_of_isPullback` for the
cartesian square of the two base changes); and since `X_{T_K} ⟶ X_{T_R}` is flat, the inverse
image of `𝒪(D - D')` is `𝒪(D_K - D'_K)`.

## References

* [Stacks Project, Tag 0DNG](https://stacks.math.columbia.edu/tag/0DNG)
* [Stacks Project, Tag 0DMM](https://stacks.math.columbia.edu/tag/0DMM)
* [Stacks Project, Tag 0DMC](https://stacks.math.columbia.edu/tag/0DMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The sheaf `𝒪_X(D - D')` only depends on the two closed subspaces. -/
theorem differenceDivisorSheaf_congr (X : AlgebraicSpaces B S hS)
    {D D' E E' : ClosedSubspaces B S hS X.1} (h : D = E) (h' : D' = E')
    (hD : IsEffectiveCartierDivisor B S hS X D) (hD' : IsEffectiveCartierDivisor B S hS X D')
    (hE : IsEffectiveCartierDivisor B S hS X E) (hE' : IsEffectiveCartierDivisor B S hS X E') :
    differenceDivisorSheaf B S hS X D D' hD hD' = differenceDivisorSheaf B S hS X E E' hE hE' := by
  subst h h'
  rfl

/-- **The extension step of Stacks 0DNG.** For `f : X ⟶ B` proper, smooth and of finite
presentation and a morphism `g : T_K ⟶ T_R` of test schemes over `B` lying over
`Spec K ⟶ Spec R`, `K` the fraction field of a valuation ring `R`, every invertible module on
`X_{T_K}` is the inverse image of an invertible module on `X_{T_R}`. -/
theorem exists_isInvertibleModule_modulePullback_iso_of_valuationRing
    (s : PicardSituation B S hS) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (hsmooth : IsSmooth B S hS s.f.hom)
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {TK TR : s.SchemesOver} (g : TK ⟶ TR)
    (hTK : (BigFppfOver.toScheme B S hS).obj TK.left = Spec (.of K))
    (hTR : (BigFppfOver.toScheme B S hS).obj TR.left = Spec (.of R))
    (hg : (BigFppfOver.toScheme B S hS).map g.left =
      eqToHom hTK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ eqToHom hTR.symm)
    (L : Modules.{u, u} B S hS (s.baseChange TK).1 (s.baseChange TK).2)
    (hL : IsInvertibleModule (s.baseChange TK) L) :
    ∃ M : Modules.{u, u} B S hS (s.baseChange TR).1 (s.baseChange TR).2,
      IsInvertibleModule (s.baseChange TR) M ∧
        Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj M ≅ L) := by
  obtain ⟨hsep, hnoeth, hreg⟩ :=
    baseChangeSpace_separated_noetherian_regular s.f hfp hproper hsmooth TK hTK
  obtain ⟨DK, DK', cDK, cDK', ⟨e⟩⟩ :=
    exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf B S hS B.contains_terminal
      (s.baseChange TK) hsep hnoeth hreg L
      (isInvertible_of_isInvertibleModule B S hS _ L hL)
  have sq : IsPullback (baseChangeMap s.f g) (baseChangeInclusion s.f TK)
      (baseChangeInclusion s.f TR) ((schemeSpaceFunctor B S hS).map g.left) :=
    isPullback_overBaseChangeMap s.f ((schemesOverToOver s.base).map g)
  have hπ := isSmooth_baseChangeInclusion s.f hsmooth TR
  have lift := exists_isEffectiveCartierDivisor_preimage_eq_of_isPullback B S hS
    g.left hTK hTR hg (baseChangeInclusion s.f TR) (baseChangeInclusion s.f TK)
    (baseChangeMap s.f g) sq hπ
  obtain ⟨D, cD, hD⟩ := lift DK cDK
  obtain ⟨D', cD', hD'⟩ := lift DK' cDK'
  have hflatg : Flat ((BigFppfOver.toScheme B S hS).map g.left) := by
    rw [hg]
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
      Flat.SpecMap_iff.mpr
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
    infer_instance
  have hflat := isFlat_baseChangeMap s.f g hflatg
  obtain ⟨e'⟩ := nonempty_modulePullback_differenceDivisorSheaf_iso B S hS
    (baseChangeMap s.f g) hflat D D' cD cD'
  refine ⟨differenceDivisorSheaf B S hS _ D D' cD cD',
    isInvertibleModule_differenceDivisorSheaf B S hS _ D D' cD cD', ⟨e' ≪≫ eqToIso ?_ ≪≫ e.symm⟩⟩
  exact differenceDivisorSheaf_congr _ (Subtype.ext hD) (Subtype.ext hD') _ _ _ _

end AlgebraicGeometry.Space
