module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomStageRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomOpenRestriction

/-!
# The relative Hom functor over a Noetherian base

Stacks 08JY: in Situation 08JT, if the base `B` is a Noetherian algebraic space, `f : X ⟶ B` is
locally of finite type and quasi-separated, `𝓕` is of finite type, and `𝒢` is of finite type,
flat over `B` and with support proper over `B`, then `Hom(𝓕, 𝒢)` is an algebraic space affine
and of finite presentation over `B`.

Replace `X` by a quasi-compact open neighbourhood `U` of the support of `𝒢`
(`isAffineFinitePresentationAlgebraicSpaceOverBase_of_restrictSource`); then `U` is Noetherian and
`U ⟶ B` is quasi-compact and quasi-separated. Choose a perfect approximation `P ⟶ 𝓕[0]` with
`m = -1` (Stacks 08HP); `K = Rf_*R𝓗om(P, 𝒢[0])` is perfect (Stacks 0DKK), and the comparison
through Stacks 08JQ identifies `Hom(𝓕, 𝒢)` with the functor of Stacks 08JX, part (2), at `K`
(`isAffineFinitePresentationAlgebraicSpaceOverBase_of_approximation`).

## Main results

Declarations are in the namespace `AlgebraicGeometry.Space.HomSituation`.

* `isAffineFinitePresentationAlgebraicSpaceOverBase_of_isNoetherian`: over a Noetherian base,
  `Hom(𝓕, 𝒢)` is affine and of finite presentation over `B`.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.HomSituation

open CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If the source `X` is Noetherian and quasi-compact over the base, the remaining hypotheses of
Stacks 08JY give that `Hom(𝓕, 𝒢)` is affine and of finite presentation over the base. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_isNoetherian_source
    (v : HomSituation B S hS) (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop v.base.1) (hXN : IsNoetherian B S hS hTop v.X.1)
    (hf : IsLocallyOfFiniteType B S hS v.f.hom) (hfqc : IsQuasiCompact B S hS v.f.hom)
    (hfqs : IsQuasiSeparated B S hS v.f.hom) (hF : SheafOfModules.IsFiniteTypeOnSite v.F)
    (hG : SheafOfModules.IsFiniteTypeOnSite v.G) (hflat : IsFlatOver B S hS v.X.2 v.f.hom v.G)
    (hproper : HasProperSupportOver v.f v.G) :
    v.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS) := by
  have := v.quasicoherent_F
  obtain ⟨E, hE, α, hiso, hepi, -, hpull⟩ :=
    exists_perfect_approximation_degreeZero_of_isNoetherian hTop v.X hXN v.F hF
  obtain ⟨C, hC, ⟨e⟩⟩ := v.isPseudoCoherent_derivedModulePushforward_smallEtaleDerivedSheafHom
    hTop hB hf hfqs hG hflat hproper E hE
  refine v.isAffineFinitePresentationAlgebraicSpaceOverBase_of_approximation α hiso hepi hE
    (fun h => (hpull h).1) hfqc hfqs hflat ⟨C, hC, ⟨e ≪≫ Iso.refl _⟩⟩

/-- In Situation 08JT assume that the base `B` is a Noetherian algebraic space, that `f : X ⟶ B` is
locally of finite type and quasi-separated, that `𝓕` is an `𝒪_X`-module of finite type, and that
`𝒢` is an `𝒪_X`-module of finite type, flat over `B`, with support proper over `B`. Then the
functor `Hom(𝓕, 𝒢)` is an algebraic space affine and of finite presentation over `B`. -/
@[stacks 08JY]
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_isNoetherian
    (s : HomSituation B S hS) (hTop : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hTop s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) (hF : SheafOfModules.IsFiniteTypeOnSite s.F)
    (hG : SheafOfModules.IsFiniteTypeOnSite s.G) (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G)
    (hproper : HasProperSupportOver s.f s.G) :
    s.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B S hS) := by
  refine s.isAffineFinitePresentationAlgebraicSpaceOverBase_of_restrictSource _ hB.1 hG hproper
    fun U j hj hU hsupp => ?_
  exact (s.restrictSource j).isAffineFinitePresentationAlgebraicSpaceOverBase_of_isNoetherian_source
    hTop hB (s.isNoetherian_restrictSource hTop hB hf hfqs j hj hU)
    (s.isLocallyOfFiniteType_restrictSource j hj hf)
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hTop s.base.2 hB.2.1 hU _)
    (s.isQuasiSeparated_restrictSource j hj hfqs)
    (isFiniteTypeOnSite_modulePullback B S hS j s.F hF)
    (isFiniteTypeOnSite_modulePullback B S hS j s.G hG)
    (s.isFlatOver_restrictSource j (isEtale_of_isOpenImmersion B S hS hj) hflat)
    (s.hasProperSupportOver_restrictSource j hj hG hsupp hproper)

end AlgebraicGeometry.Space.HomSituation

end
