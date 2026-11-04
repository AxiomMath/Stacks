module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
import StacksCore.Tactic.StacksAttribute

/-!
# The higher direct images of the twists on projective space vanish outside `0` and `n`

Let `S` be a scheme, let `n` be a natural number, let `d` be an integer and let
`f : ℙⁿ_S ⟶ S` be the structure morphism. Then

`Rᵠ f_* 𝒪(d) = 0` for every `q ≠ 0, n`.

This is the vanishing row of the display of [Stacks, Tag 01XW], in its full range: below `0`,
in the whole band `1 ≤ q ≤ n - 1`, and above `n`. No hypothesis is placed on `S`, on `n` or on
`d`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing` namespace, where
the fully-qualified form would not fit on a line.

## Main results

* `isZero_Hgroup_twistingSheaf_of_isZero`: `H^q(Proj R[T₀, …, Tₙ], 𝒪(d)) = 0` whenever the
  cohomology vanishes as a module over the coefficients, over an arbitrary commutative ring `R`.
* `isZero_Hgroup_twistOver_specOf_of_isZero` and `isZero_Hgroup_twistOver_of_isAffine_of_isZero`:
  the same on the base-change model of projective space, over `Spec R` and over an arbitrary
  affine base.
* `isZero_rightDerivedPlus_pushforward_twistOver_of_isAffine`: `Rᵠ f_* 𝒪(d) = 0` over an affine
  base, under the same hypothesis for the ring of global functions of the base.
* `isZero_rightDerivedPlus_pushforward_twistOver_of_isZero`: **the localisation of the vanishing
  to an arbitrary base**, with the absolute vanishing taken as a hypothesis quantified over the
  coefficient ring.
* `isZero_rightDerivedPlus_pushforward_twistOver_vanishing`: that localisation applied to the two
  non-vanishing cases `q = 0, d ≥ 0` and `q = n, d < 0` of [Stacks, Tag 01XT].
* `isZero_rightDerivedPlus_pushforward_twistOver_of_ne`: **`Rᵠ f_* 𝒪(d) = 0` for every integer
  `q` with `q ≠ 0` and `q ≠ n`**, over an arbitrary base.
* `isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg`: **`f_* 𝒪(d) = 0` for `d < 0` and
  `n ≥ 1`**, over an arbitrary base — the degree-zero row of the display at the negative twists,
  where the sheaf it identifies the direct image with is zero.

## Which clause of the tag this is

The display of [Stacks, Tag 01XW] has three rows: `f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d` in degree `0`,
the vanishing in the degrees `q ≠ 0, n`, and
`Rⁿ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)` in degree `n`. This module carries the
middle row, whole; the attribute sits on
`isZero_rightDerivedPlus_pushforward_twistOver_of_ne`, which is that row for every `q` outside
`{0, n}` and every integer `d`.

Of the degree-zero row this module also carries the negative twists, in
`isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg`: for `d < 0` and `n ≥ 1` the sheaf
`(𝒪_S[T₀, …, Tₙ])_d` is zero, so that row *is* a vanishing statement there.

The other two rows are carried by the sibling modules, each as an isomorphism of sheaves of
modules on `S`, in the namespace `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`:
the degree-zero row at every twist by `baseDegreeSheafIsoRightDerivedPushforwardTwistOver`, and
the degree-`n` row at every twist and over an arbitrary base by
`rightDerivedPlusTopIsoDualBaseDegreeSheaf`. The three rows together, in one statement and at
`n ≥ 1`, where the source's display is a consistent assertion, are
`rightDerivedPlusPushforwardTwistOverDisplay`.

## Implementation notes

The degrees outside the band `1 ≤ q ≤ n - 1` are
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.isZero_rightDerivedPlus_pushforward_twistOver`.

**The derived category.** `HasDerivedCategory.standard` is installed at priority `2000` so that
it is preferred to the globally declared locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms live one universe lower.
The statements below are then in the same model as the two degrees outside the band.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.ProjectiveSpace.Cohomology (twistCohomology isZero_twistCohomology)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (isZero_of_isZero_restrict_cover isZero_rightDerivedPlus_pushforward_of_isZero_cohomology)
open Stacks.Cohomology.AffineBase
  (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup)
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### The band `1 ≤ q ≤ n - 1` of the absolute computation -/

/-- **The two spellings of `H^q(ℙⁿ_R, 𝒪(d))` agree on vanishing**, on the homogeneous spectrum
of `R[T₀, …, Tₙ]` and over an arbitrary commutative ring `R`: if the cohomology vanishes as a
module over the coefficients then it vanishes as the `Hgroup` of the sheaf of rings the twisting
sheaf is a module over. -/
theorem isZero_Hgroup_twistingSheaf_of_isZero (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ)
    (h0 : IsZero (twistCohomology R n d q)) :
    IsZero (Hgroup (projRingSheaf (polyGrading R n)) ⊤ q
      (twistingSheaf (polyGrading R n) d)) := by
  have h1 : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerived q).obj
      (twistingSheaf (polyGrading R n) d)) := by
    have hs : Subsingleton (twistCohomology R n d q) := ModuleCat.subsingleton_of_isZero h0
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hs
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (projRingSheaf (polyGrading R n)) ⊤ q (twistingSheaf (polyGrading R n) d)).mp h1

/-- Vanishing of `Hᵍ` transfers along an isomorphism of schemes `φ : X ≅ Y` and an isomorphism of
a module `N` on `X` with the inverse image of a module `F` on `Y`. -/
private theorem isZero_Hgroup_iff_of_iso_pullback {X Y : Scheme.{u}} (φ : X ≅ Y) (F : Y.Modules)
    (N : X.Modules) (e : N ≅ (Scheme.Modules.pullback φ.hom).obj F) (q : ℕ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ q N) ↔ IsZero (Hgroup Y.ringCatSheaf ⊤ q F) :=
  ⟨fun h => (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff φ F q).1
      (h.of_iso ((Hfunctor X.ringCatSheaf ⊤ q).mapIso e).symm),
    fun h => ((Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff φ F q).2 h).of_iso
      ((Hfunctor X.ringCatSheaf ⊤ q).mapIso e)⟩

/-- **`H^q(ℙⁿ_{Spec R}, 𝒪(d)) = 0`** on the base-change model of projective space, over an
arbitrary commutative ring `R`, whenever the cohomology of the twist vanishes on the `Proj`
model. -/
theorem isZero_Hgroup_twistOver_specOf_of_isZero (S : Type u) [CommRing S] (n : ℕ) (d : ℤ)
    (q : ℕ) (h0 : IsZero (twistCohomology S n d q)) :
    IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of S)).ringCatSheaf ⊤ q
      (twistOver n (Spec (CommRingCat.of S)) d)) := by
  obtain ⟨e⟩ := nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv S n d
    (Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport S n d)
  exact (isZero_Hgroup_iff_of_iso_pullback (projModelIso S n).symm _ _ e q).2
    (isZero_Hgroup_twistingSheaf_of_isZero S n d q h0)

/-- **`H^q(ℙⁿ_W, 𝒪(d)) = 0` for `W` affine**, whenever the cohomology of the twist vanishes over
the coefficient ring `Γ(W, ⊤)`. -/
theorem isZero_Hgroup_twistOver_of_isAffine_of_isZero (n : ℕ) (W : Scheme.{u}) [IsAffine W]
    (d : ℤ) (q : ℕ) (h0 : IsZero (twistCohomology ↥(Γ(W, ⊤)) n d q)) :
    IsZero (Hgroup (projectiveSpaceOver n W).ringCatSheaf ⊤ q (twistOver n W d)) := by
  let eP : projectiveSpaceOver n (Spec (CommRingCat.of ↥(Γ(W, ⊤)))) ≅ projectiveSpaceOver n W :=
    asIso (projectiveSpaceOverMap n W.isoSpec.inv)
  exact (isZero_Hgroup_iff_of_iso_pullback eP _ _ (twistOverPullbackIso n W.isoSpec.inv d).symm
    q).1 (isZero_Hgroup_twistOver_specOf_of_isZero ↥(Γ(W, ⊤)) n d q h0)

/-! ### The band for the higher direct images -/

/-- **`Rᵠ f_* 𝒪(d) = 0` over an affine base**, whenever the cohomology of the twist vanishes over
the coefficient ring `Γ(W, ⊤)`. -/
theorem isZero_rightDerivedPlus_pushforward_twistOver_of_isAffine (n : ℕ) (W : Scheme.{u})
    [IsAffine W] (d : ℤ) (q : ℕ) (h0 : IsZero (twistCohomology ↥(Γ(W, ⊤)) n d q)) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n W ↘ W)).rightDerivedPlus
      (q : ℤ)).obj (twistOver n W d)) :=
  isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
    (projectiveSpaceOver n W ↘ W) (q : ℤ) (twistOver n W d)
    ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
      (projectiveSpaceOver n W) (twistOver n W d) q).2
      (isZero_Hgroup_twistOver_of_isAffine_of_isZero n W d q h0))

/-- **`Rᵠ f_* 𝒪(d) = 0` over an arbitrary base**, whenever the cohomology of the twist vanishes
over every commutative coefficient ring. -/
theorem isZero_rightDerivedPlus_pushforward_twistOver_of_isZero (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (q : ℕ) (h0 : ∀ (R : Type u) [CommRing R], IsZero (twistCohomology R n d q)) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus
      (q : ℤ)).obj (twistOver n S d)) := by
  classical
  have hcov : ∀ y : S, ∃ V : S.Opens, y ∈ V ∧ IsAffineOpen V := fun y => by
    obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ ((⊤ : S.Opens) : Set S) from trivial) (⊤ : S.Opens).isOpen
    exact ⟨V, hyV, hV⟩
  choose V hmem haff using hcov
  refine isZero_of_isZero_restrict_cover V
    (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hmem y⟩) _ fun y => ?_
  have : IsAffine (V y).toScheme := haff y
  have hA := isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) (V y)
  have hB := (isPullback_projectiveSpaceOverMap n (V y).ι).flip
  let α := hA.isoIsPullback _ _ hB
  have hfst : α.hom ≫ projectiveSpaceOverMap n (V y).ι
      = ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V y).ι :=
    IsPullback.isoIsPullback_hom_snd _ _ hA hB
  let eT : (Scheme.Modules.restrictFunctor
        ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V y).ι).obj (twistOver n S d) ≅
      (Scheme.Modules.pullback α.hom).obj (twistOver n (V y).toScheme d) :=
    (Scheme.Modules.restrictFunctorIsoPullback _).app (twistOver n S d) ≪≫
      (Scheme.Modules.pullbackCongr hfst.symm).app (twistOver n S d) ≪≫
      ((Scheme.Modules.pullbackComp α.hom
        (projectiveSpaceOverMap n (V y).ι)).app (twistOver n S d)).symm ≪≫
      (Scheme.Modules.pullback α.hom).mapIso (twistOverPullbackIso n (V y).ι d)
  have hcohV := (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
    ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V y).toScheme
    ((Scheme.Modules.restrictFunctor
      ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V y).ι).obj (twistOver n S d)) q).2
    ((isZero_Hgroup_iff_of_iso_pullback α _ _ eT q).2
      (isZero_Hgroup_twistOver_of_isAffine_of_isZero n (V y).toScheme d q
        (h0 ↥(Γ((V y).toScheme, ⊤)))))
  exact (isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
    ((projectiveSpaceOver n S ↘ S) ∣_ V y) (q : ℤ) _ hcohV).of_iso
    (rightDerivedPlusRestrictObjIso (projectiveSpaceOver n S ↘ S) (V y) q
      (twistOver n S d)).symm

/-- **`Rᵠ f_* 𝒪(d) = 0` over an arbitrary base**, outside the two non-vanishing cases of
[Stacks, Tag 01XT]. -/
@[sga "7 XI 1.1" "partial"]
theorem isZero_rightDerivedPlus_pushforward_twistOver_vanishing (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (q : ℕ) (hq : ¬ ((q = 0 ∧ 0 ≤ d) ∨ (q = n ∧ d < 0))) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus
      (q : ℤ)).obj (twistOver n S d)) :=
  isZero_rightDerivedPlus_pushforward_twistOver_of_isZero n S d q
    fun R _ => isZero_twistCohomology R n d q hq

/-- **The vanishing row of [Stacks, Tag 01XW].** For the structure morphism `f : ℙⁿ_S ⟶ S` over
an arbitrary scheme `S`, an arbitrary `n` and an arbitrary integer `d`, the higher direct image
`Rᵠ f_* 𝒪(d)` is zero in every degree `q` with `q ≠ 0` and `q ≠ n`. -/
@[stacks 01XW "the vanishing row, whole: R^q f_* 𝒪(d) = 0 for every q ≠ 0, n, every scheme S, \
every n and every integer d. The q = 0 row is \
ProjectiveSpaceHigherDirectImage.baseDegreeSheafIsoRightDerivedPushforwardTwistOver in \
...DegreeZeroRow; the q = n row is ...rightDerivedPlusTopIsoDualBaseDegreeSheaf in \
...TopDegreeRowGeneral, for every twist d over an arbitrary base. The whole display, its three \
rows in one statement at n >= 1, is \
...rightDerivedPlusPushforwardTwistOverDisplay in ...Display"]
theorem isZero_rightDerivedPlus_pushforward_twistOver_of_ne (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (q : ℤ) (hq0 : q ≠ 0) (hqn : q ≠ (n : ℤ)) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).obj
      (twistOver n S d)) := by
  rcases lt_trichotomy q 0 with h | h | h
  · exact isZero_rightDerivedPlus_pushforward_twistOver n S d q (Or.inl h)
  · exact absurd h hq0
  · rcases lt_or_gt_of_ne hqn with h' | h'
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
      exact isZero_rightDerivedPlus_pushforward_twistOver_vanishing n S d k
        (by rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega)
    · exact isZero_rightDerivedPlus_pushforward_twistOver n S d q (Or.inr h')

/-! ### The degree-zero row at a negative twist -/

/-- **`f_* 𝒪(d) = 0` for `d < 0` and `n ≥ 1`**, over an arbitrary scheme `S`: the degree-zero row
of [Stacks, Tag 01XW] at the negative twists, where the sheaf `(𝒪_S[T₀, …, Tₙ])_d` it identifies
`R⁰ f_* 𝒪(d)` with is the zero sheaf, a polynomial algebra having no homogeneous part in a
negative degree.

The hypothesis `n ≥ 1` cannot be dropped: on `ℙ⁰_S = S` the twist `𝒪(d)` is `𝒪_S` in every
degree. -/
@[ega "II 4.2.7" "special case", sga "6 VI 2.8" "partial"]
theorem isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg (n : ℕ) (hn : 0 < n)
    (S : Scheme.{u}) (d : ℤ) (hd : d < 0) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus 0).obj
      (twistOver n S d)) := by
  have h := isZero_rightDerivedPlus_pushforward_twistOver_vanishing n S d 0
    (by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega)
  rwa [Nat.cast_zero] at h

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing

end
