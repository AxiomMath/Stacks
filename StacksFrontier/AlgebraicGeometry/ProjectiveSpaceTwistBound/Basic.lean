module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSerreDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.ChowNoetherianBase.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Projective
public import StacksFrontier.AlgebraicGeometry.DivisorCluster.ProjectiveSpaceNoetherian
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The uniform high-degree bound and the coherence of the twists on `ℙⁿ_R`

[Stacks, Tag 01YS] assertion (4) — eventual vanishing of `Hⁱ(ℙⁿ_R, ℱ(d))` in each positive degree
`i`, for `ℱ` coherent over a Noetherian ring `R` — is reduced by
`Stacks.AlgebraicGeometry.ProjectiveSerreDevissage.isZero_cohomology_high_twist_of_presentation`
to three hypotheses: a uniform high-degree bound, a dévissage presentation, and Serre vanishing
for the twisting sheaves themselves. On `ℙⁿ_R` the first holds outright and the second follows
from Serre's theorem alone.

## Main results

All names below live in the namespace `Stacks.AlgebraicGeometry.ProjectiveSpaceTwistBound`.

* `quasiCompact_over`, `quasiSeparated_over`: the structure morphism `ℙⁿ_R ⟶ Spec R` is
  quasi-compact and quasi-separated, with no hypothesis on `R`.
* `isQuasicoherent_integralTwistingSheaf`, `isQuasicoherent_projectiveTwistingSheaf`,
  `isQuasicoherent_projectiveTwist`: `𝒪_{ℙⁿ_R}(d)` and every twist of a quasi-coherent module are
  quasi-coherent.
* `exists_isZero_rightDerivedPlus_projectiveTwist`: one degree above which every higher direct
  image along `ℙⁿ_R ⟶ Spec R` of every twist of every quasi-coherent module vanishes.
* `exists_isZero_hgroup_projectiveTwist`: the same bound for `Hᵖ(ℙⁿ_R, ℱ(d))`.
* `hasUniformProjectiveTwistBound`: the uniform high-degree bound on `ℙⁿ_R`, with no hypothesis
  on `R`.
* `isCoherent_projectiveTwistingSheaf`: `𝒪_{ℙⁿ_R}(k)` is coherent for a Noetherian `R`.
* `hasCoherentProjectiveTwistPresentation_of_quotients`: the dévissage presentation from Serre's
  theorem alone.
* `isZero_cohomology_high_twist_of_serre`: [Stacks, Tag 01YS] assertion (4) from Serre's theorem
  and Serre vanishing for the twisting sheaves.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceTwistBound

variable {R : Type u} [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

/-! ### The structure morphism of `ℙⁿ_R` -/

/-- **`ℙⁿ_R ⟶ Spec R` is quasi-compact**, with no hypothesis on `R` or `n`. -/
theorem quasiCompact_over :
    QuasiCompact (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)) := by
  have := AlgebraicGeometry.isProper_projectiveSpaceOver n (Spec (CommRingCat.of R))
  infer_instance

/-- **`ℙⁿ_R ⟶ Spec R` is quasi-separated**, with no hypothesis on `R` or `n`. -/
theorem quasiSeparated_over :
    QuasiSeparated (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)) := by
  have := AlgebraicGeometry.isProper_projectiveSpaceOver n (Spec (CommRingCat.of R))
  infer_instance

/-! ### Quasi-coherence of the twists -/

/-- **The `d`-th twisting sheaf of the integral model is quasi-coherent**, at the
`AlgebraicGeometry.projectiveSpaceAtUniverse` spelling of its ring sheaf. -/
theorem isQuasicoherent_integralTwistingSheaf (d : ℤ) :
    SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceAtUniverse.{u} n).ringCatSheaf)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d) :=
  Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d

/-- **`𝒪_{ℙⁿ_R}(d)` is quasi-coherent.** -/
theorem isQuasicoherent_projectiveTwistingSheaf (d : ℤ) :
    SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf)
      (projectiveTwistingSheaf (R := R) n d) :=
  have := isQuasicoherent_integralTwistingSheaf.{u} n d
  AffineBaseChange.isQuasicoherent_pullback
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of R))) _

/-- **The `d`-th twist of a quasi-coherent module on `ℙⁿ_R` is quasi-coherent.** -/
theorem isQuasicoherent_projectiveTwist
    (F : (projectiveSpaceOverRing n (CommRingCat.of R)).Modules)
    (hF : SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf) F) (d : ℤ) :
    SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf)
      (projectiveTwist n F d) :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent.{u}
    (projectiveSpaceOverRing n (CommRingCat.of R)).toRingedSpace F
    (projectiveTwistingSheaf n d) hF (isQuasicoherent_projectiveTwistingSheaf n d)

/-! ### The uniform bound -/

/-- **Tag 01XJ's uniform vanishing at `ℙⁿ_R`, applied to every twist at once.** There is a single
degree above which the higher direct image along `ℙⁿ_R ⟶ Spec R` of `ℱ(d)` vanishes, for every
quasi-coherent `ℱ` and every `d`. -/
theorem exists_isZero_rightDerivedPlus_projectiveTwist :
    ∃ m : ℤ, ∀ p : ℤ, m ≤ p →
      ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf,
        SheafOfModules.IsQuasicoherent
          (R := (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf) F → ∀ d : ℤ,
          IsZero (((Scheme.Modules.pushforward
            (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)
              )).rightDerivedPlus p).obj (projectiveTwist n F d)) := by
  have := AlgebraicGeometry.isProper_projectiveSpaceOver n (Spec (CommRingCat.of R))
  obtain ⟨m, hm⟩ :=
    Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward_of_isAffine
      (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R))
  exact ⟨m, fun p hp F hF d ↦ hm p hp (projectiveTwist n F d)
    (isQuasicoherent_projectiveTwist n F hF d)⟩

/-- **The absolute form of the bound.** There is a degree `e` such that
`Hᵖ(ℙⁿ_R, ℱ(d)) = 0` for every `p > e`, every quasi-coherent `ℱ` and every twist `d`. -/
theorem exists_isZero_hgroup_projectiveTwist :
    ∃ e : ℕ, ∀ p : ℕ, e < p →
      ∀ F : SheafOfModules.{u} (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf,
        SheafOfModules.IsQuasicoherent
          (R := (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf) F → ∀ d : ℤ,
          IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ p
            (projectiveTwist n F d)) := by
  have := AlgebraicGeometry.isProper_projectiveSpaceOver n (Spec (CommRingCat.of R))
  obtain ⟨m, hm⟩ := exists_isZero_rightDerivedPlus_projectiveTwist.{u} (R := R) n
  refine ⟨m.toNat, fun p hp F hF d ↦ ?_⟩
  exact @LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus _ _
    (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)) _ _ _
    m.toNat (projectiveTwist n F d) (isQuasicoherent_projectiveTwist n F hF d)
    (fun q hq ↦ hm (q : ℤ) (le_trans (Int.self_le_toNat m) (by exact_mod_cast hq)) F hF d)
    p (by omega) hp.le

/-- **The uniform high-degree bound `ProjectiveSerreDevissage.HasUniformProjectiveTwistBound`
holds on `ℙⁿ_R`**, with no hypothesis on `R`. -/
theorem hasUniformProjectiveTwistBound :
    ProjectiveSerreDevissage.HasUniformProjectiveTwistBound (R := R) n ⊤ := by
  obtain ⟨e, he⟩ := exists_isZero_hgroup_projectiveTwist.{u} (R := R) n
  refine ⟨e, fun p hp F hF d ↦ he p hp F ?_ d⟩
  have := hF
  exact _root_.isQuasicoherent_of_isCoherent F

/-! ### Coherence of the twisting sheaves -/

section Noetherian

variable [IsNoetherianRing R]

/-- `ℙⁿ_R` is locally Noetherian for a Noetherian ring `R`. -/
theorem isLocallyNoetherian_projectiveSpaceOverRing :
    IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of R)) :=
  projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of R))

/-- **`𝒪_{ℙⁿ_R}(k)` is coherent** for a Noetherian ring `R`, for every `k : ℤ`. -/
@[sga "6 I 3.6" "special case"]
theorem isCoherent_projectiveTwistingSheaf (k : ℤ) :
    _root_.SheafOfModules.IsCoherent (projectiveTwistingSheaf (R := R) n k) :=
  have := isLocallyNoetherian_projectiveSpaceOverRing.{u} (R := R) n
  @CoherenceCriteria.isCoherent_of_isInvertible _ this _
    (TwistFlatness.isInvertible_projectiveTwistingSheaf n k)

/-- **The dévissage presentation from Serre's theorem alone**: on `ℙⁿ_R` over a Noetherian ring,
`ProjectiveSerreDevissage.HasProjectiveTwistQuotients` gives
`ProjectiveSerreDevissage.HasCoherentProjectiveTwistPresentation`. -/
theorem hasCoherentProjectiveTwistPresentation_of_quotients
    (hquot : ProjectiveSerreDevissage.HasProjectiveTwistQuotients (R := R) n) :
    ProjectiveSerreDevissage.HasCoherentProjectiveTwistPresentation (R := R) n :=
  ProjectiveSerreDevissage.hasCoherentProjectiveTwistPresentation_of_hasProjectiveTwistQuotients
    n hquot (isCoherent_projectiveTwistingSheaf n)

/-! ### The reduction -/

/-- **[Stacks, Tag 01YS] assertion (4) from Serre's theorem and Serre vanishing for the twisting
sheaves.** For `R` Noetherian, `ℱ` coherent on `ℙⁿ_R` and `i > 0`, `Hⁱ(ℙⁿ_R, ℱ(d)) = 0` for
`d` large, given

* `hquot`, Serre's theorem on `ℙⁿ_R`, which is assertion (1) of the same tag;
* `hvan`, the vanishing of the positive-degree cohomology of `𝒪(k)(d)` for `d` large. -/
theorem isZero_cohomology_high_twist_of_serre
    (hquot : ProjectiveSerreDevissage.HasProjectiveTwistQuotients (R := R) n)
    (hvan : ProjectiveSerreDevissage.HasEventuallyAcyclicProjectiveTwists (R := R) n ⊤)
    (F : (projectiveSpaceOverRing n (CommRingCat.of R)).Modules) [hF : F.IsCoherent]
    (i : ℕ) (hi : 0 < i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i
        (projectiveTwist n F d)) :=
  ProjectiveSerreDevissage.isZero_cohomology_high_twist_of_presentation n
    (hasUniformProjectiveTwistBound n)
    (hasCoherentProjectiveTwistPresentation_of_quotients n hquot) hvan F i hi

example {S : Type u} [CommRing S] [IsNoetherianRing S] (m : ℕ)
    (hquot : ProjectiveSerreDevissage.HasProjectiveTwistQuotients (R := S) m)
    (hvan : ProjectiveSerreDevissage.HasEventuallyAcyclicProjectiveTwists (R := S) m ⊤)
    (G : (projectiveSpaceOverRing m (CommRingCat.of S)).Modules) [G.IsCoherent]
    (j : ℕ) (hj : 0 < j) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projectiveSpaceOverRing m (CommRingCat.of S)).ringCatSheaf ⊤ j
        (projectiveTwist m G d)) :=
  isZero_cohomology_high_twist_of_serre m hquot hvan G j hj

end Noetherian

end Stacks.AlgebraicGeometry.ProjectiveSpaceTwistBound

end
