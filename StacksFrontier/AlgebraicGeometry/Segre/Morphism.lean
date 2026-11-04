module

public import StacksFrontier.AlgebraicGeometry.ProductFamilyTwist.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Preimage
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Segre.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Segre morphism `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm+n+m}_ℤ`

`StacksFrontier/AlgebraicGeometry/Segre/Basic.lean` reduces [Stacks, Tag 01WD] — and with it
Chow's lemma over a Noetherian base — to `AlgebraicGeometry.HasSegreMonoZ`: for all `n` and `m`
there are an `N` and a **monomorphism** `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙᴺ_ℤ`. This file **constructs the
morphism**, at the dimension `N = nm + n + m` the source produces, so that what remains of Tag
01WD is the single statement `CategoryTheory.Mono (AlgebraicGeometry.Segre.segreMorphism n m)`.

The construction is the source's own. The invertible module is
`L = pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`; the `(n+1)(m+1)` global sections are the `XᵢYⱼ`, i.e. the tensors
of the pulled-back homogeneous coordinates; their nonvanishing loci are the
`pr₁⁻¹D₊(Xᵢ) ∩ pr₂⁻¹D₊(Yⱼ)`, which cover; and the morphism is the one those data define by
[Stacks, Tag 01NE], `Stacks.ProjectiveSpaceSections.morphismAtUniverse`. Nothing here is new
mathematics: every step is an application of existing API, and the one identification not already
available — that the canonical section of `𝒪(1)` attached to a homogeneous coordinate does not
vanish on that coordinate's standard open — is
`Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection`.

## Main definitions

* `AlgebraicGeometry.Segre.segreProduct`: the fibre product `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ`, with
  `AlgebraicGeometry.Segre.segreFst` and `AlgebraicGeometry.Segre.segreSnd` its projections.
* `AlgebraicGeometry.Segre.coordinateSection`: the global section of `𝒪(1)` on `ℙⁿ_ℤ` given by the
  `i`-th homogeneous coordinate.
* `AlgebraicGeometry.Segre.segreModule`: `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`, with its invertibility.
* `AlgebraicGeometry.Segre.segreSection`: the section `XᵢYⱼ` of that module.
* `AlgebraicGeometry.Segre.segreMorphism`: **the Segre morphism.**

## Main results

* `AlgebraicGeometry.Segre.iSup_nonvanishingOpen_coordinateSection_eq_top`: the homogeneous
  coordinates generate `𝒪(1)` on `ℙⁿ_ℤ` in the sense that their nonvanishing loci cover.
* `AlgebraicGeometry.Segre.nonvanishingOpen_segreSection`: `(ℙⁿ×ℙᵐ)_{XᵢYⱼ} = pr₁⁻¹(ℙⁿ)_{Xᵢ} ∩
  pr₂⁻¹(ℙᵐ)_{Yⱼ}`.
* `AlgebraicGeometry.Segre.segreMorphism_preimage_standardOpen`: **the Segre morphism pulls the
  standard open `D₊(Z_{ij})` back to `pr₁⁻¹D₊(Xᵢ) ∩ pr₂⁻¹D₊(Yⱼ)`**, which is the first step of
  the source's proof that it is a closed immersion.
* `AlgebraicGeometry.Segre.hasSegreMonoZSharp_of_mono` and
  `AlgebraicGeometry.Segre.hasSegreMonoZ_of_mono`: **the residue of Tag 01WD is monicity of
  `segreMorphism`.**

## What is still missing for Tag 01WD

Exactly `Mono (segreMorphism n m)`, and nothing else: by
`AlgebraicGeometry.hasSegreEmbeddingZSharp_of_hasSegreMonoZSharp` and
`AlgebraicGeometry.hasSegreEmbeddingSharp_of_hasSegreEmbeddingZSharp` that upgrades to the tag's
own statement over every base, and by
`AlgebraicGeometry.hasDenseChowModification_of_hasSegreMonoZ` it makes Chow's lemma over a
Noetherian base unconditional. No `@[stacks 01WD]` attribute is attached anywhere in this file:
everything proved here is a construction plus a reduction, and 01WD asserts a closed immersion
outright.

The route to monicity that `segreMorphism_preimage_standardOpen` opens is the source's: `Mono` is
Zariski-local on the target — the opens `(e⁻¹V) ×_V (e⁻¹V)` for `V` in a cover of the target cover
the fibre product `W ×_P W`, and the diagonal restricts to the diagonal of each `e|` — and on the
chart `pr₁⁻¹D₊(Xᵢ) ∩ pr₂⁻¹D₊(Yⱼ)`, which is affine, the morphism is dual to the ring map sending
`Z_{ab}/Z_{ij}` to `(X_a/Xᵢ)(Y_b/Yⱼ)`, which is surjective because `Z_{aj}/Z_{ij} ↦ X_a/Xᵢ` and
`Z_{ib}/Z_{ij} ↦ Y_b/Yⱼ`. What that needs and this repository does not have is the ratio
computation: `Stacks.ProjectiveSpaceSections.chartRatio` of this `L` and these sections, i.e. a
formula for `Stacks.SheafOfModules.divBySection` of a tensor of pulled-back sections as the
product of the two ratios. No `divBySection` lemma about tensor products exists in either tree.

## Implementation notes

The index set of the target's homogeneous coordinates is `Fin (nm+n+m+1)`, while the sections are
naturally indexed by `Fin (n+1) × Fin (m+1)`; `AlgebraicGeometry.Segre.segreIndexEquiv` is the
bijection, `Mathlib`'s `finProdFinEquiv` after `finCongr (by ring)`. Reindexing the covering
hypothesis is `Equiv.iSup_comp`.

`𝒪(1)` on the integral model is `AlgebraicGeometry.projectiveSpaceAtUniverseTwistingSheaf n 1`,
the library's abbreviation; no second notion is introduced. Its invertibility comes from
`Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`, whose hypothesis — the
degree-one part generates — is `Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top`
enlarged from the coordinates to the whole degree-one submodule by monotonicity of
`Algebra.adjoin`.

Two walls of the `AlgebraicGeometry.Scheme.Modules`-is-a-`def` family were met, and both have the
cures already recorded for them:

* instance search does not see `projectiveSpaceAtUniverse n = Proj (homogeneousSubmodule …)`, so
  the invertibility instance registered at the former is not found at the latter. Cure: a `have`
  stating it at the spelling the consumer wants, whose body elaborates at default transparency.
* in `nonvanishingOpen_segreSection`, `rw` with
  `Stacks.SheafOfModules.preimage_nonvanishingOpen` fails with *"the target expression is not
  type-correct under the `implicit` transparency level"*, because forming the rewrite motive has
  to unify `AlgebraicGeometry.Scheme.Modules` with `SheafOfModules (structureSheafRing …)`. Cure:
  the same equations applied as terms through `congrArg`, which forms no motive.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory Opposite Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace AlgebraicGeometry.Segre

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The total-degree grading of the homogeneous coordinate ring of `ℙⁿ_ℤ`. -/
noncomputable abbrev coordinateGrading (n : ℕ) :
    ℕ → Submodule (ULift.{u} ℤ) (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)

/-- The degree-one part of the homogeneous coordinate ring generates it over the degree-zero
part: it contains the coordinates, which generate by
`Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top`. -/
theorem adjoin_coordinateGrading_one_eq_top (n : ℕ) :
    Algebra.adjoin ↥(coordinateGrading.{u} n 0)
      ((coordinateGrading.{u} n 1 :
          Submodule (ULift.{u} ℤ) (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) :
        Set (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) = ⊤ :=
  top_unique
    ((Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top (ULift.{u} ℤ) n).ge.trans
    (Algebra.adjoin_mono (by
      rintro x ⟨i, rfl⟩
      exact Stacks.ProjectiveChart.X_mem_degree_one _ i)))

/-- **`𝒪(1)` on the integral model of projective space is invertible.** -/
instance isInvertible_projectiveSpaceAtUniverseTwistingSheaf_one (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceAtUniverse.{u} n).presheaf
      (structureSheafRing
        (projectiveSpaceAtUniverse.{u} n).toRingedSpace).property
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf _
    (adjoin_coordinateGrading_one_eq_top.{u} n) 1

/-- The global section of `𝒪(1)` on `ℙⁿ_ℤ` given by the `i`-th homogeneous coordinate. -/
noncomputable def coordinateSection (n : ℕ) (i : Fin (n + 1)) :
    (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1).sections :=
  Stacks.ProjTwistSection.homogeneousSection (coordinateGrading.{u} n) (MvPolynomial.X i)
    (Stacks.ProjectiveChart.X_mem_degree_one _ i)

/-- **The nonvanishing loci of the homogeneous coordinates cover `ℙⁿ_ℤ`.** Each contains the
corresponding standard open by
`Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection`, and the standard opens
cover by [Stacks, Tag 01NG]. -/
theorem iSup_nonvanishingOpen_coordinateSection_eq_top (n : ℕ) :
    (⨆ i : Fin (n + 1), Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i)) = ⊤ := by
  refine top_unique ((Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n).ge.trans
    (iSup_mono fun i => ?_))
  have hinv : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule (coordinateGrading.{u} n) 1) :=
    isInvertible_projectiveSpaceAtUniverseTwistingSheaf_one.{u} n
  exact Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection
    (coordinateGrading.{u} n) _ (Stacks.ProjectiveChart.X_mem_degree_one _ i)

/-- A morphism to `ℙᴺ_ℤ` pulls the covering by the coordinate nonvanishing loci back to a cover. -/
private theorem iSup_preimage_nonvanishingOpen_coordinateSection_eq_top {X : Scheme.{u}}
    (N : ℕ) (f : X ⟶ projectiveSpaceAtUniverse.{u} N) :
    (⨆ i : Fin (N + 1), f ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} N).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} N 1) (coordinateSection.{u} N i)) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ (iSup_nonvanishingOpen_coordinateSection_eq_top.{u} N)

/-- The nonvanishing locus of a pulled-back coordinate section is the preimage of the
coordinate's nonvanishing locus. -/
private theorem nonvanishingLocus_pullback_coordinateSection {X : Scheme.{u}} (N : ℕ)
    (f : X ⟶ projectiveSpaceAtUniverse.{u} N) (i : Fin (N + 1)) :
    Stacks.SheafOfModules.nonvanishingLocus ((Scheme.Modules.pullback f).obj
        (projectiveSpaceAtUniverseTwistingSheaf.{u} N 1))
      (Stacks.SheafOfModules.modulePullbackSection f.toLRSHom
        (projectiveSpaceAtUniverseTwistingSheaf.{u} N 1) (coordinateSection.{u} N i)) =
    ((f ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveSpaceAtUniverse.{u} N).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} N 1) (coordinateSection.{u} N i) :
        X.Opens) : Set X) :=
  (congrArg (fun U : X.Opens => (U : Set X))
    (Stacks.SheafOfModules.preimage_nonvanishingOpen f
      (projectiveSpaceAtUniverseTwistingSheaf.{u} N 1) (coordinateSection.{u} N i))).symm

/-- The fibre product `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ`, with `Spec ℤ` realised as the terminal scheme. -/
noncomputable abbrev segreProduct (n m : ℕ) : Scheme.{u} :=
  pullback (terminal.from (ProjectiveSpaceZ.{u} n)) (terminal.from (ProjectiveSpaceZ.{u} m))

/-- The first projection of `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ`. -/
noncomputable def segreFst (n m : ℕ) :
    segreProduct.{u} n m ⟶ projectiveSpaceAtUniverse.{u} n :=
  pullback.fst _ _

/-- The second projection of `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ`. -/
noncomputable def segreSnd (n m : ℕ) :
    segreProduct.{u} n m ⟶ projectiveSpaceAtUniverse.{u} m :=
  pullback.snd _ _

/-- `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` on `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ`. -/
@[ega "II 4.3.1" "partial"]
noncomputable def segreModule (n m : ℕ) : (segreProduct.{u} n m).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((segreProduct.{u} n m).toRingedSpace)).presheaf,
        (((segreProduct.{u} n m).toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pullback (segreFst.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1)))).obj
      (((Scheme.Modules.pullback (segreSnd.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1))))

/-- **`pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` is invertible**: a pullback of an invertible module is invertible
by [Stacks, Tag 0B8L], and a tensor product of invertible modules is invertible by
[Stacks, Tag 01CT]. -/
instance isInvertible_segreModule (n m : ℕ) : Stacks.SheafOfModules.IsInvertible
    (segreProduct.{u} n m).presheaf
    (structureSheafRing (segreProduct.{u} n
      m).toRingedSpace).property
    (segreModule.{u} n m) :=
  @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ (segreProduct.{u} n m).presheaf
    (structureSheafRing (segreProduct.{u} n
      m).toRingedSpace).property _ _
    ((Scheme.Modules.pullback (segreFst.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1))
    ((Scheme.Modules.pullback (segreSnd.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1))
    (Stacks.Modules.isInvertible_pullback _ _) (Stacks.Modules.isInvertible_pullback _ _)

/-- The global section `XᵢYⱼ` of `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`. -/
noncomputable def segreSection (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (segreModule.{u} n m).sections :=
  Stacks.SheafOfModules.tensorSections _ _
    (Stacks.SheafOfModules.modulePullbackSection (segreFst.{u} n m).toLRSHom
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
    (Stacks.SheafOfModules.modulePullbackSection (segreSnd.{u} n m).toLRSHom
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j))

/-- **The nonvanishing locus of `XᵢYⱼ` is `pr₁⁻¹(ℙⁿ)_{Xᵢ} ∩ pr₂⁻¹(ℙᵐ)_{Yⱼ}`**: the nonvanishing
locus of a tensor of sections is the intersection of the two, and the nonvanishing locus of a
pulled-back section is the preimage of the nonvanishing locus, which is [Stacks, Tag 0H78]. -/
theorem nonvanishingOpen_segreSection (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (segreProduct.{u} n m).toRingedSpace)
        (segreModule.{u} n m) (segreSection.{u} n m i j)
      = (segreFst.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
        ⊓ (segreSnd.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j)) := by
  refine TopologicalSpace.Opens.ext ?_
  refine Eq.trans (Stacks.SheafOfModules.nonvanishingLocus_tensorSections
    ((Scheme.Modules.pullback (segreFst.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1))
    ((Scheme.Modules.pullback (segreSnd.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1))
    (Stacks.SheafOfModules.modulePullbackSection (segreFst.{u} n m).toLRSHom
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
    (Stacks.SheafOfModules.modulePullbackSection (segreSnd.{u} n m).toLRSHom
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j))) ?_
  exact congrArg₂ (· ∩ ·) (nonvanishingLocus_pullback_coordinateSection.{u} n _ i)
    (nonvanishingLocus_pullback_coordinateSection.{u} m _ j)

/-- **The nonvanishing loci of the `(n+1)(m+1)` sections `XᵢYⱼ` cover the product.** -/
theorem iSup_nonvanishingOpen_segreSection_eq_top (n m : ℕ) :
    (⨆ p : Fin (n + 1) × Fin (m + 1), Stacks.SheafOfModules.nonvanishingOpen
      (X := (segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
      (segreSection.{u} n m p.1 p.2)) = ⊤ := by
  have h1 := iSup_preimage_nonvanishingOpen_coordinateSection_eq_top.{u} n (segreFst.{u} n m)
  have h2 := iSup_preimage_nonvanishingOpen_coordinateSection_eq_top.{u} m (segreSnd.{u} n m)
  have key : (⨆ p : Fin (n + 1) × Fin (m + 1), Stacks.SheafOfModules.nonvanishingOpen
        (X := (segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
        (segreSection.{u} n m p.1 p.2))
      = (⨆ i : Fin (n + 1), segreFst.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
        ⊓ (⨆ j : Fin (m + 1), segreSnd.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j)) := by
    rw [iSup_inf_iSup]
    exact iSup_congr fun p => nonvanishingOpen_segreSection.{u} n m p.1 p.2
  rw [key, h1, h2, top_inf_eq]

/-- The sections `XᵢYⱼ`, indexed by the homogeneous coordinates of the target. -/
noncomputable def segreSections (n m : ℕ) (k : Fin (n * m + n + m + 1)) :
    (segreModule.{u} n m).sections :=
  segreSection.{u} n m (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).1
    (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).2

/-- The nonvanishing loci of the sections `segreSections n m k` cover the product
`segreProduct n m`. -/
theorem iSup_nonvanishingChart_segreSections_eq_top (n m : ℕ) :
    (⨆ k, Stacks.ProjectiveSpaceSections.nonvanishingChart (segreModule.{u} n m)
      (segreSections.{u} n m k)) = ⊤ := by
  rw [← iSup_nonvanishingOpen_segreSection_eq_top.{u} n m]
  exact Equiv.iSup_comp (g := fun p : Fin (n + 1) × Fin (m + 1) =>
      Stacks.SheafOfModules.nonvanishingOpen
        (X := (segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
        (segreSection.{u} n m p.1 p.2)) (Stacks.ProductFamilyTwist.segreIndexEquiv n m)

/-- **The Segre morphism** `ℙⁿ_ℤ ×_{Spec ℤ} ℙᵐ_ℤ ⟶ ℙ^{nm+n+m}_ℤ`: the morphism to projective
space defined by the invertible module `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` and its `(n+1)(m+1)` global
sections `XᵢYⱼ`, whose nonvanishing loci cover. -/
@[ega "II 4.3.1" "special case"]
noncomputable def segreMorphism (n m : ℕ) :
    segreProduct.{u} n m ⟶ ProjectiveSpaceZ.{u} (n * m + n + m) :=
  Stacks.ProjectiveSpaceSections.morphismAtUniverse (segreModule.{u} n m)
    (segreSections.{u} n m) (iSup_nonvanishingChart_segreSections_eq_top.{u} n m)

/-- **The Segre morphism pulls the standard open `D₊(Z_{ij})` back to
`pr₁⁻¹D₊(Xᵢ) ∩ pr₂⁻¹D₊(Yⱼ)`.** This is the first step of the source's proof that the Segre
morphism is a closed immersion: those `(n+1)(m+1)` opens cover the product, each is affine, and on
each the morphism is dual to a surjection of rings. -/
theorem segreMorphism_preimage_standardOpen (n m : ℕ) (k : Fin (n * m + n + m + 1)) :
    segreMorphism.{u} n m ⁻¹ᵁ
        Stacks.ProjectiveSpaceSections.standardOpen.{u} (n * m + n + m) k
      = (segreFst.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1)
            (coordinateSection.{u} n (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).1))
        ⊓ (segreSnd.{u} n m ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen
            (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1)
            (coordinateSection.{u} m (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).2)) :=
  (Stacks.ProjectiveSpaceSections.morphismAtUniverse_preimage_basicOpen (segreModule.{u} n m)
    (segreSections.{u} n m) (iSup_nonvanishingChart_segreSections_eq_top.{u} n m) k).trans
    (nonvanishingOpen_segreSection.{u} n m _ _)

/-- **The residue of [Stacks, Tag 01WD], in the sharp form.** If the Segre morphism is a
monomorphism for all `n` and `m`, then `AlgebraicGeometry.HasSegreMonoZSharp` holds — and hence,
by `AlgebraicGeometry.hasSegreEmbeddingZSharp_of_hasSegreMonoZSharp` and
`AlgebraicGeometry.hasSegreEmbeddingSharp_of_hasSegreEmbeddingZSharp`, Tag 01WD over every
base. -/
theorem hasSegreMonoZSharp_of_mono (h : ∀ n m : ℕ, Mono (segreMorphism.{u} n m)) :
    HasSegreMonoZSharp.{u} :=
  fun n m => ⟨segreMorphism.{u} n m, h n m⟩

/-- **The residue of Chow's lemma over a Noetherian base.** If the Segre morphism is a
monomorphism for all `n` and `m`, then `AlgebraicGeometry.HasSegreMonoZ` holds, and
`AlgebraicGeometry.hasDenseChowModification_of_hasSegreMonoZ` becomes unconditional. -/
theorem hasSegreMonoZ_of_mono (h : ∀ n m : ℕ, Mono (segreMorphism.{u} n m)) :
    HasSegreMonoZ.{u} :=
  (hasSegreMonoZSharp_of_mono.{u} h).hasSegreMonoZ

end AlgebraicGeometry.Segre

end
