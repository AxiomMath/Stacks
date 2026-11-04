module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild

/-!
# The sheaf-level `θ` of Stacks Tag 01NK is functorial in the graded ring

For `φ : 𝒜 →+*ᵍ ℬ` and `ψ : GradedSections ℬ L`, the graded map `χ = ψ ∘ φ` of
`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap` carries the [Stacks, Tag 01NK]
datum of `ψ` back to the graded ring `A`.  The sibling file
`ProjChartGradedThetaRingFunctoriality.lean` proves that the **chart-level** comparison of `χ` is
that of `ψ` at the image fraction; this file lifts that to the **sheaf-level** `θ`, the morphism
`…ProjChartGradedThetaBuild.pushTheta` of sheaves of modules on `Proj 𝒜`.

Together with `…ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projMap`, which is the same
compatibility for the *morphism* `r_{L, ψ}`, this completes the graded-ring half of
[Stacks, Tag 01NK]'s functoriality for both of the tag's outputs.  Before these two files the
ladder existed for the morphism at every level and **stopped short of `θ`**: none of
`ProjChartGradedRingFunctoriality.lean`, `ProjChartGradedPullback.lean` or
`ProjChartGradedTransport.lean` mentions `θ` at all, and no declaration in the library took two
`GradedSections` arguments.

## Main results

* `…pushTheta_comap_app_basicOpen`: **`θ` for the pulled-back datum, on the sections over
  `D₊(f)`, is `ψ`'s chart comparison at the image fraction.**  This is the sheaf-level statement.
* `…pushTheta_app_basicOpen_eq_intChartSection`: the same reading of `θ` for `ψ` itself over
  `D₊(φ f)`, so that a consumer can compare the two.
* `…chartOpen_comap_eq`: the two chart opens in `T` coincide, `T_{χ(f)} = T_{ψ(φ f)}`.

## Implementation notes

**The pivot is `intChartSection`, not the other `pushTheta`, and that is deliberate.**  The two
chart opens `χ.chartOpen f` and `ψ.chartOpen (φ f)` are *equal* (`chartOpen_comap_eq`) but not
definitionally so: `…GradedSections.chartOpen` is the image in `T` of the preimage of `D₊(f)`
under `r`, and `χ` and `ψ` have different domains `U(χ) ⊆ U(ψ)` over different homogeneous
spectra.  Stating the comparison directly between the two `pushTheta`s would therefore have to
transport one side along that equality, which is exactly the `eqToHom` gymnastics this library
avoids.  Instead each `pushTheta` is read against `ψ`'s chart comparison over *its own* chart
open, and the two readings are related by the one open equality when a consumer needs it.

**Nothing is transported in the main result, because one term serves as both nonvanishing
hypotheses.**  `…ProjChartGradedRingFunctoriality.comap_toFun` holds by `rfl`, so the value
`χ(f)` *is* the value `ψ(φ f)`, and the single proof `(χ.chartOpen_eq hf he).le` has both the type
`χ.chartOpen f ≤ T_{χ(f)}` that `χ`'s chart comparison wants and the type
`χ.chartOpen f ≤ T_{ψ(φ f)}` that `ψ`'s wants.  So `intChartSection_comap` applies with that one
term on both sides and the equation stays inside `Γ(L^{⊗ n}, χ.chartOpen f)`.

**Why `D₊(f)` suffices and no gluing argument is needed here.**
`…ProjChartGradedThetaBuild.pushTheta_app_basicOpen` already computes `θ`'s action on the sections
over a standard open of a homogeneous element of positive degree by the chart comparison, and
those standard opens are a basis
(`…ProjShared.exists_basicOpen_homogeneous_le`).  So the content of the sheaf-level statement is
precisely the chart-level one, and the proof is that computation, the cancellation
`Iso.inv_hom_id_apply`, and `intChartSection_comap` — no re-run of the cover argument that built
`pushTheta`.

**The statements are at representatives.**  As in the sibling file, no map
`(A_f)_n ⟶ (B_{φ f})_n` induced by `φ` exists in this repository, so the two elements compared are
passed in with representatives `x / f ^ j` and `φ x / (φ f) ^ j`; `…intChartSection_mk` makes any
choice of representative compute the same section.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal Graded
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistingSheaf)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild
open Stacks.AlgebraicGeometry.ProjChartGradedThetaRingFunctoriality

universe u

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaSheafRingFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L) {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e)

/-- The chart target isomorphism sends `θ` on `D₊(g)` to the chart comparison of the section. -/
private theorem chartTargetIso_hom_pushTheta_app_basicOpen {C ρ : Type u} [CommRing C]
    [SetLike ρ C] [AddSubgroupClass ρ C] (𝒞 : ℕ → ρ) [GradedRing 𝒞] (χ : GradedSections 𝒞 L)
    {g : C} (hg : g ∈ 𝒞 e) (n : ℤ)
    (s : Γ(twistM 𝒞 n, AlgebraicGeometry.Proj.basicOpen 𝒞 g)) :
    (χ.chartTargetIso n g).hom ((pushTheta 𝒞 χ n).app (AlgebraicGeometry.Proj.basicOpen 𝒞 g) s)
      = intChartSection χ hg (χ.chartOpen_eq hg he).le he n
          (sectionsTwistEquivGradedPiece 𝒞 hg he n s) :=
  (congrArg (χ.chartTargetIso n g).hom
    (pushTheta_app_basicOpen 𝒞 χ n ⟨⟨e, ⟨g, hg⟩⟩, he⟩ s)).trans
    (CategoryTheory.Iso.inv_hom_id_apply _ _)

/-- **The sheaf-level `θ` of [Stacks, Tag 01NK] for the pulled-back datum `χ = ψ ∘ φ`, read on the
sections over `D₊(f)`, is `ψ`'s chart comparison at the image fraction.**

For `s` a section of the `n`-th twist over `D₊(f)` whose fraction is `x / f ^ j`, and `z` the
element of the degree-`n` part of `B_{φ f}` with fraction `φ x / (φ f) ^ j`, the value of
`pushTheta 𝒜 (comap φ ψ) n` at `s` — read through the identification of the sections of the direct
image with the sections of `L ^⊗ n` over the chart open — is `ψ`'s integer-degree chart comparison
at `z`.

This is the rung the functoriality ladder of [Stacks, Tag 01NK] was missing: the morphism
`r_{L, ψ}` had `…ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projMap`, and `θ` had
nothing. -/
public theorem pushTheta_comap_app_basicOpen (n : ℤ)
    (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f))
    (z : gradedPiece ℬ (integerGrading (S := B) ℬ) (φ f) n)
    (j d : ℕ) (hd : ((j * e : ℕ) : ℤ) + n = (d : ℕ)) (x : A) (hx : x ∈ 𝒜 d)
    (hy : (sectionsTwistEquivGradedPiece 𝒜 hf he n s : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hz : (z : LocalizedModule.Away (φ f) B)
      = LocalizedModule.mk (φ x) (⟨(φ f) ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers (φ f))) :
    ((comap φ ψ).chartTargetIso n f).hom
        ((pushTheta 𝒜 (comap φ ψ) n).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) s)
      = intChartSection ψ (map_mem φ hf)
          (((comap φ ψ).chartOpen_eq hf he).le) he n z := by
  refine (chartTargetIso_hom_pushTheta_app_basicOpen he 𝒜 (comap φ ψ) hf n s).trans ?_
  exact intChartSection_comap φ ψ hf (((comap φ ψ).chartOpen_eq hf he).le)
    (((comap φ ψ).chartOpen_eq hf he).le) he n _ z j d hd x hx hy hz

include hf he in
/-- **The chart opens of `χ = ψ ∘ φ` at `f` and of `ψ` at `φ f` are the same open of `T`.**  Both
are the nonvanishing locus of one and the same section `ψ(φ f)` of `L ^⊗ e`, by clause (1) of the
tag (`…GradedSections.chartOpen_eq`) on each side and `comap_toFun`.  They are **not**
definitionally equal: each is the image of a preimage under a different morphism, out of a
different domain over a different homogeneous spectrum. -/
public theorem chartOpen_comap_eq : (comap φ ψ).chartOpen f = ψ.chartOpen (φ f) :=
  ((comap φ ψ).chartOpen_eq hf he).trans (ψ.chartOpen_eq (map_mem φ hf) he).symm

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **`θ` for `ψ` itself over `D₊(φ f)`, read against the same chart comparison.**  The companion
of `pushTheta_comap_app_basicOpen` on the other side, so that the two `pushTheta`s can be compared
through `ψ`'s chart comparison as the common pivot — over `ψ.chartOpen (φ f)` here and over
`χ.chartOpen f` there, the two being identified by `chartOpen_comap_eq`.

The content is only `…pushTheta_app_basicOpen` and the independence of the chart comparison from
the representative chosen (`…intChartSection_mk`). -/
public theorem pushTheta_app_basicOpen_eq_intChartSection (n : ℤ)
    (t : Γ(twistM ℬ n, AlgebraicGeometry.Proj.basicOpen ℬ (φ f)))
    (z : gradedPiece ℬ (integerGrading (S := B) ℬ) (φ f) n)
    (j d : ℕ) (hd : ((j * e : ℕ) : ℤ) + n = (d : ℕ)) (x : B) (hx : x ∈ ℬ d)
    (ht : (sectionsTwistEquivGradedPiece ℬ (map_mem φ hf) he n t : LocalizedModule.Away (φ f) B)
      = LocalizedModule.mk x (⟨(φ f) ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers (φ f)))
    (hz : (z : LocalizedModule.Away (φ f) B)
      = LocalizedModule.mk x (⟨(φ f) ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers (φ f))) :
    (ψ.chartTargetIso n (φ f)).hom
        ((pushTheta ℬ ψ n).app (AlgebraicGeometry.Proj.basicOpen ℬ (φ f)) t)
      = intChartSection ψ (map_mem φ hf)
          ((ψ.chartOpen_eq (map_mem φ hf) he).le) he n z := by
  refine (chartTargetIso_hom_pushTheta_app_basicOpen he ℬ ψ (map_mem φ hf) n t).trans ?_
  refine Eq.trans (Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_mk ψ
    (map_mem φ hf) ((ψ.chartOpen_eq (map_mem φ hf) he).le) he n _ j d hd x hx ht) ?_
  exact (Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_mk ψ
    (map_mem φ hf) ((ψ.chartOpen_eq (map_mem φ hf) he).le) he n z j d hd x hx hz).symm

end Stacks.AlgebraicGeometry.ProjChartGradedThetaSheafRingFunctoriality

end
