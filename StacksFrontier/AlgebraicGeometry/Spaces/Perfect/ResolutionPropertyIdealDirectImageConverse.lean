module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFinitePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyNoetherianApproximationStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyNoetherianIdealCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffineMain
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertySmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSubmoduleIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardUnitTensorMultiplication
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaFinitePresentation

/-!
# The Noetherian stage of the converse of Stacks 0GV1

In the situation of Stacks 0GUY — a quasi-compact and quasi-separated algebraic space `X`, an
affine surjective étale chart `φ : V → X` factored as an open immersion `j : V → Y` followed by a
finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y` with
`V(ℐ) = Y ∖ j(V)` — Stacks 0GV1 asserts that `X` has the resolution property if and only if
`π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module.  The source proves the converse by
reducing to a Noetherian stage `X_i` of an absolute Noetherian approximation, where it applies
Stacks 0GV0.  This file carries what that last step needs.

## Main definitions

* `ResolutionPropertyDescentSituation.idealDirectImageIsoModulePushforwardIdeal`: the two
  spellings of `π_*ℐ` in the development — `idealDirectImage`, the direct image along small-chart
  base change in which the implication of Stacks 0GV1 from the resolution property is stated,
  and `modulePushforwardIdeal`, the direct image of Stacks 03LU in which Stacks 0GV0 is stated —
  are isomorphic.

## Main results

* `ResolutionPropertyDescentSituation.exists_epi_idealDirectImage_iff`: `π_*ℐ` is a quotient of a
  finite locally free module in one spelling iff in the other.
* `hasResolutionProperty_of_exists_epi_idealDirectImage_of_isNoetherian`: Stacks 0GV0, the
  direction towards the resolution property, in the spelling of Stacks 0GV1.
* `hasResolutionProperty_of_epi_pushforwardSubmodule_of_isNoetherian`: for a Noetherian `X` and a
  situation of Stacks 0GUY over it, a surjection from a finite locally free module onto the
  direct image `π_*ℐ`, read as the submodule `pushforwardSubmodule` of `π_*𝒪_Y`, implies that `X`
  has the resolution property.
* `hasResolutionProperty_of_pushforwardSubmodule_eq_imageSubmodule_of_isNoetherian`: the same,
  from a map `ℰ ⟶ π_*𝒪_Y` from a finite locally free module whose image is `π_*ℐ`.
* `hasResolutionProperty_of_hasResolutionProperty_noetherianApproximation_stage`: if a stage of a
  Noetherian approximation of `X` has the resolution property, so does `X` (Stacks 0GUU along
  the projection).
* `hasResolutionProperty_of_exists_epi_idealDirectImage_of_forall_integers`: the converse of
  Stacks 0GV1 over every base follows from the converse over `Spec ℤ` (Stacks 03I5).
* `hasResolutionProperty_of_exists_epi_idealDirectImage_of_isFinitePresentation`: the converse of
  Stacks 0GV1 over `Spec ℤ` with `π` of finite presentation.
* `hasResolutionProperty_iff_exists_epi_idealDirectImage`: `X` has the resolution property iff
  `π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module (Stacks 0GV1).

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    {hqc : IsQuasiCompactSpace B S hS X.1}
    {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}

/-- Composing an epimorphism with an isomorphism gives an epimorphism. -/
private theorem epi_comp_hom_of_epi {C : Type*} [Category C] {X Y Z : C} {p : X ⟶ Y} (_ : Epi p)
    (e : Y ≅ Z) : Epi (p ≫ e.hom) :=
  inferInstance

namespace ResolutionPropertyDescentSituation

variable (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **The two spellings of `π_*ℐ` agree**: the direct image along small-chart base change,
`idealDirectImage`, and the direct image of Stacks 03LU, `modulePushforwardIdeal`, are identified
by `AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
def idealDirectImageIsoModulePushforwardIdeal :
    idealDirectImage B S hS hZ sit ≅ modulePushforwardIdeal B S hS hZ X hqc hqs sit :=
  ((modulePushforwardChartIso B S hS sit.πHom
      (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).app
    sit.I.toSheafOfModules).symm

/-- `π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module in the spelling
`idealDirectImage` if and only if it is in the spelling `modulePushforwardIdeal`. -/
theorem exists_epi_idealDirectImage_iff :
    (∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
        (p : E ⟶ idealDirectImage B S hS hZ sit), Epi p) ↔
      ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
        (p : E ⟶ modulePushforwardIdeal B S hS hZ X hqc hqs sit), Epi p := by
  constructor
  · rintro ⟨E, hE, p, hp⟩
    exact ⟨E, hE, _,
      epi_comp_hom_of_epi hp (idealDirectImageIsoModulePushforwardIdeal B S hS hZ sit)⟩
  · rintro ⟨E, hE, p, hp⟩
    exact ⟨E, hE, _,
      epi_comp_hom_of_epi hp (idealDirectImageIsoModulePushforwardIdeal B S hS hZ sit).symm⟩

end ResolutionPropertyDescentSituation

/-- **Stacks 0GV0, the direction towards the resolution property, in the spelling of Stacks
0GV1.**  In the situation of Stacks 0GUY with `X` Noetherian, if the direct image `π_*ℐ` (as
`idealDirectImage`) is the quotient of a finite locally free `𝒪_X`-module, then `X` has the
resolution property. -/
theorem hasResolutionProperty_of_exists_epi_idealDirectImage_of_isNoetherian
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)
    (hX : IsNoetherian B S hS hZ X.1)
    (h : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ sit.idealDirectImage B S hS hZ), Epi p) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 :=
  hasResolutionProperty_of_exists_epi_modulePushforwardIdeal B S hS hZ X hqc hqs sit hX
    ((sit.exists_epi_idealDirectImage_iff B S hS hZ).1 h)

/-- **The Noetherian stage of the proof of Stacks 0GV1.**  Let `X` be a Noetherian algebraic
space, `V` an affine scheme with a surjective étale `φ : V ⟶ X` factored as an open immersion
`j : V ⟶ Y` followed by a finite `π : Y ⟶ X`, and `ℐ ⊆ 𝒪_Y` a finite type quasi-coherent sheaf
of ideals with `|V(ℐ)| = |Y| ∖ |j(V)|`.  If some finite locally free `𝒪_X`-module surjects onto
the direct image `π_*ℐ ⊆ π_*𝒪_Y`, then `X` has the resolution property.

This assembles the situation of Stacks 0GUY from its data and applies Stacks 0GV0; the direct
image is the submodule `AlgebraicGeometry.Space.pushforwardSubmodule`, which is the form in which
`AlgebraicGeometry.Space.exists_ideal_pushforwardSubmodule_eq` produces it. -/
theorem hasResolutionProperty_of_epi_pushforwardSubmodule_of_isNoetherian
    (hX : IsNoetherian B S hS hZ X.1)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ X.1) (hφs : IsSurjective B S hS φ) (hφe : IsEtale B S hS φ)
    (Y : AlgebraicSpaces B S hS) (j : yoneda.obj V ⟶ Y.1) (π : Y ⟶ X)
    (hj : IsOpenImmersion B S hS j) (hπ : IsFinite B S hS π.hom) (hcomp : j ≫ π.hom = φ)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS Y I)
    (hIV : idealZeroLocus B S hS Y I = (Set.range (pointsMap B S hS (yoneda.obj V) j))ᶜ)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (p : E ⟶ (pushforwardSubmodule B S hS π (relativelyRepresentable_hom_of_isFinite B S hS π hπ)
      _ I).toSheafOfModules) [Epi p] :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  let sit : ResolutionPropertyDescentSituation B S hS hZ X hX.1 hX.2.1 :=
    { V := V, isAffine_V := hV, φ := φ, isSurjective_φ := hφs, isEtale_φ := hφe, Y := Y, j := j,
      π := π.hom, isOpenImmersion_j := hj, isFinite_π := hπ, comp_eq := hcomp, I := I,
      isFiniteTypeQuasicoherent_I := hI, idealZeroLocus_I := hIV }
  exact hasResolutionProperty_of_exists_epi_idealDirectImage_of_isNoetherian B S hS hZ sit hX
    ⟨E, hE, _, epi_comp_hom_of_epi ‹_› (pushforwardSubmoduleIso B S hS π _ _ I)⟩

/-- **The Noetherian stage of the proof of Stacks 0GV1, from a map to `π_*𝒪_Y`.**  In the data of
`AlgebraicGeometry.Space.hasResolutionProperty_of_epi_pushforwardSubmodule_of_isNoetherian`, it
suffices that the direct image `π_*ℐ ⊆ π_*𝒪_Y` is the image of a map `ℰ ⟶ π_*𝒪_Y` from a finite
locally free module: `ℰ` surjects onto its image. -/
theorem hasResolutionProperty_of_pushforwardSubmodule_eq_imageSubmodule_of_isNoetherian
    (hX : IsNoetherian B S hS hZ X.1)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ X.1) (hφs : IsSurjective B S hS φ) (hφe : IsEtale B S hS φ)
    (Y : AlgebraicSpaces B S hS) (j : yoneda.obj V ⟶ Y.1) (π : Y ⟶ X)
    (hj : IsOpenImmersion B S hS j) (hπ : IsFinite B S hS π.hom) (hcomp : j ≫ π.hom = φ)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS Y I)
    (hIV : idealZeroLocus B S hS Y I = (Set.range (pointsMap B S hS (yoneda.obj V) j))ᶜ)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (f : E ⟶ (smallBaseChangeModulePushforward.{u, u} B S hS π
      (relativelyRepresentable_hom_of_isFinite B S hS π hπ)).obj (SheafOfModules.unit _))
    (h : pushforwardSubmodule B S hS π (relativelyRepresentable_hom_of_isFinite B S hS π hπ) _ I =
      Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  have heq : (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f).toSheafOfModules =
      (pushforwardSubmodule B S hS π (relativelyRepresentable_hom_of_isFinite B S hS π hπ)
        _ I).toSheafOfModules :=
    congrArg SheafOfModules.Submodule.toSheafOfModules h.symm
  let p := Stacks.SheafOfModules.ImageSubsheaf.toImage f ≫ eqToHom heq
  have : Epi p := epi_comp_hom_of_epi (Stacks.SheafOfModules.ImageSubsheaf.epi_toImage f)
    (eqToIso heq)
  exact hasResolutionProperty_of_epi_pushforwardSubmodule_of_isNoetherian B S hS hZ hX V hV φ hφs
    hφe Y j π hj hπ hcomp I hI hIV E hE p

/-- **The last step of the proof of Stacks 0GV1**: Stacks 0GUU along the projection to a stage.
For a Noetherian approximation `X = lim X_i` under the chapter's convention, if a stage `X_i` has
the resolution property then so does `X`: the projection `X ⟶ X_i` is affine
(`AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`) and `X_i` is
quasi-compact and quasi-separated. -/
theorem hasResolutionProperty_of_hasResolutionProperty_noetherianApproximation_stage
    {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X.1)
    (hconv : letI := A.preorder; letI := A.nonempty; letI := A.isDirected
      SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram)
    (i : letI := A.preorder; (A.I)ᵒᵖ)
    (hi : letI := A.preorder
      HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ (A.diagram.obj i)
        (A.isAlgebraicSpace i)) :
    HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ X.1 X.2 := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  have := A.isCofiltered_op
  have haff : IsAffineHom B (⊤_ Scheme.{u}) hZ (A.π.app i) := by
    rw [← A.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit A.diagram) i]
    exact isAffineHom_comp B (⊤_ Scheme.{u}) hZ _ _ (isAffineHom_of_isIso _)
      (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram hconv
        (fun g => A.isAffineHom_map g) i)
  have hN := A.isNoetherian i
  exact hasResolutionProperty_source_of_isAffineHom hZ
    (X := X) (Y := ⟨A.diagram.obj i, A.isAlgebraicSpace i⟩) (ObjectProperty.homMk (A.π.app i))
    haff hN.1 hN.2.1 hi

/-- **The first reduction of the proof of Stacks 0GV1: view `X` over `Spec ℤ`** (Stacks 03I5).
If the implication from `π_*ℐ` being a quotient of a finite locally free module to the resolution
property holds for every situation of Stacks 0GUY over `Spec ℤ`, it holds over every base
`S`. -/
theorem hasResolutionProperty_of_exists_epi_idealDirectImage_of_forall_integers
    (hTop : ∀ (X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ)
      (hqc' : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X'.1)
      (hqs' : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X'.1)
      (sit' : ResolutionPropertyDescentSituation B (⊤_ Scheme.{u}) hZ hZ X' hqc' hqs'),
      (∃ (E : Modules.{u, u} B (⊤_ Scheme.{u}) hZ X'.1 X'.2)
          (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
          (p : E ⟶ sit'.idealDirectImage B (⊤_ Scheme.{u}) hZ hZ), Epi p) →
        HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ X'.1 X'.2)
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)
    (h : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ sit.idealDirectImage B S hS hZ), Epi p) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  have hqc' : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ X.1) :=
    isQuasiCompactSpace_relocalize B S hS hZ (integersMap B S hS hZ) hqc
  have hqs' := isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X.1 hqs
  obtain ⟨sit', E', hE', p', hp'⟩ :=
    ResolutionPropertyDescentSituation.exists_viewOverIntegers_of_exists_epi_idealDirectImage
      B S hS hZ X hqc hqs sit hqc' hqs' h
  have hres := hTop ⟨viewOverIntegers B S hS hZ X.1, isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u})
    hS hZ (integersMap B S hS hZ) X.1 X.2⟩ hqc' hqs' sit' ⟨E', hE', p', hp'⟩
  exact (hasResolutionProperty_viewOverIntegers_iff B hS hZ X.1 X.2).1 hres

/-- **The second paragraph of the proof of Stacks 0GV1.**  In the situation of Stacks 0GUY over
`Spec ℤ` with `π : Y ⟶ X` of finite presentation, if `π_*ℐ` is the quotient of a finite locally
free `𝒪_X`-module then `X` has the resolution property. -/
theorem hasResolutionProperty_of_exists_epi_idealDirectImage_of_isFinitePresentation
    {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    {hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.1}
    {hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X.1}
    (sit : ResolutionPropertyDescentSituation B (⊤_ Scheme.{u}) hZ hZ X hqc hqs)
    (hfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ sit.π)
    (h : ∃ (E : Modules.{u, u} B (⊤_ Scheme.{u}) hZ X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ sit.idealDirectImage B (⊤_ Scheme.{u}) hZ hZ), Epi p) :
    HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ X.1 X.2 := by
  obtain ⟨A, hconv, i, sit', E', hE', f, hf⟩ :=
    exists_noetherianApproximation_stage_of_isFinitePresentation B hZ sit hfp h
  let := A.preorder
  exact hasResolutionProperty_of_hasResolutionProperty_noetherianApproximation_stage B hZ A hconv i
    (hasResolutionProperty_of_pushforwardSubmodule_eq_imageSubmodule_of_isNoetherian B _ hZ hZ
      (X := ⟨A.diagram.obj i, A.isAlgebraicSpace i⟩) (A.isNoetherian i) sit'.V sit'.isAffine_V
      sit'.φ sit'.isSurjective_φ sit'.isEtale_φ sit'.Y sit'.j sit'.πHom sit'.isOpenImmersion_j
      sit'.isFinite_π sit'.comp_eq sit'.I sit'.isFiniteTypeQuasicoherent_I sit'.idealZeroLocus_I
      E' hE' f hf)

/-- In the situation of Stacks 0GUY — `X` a quasi-compact and quasi-separated algebraic space
over `S`, `V` an affine scheme with a surjective étale `φ : V ⟶ X` factored as an open immersion
`j : V ⟶ Y` followed by a finite `π : Y ⟶ X`, and `ℐ ⊆ 𝒪_Y` a finite type quasi-coherent sheaf
of ideals with `|V(ℐ)| = |Y| ∖ |j(V)|` — the algebraic space `X` has the resolution property if
and only if `π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module. -/
@[stacks 0GV1]
theorem hasResolutionProperty_iff_exists_epi_idealDirectImage
    (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 ↔
      ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
        (p : E ⟶ sit.idealDirectImage B S hS hZ), Epi p :=
  ⟨sit.exists_isFiniteLocallyFreeOnSite_epi_idealDirectImage_of_hasResolutionProperty B S hS hZ,
    hasResolutionProperty_of_exists_epi_idealDirectImage_of_forall_integers B S hS hZ
      (fun _ _ _ sit' h' => by
        obtain ⟨sit'', hfp, h''⟩ :=
          exists_isFinitePresentation_of_exists_epi_idealDirectImage B _ hZ hZ sit' h'
        exact hasResolutionProperty_of_exists_epi_idealDirectImage_of_isFinitePresentation B hZ
          sit'' hfp h'') sit⟩

end AlgebraicGeometry.Space

end
