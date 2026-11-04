module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureModuleSmallBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationQuasicoherentOnSite

/-!
# The situation for descending the resolution property exists

Stacks 0GUY fixes, for a quasi-compact and quasi-separated algebraic space `X` over `S`, an
affine surjective étale chart `φ : V ⟶ X`, a factorization `φ = π ∘ j` with `j : V ⟶ Y` an open
immersion and `π : Y ⟶ X` finite, and a finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`
with `|V(ℐ)| = |Y| ∖ |j(V)|`, saying in parentheses that each of these exists: by Stacks 03H6,
Stacks 082K and Stacks 0855. The data are the structure
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation`; this file shows it is inhabited,
for every affine surjective étale chart, with `π` moreover finite and of finite presentation
(Stacks 0874) and `π_* 𝒪_Y` a finitely presented `𝒪_X`-module (Stacks 0610).

## Main results

* `ResolutionPropertyDescentSituation.exists_eq_chart_isFinitePresentation`:
  the situation exists with any prescribed chart `V`, `φ`.
* `ResolutionPropertyDescentSituation.exists_isFinitePresentation`:
  the situation exists.

## Implementation notes

`π_* 𝒪_Y` is stated in both spellings of the direct image that the section uses: the base-change
form `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, in which
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.idealDirectImage` is defined, and
`AlgebraicGeometry.Space.pushforwardStructureModule`; they are identified by
`AlgebraicGeometry.Space.pushforwardStructureModuleIsoSmallBaseChange`. Finite presentation is
`SheafOfModules.IsFinitePresentationOnSite`, the reading of Stacks 03DL(7) used throughout the
section.

## References

* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0874](https://stacks.math.columbia.edu/tag/0874)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

namespace ResolutionPropertyDescentSituation

/-- **Stacks 0GUY, the situation exists at every chart.** Let `X` be a quasi-compact and
quasi-separated algebraic space over `S` and let `φ : V ⟶ X` be a surjective étale morphism
from an affine scheme `V` of the site. Then there is a situation of Stacks 0GUY with chart
`V` and `φ` itself, in which the finite morphism `π : Y ⟶ X` is moreover of finite
presentation and `π_* 𝒪_Y` is a finitely presented `𝒪_X`-module, both for the direct image
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` along `π` and for
`AlgebraicGeometry.Space.pushforwardStructureModule`.

`φ` is quasi-finite (étale, and quasi-compact because `V` is quasi-compact and `X`
quasi-separated, Stacks 073B), separated (Stacks 03FZ, `V` being affine) and locally of finite
presentation, so Stacks 0874 factors it as a quasi-compact open immersion `j : V ⟶ Y` followed
by a finite morphism `π` of finite presentation. `Y` is quasi-compact and quasi-separated,
being finite over `X`, and `j(V)` is a quasi-compact open subspace, so Stacks 0855
((2) implies (3)) provides the finite type quasi-coherent sheaf of ideals `ℐ` with
`|V(ℐ)| = |Y| ∖ |j(V)|`. Finally `π_* 𝒪_Y` is of finite presentation by Stacks 0610. -/
theorem exists_eq_chart_isFinitePresentation (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hφs : IsSurjective B S hS φ) (hφe : IsEtale B S hS φ) :
    ∃ (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs) (e : sit.V = V),
      sit.φ = eqToHom (congrArg yoneda.obj e) ≫ φ ∧
      IsFinitePresentation B S hS sit.π ∧
      ((smallBaseChangeModulePushforward B S hS sit.πHom
          (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS sit.Y))).IsFinitePresentationOnSite ∧
      (pushforwardStructureModule B S hS sit.πHom).IsFinitePresentationOnSite := by
  classical
  have hVa := isAlgebraicSpace_yoneda B S hS V
  -- `φ` is quasi-finite, separated and locally of finite presentation
  have hφsep : IsSeparated B S hS φ := isSeparated_of_isEtale_of_isAffine B S hS X.2 V hV φ hφe
  have hφqc : IsQuasiCompact B S hS φ :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) φ
  have hφqf : IsQuasiFinite B S hS φ := ⟨isLocallyQuasiFinite_of_isEtale B S hS X.2 hφe, hφqc⟩
  have hφlfp : IsLocallyOfFinitePresentation B S hS φ :=
    isLocallyOfFinitePresentation_of_isEtale B S hS hφe
  -- Stacks 0874
  obtain ⟨T, j, π, hT, hj, -, hπfin, hπfp, hfac⟩ :=
    exists_isOpenImmersion_isFinitePresentation_of_isQuasiFinite
      (fun g hX' hY' hg hqc' hqs' => exists_integralFiniteSystem_of_isFinite B S hS g hX' hY' hg
        hqc' hqs') φ hVa X.2 hφqf hφsep hqc hqs hφlfp
  let Y : AlgebraicSpaces B S hS := ⟨T, hT⟩
  have hYqc : IsQuasiCompactSpace B S hS T :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hqc hπfp.2.1
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ T :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hT hqs hπfp.2.2
  -- Stacks 0855, for the quasi-compact open subspace `j(V)`
  have hjmono : Mono j := mono_of_presheaf_isOpenImmersion hj
  have hU : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hVa j hj
  have hUqc : IsQuasiCompactSpace B S hS (Subfunctor.range j).toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange j))
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV)
  obtain ⟨I, hI, hIz⟩ :=
    hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace B S hS hZ Y hYqc hYqs hU hUqc
  have hrange : Set.range (pointsMap B S hS (Subfunctor.range j).toFunctor (Subfunctor.range j).ι) =
      Set.range (pointsMap B S hS (yoneda.obj V) j) := by
    rw [← (surjective_pointsMap_of_isIso B S hS (asIso (Subfunctor.toRange j))).range_comp,
      ← pointsMap_comp, asIso_hom, Subfunctor.toRange_ι]
  let sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs :=
    { V := V
      isAffine_V := hV
      φ := φ
      isSurjective_φ := hφs
      isEtale_φ := hφe
      Y := Y
      j := j
      π := π
      isOpenImmersion_j := hj
      isFinite_π := hπfin
      comp_eq := hfac
      I := I
      isFiniteTypeQuasicoherent_I := hI
      idealZeroLocus_I := by rw [← hIz, hrange] }
  -- Stacks 0610 for the structure sheaf
  have hunitOn :
      (SheafOfModules.unit (structureRingSheaf B S hS sit.Y)).IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
      SheafOfModules.isFiniteLocallyFreeOnSite_unit
  have hunit : SheafOfModules.IsFinitePresentation
      (SheafOfModules.unit (structureRingSheaf B S hS sit.Y)) :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ hunitOn
  have hfp : ((smallBaseChangeModulePushforward B S hS sit.πHom
      (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS sit.Y))).IsFinitePresentation :=
    (isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite B S hS
      sit.πHom hπfin hπfp _
      (@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hunitOn)).1
      hunit
  have hfp' := SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation _ (h := hfp)
  refine ⟨sit, rfl, by simp [sit], hπfp, hfp', ?_⟩
  exact SheafOfModules.IsFinitePresentationOnSite.of_iso
    (pushforwardStructureModuleIsoSmallBaseChange B S hS sit.πHom
      (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).symm hfp'

/-- **Stacks 0GUY, the situation exists.** For a quasi-compact and quasi-separated algebraic
space `X` over `S` there is a situation of Stacks 0GUY in which the finite morphism
`π : Y ⟶ X` is moreover of finite presentation and `π_* 𝒪_Y` is a finitely presented
`𝒪_X`-module, both for `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` and for
`AlgebraicGeometry.Space.pushforwardStructureModule`. -/
theorem exists_isFinitePresentation (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs,
      IsFinitePresentation B S hS sit.π ∧
      ((smallBaseChangeModulePushforward B S hS sit.πHom
          (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS sit.Y))).IsFinitePresentationOnSite ∧
      (pushforwardStructureModule B S hS sit.πHom).IsFinitePresentationOnSite := by
  obtain ⟨V, φ, hV, hφs, hφe⟩ :=
    exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace B S hS X hqc
  obtain ⟨sit, -, -, h⟩ := exists_eq_chart_isFinitePresentation B S hS hZ X hqc hqs V φ hV hφs hφe
  exact ⟨sit, h⟩

end ResolutionPropertyDescentSituation

end AlgebraicGeometry.Space

end
