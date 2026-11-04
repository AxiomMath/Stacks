module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentationInstances
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHomCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectSourceCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalApproximationWithCone
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
import StacksCore.Tactic.StacksAttribute

/-! # Derived internal Hom of coherent complexes on a locally Noetherian algebraic space

Let `X` be a locally Noetherian algebraic space over a scheme `S`, let `K` be in `D⁻_Coh(𝒪_X)`
and let `L` be in `D⁺_Coh(𝒪_X)`. Stacks 0D0S asserts that `RSheafHom(K, L)` lies in
`D⁺_Coh(𝒪_X)`.

`RSheafHom(K, L)` is read, as the source reads it, on models: it is the internal Hom complex
`SheafHom(A, J)` of a complex `A` concentrated in degrees `≤ d` representing `K` and a
K-injective complex `J` concentrated in degrees `≥ b` representing `L`.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_homology_sheafHomComplex`: every cohomology sheaf of
  `SheafHom(A, J)` is coherent.
* `AlgebraicGeometry.Space.derivedCategoryBPlus_isCoherentOnSite_sheafHomComplex`: **Stacks
  0D0S**, both clauses.

## Implementation notes

The internal Hom complex of Stacks 0A8Z raises the module universe of a site whose objects lie in
`Type (u + 1)` from `u` to `u + 1`, so `SheafHom(A, J)` is a complex of `𝒪_X`-modules with
sections in `u + 1` while `A` and `J` have sections in `u`, the universe of the structure rings;
coherence is `SheafOfModules.IsCoherentOnSite`, coherence on the site (Stacks 01BW), at both.

## References

* [Stacks Project, Tag 0D0S](https://stacks.math.columbia.edu/tag/0D0S)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.RingedSite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe t u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The small étale site of an algebraic space is essentially small. -/
local instance essentiallySmall_site :
    EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C :=
  smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2

/-- Every slice of the small étale site of an algebraic space is essentially small. -/
local instance essentiallySmall_site_over (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    EssentiallySmall.{u} ((smallEtaleRingedSite B S hS X.1 X.2).over V).C :=
  inferInstanceAs (EssentiallySmall.{u} (Over V))

/-- **Every cohomology sheaf of `SheafHom(A, J)` is coherent** on a locally Noetherian algebraic
space, for `A` concentrated in degrees `≤ d` with coherent cohomology and `J` K-injective,
concentrated in degrees `≥ b` and with coherent cohomology. -/
theorem isCoherentOnSite_homology_sheafHomComplex
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (d b : ℤ) (A J : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    [CochainComplex.IsStrictlyLE A d] [CochainComplex.IsKInjective J]
    [CochainComplex.IsStrictlyGE J b]
    (hA : ∀ i, SheafOfModules.IsCoherentOnSite (A.homology i))
    (hJ : ∀ i, SheafOfModules.IsCoherentOnSite (J.homology i)) (n : ℤ) :
    SheafOfModules.IsCoherentOnSite
      ((sheafHomComplex (smallEtaleRingedSite B S hS X.1 X.2) A J).obj.homology n) := by
  classical
  let _ := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  have hpc : IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) A (b - n - 1) := by
    refine isPseudoCoherentComplexFrom_of_iso_general _ (DerivedCategory.Q.obj A)
      (b - n - 1) ?_ A (Iso.refl _)
    refine isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove B S hS X.1 X.2 hN
      (DerivedCategory.Q.obj A) (b - n - 1) (fun i _ => ?_) ⟨d, fun i hi => ?_⟩
    · exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
        ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS X.1 X.2) i).app A).symm
        (hA i)
    · exact IsZero.of_iso (CochainComplex.exactAt_of_isLE A d i hi).isZero_homology
        ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS X.1 X.2) i).app A)
  choose Sv hSv hdata using fun U : (smallEtaleRingedSite B S hS X.1 X.2).C =>
    exists_local_strictlyPerfect_approximation_with_cone
      (smallEtaleRingedSite B S hS X.1 X.2) A (b - n - 1) hpc U
  refine (Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite
    (smallEtaleRingedSite B S hS X.1 X.2) _).2
    ⟨Σ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
        Σ V : (smallEtaleRingedSite B S hS X.1 X.2).C, {f : V ⟶ U // Sv U f},
      fun i => i.2.1, fun W => ?_, ?_⟩
  · refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_ (hSv W)
    rintro Z g ⟨Z', a, c, hc, rfl⟩
    exact ⟨⟨W, Z', ⟨c, hc⟩⟩, ⟨a⟩⟩
  · rintro ⟨U, V, f, hf⟩
    obtain ⟨P, hP, -, α, -, -, hcone⟩ := hdata U f hf
    let Jres : CochainComplex (SheafOfModules.{u}
        (ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over V).O)) ℤ :=
      restrictComplex (smallEtaleRingedSite B S hS X.1 X.2) J V
    have : CochainComplex.IsKInjective Jres :=
      Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall
        (smallEtaleRingedSite B S hS X.1 X.2).J
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V J
    have : CochainComplex.IsStrictlyGE Jres b := (CochainComplex.isStrictlyGE_iff Jres b).2
      fun i hi => (SheafOfModules.overFunctor.{u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V).map_isZero
        ((CochainComplex.isStrictlyGE_iff J b).1 inferInstance i hi)
    have hJres : ∀ q : ℤ, SheafOfModules.IsCoherentOnSite (Jres.homology q) := fun q =>
      Stacks.SheafOfModules.isCoherentOnSite_of_iso
        ((Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u}
            (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V) q).app J).symm
        (Stacks.SheafOfModules.isCoherentOnSite_over (J.homology q) (hJ q) V)
    have hslice := Raised.isCoherentOnSite_homology_sheafHomComplex_of_approximation
      ((smallEtaleRingedSite B S hS X.1 X.2).over V) hP α Jres (b - n - 1) b n hcone hJres
      (by omega)
    exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (Raised.sheafHomRestrictionComplexIso
          (smallEtaleRingedSite B S hS X.1 X.2) V A J)).symm ≪≫
        (Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u + 1}
            (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V) n).app
          (sheafHomComplex (smallEtaleRingedSite B S hS X.1 X.2) A J).obj) hslice

/-- **Stacks 0D0S.** On a locally Noetherian algebraic space, `RSheafHom(K, L)` lies in
`D⁺_Coh(𝒪_X)` for `K` in `D⁻_Coh(𝒪_X)` and `L` in `D⁺_Coh(𝒪_X)`, read on a model `A` of `K` and
a K-injective model `J` of `L`. -/
@[stacks 0D0S "read on a model of K and a K-injective model of L"]
theorem derivedCategoryBPlus_isCoherentOnSite_sheafHomComplex
    [HasDerivedCategory.{t} (Modules.{u, u + 1} B S hS X.1 X.2)]
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (d b : ℤ) (A J : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    [CochainComplex.IsStrictlyLE A d] [CochainComplex.IsKInjective J]
    [CochainComplex.IsStrictlyGE J b]
    (hA : ∀ i, SheafOfModules.IsCoherentOnSite (A.homology i))
    (hJ : ∀ i, SheafOfModules.IsCoherentOnSite (J.homology i)) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun N : Modules.{u, u + 1} B S hS X.1 X.2 => SheafOfModules.IsCoherentOnSite N)
      (DerivedCategory.Q.obj
        (sheafHomComplex (smallEtaleRingedSite B S hS X.1 X.2) A J).obj) := by
  have := isStrictlyGE_sheafHomComplex (smallEtaleRingedSite B S hS X.1 X.2) A J d b
  refine ⟨⟨b - d, fun i hi => (DerivedCategory.isGE_iff _ (b - d)).1 inferInstance i hi⟩,
    fun i => ?_⟩
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((DerivedCategory.homologyFunctorFactors (Modules.{u, u + 1} B S hS X.1 X.2) i).app _).symm
    (isCoherentOnSite_homology_sheafHomComplex B S hS X hN d b A J hA hJ i)

end AlgebraicGeometry.Space

end
