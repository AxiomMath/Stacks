module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescendAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine

/-!
# Perfect objects on a limit of algebraic spaces

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms `f_{i'i}`, a limit `X` with
projections `f_i`, and a chosen index `0` — the category of perfect objects of `D(𝒪_X)` is the
colimit of the categories of perfect objects of the `D(𝒪_{X_i})`, `i ≥ 0`.  This is Stacks 09RJ,
and it consists of two statements about the comparison functor out of the colimit.

* **Full faithfulness.**  For perfect objects `E₀` and `K₀` of `D(𝒪_{X₀})`,
  `Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)` is the filtered colimit of the
  `Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀)`, the maps being induced by the derived pullbacks
  along the transition morphisms and the projections.  Since the chosen index is arbitrary, this
  covers any two objects of the colimit, which come from a common stage.
* **Essential surjectivity.**  Every perfect object of `D(𝒪_X)` is the derived pullback
  `Lf_i^*E_i` of a perfect object `E_i` of some `D(𝒪_{X_i})`, `i ≥ 0`.

The derived pullbacks are taken with the canonical pseudofunctoriality of derived pullback
(`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`), and the colimit of
homomorphism sets is stated in the elementwise form `Stacks.IsStagesColimit`
(`CategoryTheory.PullbackData.LimitSystem.IsColim`) for the system of the stages of the
situation over the chosen stage (`AlgebraicGeometry.Space.DescentSituation.stagesLimitSystem`).

The index set lies in the universe of the site, and the system is assumed to satisfy the
chapter's standing convention of Section 70.2 (Stacks 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limits of the base changes of the
stages to affine objects of the site lie in the site.  The size bound `#I < B.cutoff.ord.cof` of
Stacks 07SF implies it, and the second form of the statement assumes that bound instead.

## Main definitions

* `DescentSituation.PerfectObjectsDescendOver`: the condition, on a quasi-compact quasi-separated
  algebraic space over `X₀`, that perfect objects descend along the base changes of the situation.

## Main results

* `DescentSituation.perfect_isColim_and_perfectObjectsDescend_of_siteContainsBaseChangeLimits`:
  Stacks 09RJ under the chapter's convention of Stacks 07SD.
* `DescentSituation.perfect_isColim_and_perfectObjectsDescend`: Stacks 09RJ under the size bound
  of Stacks 07SF.
* `DescentSituation.perfectObjectsDescendOver_self`: the condition holds over `X₀` itself.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The condition on an algebraic space `y : Y ⟶ X₀` that `Y` is quasi-compact and
quasi-separated and that perfect objects descend along every directed system presented as the
base change of Situation 09RH along `y`. -/
def PerfectObjectsDescendOver (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (y : Y ⟶ (D.stage D.base).1) : Prop :=
  IsQuasiCompactSpace B S hS Y ∧ IsAbsolutelyQuasiSeparated B S hS hZ Y ∧
    ∀ (hY : IsAlgebraicSpace B S hS Y)
      (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) ⟨Y, hY⟩ D.Stages),
      D.BaseChangeData (ObjectProperty.homMk y) Sys → PerfectObjectsDescend Sys.proj

/-- **Perfect objects descend over `X₀` itself**: `X₀` satisfies
`AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescendOver`, under the chapter's
convention of Stacks 07SD. -/
theorem perfectObjectsDescendOver_self (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    D.PerfectObjectsDescendOver (D.stage D.base).1 (𝟙 _) :=
  qcqs_induction_on_self B S hS hZ (D.stage D.base) (D.quasiCompact D.base)
    (D.quasiSeparated D.base) D.PerfectObjectsDescendOver
    (fun _ hVaff => ⟨hVaff.isQuasiCompactSpace,
      isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVaff,
      fun _ _ β => β.perfectObjectsDescend_of_isAffineSpace hconv hVaff⟩)
    (fun _ _ _ _ hf hsq hWqc hWqs _ _ hU hV hP => ⟨hWqc, hWqs, fun _ _ β =>
      β.perfectObjectsDescend_of_eds hsq hconv hP.1 hP.2.1 (hU.2.2 _ _ (β.edsOpen hsq rfl))
        (hV.2.2 _ _ (β.edsEtale hsq (ObjectProperty.hom_ext _ hf)))⟩)

/-- **Stacks 09RJ: the category of perfect objects on the limit is the colimit of the categories
of perfect objects on the stages, under the chapter's convention.**  In Situation 09RH whose
system satisfies the convention of Stacks 07SD
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`):

* for perfect objects `E₀` and `K₀` of `D(𝒪_{X₀})`, `Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)` is the
  filtered colimit of the `Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀)` over the stages `i ≥ 0`
  (full faithfulness of the comparison functor out of the colimit);
* every perfect object of `D(𝒪_X)` is `Lf_i^*E_i` for a perfect object `E_i` of some
  `D(𝒪_{X_i})`, `i ≥ 0` (its essential surjectivity). -/
theorem perfect_isColim_and_perfectObjectsDescend_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (D.stage D.base).1 (D.stage D.base).2)
    (∀ E₀ K₀ : @DerivedCategory (Modules.{u, u} B S hS (D.stage D.base).1 (D.stage D.base).2)
      _ _ (HasDerivedCategory.standard _),
      (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect E₀ →
      (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect K₀ →
        D.stagesLimitSystem.IsColim (DerivedPullbackComposition.canonical B S hS).toPullbackData
          E₀ K₀) ∧
      PerfectObjectsDescend (fun i : D.Stages => D.projection i.1) :=
  ⟨fun E₀ K₀ hE₀ hK₀ => D.stagesBaseChangeData.isColim_of_isPerfect hconv (D.quasiCompact D.base)
      (D.quasiSeparated D.base) E₀ K₀ hE₀ hK₀,
    (D.perfectObjectsDescendOver_self hconv).2.2 (D.stage D.base).2 D.stagesLimitSystem
      D.stagesBaseChangeData⟩

/-- **Stacks 09RJ: the category of perfect objects on the limit is the colimit of the categories
of perfect objects on the stages.**  In Situation 09RH:

* for perfect objects `E₀` and `K₀` of `D(𝒪_{X₀})`, `Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)` is the
  filtered colimit of the `Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀)` over the stages `i ≥ 0`
  (full faithfulness of the comparison functor out of the colimit);
* every perfect object of `D(𝒪_X)` is `Lf_i^*E_i` for a perfect object `E_i` of some
  `D(𝒪_{X_i})`, `i ≥ 0` (its essential surjectivity). -/
theorem perfect_isColim_and_perfectObjectsDescend (hI : #I < B.cutoff.ord.cof) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        (D.stage D.base).1 (D.stage D.base).2)
    (∀ E₀ K₀ : @DerivedCategory (Modules.{u, u} B S hS (D.stage D.base).1 (D.stage D.base).2)
      _ _ (HasDerivedCategory.standard _),
      (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect E₀ →
      (smallEtaleRingedSite B S hS (D.stage D.base).1 (D.stage D.base).2).IsPerfect K₀ →
        D.stagesLimitSystem.IsColim (DerivedPullbackComposition.canonical B S hS).toPullbackData
          E₀ K₀) ∧
      PerfectObjectsDescend (fun i : D.Stages => D.projection i.1) :=
  D.perfect_isColim_and_perfectObjectsDescend_of_siteContainsBaseChangeLimits
    (D.siteContainsBaseChangeLimits_of_lt_cof hI)

end DescentSituation

end AlgebraicGeometry.Space

end
