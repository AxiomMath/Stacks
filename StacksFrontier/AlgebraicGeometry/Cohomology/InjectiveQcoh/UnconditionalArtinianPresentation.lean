module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.NoetherianInjectiveEtaleAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardFilteredColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Injective quasi-coherent modules on a Noetherian algebraic space, unconditionally

Let `X` be a Noetherian algebraic space over a scheme `S`.  Every injective object `𝒥` of the
category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale site of `X` is a direct
summand of a filtered colimit of quasi-coherent modules `(Z_i ⟶ X)_*𝒢_i` with `Z_i` the spectrum
of an Artinian ring and `𝒢_i` coherent (Stacks 09TJ), and `H^p(U, 𝒥|_U) = 0` for `p > 0` and
every quasi-compact quasi-separated algebraic space `U` étale over `X` (Stacks 09TL, part (1)).

## Main results

* `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian`:
  **Stacks 09TJ**.
* `AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian`:
  **Stacks 09TL, part (1)**.
* the input both of them consume, in the same namespace,
  `...preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine`: the direct image
  along a morphism from an affine object of the site to a quasi-separated algebraic space
  preserves filtered colimits of quasi-coherent modules.

## Implementation notes

The two statements are the conditional ones of
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/InjectiveQcohSpace.lean` and
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/NoetherianInjectiveEtaleAcyclicity.lean`
with their assumed inputs discharged.  The last of those was Stacks 07U6 read in `QCoh` at the
affine surjective étale chart of Stacks 03H6, which is now
`AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_schemeSpace`
and whose quasi-compactness and quasi-separatedness hypotheses on the chart morphism are
supplied, as in `AlgebraicGeometry.Space.chartArtinianPresentation_of_isAffine`, by Stacks 073B
from affineness of the chart's source and quasi-separatedness of `X`.  The remaining hypothesis
`hZ`, that the big fppf site contains the terminal scheme, is the site side condition under which
the absolute quasi-separatedness of Stacks 03BS, part (3), is phrased.

Part (2) of Stacks 09TL, the vanishing `R^p f_*𝒥 = 0` for `f : X ⟶ Y` with `Y` quasi-separated,
is not stated here.

## References

* [Stacks Project, Tag 09TJ](https://stacks.math.columbia.edu/tag/09TJ)
* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 07U6](https://stacks.math.columbia.edu/tag/07U6)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07U6 in degree zero, read in `QCoh` at an affine chart.**  For a morphism
`j : W ⟶ X` from an affine object of the site to a quasi-separated algebraic space, the direct
image of quasi-coherent modules preserves filtered colimits.

The chart morphism is quasi-compact and quasi-separated by Stacks 073B, parts (1) and (2), its
source being an affine, hence quasi-compact and absolutely quasi-separated, algebraic space. -/
theorem preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : BigFppfOver B S hS) (j : schemeSpace W ⟶ X)
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hqcoh : ∀ M : QuasicoherentSheaves.{u, u} B S hS
        (schemeSpace W).1 (schemeSpace W).2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite) :
    PreservesFilteredColimitsOfSize.{u, u}
      (chartQuasicoherentPushforward B S hS j hqcoh) :=
  preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_schemeSpace B S hS hZ W j
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS W hWaff) j.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ (schemeSpace W).2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS W hWaff)) j.hom)
    hqcoh

/-- **Stacks 09TJ.**  Let `X` be a Noetherian algebraic space over a scheme `S` of a big fppf
site.  Every injective object `J` of the category `QCoh(𝒪_X)` of quasi-coherent modules on the
small étale site of `X` is a direct summand — a retract — of a filtered colimit of quasi-coherent
modules `(Z_i ⟶ X)_*𝒢_i` with `Z_i` the spectrum of an Artinian ring and `𝒢_i` coherent on
`Z_i`. -/
@[stacks 09TJ]
theorem exists_filtered_colimit_artinian_pushforwards_retract_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hX : IsNoetherian B S hS hZ X.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (c : Cocone D),
        (∀ i, IsArtinianPushforward B S hS X (D.obj i).obj) ∧
          Nonempty (IsColimit c) ∧ Nonempty (Retract J c.pt) :=
  exists_filtered_colimit_artinian_pushforwards_retract B S hS hZ X hX
    (fun W j hWaff hWnoeth _ _ =>
      chartArtinianPresentation_of_isAffine B S hS hZ hX.2.1 W j hWaff hWnoeth
        fun hqcoh =>
          preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine
            B S hS hZ hX.2.1 W j hWaff hqcoh)
    J

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **Stacks 09TL, part (1).**  Let `X` be a Noetherian algebraic space over a scheme `S` of a
big fppf site and let `𝒥` be an injective object of `QCoh(𝒪_X)`.  Then `H^p(U, 𝒥|_U) = 0` for
`p > 0` and every quasi-compact and quasi-separated algebraic space `U` étale over `X`. -/
@[stacks 09TL "part (1)"]
theorem isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J]
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((etaleRestrictionCohomology B S hS g hg p).obj J) :=
  isZero_etaleRestrictionCohomology_of_injective_of_pushforwardColimits B S hS hZ hX
    (fun W j hWaff _ _ _ hqcoh =>
      preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine
        B S hS hZ hX.2.1 W j hWaff hqcoh)
    J g hg hUqc hUqs p hp

end AlgebraicGeometry.Space

end

end
