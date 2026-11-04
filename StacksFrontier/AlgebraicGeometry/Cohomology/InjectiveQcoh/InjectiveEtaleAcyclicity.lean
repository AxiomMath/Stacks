module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ArtinianPushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleCohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties

/-!
# Acyclicity of retracts of filtered colimits of Artinian direct images

Let `X` be a quasi-separated algebraic space over a scheme `S`, let `g : U ⟶ X` be étale with
`U` quasi-compact and quasi-separated, and let `𝒥` be a quasi-coherent `𝒪_X`-module which is a
retract of a filtered colimit, in `QCoh(𝒪_X)`, of Artinian direct images. Then
`H^p(U, 𝒥|_U) = 0` for `p > 0`. Together with the Artinian presentation of Stacks 09TJ this is
part (1) of Stacks 09TL.

## Main results

* `AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_retract_colimit`: if `𝒥` is a
  retract of a filtered colimit of Artinian direct images, then `H^p(U, 𝒥|_U) = 0` for `p > 0`
  and every quasi-compact and quasi-separated `U` étale over `X`.

## References

* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 09TJ](https://stacks.math.columbia.edu/tag/09TJ)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **Retracts of filtered colimits of Artinian direct images are acyclic.**  Let `X` be a
quasi-separated algebraic space, `g : U ⟶ X` étale with `U` quasi-compact and quasi-separated,
and let `𝒥` be a quasi-coherent `𝒪_X`-module which is a retract of a filtered colimit, in
`QCoh(𝒪_X)`, of Artinian direct images.  Then `H^p(U, 𝒥|_U) = 0` for `p > 0`. -/
theorem isZero_etaleRestrictionCohomology_of_retract_colimit
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U : AlgebraicSpaces B S hS}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1) (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (p : ℕ) (hp : 0 < p) (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (c : Cocone D)
    (hart : ∀ i, IsArtinianPushforward B S hS X (D.obj i).obj) (hc : IsColimit c)
    (r : Retract J c.pt) :
    IsZero ((etaleRestrictionCohomology B S hS g hg p).obj J) := by
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) := by
    have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
      show EssentiallySmall.{u} (SmallEtale B S hS X.1)
      infer_instance
    exact SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have := isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall B S hS X.1 X.2 I
  have hcM : IsColimit ((ObjectProperty.ι _).mapCocone c) := isColimitOfPreserves _ hc
  have := preservesColimitsOfSize_etaleModulePullback B S hS g hg
  have hcU : IsColimit ((etaleModulePullback B S hS g hg).mapCocone
      ((ObjectProperty.ι _).mapCocone c)) := isColimitOfPreserves _ hcM
  have hzero : IsZero ((etaleRestrictionCohomology B S hS g hg p).obj c.pt) :=
    isZero_rightDerived_globalSectionsFunctor_of_isColimit B S hS hZ U.1 U.2 hUqc hUqs
      (D ⋙ ObjectProperty.ι _ ⋙ etaleModulePullback B S hS g hg) _ hcU p
      (fun i => isZero_etaleRestrictionCohomology_of_isArtinianPushforward B S hS hZ hXqs g hg
        hUqc hUqs p hp (D.obj i) (hart i))
  exact hzero.of_retract (r.map (etaleRestrictionCohomology B S hS g hg p))

end AlgebraicGeometry.Space

end

end
