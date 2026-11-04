module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsQcqs

/-!
# A lattice in the direct image from the generic fibre over a valuation ring

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation, the standing datum of
`AlgebraicGeometry.Space.CoherentSituation`, `R` a domain with fraction field `K`, and
`h : U ⟶ T` a morphism of test schemes over `Y` lying over `Spec K ⟶ Spec R`, so that
`j = X_h : X_U ⟶ X_T` is the inclusion of the generic fibre. For a quasi-coherent
`𝒪_{X_U}`-module `F_K` of finite type, there is a quasi-coherent submodule `G ⊆ j_*F_K` of finite
type with `j^*G = F_K`.

## Main results

* `AlgebraicGeometry.Space.exists_lattice_modulePushforward_baseChangeMap`: the submodule
  `G ⊆ j_*F_K`.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A lattice in the direct image from the generic fibre.**  Let `f : X ⟶ Y` be of finite
presentation, `R` a domain with fraction field `K`, `h : U ⟶ T` a morphism of test schemes
over `Y` lying over `Spec K ⟶ Spec R`, and `j = X_h : X_U ⟶ X_T` the induced inclusion of the
generic fibre.  For every quasi-coherent `𝒪_{X_U}`-module `F_K` of finite type there is a
quasi-coherent submodule `G ⊆ j_*F_K` of finite type such that `j^*G ⟶ j^*j_*F_K ⟶ F_K`, the
inclusion followed by the counit, is an isomorphism. -/
theorem exists_lattice_modulePushforward_baseChangeMap {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom) (hZ : B.Contains (⊤_ Scheme.{u}))
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (b : Spec (.of R) ⟶ S) {U T : SchemesOver Y} (h : U ⟶ T)
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
        siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hFq : F.IsQuasicoherentOnSite) (hFf : F.IsFiniteType) :
    ∃ G : Subobject ((modulePushforward B S hS (baseChangeMap f h)).obj F),
      (G : Modules.{u, u} B S hS (baseChangeSpace f T).1
        (baseChangeSpace f T).2).IsQuasicoherentOnSite ∧
      (G : Modules.{u, u} B S hS (baseChangeSpace f T).1 (baseChangeSpace f T).2).IsFiniteType ∧
      IsIso ((modulePullback B S hS (baseChangeMap f h)).map G.arrow ≫
        (modulePullbackAdjunction B S hS (baseChangeMap f h)).counit.app F) := by
  let D : CoherentSituation B S hS := ⟨X, Y, f, hf⟩
  have haff := isAffine_left_of_isHomLift (Y := Y) R K h hh
  have hU := D.qcqs_space hZ U haff.1
  have hT := D.qcqs_space hZ T haff.2
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hflat := isFlat_baseChangeMap_of_isHomLift f R K h hh
  have hfin := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (baseChangeMap f h) hflat
  have hcos : PreservesLimitsOfShape WalkingCospan (modulePullback B S hS (baseChangeMap f h)) :=
    hfin.preservesFiniteLimits WalkingCospan
  have hmono : (modulePullback B S hS (baseChangeMap f h)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have hH := isQuasicoherentOnSite_modulePushforward_baseChangeMap_of_isHomLift f R K h hh F hFq
  have : ((modulePushforward B S hS (baseChangeMap f h)).obj F).IsQuasicoherentOnSite := hH
  have hcounit := isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_epi f R K h hh F hFq
  have hcol := nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs B S hS hZ
    (baseChangeSpace f T).1 (baseChangeSpace f T).2 hT.1 hT.2
    ((modulePushforward B S hS (baseChangeMap f h)).obj F)
  exact exists_subobject_isIso_modulePullback_comp_counit (baseChangeMap f h) hU.1 hmono F hFf
    hcounit hH hcol

end AlgebraicGeometry.Space

end
