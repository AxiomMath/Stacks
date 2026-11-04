module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusIrreducible
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric genus is at most the genus in the geometrically irreducible case

Let `X` be a proper scheme over a field `k` whose base change `X_{k̄}` to an algebraic closure is
irreducible, reduced and of dimension one. Then `g_geom(X/k) ≤ g(X)`. The inequality
`AlgebraicGeometry.geometricGenus_le_genus` assumes in addition three cohomological facts about the
normalization `ν` of `X_{k̄}`: vanishing of `H²` of the kernel and of `H¹` of the cokernel of
`𝒪_{X_{k̄}} ⟶ ν_*𝒪`, and finite-dimensionality of `H¹(𝒪_{X_{k̄}})`. All three hold under the
hypotheses above.

The kernel vanishing is Grothendieck's vanishing theorem by dimension alone,
`isZero_cohomologyOverField_of_topologicalKrullDim_le` with `d = 1 < 2 = i`. The finiteness of
`H¹` is `finiteDimensional_cohomologyOverField_of_isProper` applied to the coherent structure
sheaf, `isCoherent_unit`.

For the cokernel, the normalization morphism is finite and birational, and the normalization has
the same dimension as its target
(`AlgebraicGeometry.topologicalKrullDim_normalizationSchemeOverField`). Both schemes, being
irreducible of dimension one, have a single generic point of a one-dimensional component, and the
morphism exchanges them. By the "more generally" clause of [Stacks, Tag 0AYU]
(`curveDegree_pullback_eq_of_bijOn_genericPointsOne`), the fibre over the generic point of the
target is that point of the source
(`AlgebraicGeometry.preimage_singleton_subset_genericPointsOne`). Together with the isomorphism of
local rings there given by birationality, the support of the cokernel avoids the generic point
(`AlgebraicGeometry.Scheme.Modules.notMem_supp_cokernel_pushforwardUnitHom`), so it has dimension
at most zero (`topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne`), and its `H¹`
vanishes by [Stacks, Tag 0AYT] (3)
(`isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero`).

## Main results

* `AlgebraicGeometry.geometricGenus_le_genus_of_irreducible`: [Stacks, Tag 0CE5] for `κ = k`, when
  `X_{k̄}` is irreducible, reduced and of dimension one.
* `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_irreducible`: the same
  inequality in the form `g_geom(X/k) ≤ [κ : k]_s · dim_κ H¹(X, 𝒪_X)`, where `κ = Γ(X, ⊤)`.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.BirationalCurveFinite
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field and `g : X ⟶ Spec k` proper. If the base change `X_{k̄}` of `X` to an
algebraic closure `k̄` of `k` is irreducible, reduced and of dimension one, then
`g_geom(X/k) ≤ g(X)`. -/
@[stacks 0CE5 "κ = k, geometrically irreducible of dimension one"]
theorem geometricGenus_le_genus_of_irreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hirr : IrreducibleSpace (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hred : IsReduced (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) = 1) :
    geometricGenus k g ≤ genus g := by
  classical
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  set Y := pullback (C := Scheme.{u}) g a
  set p := pullback.snd g a
  have hintY : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hvar : IsVariety (AlgebraicClosure k) p := {}
  have hdimXn : topologicalKrullDim (normalizationSchemeOverField (AlgebraicClosure k) p
      : Type u) = 1 :=
    (topologicalKrullDim_normalizationSchemeOverField (AlgebraicClosure k) p).trans hdim
  have hbir : IsBirational (normalizationOverField (AlgebraicClosure k) p) :=
    Scheme.isBirational_normalization Y
      (finite_irreducibleComponents_of_locallyOfFiniteType (AlgebraicClosure k) p)
  have hp' : IsProper (normalizationOverField (AlgebraicClosure k) p ≫ p) :=
    isProper_normalizationOverField_comp (AlgebraicClosure k) p
  have hProperν : IsProper (normalizationOverField (AlgebraicClosure k) p) :=
    isProper_of_comp_eq (f := normalizationOverField (AlgebraicClosure k) p) (p := p) rfl
  obtain ⟨η, hη, hgz⟩ := hbir.bijOn.surjOn (by simp [genericPoints_eq_singleton] :
    genericPoint (Y : Type u) ∈ genericPoints (Y : Type u))
  have hsingle : genericPoints (normalizationSchemeOverField (AlgebraicClosure k) p : Type u)
      = {η} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hη, fun z hz => hbir.bijOn.injOn hz hη ?_⟩
    rw [hgz]
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hbir.bijOn.mapsTo hz
  have hone : genericPoint (Y : Type u) ∈ genericPointsOne Y := by
    simp [genericPointsOne_eq_singleton Y hdim]
  have hfib : (normalizationOverField (AlgebraicClosure k) p).base
      ⁻¹' {(normalizationOverField (AlgebraicClosure k) p).base η} ⊆ {η} := by
    have himg : (normalizationOverField (AlgebraicClosure k) p).base η
        = genericPoint (Y : Type u) := hgz
    rw [himg]
    intro w hw
    have hw' : w ∈ genericPointsOne (normalizationSchemeOverField (AlgebraicClosure k) p) :=
      preimage_singleton_subset_genericPointsOne (AlgebraicClosure k)
        (normalizationOverField (AlgebraicClosure k) p ≫ p) p hdimXn.le
        (normalizationOverField (AlgebraicClosure k) p) rfl hone hw
    rw [← hsingle]
    exact (mem_genericPointsOne_iff.mp hw').1
  have hiso : IsIso ((normalizationOverField (AlgebraicClosure k) p).stalkMap η) :=
    hbir.isIso_stalkMap η hη
  have hcokerAll : ∀ y ∈ genericPointsOne Y, y ∉ _root_.SheafOfModules.supp
      (cokernel
        (Scheme.Modules.pushforwardUnitHom (normalizationOverField (AlgebraicClosure k) p))) := by
    rw [genericPointsOne_eq_singleton Y hdim]
    rintro y rfl
    exact hgz ▸ Scheme.Modules.notMem_supp_cokernel_pushforwardUnitHom
      (normalizationOverField (AlgebraicClosure k) p) η
      (normalizationOverField (AlgebraicClosure k) p).isClosedMap hfib hiso
  let : IsLocallyNoetherian Y :=
    isLocallyNoetherian_of_isProper_over_field (AlgebraicClosure k) p
  let : IsFinite (normalizationOverField (AlgebraicClosure k) p) :=
    isFinite_normalizationOverField (AlgebraicClosure k) p
  have hOY : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent :=
    isCoherent_unit (AlgebraicClosure k) p
  have hOXn : (SheafOfModules.unit
      (normalizationSchemeOverField (AlgebraicClosure k) p).ringCatSheaf).IsCoherent :=
    isCoherent_unit (AlgebraicClosure k) (normalizationOverField (AlgebraicClosure k) p ≫ p)
  have hP : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (normalizationOverField (AlgebraicClosure k) p)).obj
        (SheafOfModules.unit
          (normalizationSchemeOverField (AlgebraicClosure k) p).ringCatSheaf)) :=
    isCoherent_pushforward_of_isFinite (normalizationOverField (AlgebraicClosure k) p) _
  have hQc : SheafOfModules.IsCoherent
      (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p))) :=
    isCoherent_cokernel
      (Scheme.Modules.pushforwardUnitHom (normalizationOverField (AlgebraicClosure k) p))
  have hsuppCoker : topologicalKrullDim
      (_root_.SheafOfModules.supp
        (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p)))
        : Set Y) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim.le
      (cokernel (Scheme.Modules.pushforwardUnitHom (normalizationOverField (AlgebraicClosure k) p)))
      hQc hcokerAll
  have hcoker : IsZero (cohomologyOverField (AlgebraicClosure k) p
      (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p)))
      1) :=
    @isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero (AlgebraicClosure k) _ Y p _
      (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p)))
      hQc hsuppCoker 1 (by norm_num)
  have hker : IsZero (cohomologyOverField (AlgebraicClosure k) p
      (kernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p)))
      2) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le (AlgebraicClosure k) p
      (kernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k) p)))
      (d := 1) (i := 2) hdim.le (by norm_num)
  have hfin : FiniteDimensional (AlgebraicClosure k) (cohomologyOverField (AlgebraicClosure k) p
      (structureSheafModule Y) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper (AlgebraicClosure k) p
      (structureSheafModule Y) 1
  exact geometricGenus_le_genus k g hirr hred hdim hcoker hker hfin

/-- Let `k` be a field and let `X` be a proper integral scheme over `k` whose global
regular functions are exactly `k` and whose base change to an algebraic closure of `k` is
irreducible, reduced and of dimension one. Writing `κ = Γ(X, ⊤)`, the geometric genus of `X` over
`k` is at most `[κ : k]_s · dim_κ H¹(X, 𝒪_X)`. -/
theorem geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_irreducible
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of k)) [IsProper g]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop)]
    (hirr : IrreducibleSpace (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hred : IsReduced (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) = 1) :
    letI : Field Γ(X, ⊤) := (isField_of_universallyClosed k g).toField
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    geometricGenus k g ≤ Field.finSepDegree k Γ(X, ⊤) * genus X.toSpecΓ := by
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k g).toField
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  show geometricGenus k g ≤ Field.finSepDegree k Γ(X, ⊤) * genus X.toSpecΓ
  rw [finSepDegree_globalSections_eq_one k g, one_mul, genus_toSpecΓ_eq_genus k g]
  exact geometricGenus_le_genus_of_irreducible k g hirr hred hdim

end AlgebraicGeometry

end
