module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.LipmanSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionIntegralMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationBirationalIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceResolutionCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.ResolutionTransferAssembly

/-!
# (4) implies (3) in Stacks 0BHY

Let `Y` be a two dimensional integral Noetherian algebraic space over a scheme `S` whose
normalization `Y^ν ⟶ Y` is finite, has finitely many singular points, and has normal completed
henselian local rings at them. Then `Y` has a resolution of singularities by normalized blowups
(Stacks 0BHX). This is the implication (4) `⇒` (3) of Stacks 0BHY.

The proof is the source's. `Y^ν` is normal, Noetherian and of dimension at most two, so its
singular points are closed and have elementary étale neighbourhoods `(Vᵢ, vᵢ)` which are normal
integral affine Noetherian schemes with `vᵢ` the only singular point, and the completion of
`𝒪_{Vᵢ, vᵢ}` agrees with that of the henselian local ring of `Y^ν` at the singular point, hence is
normal. By Lipman's theorem for schemes (Stacks 0BGP, in its local form for the two dimensional
Noetherian local normal domain `𝒪_{Vᵢ, vᵢ}` with normal completion) the spectrum of `𝒪_{Vᵢ, vᵢ}`
has a resolution by normalized blowups, which spreads out to a resolution of `Vᵢ` centred over
`vᵢ`; these lift to `Y^ν` (Stacks 0BHL), and the result is regular because it is so over each
`Vᵢ` and over the regular locus of `Y^ν`.

## Main results

* `AlgebraicGeometry.Space.exists_normalizedBlowUpChain_isRegular_of_normalization`: a finite
  normalization satisfying the criterion is the start of a sequence of normalized blowups with
  regular top.
* `AlgebraicGeometry.Space.hasResolutionByNormalizedBlowUps_of_isSurfaceResolutionCriterion`:
  Stacks 0BHY, (4) `⇒` (3).

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The transfer from schemes to algebraic spaces.** Let `ν : X ⟶ Y` be a finite
normalization of `Y` with `X` integral, normal, locally Noetherian and of dimension at most two,
finitely many singular points and normal completed henselian local rings at them. Then `Y` has
a sequence of normalized blowups in the sense of Stacks 0BHX starting with `ν` whose top is
regular. Lipman's theorem for schemes enters through
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion`. -/
theorem exists_normalizedBlowUpChain_isRegular_of_normalization
    {X Y : AlgebraicSpaces B S hS} (ν : X ⟶ Y) (hν : IsProper B S hS ν.hom)
    (hνnorm : ∃ (Dn : NormalizationData B S hS Y.obj) (e : X.obj ≅ Dn.space),
      ν.hom = e.hom ≫ Dn.hom)
    (hXint : IsIntegralSpace B S hS X.obj) (hXn : Space.IsNormal B S hS X.obj)
    (hXln : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXdim : dimension B S hS X.obj X.property ≤ 2)
    (hsing : {y : points B S hS X.obj | ¬ IsRegularAt B S hS X.obj y}.Finite)
    (hcompl : ∀ y, ¬ IsRegularAt B S hS X.obj y →
      letI := henselianLocalRing_isLocalRing B S hS X.obj X.property y
        (hXint.isDecentSpace B S hS X.obj)
      IsNormalRing (AdicCompletion
        (IsLocalRing.maximalIdeal (henselianLocalRing B S hS X.obj X.property y
          (hXint.isDecentSpace B S hS X.obj) : Type (u + 1)))
        (henselianLocalRing B S hS X.obj X.property y
          (hXint.isDecentSpace B S hS X.obj) : Type (u + 1)))) :
    ∃ (A : AlgebraicSpaces B S hS) (f : A ⟶ Y), NormalizedBlowUpChain B S hS Y A f ∧
      HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsRegular T) := by
  let := hasSheafify_bigFppfOver B S hS
  obtain ⟨n, Dc, hDX, hrange, hV⟩ :=
    exists_closedPointNeighborhoods_singularPoints B S hS X hXint hXn hXln hXdim hsing hcompl
  subst hDX
  refine Dc.exists_normalizedBlowUpChain_isRegular ν hν hνnorm hXn hXln
    (fun x hx => by simpa only [hrange, Set.mem_ofPred_eq, not_not] using hx) fun i => ?_
  obtain ⟨hVaff, hVint, hVn, hVln, hVsing, hVdim, hVcompl⟩ := hV i
  set V := Dc.neighborhoodScheme i
  set v := (Dc.neighborhood i).point
  have : IsAffine V := hVaff
  have : _root_.AlgebraicGeometry.IsNormal V := hVn
  have : IsLocallyNoetherian V := hVln
  have : AlgebraicGeometry.IsNoetherian V := {}
  have hv : IsClosed ({v} : Set V) := by
    have h0 := Dc.isClosed_neighborhoodPoint i
    rw [Dc.neighborhoodPoint_eq_schemeSpacePoint] at h0
    exact isClosed_singleton_of_isClosed_schemeSpacePoint _ h0
  have : IsNormalDomain (V.presheaf.stalk v) :=
    ⟨IsNormal.stalk_isDomain v, IsNormal.stalk_normal v⟩
  exact exists_reflTransGen_isProperNormalizedBlowUpOutside_of_singularLocus V v hv hVsing
    (AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion
      (V.presheaf.stalk v) hVdim hVcompl)

/-- **Stacks 0BHY, (4) `⇒` (3).** Let `Y` be a two dimensional integral Noetherian algebraic space
over `S` and let `D` be a normalization of `Y` satisfying condition (4) of Stacks 0BHY: the
normalization morphism is finite, `Y^ν` has finitely many singular points, and the completion of
the henselian local ring of `Y^ν` at each of them is normal. Then `Y` has a resolution of
singularities by normalized blowups (Stacks 0BHX).

Lipman's theorem enters through its scheme form for the spectrum of a two dimensional
Noetherian local normal domain with normal completion,
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion`. -/
theorem hasResolutionByNormalizedBlowUps_of_isSurfaceResolutionCriterion
    (hZ : B.Contains (⊤_ Scheme.{u})) (Y : AlgebraicSpaces B S hS)
    (hYdim : dimension B S hS Y.obj Y.property = 2) (hYnoeth : IsNoetherian B S hS hZ Y.obj)
    (hYint : IsIntegralSpace B S hS Y.obj) (D : NormalizationData B S hS Y.obj)
    (hD : D.IsSurfaceResolutionCriterion Y.property (hYint.isDecentSpace B S hS Y.obj)) :
    HasResolutionByNormalizedBlowUps B S hS hZ Y hYdim hYnoeth hYint := by
  obtain ⟨hfin, hsing, hcompl⟩ := hD
  let X : AlgebraicSpaces B S hS := ⟨D.space, D.isAlgebraicSpace⟩
  let ν : X ⟶ Y := ObjectProperty.homMk D.hom
  have hν : IsProper B S hS ν.hom :=
    (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS X.property Y.property _ hfin).1
  exact exists_normalizedBlowUpChain_isRegular_of_normalization ν hν
    ⟨D, Iso.refl _, by simp [ν]⟩ (D.isIntegralSpace Y.property hYint) (D.isNormal Y.property)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.property
      Y.property _ hν.2.1.1 hYnoeth.2.2)
    ((dimension_le_of_isIntegralHom B S hS X.property Y.property _
      (D.isIntegralHom_hom Y.property)).trans hYdim.le)
    hsing hcompl

end AlgebraicGeometry.Space
