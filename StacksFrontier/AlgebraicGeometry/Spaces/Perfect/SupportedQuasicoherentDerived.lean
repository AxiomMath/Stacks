module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportTriangles
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded

/-!
# The category `D_{QCoh,T}(𝒪_X)` and its direct sums

Let `X` be an algebraic space over a scheme `S` and `T ⊆ |X|` a closed subset. The objects of
`D(𝒪_X)` whose cohomology sheaves are supported on `T` form a strictly full triangulated
subcategory `D_T(𝒪_X)`, and, since taking cohomology sheaves commutes with direct sums, it is
closed under direct sums in `D(𝒪_X)`. Intersecting with `D_QCoh(𝒪_X)` gives `D_{QCoh,T}(𝒪_X)`,
which is closed under direct sums in `D_QCoh(𝒪_X)`; so `D_{QCoh,T}(𝒪_X)` has direct sums and they
are those of `D_QCoh(𝒪_X)` and of `D(𝒪_X)`. This is the remark of the source preceding Stacks
0AED.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedSupportedOn`: the property of an object of
  `D_QCoh(𝒪_X)` of having cohomology sheaves supported on `T`; its full subcategory is
  `D_{QCoh,T}(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isTriangulated_cohomologySupportedOn`: `D_T(𝒪_X)` is a triangulated
  subcategory of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.supportOfSheaf_sigma_subset`: the support of a direct sum of
  `𝒪_X`-modules supported on a closed `T` is contained in `T`.
* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_cohomologySupportedOn`: `D_T(𝒪_X)` is
  closed under direct sums in `D(𝒪_X)`.
* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn`:
  `D_{QCoh,T}(𝒪_X)` is closed under direct sums in `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0AED](https://stacks.math.columbia.edu/tag/0AED)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 08F3](https://stacks.math.columbia.edu/tag/08F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Support on `T` is invariant under isomorphism in `D(𝒪_X)`. -/
instance isClosedUnderIsomorphisms_cohomologySupportedOn (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    ObjectProperty.IsClosedUnderIsomorphisms (CohomologySupportedOn B S hS X.1 X.2 T) where
  of_iso e h := cohomologySupportedOn_of_iso' B S hS e h

/-- **`D_T(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`**: it contains zero, is stable under
the shifts, and contains the middle object of a distinguished triangle whose two other objects it
contains. -/
instance isTriangulated_cohomologySupportedOn (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    ObjectProperty.IsTriangulated (CohomologySupportedOn B S hS X.1 X.2 T) where
  exists_zero := ⟨0, isZero_zero _, fun i =>
    ((supportOfSheaf_eq_empty_iff_isZero B S hS X _).2
      ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))).le.trans
      (Set.empty_subset _)⟩
  isStableUnderShiftBy n := ⟨fun E h => cohomologySupportedOn_shift B S hS X T E h n⟩
  ext₂' Tri hTri h₁ h₃ := ObjectProperty.le_isoClosure _ _
    (cohomologySupportedOn_obj₂_of_distinguished B S hS X.1 X.2 T Tri hTri h₁ h₃)

/-- **The support of a direct sum of modules supported on a closed `T` lies in `T`.** -/
theorem supportOfSheaf_sigma_subset (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))
    (hT : IsClosed T) {J : Type u} (M : J → Modules.{u, u} B S hS X.1 X.2) [HasCoproduct M]
    (hM : ∀ j, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
        (M j)) ⊆ T) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj
        (∐ M)) ⊆ T := by
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  let jV := openSubspaceHom B S hS G.1 G.2
  have hjV : IsEtale B S hS jV.hom := isEtale_openSubspaceHom B S hS G.1 G.2
  have hrange : Set.range (pointsMap B S hS (openSubspaceSpace B S hS G.1 G.2).1 jV.hom) = Tᶜ :=
    range_openSubspacesOrderIso_symm B S hS X.1 X.2 T hT
  let L := etaleModulePullback.{u, u} B S hS jV hjV
  have : PreservesColimitsOfShape (Discrete J) L :=
    (etaleModulePullbackAdjunction B S hS jV hjV).leftAdjoint_preservesColimits.1
  have hzero : ∀ j, IsZero (L.obj (M j)) := fun j =>
    (isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS jV hjV (M j)).2
      (hrange ▸ Set.disjoint_compl_right_iff_subset.2 (hM j))
  have hc := isColimitOfPreserves L (coproductIsCoproduct M)
  have hL : IsZero (L.obj (∐ M)) := by
    rw [IsZero.iff_id_eq_zero]
    exact hc.hom_ext fun j => (hzero j.as).eq_of_src _ _
  have h := (isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS jV hjV (∐ M)).1 hL
  rwa [hrange, Set.disjoint_compl_right_iff_subset] at h

/-- **`D_T(𝒪_X)` is closed under direct sums in `D(𝒪_X)`**, for `T` closed. -/
theorem isClosedUnderColimitsOfShape_cohomologySupportedOn (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (J : Type u) :
    ObjectProperty.IsClosedUnderColimitsOfShape (CohomologySupportedOn B S hS X.1 X.2 T)
      (Discrete J) := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨G, hG⟩ n
  refine (supportOfSheaf_eq_of_iso B S hS X
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).mapIso
        (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := G))) ≪≫
      Stacks.Duality.isoCoproductHomologyDerived (Modules.{u, u} B S hS X.1 X.2)
        (fun i => G.obj ⟨i⟩) n)).le.trans ?_
  exact supportOfSheaf_sigma_subset X T hT _ fun i => hG ⟨i⟩ n

/-- **`D_{QCoh,T}(𝒪_X)`.** The property of an object of `D_QCoh(𝒪_X)` of having all of its
cohomology sheaves supported on `T ⊆ |X|`; its full subcategory is `D_{QCoh,T}(𝒪_X)`. -/
abbrev quasicoherentDerivedSupportedOn (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    ObjectProperty (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
  ObjectProperty.inverseImage (CohomologySupportedOn B S hS X.1 X.2 T) (ObjectProperty.ι _)

/-- **`D_{QCoh,T}(𝒪_X)` is closed under direct sums in `D_QCoh(𝒪_X)`**, for `T` closed. Direct
sums in `D_QCoh(𝒪_X)` are direct sums in `D(𝒪_X)` (Stacks 08F3), and `D_T(𝒪_X)` is closed under
those. -/
theorem isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (J : Type u) :
    (quasicoherentDerivedSupportedOn X T).IsClosedUnderColimitsOfShape (Discrete J) := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS X.1 X.2 J
    fun M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS X.1 X.2
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2) M hM
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := isClosedUnderColimitsOfShape_cohomologySupportedOn X T hT J
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  exact ObjectProperty.prop_of_iso (CohomologySupportedOn B S hS X.1 X.2 T)
    (preservesColimitIso (ObjectProperty.ι _) F).symm
    (ObjectProperty.prop_colimit (CohomologySupportedOn B S hS X.1 X.2 T) _ fun j => hF j)

end AlgebraicGeometry.Space

end
