module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleLength
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated

/-!
# The cycle of a closed subspace does not depend on the ambient space

In Situation 0EDT let `X/B` be good and let `Y ⊆ X` be a closed subspace. A closed subspace
`A ⊆ Y` is, through `Y → X`, also a closed subspace of `X`, but as a subfunctor of `X` it is a
different presheaf `A''`, isomorphic to `A` over `X`. The `k`-cycle `[A]_k` of Stacks 0EE9 may
be formed in `Y` and pushed forward to `X`, or formed in `X` from `A''`. This file proves the two
agree. The comparison is used whenever two constructions of the source form the "same"
intersection in different ambient spaces, for instance `D ∩ W` as a closed subspace of the
vanishing locus `D` (Stacks 0ER1) and as the zero scheme `Z(s|_W)` on `W` (Stacks 0EQL).

## Main results

* `AlgebraicGeometry.Space.geometricLength_unit_eq_of_isIso`: the length of the structure sheaf
  at a geometric point is invariant under an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq`: the
  pushforward along `Y → X` of `[A]_k` formed in `Y` is `[A'']_k` formed in `X`.

## Implementation notes

The invariance of the length is read off Stacks 02M1 along a flat morphism,
`AlgebraicGeometry.Space.geometricLength_mul_length_quotient_extendedMaximalIdeal`. An
isomorphism is flat, and the colength of the extended maximal ideal along a local homomorphism
is at least one. So pulling back along the isomorphism and along its inverse gives the two
inequalities, without computing the colength.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section IsoLength

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The colength of the extended maximal ideal along a local homomorphism of local rings is
positive: the extended ideal is proper. -/
theorem one_le_length_quotient_map_maximalIdeal {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (φ : R →+* T) [IsLocalHom φ] :
    1 ≤ Module.length T (T ⧸ Ideal.map φ (maximalIdeal R)) := by
  have hle : Ideal.map φ (maximalIdeal R) ≤ maximalIdeal T :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  have hne : Ideal.map φ (maximalIdeal R) ≠ ⊤ := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal T).ne_top hle
  have : Nontrivial (T ⧸ Ideal.map φ (maximalIdeal R)) := Ideal.Quotient.nontrivial_iff.2 hne
  exact Order.one_le_iff_pos.2 Module.length_pos

/-- The length of the structure sheaf at a geometric point is at most its length after
pullback along a flat morphism: the length multiplies by the positive colength of the extended
maximal ideal, Stacks 02M1. -/
theorem geometricLength_unit_le_of_isFlat {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) (x : GeometricPoint B S hS X.1) :
    geometricLength B S hS Y (geometricPointMap f.hom x) (SheafOfModules.unit _) ≤
      geometricLength B S hS X x (SheafOfModules.unit _) := by
  have : IsLocalRing ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)) :=
    isLocalRing_etaleLocalRing B S hS Y.1 Y.2 (geometricPointMap f.hom x)
  have : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  have : IsLocalHom (etaleLocalRingMap X.2 f.hom x) :=
    isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom x
  have h := geometricLength_mul_length_quotient_extendedMaximalIdeal B S hS f hf x
    (SheafOfModules.unit _)
  rw [geometricLength_eq_of_iso B S hS X x (modulePullbackUnitIso B S hS f)] at h
  rw [← h]
  exact le_mul_of_one_le_right' (one_le_length_quotient_map_maximalIdeal _)

/-- **The length of the structure sheaf is invariant under an isomorphism of algebraic
spaces.** -/
theorem geometricLength_unit_eq_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [IsIso f.hom] (x : GeometricPoint B S hS X.1) :
    geometricLength B S hS Y (geometricPointMap f.hom x) (SheafOfModules.unit _) =
      geometricLength B S hS X x (SheafOfModules.unit _) := by
  let g : Y ⟶ X := ObjectProperty.homMk (inv f.hom)
  have hfl : IsFlat B S hS f.hom := isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS f.hom)
  have hgl : IsFlat B S hS g.hom := isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS (inv f.hom))
  refine le_antisymm (geometricLength_unit_le_of_isFlat B S hS f hfl x) ?_
  have h := geometricLength_unit_le_of_isFlat B S hS g hgl (geometricPointMap f.hom x)
  have hx : geometricPointMap g.hom (geometricPointMap f.hom x) = x := by
    change geometricPointMap (f.hom ≫ inv f.hom) x = x
    rw [IsIso.hom_inv_id]
    rfl
  rwa [hx] at h

end IsoLength

section Ambient

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Two integral closed subspaces with the same point set are equal. -/
theorem IntegralClosedSubspace.eq_of_subspacePointSet_eq (hX : IsAlgebraicSpace D.site D.base
    D.base_mem X) {Z W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : subspacePointSet D.site D.base D.base_mem X Z.subspace =
      subspacePointSet D.site D.base D.base_mem X W.subspace) : Z = W :=
  injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX (IrreducibleCloseds.ext h)

variable (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (hYg : D.IsGood (Y.ι ≫ sX))
    (A : Subfunctor Y.toFunctor) (hA : IsClosedSubspace D.site D.base D.base_mem A)
    (A'' : Subfunctor X) (hA'' : IsClosedSubspace D.site D.base D.base_mem A'')
    (φ : A.toFunctor ⟶ A''.toFunctor) [IsIso φ] (hφ : φ ≫ A''.ι = A.ι ≫ Y.ι) (k : ℤ)

include hφ in
/-- The image in `X` of the image in `Y` of an integral closed subspace of `A` is the image in
`X` of its transport to `A''`. -/
theorem pushforward_closedSubspaceComponentImage_eq
    (V : IntegralClosedSubspace D.site D.base D.base_mem A.toFunctor) :
    IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2
        (closedSubspaceComponentImage D (Y.ι ≫ sX) hYg A hA V) =
      closedSubspaceComponentImage D sX hX A'' hA''
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hA''.1 hA.1
          (D.isDecentSpace_of_isGood _ (isGood_closedSubspace D sX hX ⟨A'', hA''⟩))
          (isClosedImmersion_of_isIso D.site D.base D.base_mem φ) V) := by
  apply IntegralClosedSubspace.eq_of_subspacePointSet_eq D hX.1
  simp only [closedSubspaceComponentImage, IntegralClosedSubspace.subspacePointSet_pushforward,
    Set.image_image]
  exact Set.image_congr fun x _ => (pointsMap_apply_comm D.site D.base D.base_mem hφ x).symm

include hφ in
/-- **The cycle of a closed subspace does not depend on the ambient space.** Let `Y ⊆ X` be a
closed subspace, `A ⊆ Y` a closed subspace of `Y` and `A'' ⊆ X` a closed subspace of `X`
isomorphic to `A` over `X`. Then the pushforward along `Y → X` of the cycle `[A]_k` formed in
`Y` is the cycle `[A'']_k` formed in `X`: the components correspond under the isomorphism and
the multiplicities, lengths of the structure sheaves at their generic points, agree by
`AlgebraicGeometry.Space.geometricLength_unit_eq_of_isIso`. -/
theorem cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq :
    cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (cycleCoeffOfClosedSubspace D (Y.ι ≫ sX) hYg A hA k
          (canonicalGeometricPoint D.site D.base D.base_mem A.toFunctor)) =
      cycleCoeffOfClosedSubspace D sX hX A'' hA'' k
        (canonicalGeometricPoint D.site D.base D.base_mem A''.toFunctor) := by
  have hAg : D.IsGood (A.ι ≫ Y.ι ≫ sX) := isGood_closedSubspace D (Y.ι ≫ sX) hYg ⟨A, hA⟩
  have hA''g : D.IsGood (A''.ι ≫ sX) := isGood_closedSubspace D sX hX ⟨A'', hA''⟩
  have hAdec := D.isDecentSpace_of_isGood _ hAg
  have hA''dec := D.isDecentSpace_of_isGood _ hA''g
  have hφi := isClosedImmersion_of_isIso D.site D.base D.base_mem φ
  have hψi := isClosedImmersion_of_isIso D.site D.base D.base_mem (inv φ)
  -- transport of integral closed subspaces between `A` and `A''`
  set tr := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hA''.1 hA.1 hA''dec hφi
  set tr' := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hA.1 hA''.1 hAdec hψi
  have htr : ∀ V'', tr (tr' V'') = V'' := fun V'' => by
    apply IntegralClosedSubspace.eq_of_subspacePointSet_eq D hA''.1
    simp only [tr, tr', IntegralClosedSubspace.subspacePointSet_pushforward, Set.image_image]
    conv_rhs => rw [← Set.image_id (subspacePointSet D.site D.base D.base_mem _ V''.subspace)]
    refine Set.image_congr fun x _ => ?_
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id_apply]
    rfl
  funext Z
  by_cases hex : ∃ V'', closedSubspaceComponentImage D sX hX A'' hA'' V'' = Z
  · obtain ⟨V'', rfl⟩ := hex
    have hV : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2
        (closedSubspaceComponentImage D (Y.ι ≫ sX) hYg A hA (tr' V'')) =
          closedSubspaceComponentImage D sX hX A'' hA'' V'' :=
      (pushforward_closedSubspaceComponentImage_eq D sX hX Y hY hYg A hA A'' hA'' φ hφ
        (tr' V'')).trans (congrArg _ (htr V''))
    rw [cycleCoeffOfClosedSubspace_closedSubspaceComponentImage D sX hX A'' hA'', ← hV,
      cycleClosedPushforward_apply_pushforward,
      cycleCoeffOfClosedSubspace_closedSubspaceComponentImage,
      IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2]
    congr 2
    -- the multiplicities agree
    have hgen : (tr' V'').ambientGenericPoint D.site D.base D.base_mem =
        pointsMap D.site D.base D.base_mem _ (inv φ)
          (V''.ambientGenericPoint D.site D.base D.base_mem) :=
      IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hA.1
        hA''.1 hAdec hψi V''
    have : (SheafOfModules.unit _ : Modules.{u, u} D.site D.base D.base_mem A.toFunctor
        hA.1).IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
    rw [geometricLength_eq_of_image_eq D.site D.base D.base_mem hA.1 _
      (geometricPointMap (inv φ) (canonicalGeometricPoint D.site D.base D.base_mem _
        (V''.ambientGenericPoint D.site D.base D.base_mem)))
      (by rw [canonicalGeometricPoint_image, geometricPointMap_image, canonicalGeometricPoint_image,
        hgen]) (SheafOfModules.unit _)]
    have : IsIso (ObjectProperty.homMk (inv φ) : (⟨A''.toFunctor, hA''.1⟩ :
        AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨A.toFunctor, hA.1⟩).hom :=
      inferInstanceAs (IsIso (inv φ))
    exact congrArg ENat.toNat (geometricLength_unit_eq_of_isIso D.site D.base D.base_mem
      (X := ⟨A''.toFunctor, hA''.1⟩) (Y := ⟨A.toFunctor, hA.1⟩) (ObjectProperty.homMk (inv φ)) _)
  · rw [cycleCoeffOfClosedSubspace_eq_zero D sX hX A'' hA'' k _ Z fun V'' h => hex ⟨V'', h⟩]
    by_cases hZ : ∃ ZY, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 ZY = Z
    · obtain ⟨ZY, rfl⟩ := hZ
      rw [cycleClosedPushforward_apply_pushforward]
      refine cycleCoeffOfClosedSubspace_eq_zero D (Y.ι ≫ sX) hYg A hA k _ ZY fun V hV => hex ?_
      exact ⟨tr V, by rw [← hV]; exact
        (pushforward_closedSubspaceComponentImage_eq D sX hX Y hY hYg A hA A'' hA'' φ hφ V).symm⟩
    · exact cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ Z
        fun ZY h => hZ ⟨ZY, h⟩

end Ambient

end AlgebraicGeometry.Space

end
