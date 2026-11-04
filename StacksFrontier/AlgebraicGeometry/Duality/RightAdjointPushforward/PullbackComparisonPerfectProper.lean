module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekComparisonLocal

/-!
# Equation 48.8.0.1 for a perfect proper morphism of Noetherian schemes

Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes. The comparison map
`Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` of [Stacks, Tag 0A9S] is an isomorphism for every `K ∈ D_QCoh(𝒪_Y)`
([Stacks, Tag 0A9U]). For `K` bounded below the question is local on
`Y` ([Stacks, Tag 0A9P]), and over an affine base it is
`Stacks.Duality.isIso_comparisonMap_of_isAffine`. The compact objects of `D_QCoh(𝒪_Y)` are
bounded below, so the map is invertible at every shift of a compact generating family
([Stacks, Tag 09IS]); both sides being exact and commuting with direct sums, it is then invertible
everywhere.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open MonoidalCategory Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [Perfect f] [IsProper f]

/-- **The comparison map `Lf^*K ⊗ a(𝒪_Y) ⟶ a(K ⊗ 𝒪_Y)` for `K` bounded below**, `f` perfect and
proper and `Y` Noetherian: invertibility is local on `Y`, and holds over affine opens. -/
theorem isIso_comparisonMap_structureSheaf_of_isBoundedBelow
    (K : quasiCoherentDerivedCategory Y) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comparisonMap
      (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        K (derivedStructureSheaf Y)) := by
  have hO := Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj
    (SheafOfModules.unit Y.ringCatSheaf)
  refine isIso_of_forall_isIso_quasiCoherentDerivedPullback (fun V : Y.affineOpens => f ⁻¹ᵁ V.1)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.1) _ fun V => ?_
  have : IsAffine V.1.toScheme := V.2
  have : IsNoetherian V.1.toScheme := isNoetherian_of_isOpenImmersion V.1.ι
  have sq := (isPullback_morphismRestrict f V.1).flip
  have : IsProper (f ∣_ V.1) := MorphismProperty.of_isPullback sq inferInstance
  have : Perfect (f ∣_ V.1) := perfect_of_isPullback_of_flat sq
  have : IsNoetherian (f ⁻¹ᵁ V.1).toScheme := isNoetherian_of_isProper (f ∣_ V.1)
  exact (isIso_map_comparisonMap_baseChange_iff (f ⁻¹ᵁ V.1).ι (f ∣_ V.1) f V.1.ι sq (𝟭 _) K
    (derivedStructureSheaf Y) hO (isBoundedBelow_tensor_derivedStructureSheaf K hK)).2
    (isIso_comparisonMap_of_isAffine (f ∣_ V.1) _ _)

/-- **Stacks Project, Tag 0A9U (Lemma 48.13.3).** Let `f : X ⟶ Y` be a perfect proper morphism of
Noetherian schemes. The map `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of [Stacks, Tag 0A9S] is an
isomorphism for every object `K` of `D_QCoh(𝒪_Y)`. -/
@[stacks 0A9U]
theorem isIso_twistedInverseImageCompareWithPullback_of_perfect_of_isProper
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (twistedInverseImageCompareWithPullback f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (quasiCoherentDerivedPullbackTensorIso f).hom
      (quasiCoherentDerivedTensorRightUnitor Y) K) := by
  let hpull := isQuasicoherent_homology_derivedPullback' f
  let hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let α := (quasiCoherentDerivedPullbackTensorIso f).hom
  have hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
      (quasiCoherentDerivedPullback f hpull).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback f hpull) Q P ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
          ((quasiCoherentDerivedPullback f hpull).obj Q)).app
          ((quasiCoherentDerivedPullback f hpull).obj P) := fun _ _ => rfl
  let ρ := quasiCoherentDerivedTensorRightUnitor Y
  let adj := twistedInverseImageAdjunction f hpush
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  have : (twistedInverseImage f hpush).IsTriangulated := adj.isTriangulated_rightAdjoint
  have hsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (twistedInverseImage f hpush) :=
    preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_hpush f hpush adj
  let e := (twistedInverseImageTensorRightIso f hpush ρ).symm
  let := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have : (quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙
      twistedInverseImage f hpush).IsTriangulated := Functor.isTriangulated_of_iso e
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙
        twistedInverseImage f hpush) := fun J =>
    have := hsum J
    preservesColimitsOfShape_of_natIso e
  obtain ⟨ι, E, hEc, hE⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory Y
  have : ObjectProperty.IsTriangulated (IsCompactObject.{u, _, _}
      (C := quasiCoherentDerivedCategory Y)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := quasiCoherentDerivedCategory Y)).2.1
  have h₁ : IsIso (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y)) := by
    refine isIso_compareWithPullbackTensor_of_forall_shift f hpush α adj
      (derivedStructureSheaf Y) E hEc hE (fun i n => ?_) K
    have hc : IsCompactObject.{u} ((E i)⟦n⟧) := ObjectProperty.le_shift
      (IsCompactObject.{u, _, _} (C := quasiCoherentDerivedCategory Y)) n _ (hEc i)
    have h := isIso_comparisonMap_structureSheaf_of_isBoundedBelow f ((E i)⟦n⟧)
      (isBoundedBelow_of_isCompactObject _ hc)
    rw [compareWithPullbackTensor_eq_comparisonMap f hpush α hα adj]
    infer_instance
  have h₂ : IsIso ((twistedInverseImage f hpush).map (ρ.hom.app K)) := inferInstance
  change IsIso (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
    (twistedInverseImage f hpush).map (ρ.hom.app K))
  infer_instance

end Stacks.Duality

end
