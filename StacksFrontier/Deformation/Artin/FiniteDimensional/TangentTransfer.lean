module

public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective
public import StacksFrontier.Deformation.VersalObject.ChangeOfFieldsTangentSpace
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction

/-!
# Transporting finite-dimensionality of tangent spaces

Finite-dimensionality of the tangent space of a deformation category is carried along a smooth
`1`-morphism into it (Stacks 06HN and 06IJ), back along a fully faithful `1`-morphism out of it,
and down a field extension (Stacks 07WB).

## Main results

* `Deformation.finiteDimensional_of_finiteDimensional_tensorProduct`: a vector space whose scalar
  extension along a field extension is finite-dimensional is finite-dimensional.
* `Deformation.essSurj_of_isSmooth_of_isPredeformationCategory`: a smooth `1`-morphism of
  predeformation categories is essentially surjective.
* `Deformation.finiteDimensional_tangentModuleAt_of_isSmooth`: finite-dimensionality of tangent
  modules passes to the target of a smooth `1`-morphism.
* `Deformation.finiteDimensional_tangentModuleAt_of_fullyFaithful`: finite-dimensionality of
  tangent modules passes to the source of a fully faithful `1`-morphism.
* `Deformation.finiteDimensional_artinianTangentSpace_iff_tangentModuleAt`: the tangent space is
  finite-dimensional exactly when the tangent module at `k` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

universe u w u₁ v₁ u₂ v₂

/-- A vector space whose scalar extension along a field extension is finite-dimensional is
itself finite-dimensional. -/
theorem finiteDimensional_of_finiteDimensional_tensorProduct {k l V : Type*} [Field k] [Field l]
    [Algebra k l] [AddCommGroup V] [Module k V]
    (h : FiniteDimensional l (TensorProduct k l V)) : FiniteDimensional k V := by
  have h' : Module.rank l (TensorProduct k l V) < Cardinal.aleph0 :=
    Module.rank_lt_aleph0_iff.mpr h
  rw [Module.rank_baseChange] at h'
  exact Module.rank_lt_aleph0_iff.mp (Cardinal.lift_lt_aleph0.mp h')

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- **Stacks 06HN** for predeformation categories: a smooth `1`-morphism of predeformation
categories is essentially surjective. -/
theorem essSurj_of_isSmooth_of_isPredeformationCategory (φ : 𝓕 ⥤ᵇ 𝓖)
    (h𝓕 : IsPredeformationCategory 𝓕.p) (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hφ : IsSmooth φ) : φ.toFunctor.EssSurj := by
  refine essSurj_of_isSmooth_of_fiber_essSurj φ h𝓖.cofibered hφ ⟨fun y => ?_⟩
  obtain ⟨E⟩ := h𝓕.specialFiber
  let x := E.inverse.obj ⟨PUnit.unit⟩
  obtain ⟨i, -⟩ := existsUnique_pointIso.{u, w, w} h𝓖 ((fiberFunctor φ _).obj x) y
  exact ⟨x, ⟨i⟩⟩

/-- The tangent module of the target of a smooth `1`-morphism of deformation categories is
finite-dimensional when that of the source is. -/
theorem finiteDimensional_tangentModuleAt_of_isSmooth (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p) (φ : 𝓕 ⥤ᵇ 𝓖) (hφ : IsSmooth φ)
    (M : FGModuleCat.{w} k) (hfin : FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓖 h𝓖 M) := by
  have := essSurj_of_isSmooth_of_isPredeformationCategory φ h𝓕.predeformation
    h𝓖.predeformation hφ
  exact Module.Finite.of_surjective _ (tangentMapAt_surjective_of_essSurj.{u, w, w} h𝓕 h𝓖 φ M)

/-- The tangent module of the source of a fully faithful `1`-morphism of deformation categories
is finite-dimensional when that of the target is. -/
theorem finiteDimensional_tangentModuleAt_of_fullyFaithful
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) [φ.toFunctor.Full] [φ.toFunctor.Faithful] (M : FGModuleCat.{w} k)
    (hfin : FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓖 h𝓖 M)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M) := by
  let A := (squareZeroExtensionArtinian.{u, w, w} Λ k).obj M
  have : (fiberFunctor φ A).Full := full_fiberFunctor φ A
  have : (fiberFunctor φ A).Faithful := faithful_fiberFunctor φ A
  refine Module.Finite.of_injective (tangentMapAt.{u, w, w} h𝓕 h𝓖 φ M) ?_
  intro s t hst
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M s
  obtain ⟨y, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M t
  rw [tangentMapAt_tangentClassAt, tangentMapAt_tangentClassAt,
    tangentClassAt_eq_iff] at hst
  obtain ⟨i⟩ := hst
  exact (tangentClassAt_eq_iff.{u, w, w} 𝓕 h𝓕 M x y).mpr ⟨(fiberFunctor φ A).preimageIso i⟩

/-- The lifted tangent space `tangentSpaceArtinian` of a deformation category is
finite-dimensional as soon as its tangent module at the rank-one module `ULift k` is. -/
theorem finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
    (hfin : FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕
      (FGModuleCat.of k (ULift.{w} k)))) :
    letI : Fact (IsPredeformationCategory.{u, w, w} (BasedCategory.ofFunctor 𝓕.p).p) :=
      ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor 𝓕.p) h𝓕.predeformation.cofibered))) :=
      ⟨tangentConditionS2.{u, w, w} h𝓕⟩
    FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor 𝓕.p) h𝓕.predeformation.cofibered)) := by
  let : Fact (IsPredeformationCategory.{u, w, w} 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨tangentConditionS2.{u, w, w} h𝓕⟩
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, w, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, w, w} h𝓕)).finiteDimensional

/-- The unlifted tangent space `artinianTangentSpace` of a deformation category is
finite-dimensional exactly when its tangent module at the rank-one module `k` is. -/
theorem finiteDimensional_artinianTangentSpace_iff_tangentModuleAt
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨tangentConditionS2.{u, w, w} h𝓕⟩
    FiniteDimensional k (artinianTangentSpace Λ k
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) ↔
      FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 (FGModuleCat.of k k)) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨tangentConditionS2.{u, w, w} h𝓕⟩
  let e := associatedTangentSpaceCarrierLinearEquivUnlifted 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, w, w} h𝓕)
  exact ⟨fun _ => Module.Finite.equiv e.symm,
    fun h => by
      have : Module.Finite k ↥((associatedTangentSpaceModuleStructureUnlifted 𝓕
          h𝓕.predeformation (tangentConditionS2.{u, w, w} h𝓕)).functor.obj
          (FGModuleCat.of k k)) := h
      exact Module.Finite.equiv e⟩

/-- The tangent module of a deformation category at the rank-one module `ULift k` is
finite-dimensional exactly when its tangent module at `k` is. -/
theorem finiteDimensional_tangentModuleAt_uLift_iff (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p) :
    FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 (FGModuleCat.of k (ULift.{w} k))) ↔
      FiniteDimensional k ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 (FGModuleCat.of k k)) := by
  let e := ((associatedTangentSpaceModuleStructure.{u, w, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, w, w} h𝓕)).functor.mapIso fgModuleCatULiftSelfIso).toLinearEquiv
  exact ⟨fun _ => e.finiteDimensional, fun _ => e.symm.finiteDimensional⟩

end

end Deformation
