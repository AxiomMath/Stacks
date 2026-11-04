module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.FppfLocalTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normal morphisms with locally Noetherian fibres are smooth local on the source

For a morphism of schemes, the property of having locally Noetherian fibres and being normal may
be tested after a smooth covering of the source.

## Main results

* `AlgebraicGeometry.isNormal_isLocal_smooth`: normality of schemes is local in the smooth
  topology.
* `AlgebraicGeometry.isGeometricallyNormal_iff_of_smoothZeroHypercover`: geometric normality over
  a field may be tested on a smooth covering family.
* `AlgebraicGeometry.normalWithLocallyNoetherianFibers_isLocalAtSource_smooth`: the property is
  local on the source for the smooth topology.

## References

* [Stacks Project, Tag 0393](https://stacks.math.columbia.edu/tag/0393)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- Normality of a stalk is unchanged by passing along an open immersion. -/
private theorem isNormalRing_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (x : X) :
    IsNormalRing (X.presheaf.stalk x) ↔ IsNormalRing (Y.presheaf.stalk (j x)) :=
  ⟨IsNormalRing.congr (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm,
    IsNormalRing.congr (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv⟩

/-- An affine scheme is normal exactly when its ring of global sections is a normal ring. -/
private theorem isNormal_iff_isNormalRing_appTop (X : Scheme.{u}) [IsAffine X] :
    IsNormal X ↔ IsNormalRing Γ(X, ⊤) := by
  have h12 := (isNormal_tfae X).out 1 2
  have h13 := (isNormal_tfae X).out 1 3
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact fun p hp ↦ have _ : p.IsPrime := hp; h12.mp h ⟨⊤, isAffineOpen_top X⟩ p
  · refine h13.mpr ⟨ULift.{u} Unit, fun _ ↦ ⟨⊤, isAffineOpen_top X⟩,
      by simp [TopologicalSpace.IsOpenCover], fun _ p hp ↦ ?_⟩
    have _ : p.IsPrime := hp
    exact h p

/-- Normality of schemes is a Zariski local condition. -/
private instance isNormal_isLocal_zariski :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNormal X) Scheme.zariskiPrecoverage := by
  refine ObjectProperty.IsLocal.mk_of_zeroHypercover fun X 𝒰 ↦ ?_
  have hdata : (∀ x : X, ∃ i, x ∈ Set.range (𝒰.f i).base) ∧
      ∀ i, IsOpenImmersion (𝒰.f i) := by
    simpa [Scheme.zariskiPrecoverage] using 𝒰.mem₀
  refine ⟨fun hX i ↦ ?_, fun h ↦ ?_⟩
  · have _ : IsOpenImmersion (𝒰.f i) := hdata.2 i
    exact (AlgebraicGeometry.isNormal_iff_stalk_isNormalRing (𝒰.X i)).2 fun z ↦
      (isNormalRing_stalk_iff_of_isOpenImmersion (𝒰.f i) z).mpr
        ((AlgebraicGeometry.isNormal_iff_stalk_isNormalRing X).mp hX (𝒰.f i z))
  · refine (AlgebraicGeometry.isNormal_iff_stalk_isNormalRing X).2 fun x ↦ ?_
    obtain ⟨i, z, hz⟩ := hdata.1 x
    have _ : IsOpenImmersion (𝒰.f i) := hdata.2 i
    rw [← hz]
    exact (isNormalRing_stalk_iff_of_isOpenImmersion (𝒰.f i) z).mp
      ((AlgebraicGeometry.isNormal_iff_stalk_isNormalRing (𝒰.X i)).mp (h i) z)

/-- Smooth covering families are stable under base change. -/
public instance smoothPrecoverage_isStableUnderBaseChange :
    (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).IsStableUnderBaseChange :=
  precoverage_isStableUnderBaseChange _

/-- Normality of schemes is local in the smooth topology. -/
@[stacks 034F, sga "3 X 8.9" "more general"]
public instance isNormal_isLocal_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNormal X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) := by
  refine isLocal_smoothPrecoverage_of_affine (fun X : Scheme.{u} => IsNormal X) ?_ ?_
  · intro X S hX hS f hsm hSnormal
    have _ : IsAffine X := hX
    have _ : IsAffine S := hS
    have _ : Smooth f := hsm
    have hmap : (f.appTop).hom.Smooth := by
      simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        hsm.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl
    let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have _ : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) := RingHom.smooth_algebraMap.mp hmap
    exact (isNormal_iff_isNormalRing_appTop X).mpr
      (Algebra.isNormalRing_of_smooth Γ(S, ⊤) Γ(X, ⊤)
        ((isNormal_iff_isNormalRing_appTop S).mp hSnormal))
  · intro X S hX hS f hsm hsurj hXnormal
    have _ : IsAffine X := hX
    have _ : IsAffine S := hS
    have _ : Smooth f := hsm
    let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have _ : Module.FaithfullyFlat Γ(S, ⊤) Γ(X, ⊤) := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      simpa [RingHom.algebraMap_toAlgebra] using
        (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, hsurj⟩
    exact (isNormal_iff_isNormalRing_appTop S).mpr
      (isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
        ((isNormal_iff_isNormalRing_appTop X).mp hXnormal))

/-- Geometric normality of a scheme over a field may be tested on a smooth covering family of the
scheme. -/
public theorem isGeometricallyNormal_iff_of_smoothZeroHypercover {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (𝒰 : (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).ZeroHypercover X) :
    IsGeometricallyNormal f ↔ ∀ i, IsGeometricallyNormal (𝒰.f i ≫ f) := by
  have hX := (geometricallyNormal_tfae k X f).out 1 2
  have key : ∀ (K : Type u) [Field K] [Algebra k K],
      IsNormal (pullback f (Spec.map (ofHom (algebraMap k K)))) ↔
        ∀ i, IsNormal (pullback (𝒰.f i ≫ f) (Spec.map (ofHom (algebraMap k K)))) := by
    intro K _ _
    refine (ObjectProperty.iff_of_zeroHypercover (P := fun Z : Scheme.{u} ↦ IsNormal Z)
      (𝒰.pullback₁ (pullback.fst f (Spec.map (ofHom (algebraMap k K)))))).trans
      (forall_congr' fun i ↦ ?_)
    have he := compPullbackIso f (Spec.map (ofHom (algebraMap k K))) (𝒰.f i)
    exact ObjectProperty.prop_iff_of_iso (fun Z : Scheme.{u} ↦ IsNormal Z) he
  have hXi : ∀ i, _ := fun i ↦ (geometricallyNormal_tfae k (𝒰.X i) (𝒰.f i ≫ f)).out 1 2
  rw [hX]
  exact ⟨fun h i ↦ (hXi i).mpr fun K _ _ ↦ (key K).mp (h K) i,
    fun h K _ _ ↦ (key K).mpr fun i ↦ (hXi i).mp (h i) K⟩

/-- The fibres of a morphism of schemes are geometrically normal exactly when the fibres of the
members of a smooth covering family of the source are. -/
private theorem geometricallyNormalFibers_iff_of_smoothZeroHypercover {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (𝒰 : (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).ZeroHypercover X) :
    (∀ y : Y, IsGeometricallyNormal (f.fiberToSpecResidueField y)) ↔
      ∀ i, ∀ y : Y, IsGeometricallyNormal ((𝒰.f i ≫ f).fiberToSpecResidueField y) := by
  rw [forall_comm]
  refine forall_congr' fun y ↦ ?_
  refine (isGeometricallyNormal_iff_of_smoothZeroHypercover
    (f.fiberToSpecResidueField y) (𝒰.pullback₁ (f.fiberι y))).trans
    (forall_congr' fun i ↦ ?_)
  show IsGeometricallyNormal (pullback.fst (pullback.fst f (Y.fromSpecResidueField y))
      (𝒰.f i) ≫ pullback.snd f (Y.fromSpecResidueField y)) ↔
    IsGeometricallyNormal (pullback.snd (𝒰.f i ≫ f) (Y.fromSpecResidueField y))
  exact isGeometricallyNormal_iff_of_isoOver _ _
    (compPullbackIso f (Y.fromSpecResidueField y) (𝒰.f i))
    (compPullbackIso_hom_snd f (Y.fromSpecResidueField y) (𝒰.f i))

/-- Normality of a morphism of schemes is local on the source for the smooth topology. -/
public instance normalMorphisms_isLocalAtSource_smooth :
    (normalMorphisms : MorphismProperty Scheme.{u}).IsLocalAtSource
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) := by
  have hflatLocal : MorphismProperty.IsLocalAtSource
      (@Flat : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.smoothPrecoverage_le_fpqcPrecoverage
  have _ : MorphismProperty.RespectsIso (normalMorphisms : MorphismProperty Scheme.{u}) :=
    inferInstance
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒰
  calc (normalMorphisms f)
      ↔ Flat f ∧ ∀ y : Y, IsGeometricallyNormal (f.fiberToSpecResidueField y) :=
        Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers f
    _ ↔ (∀ i, Flat (𝒰.f i ≫ f)) ∧
        ∀ i, ∀ y : Y, IsGeometricallyNormal ((𝒰.f i ≫ f).fiberToSpecResidueField y) :=
        (MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover (P := @Flat) 𝒰).and
          (geometricallyNormalFibers_iff_of_smoothZeroHypercover f 𝒰)
    _ ↔ ∀ i, Flat (𝒰.f i ≫ f) ∧
        ∀ y : Y, IsGeometricallyNormal ((𝒰.f i ≫ f).fiberToSpecResidueField y) :=
        Iff.symm forall_and
    _ ↔ ∀ i, normalMorphisms (𝒰.f i ≫ f) :=
        forall_congr' fun i ↦
          (Scheme.Hom.isNormal_iff_flat_and_geometricallyNormalFibers (𝒰.f i ≫ f)).symm

/-- Having locally Noetherian fibres and being normal is local on
the source for the smooth topology. -/
@[stacks 0393 "smooth local on the source"]
public instance normalWithLocallyNoetherianFibers_isLocalAtSource_smooth :
    (normalWithLocallyNoetherianFibers : MorphismProperty Scheme.{u}).IsLocalAtSource
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) := by
  have _ : MorphismProperty.IsLocalAtSource
      (locallyNoetherianFibers : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  infer_instance

end AlgebraicGeometry
