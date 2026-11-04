module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoherentTorAmplitudePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeNoetherianTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportDerivedPushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorProperSupport

/-!
# Perfectness of `Rf_*(E ⊗^L 𝒢^•)` over a Noetherian base

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` locally of finite type, quasi-compact and
quasi-separated, `E` a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded complex of coherent
`𝒪_X`-modules flat over `Y` with support proper over `Y`. Then `Rf_*(E ⊗^L 𝒢^•)` is a perfect
object of `D(𝒪_Y)`.

`E ⊗^L 𝒢^•` is bounded with coherent cohomology whose supports are proper over `Y`, so its direct
image is bounded with coherent cohomology; its Tor amplitude is finite by the projection formula
(Stacks 08IN) and the test of Stacks 08IL; coherent cohomology and finite Tor amplitude give
perfectness on a locally Noetherian space (Stacks 08G8, 066E, 0658). This is the case of the
Noetherian base used in the proof of Stacks 0A1P.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_tensor_of_isNoetherian`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*(E ⊗^L 𝒢^•)` is perfect over a Noetherian base**, for `f` locally of finite type,
quasi-compact and quasi-separated, `E` perfect and `𝒢^•` a bounded complex of coherent modules
flat over `Y` with support proper over `Y`. -/
theorem isPerfect_derivedModulePushforward_tensor_of_isNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    (hY : IsNoetherian B S hS hZ Y.1) (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hGcoh : ∀ n, IsCoherent B S hS X.1 X.2 (G.X n))
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom hft
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) := by
  set M := ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)
  set K := (derivedModulePushforward B S hS f).obj M
  have hXN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hft
      hY.2.2
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS Y.2 hY.1 hfqc
  have hflat : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x := fun n => by
    have := (hGcoh n).toIsQuasicoherentOnSite
    exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f (G.X n)).1 (hGflat n)
  obtain ⟨a, ha⟩ := hGb.bddBelow
  obtain ⟨b, hb⟩ := hGb.bddAbove
  have hz : ∀ i, i < a ∨ b < i → IsZero (G.X i) := fun i hi =>
    not_not.1 fun h => by have := ha h; have := hb h; omega
  -- `E ⊗^L 𝒢^•` is bounded with coherent cohomology, supported properly over `Y`
  have hMcoh := derivedCategoryB_isCoherent_tensor_of_isPerfect hXN E hE G hGb hGcoh
  have hMq : QcohDerived B S hS X M := fun n => (hMcoh n).toIsQuasicoherentOnSite
  obtain ⟨m₁, hm₁⟩ := exists_isGE_smallEtaleDerivedTensor_of_isFlatOver f hXqc E hE G hGb a
    (fun i hi => hz i (.inl hi)) hflat
  obtain ⟨m₂, hm₂⟩ := exists_isLE_smallEtaleDerivedTensor_of_isPerfect hXqc E hE G b
    (fun i hi => hz i (.inr hi))
  have hMb : DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) M :=
    ⟨⟨⟨m₁, (DerivedCategory.isGE_iff M m₁).1 hm₁⟩, ⟨m₂, (DerivedCategory.isLE_iff M m₂).1 hm₂⟩⟩,
      hMcoh⟩
  -- its direct image is bounded with coherent cohomology
  obtain ⟨⟨-, ⟨c, hc⟩⟩, hKcoh⟩ := derivedCategoryBBounded_derivedModulePushforward B S hS hZ f hft
    hY M hMb (hasProperSupport_homology_tensor hXN f hft E hE G hGb hGcoh hGsupp)
  have hKq : QcohDerived B S hS Y K :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs M hMq
  obtain ⟨t, ht⟩ := exists_hasTorAmplitude_derivedModulePushforward_tensor hZ f hfqc hfqs hY.2.1
    hXqc E hE G hGb a (fun i hi => hz i (.inl hi)) hflat hMq c hc
  exact isPerfect_of_isCoherent_homology_of_hasTorAmplitude B S hS Y hY.2.2 K hKq hKcoh t c ht

end AlgebraicGeometry.Space

end
