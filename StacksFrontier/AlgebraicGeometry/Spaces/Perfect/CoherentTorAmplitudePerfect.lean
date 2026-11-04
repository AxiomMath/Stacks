module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeEtalePullbackTests
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentLocal
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfectModel

/-!
# Coherent cohomology and finite Tor amplitude give perfectness on a locally Noetherian space

Let `X` be a locally Noetherian algebraic space and `E ∈ D_QCoh(𝒪_X)` with coherent cohomology
sheaves and Tor amplitude in `[a, b]`. Then `E` is perfect. On an affine étale chart
`W = Spec R` the object `RΓ(W, E|_W)` of `D(R)` is pseudo-coherent (Stacks 066E) and has Tor
amplitude in `[a, b]` (Stacks 08E9 on the étale site), hence is perfect (Stacks 0658), and its
associated object, which is `E|_W`, has a strictly perfect model.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitude_smallEtaleDerivedModulePullback_of_isEtale`: Tor
  amplitude passes to the derived pullback along a separated étale morphism.
* `AlgebraicGeometry.Space.isPerfect_of_isCoherent_homology_of_hasTorAmplitude`: the perfectness
  criterion.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- `SheafOfModules.hasBinBiprod`, universe-polymorphic in the module universe, gives a second
-- route to the biproducts of sheaves of modules, and the derived tensor product of the small étale
-- site no longer elaborates against it: the two routes leave the module universe stuck at
-- `max ?v ?w =?= u`.
attribute [-instance] SheafOfModules.hasBinBiprod

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Tor amplitude passes to the derived pullback along a separated étale morphism.** For
`f : X ⟶ Y` separated and étale and `E ∈ D(𝒪_Y)` of Tor amplitude in `[a, b]`, the derived
pullback `Lf^*E` has Tor amplitude in `[a, b]`: every `𝒪_X`-module is a retract of one pulled
back from `Y` (Stacks 0HAP), and `Hⁱ(Lf^*E ⊗^L f^*𝒩) = f^*Hⁱ(E ⊗^L 𝒩)`. -/
theorem hasTorAmplitude_smallEtaleDerivedModulePullback_of_isEtale {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (a b : ℤ)
    (h : DerivedTensorProduct.HasTorAmplitude (smallEtaleDerivedTensorProduct B S hS Y) E a b) :
    DerivedTensorProduct.HasTorAmplitude (smallEtaleDerivedTensorProduct B S hS X)
      ((smallEtaleDerivedModulePullback B S hS f).obj E) a b :=
  hasTorAmplitude_of_forall_modulePullback B S hS f hf hsep _ _ a b fun N i hi =>
    ((modulePullback B S hS f).map_isZero (h N i hi)).of_iso
      (etaleTensorHomologyIso B S hS f hf E N i)

/-- **Coherent cohomology and finite Tor amplitude give perfectness.** Let `X` be a locally
Noetherian algebraic space and `E ∈ D_QCoh(𝒪_X)` an object whose cohomology sheaves are coherent
and which has Tor amplitude in `[a, b]`. Then `E` is perfect.

Perfectness is checked on the affine étale charts `p : W ⟶ X`, `W = Spec R`
(`AlgebraicGeometry.Space.isPerfect_of_hasStrictlyPerfectModel_chart`). There `RΓ(W, Lp^*E)` is
pseudo-coherent, its cohomology being finite over the Noetherian ring `R` and vanishing above
`b`; it has Tor amplitude in `[a, b]`, as `Lp^*E` has; so it is perfect (Stacks 0658), and its
associated object `Lp^*E` has a strictly perfect model. -/
theorem isPerfect_of_isCoherent_homology_of_hasTorAmplitude (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (hcoh : ∀ i : ℤ, IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))
    (a b : ℤ)
    (htor : DerivedTensorProduct.HasTorAmplitude (smallEtaleDerivedTensorProduct B S hS X) E a b) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E := by
  set T := smallEtaleDerivedTensorProduct B S hS X
  have hb : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) :=
    fun i hi => (htor _ i (by simp only [Set.mem_Icc]; omega)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (T.unitIso E).symm)
  refine isPerfect_of_hasStrictlyPerfectModel_chart E fun U =>
    ⟨fun W _ => IsAffineChart B S hS X.1 W, generate_isAffineChart_mem_topology B S hS X U,
      fun W g hW => ?_⟩
  have hWa : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
    hW
  let U₀ := (SmallEtale.toOver B S hS X.1).obj W
  let p := chartToSpace B S hS X W
  have hp := isEtale_chartToSpace B S hS X W
  let L := (smallEtaleDerivedModulePullback B S hS p).obj E
  have hL : QcohDerived B S hS ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ L :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ p E hE
  let M := (representedAffineDerivedSections B S hS U₀).obj L
  -- `RΓ(W, Lp^*E)` is pseudo-coherent
  have hMpc : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      (R := Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)) M 0).1.2 fun m =>
      isPseudoCoherentFrom_representedAffineDerivedSections_chart X hN E hE m
        (fun i _ => hcoh i) b hb W hW
  -- `Φ(M) ≅ Lp^*E`
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U₀ L hL
  let e : (representedAffineDerivedAssociated B S hS U₀).obj M ≅ L :=
    asIso ((representedAffineDerivedAdjunction B S hS U₀).counit.app L)
  -- Tor amplitude of `Lp^*E`, then of `M`
  have hsep : IsSeparated B S hS p.hom :=
    isSeparated_of_isEtale_of_isAffine B S hS X.2 _ hWa p.hom hp
  have htorL := hasTorAmplitude_smallEtaleDerivedModulePullback_of_isEtale B S hS p hp hsep E a b
    htor
  have htorM := (hasTorAmplitude_representedAffineDerivedAssociated_iff B S hS U₀ M a b).1
    (htorL.of_iso e.symm)
  obtain ⟨F, hF, hFGE, hFLE, ⟨eF⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ M a b).1 htorM
  have hMperf : StacksDraft.Perfect.IsPerfect M :=
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} M).1.2
      ⟨hMpc, a, b, F, hF, hFGE, hFLE, ⟨eF⟩⟩)
  obtain ⟨P, hP, hPb, ⟨eP⟩⟩ :=
    hasStrictlyPerfectModel_representedAffineDerivedAssociated_obj B S hS U₀ M hMperf
  exact ⟨P, hP, hPb, ⟨e.symm ≪≫ eP⟩⟩

end AlgebraicGeometry.Space

end
