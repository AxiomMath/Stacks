module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts
import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget

/-!
# Representable étale morphisms of Noetherian affine formal algebraic spaces are rig-étale

A morphism `f : X ⟶ Y` of Noetherian affine formal algebraic spaces which is representable by
algebraic spaces and étale is rig-étale (Definition 0AQM). By Stacks 0AN8 the morphism is, up to
isomorphism, the formal spectrum of the canonical map `A → (A₁)^∧` to the completion of an étale
`A`-algebra, which is rig-étale; condition (4) of Stacks 0GCZ, for the covering of `X` by its
identity, then gives rig-étaleness.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isNoetherian`: a Noetherian affine formal
  algebraic space is locally Noetherian.
* `AlgebraicGeometry.FormalSpace.correspondsToRigEtaleMap_of_isRepresentableEtale`: a
  representable étale morphism from an affine formal algebraic space to the formal spectrum of a
  Noetherian adic ring corresponds to a rig-étale map in `WAdm^{Noeth}`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_isRepresentableEtale`: representable étale
  morphisms of Noetherian affine formal algebraic spaces are rig-étale.

## References

* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The covering of a sheaf by its identity is locally surjective. -/
theorem isLocallySurjective_sigmaDesc_id (X : FppfSheaf B S hS) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc (fun _ : PUnit.{u + 2} ↦ (𝟙 X : X ⟶ X))) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hsplit : IsSplitEpi (Sigma.desc (fun _ : PUnit.{u + 2} ↦ (𝟙 X : X ⟶ X))) :=
    ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ X) PUnit.unit, by simp⟩⟩
  have _ := hsplit
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

/-- A Noetherian affine formal algebraic space is locally Noetherian: it is its own atlas. -/
theorem isLocallyNoetherian_of_isNoetherian {X : FppfSheaf B S hS} (hX : IsNoetherian B S hS X) :
    IsLocallyNoetherian B S hS X :=
  ⟨isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX.1.1,
    PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX.1.1,
    fun _ ↦ isRepresentableEtale_id B S hS X, isLocallySurjective_sigmaDesc_id B S hS X,
    fun _ ↦ hX⟩

/-- **A representable étale morphism to the formal spectrum of a Noetherian adic ring corresponds
to a rig-étale map.** By Stacks 0AN8 it is the formal spectrum of the canonical map to the
completion of an étale algebra, which is rig-étale. -/
theorem correspondsToRigEtaleMap_of_isRepresentableEtale {U U' : FppfSheaf B S hS}
    (q : U' ⟶ U) (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hq : IsRepresentableEtale B S hS q) {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hCR : IsNoetherianAdic R)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) :
    CorrespondsToRigEtaleMap B S hS q := by
  have : IsNoetherianRing R := hCR.2
  obtain ⟨R₁, _, _, _, E₁, c, ε, hc, hε⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS q hU' hq R hCR.1 E eU
  have hR₁ : IsNoetherianAdic (CompletionOver (algebraMap R R₁)) :=
    completionOver_isNoetherianAdic _ hCR (Algebra.FiniteType.isNoetherianRing R R₁)
  have : IsNoetherianRing (CompletionOver (algebraMap R R₁)) := hR₁.2
  refine ⟨R, CompletionOver (algebraMap R R₁), _, _, _, _, _, _, _, _, hCR, hR₁,
    hCR.1.isWeaklyAdmissible, E, E₁, ε, eU, c, ?_, ?_⟩
  · rw [← Category.assoc, hε]
    simp
  · intro _ _ _ _
    rw [hc]
    exact Rig.isRigEtale_canonicalMap (algebraMap R R₁)
      (RingHom.etale_algebraMap.mpr inferInstance) hCR.1 hR₁.1

/-- **Representable étale morphisms of Noetherian affine formal algebraic spaces are
rig-étale.** Condition (4) of Stacks 0GCZ holds for the covering of `X` by its identity and the
chart `𝟙 Y` of `Y`, by
`AlgebraicGeometry.FormalSpace.correspondsToRigEtaleMap_of_isRepresentableEtale`. -/
theorem isRigEtale_of_isRepresentableEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsNoetherian B S hS X) (hY : IsNoetherian B S hS Y)
    (hf : IsRepresentableEtale B S hS f) : IsRigEtale B S hS f := by
  have key := (isRigEtale_tfae_of_isLocallyNoetherian' B S hS f
    (isLocallyNoetherian_of_isNoetherian B S hS hX)
    (isLocallyNoetherian_of_isNoetherian B S hS hY)).out 1 4
  refine key.mpr ⟨PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X,
    ⟨fun _ ↦ hX.1.1, fun _ ↦ isRepresentableEtale_id B S hS X,
      isLocallySurjective_sigmaDesc_id B S hS X⟩, fun _ ↦ ⟨Y, 𝟙 Y, f, hY.1.1,
        isRepresentableEtale_id B S hS Y, by simp, ?_⟩⟩
  obtain ⟨-, A, _, _, _, _, ⟨hwA, ⟨P⟩⟩, hnA, haA⟩ := hY
  exact correspondsToRigEtaleMap_of_isRepresentableEtale B S hS f hX.1.1 hf ⟨haA, hnA⟩
    P.quotientSystem P.formalSpectrumIso

end AlgebraicGeometry.FormalSpace

end
