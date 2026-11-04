module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimension
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineBaseTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.ChartRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Further results

Results complementing
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineSchemeTorDimension`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.TorAmplitude
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### [Stacks, Tag 06Z0] at a complex of modules -/

/-! ### Transport of Tor amplitude along an isomorphism of schemes -/

/-! ### A morphism of affine schemes as a morphism of spectra -/

/-! ### The affine base case at a morphism of affine schemes -/

/-- **The affine base case of the Tor-dimension half of [Stacks, Tag 08EV], for a ring map of
finite Tor dimension.** Let `h : Z ⟶ W` be a morphism of affine schemes such that `Γ(Z, ⊤)` has
finite Tor dimension over `Γ(W, ⊤)`, and let `B` be an object of `D(𝒪_Z)` whose cohomology sheaves
are quasi-coherent and which has finite Tor dimension on `Z`. Then `Rh_*B` has finite Tor dimension
on `W`.

This is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap`, which proves
it for a morphism `Spec φ`, carried across the Cartesian square of
`AlgebraicGeometry.isPullback_isoSpec` by [Stacks, Tag 08FE] on the functor and by
`AlgebraicGeometry.hasTorAmplitude_restrictFunctor_iso_iff` on the Tor-amplitude predicate. Its
hypothesis `hA` is `AlgebraicGeometry.exists_tildeComplex_iso`, that is, quasi-coherence of the
cohomology of `B`. -/
@[sga "5 III 6.3" "special case"]
theorem hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_of_torAmplitude
    {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (h : Z ⟶ W)
    (hφ : letI : Algebra Γ(W, ⊤) Γ(Z, ⊤) := (h.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
      ∃ c d : ℤ, HasTorAmplitudeCanonical Γ(W, ⊤)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(W, ⊤)) 0).obj
          ((ModuleCat.restrictScalars (algebraMap Γ(W, ⊤) Γ(Z, ⊤))).obj
            (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)))) c d)
    (B : DerivedCategory Z.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B).IsQuasicoherent)
    (hTor : HasFiniteTorDimension Z.toRingedSpace B) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward h).obj B) := by
  have hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤ := by simp
  have hAqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(Z, ⊤)).Modules i).obj
      ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategory.obj B)).IsQuasicoherent :=
    isQuasicoherent_homology_restrictFunctor_mapDerivedCategory Z.isoSpec.inv hqc
  have hAtor : HasFiniteTorDimension (Spec Γ(Z, ⊤)).toRingedSpace
      ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategory.obj B) := by
    obtain ⟨a, b, hab⟩ := hTor
    exact ⟨a, b, (hasTorAmplitude_restrictFunctor_iso_iff Z.isoSpec.symm B a b).2 hab⟩
  obtain ⟨a, b, hab⟩ := hasFiniteTorDimension_schemeDerivedPushforward_specMap
    (h.appLE ⊤ ⊤ hle) hφ _ (exists_tildeComplex_iso Γ(Z, ⊤) _ hAqc) hAtor
  refine ⟨a, b, (hasTorAmplitude_restrictFunctor_iso_iff W.isoSpec.symm _ a b).1 ?_⟩
  exact FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec Γ(W, ⊤)).toRingedSpace) hab
    (schemeDerivedPushforwardRestrictOpenIso h W.isoSpec.inv (Spec.map (h.appLE ⊤ ⊤ hle))
      Z.isoSpec.inv (isPullback_isoSpec h hle) B)

end AlgebraicGeometry

end
