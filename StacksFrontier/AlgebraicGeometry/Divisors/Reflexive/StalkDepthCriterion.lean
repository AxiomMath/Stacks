module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineLocalCriterion

/-!
# Reflexivity of a coherent module through depth of its stalks

On an integral locally Noetherian scheme a coherent module is reflexive exactly when at every
point its stalk is either a reflexive module over the local ring or has depth at least two
there.  This is the sheaf form of the module-theoretic criterion
`isReflexive_iff_localized_isReflexive_or_depth_two`, transported across the affine-local
criterion for reflexivity and the identification of a stalk with a localization of the
sections.

## Main results

* `AlgebraicGeometry.depth_stalk_eq_depth_localizedModule`: at a point of an affine open, the
  depth of the stalk is the depth of the localization of the sections.
* `AlgebraicGeometry.two_le_depth_stalk_iff_localizedModule`: at a point of an affine open,
  depth at least two of the stalk is depth at least two of the localization of the sections.
* `AlgebraicGeometry.isReflexive_iff_stalk_isReflexive_or_depth_two`: the pointwise criterion.

## Implementation notes

The depth comparison is stated and proved here because the only version in the library sits
inside `StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/Depth.lean` as a `private`
lemma and so cannot be cited.

Over the empty open the ring of sections is the zero ring, which is not a domain, so the
module-theoretic criterion does not apply there; the sections of any module over the empty
open form a subsingleton and are reflexive for that reason.

## References

* [Stacks Project, Tag 0AY5](https://stacks.math.columbia.edu/tag/0AY5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- At a point `x` of an affine open `U`, the depth of the stalk `F_x` over `𝒪_{X,x}` equals the
depth of the localization of `Γ(F, U)` at the prime of `x` over the localization of `Γ(X, U)` at
that prime: the germ maps identify the two, semilinearly over the canonical isomorphism of the
two local rings. -/
theorem depth_stalk_eq_depth_localizedModule
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) =
      Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) := by
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal with hp
  have hprime : p.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let T := X.presheaf.stalk x
  let N := F.presheaf.stalk x
  let S := Localization.AtPrime p
  let : Module Γ(X, U) N := affineStalkModule F U x hx
  let : Algebra Γ(X, U) T := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsScalarTower Γ(X, U) T N := IsScalarTower.of_algebraMap_smul fun r z => by
    show (X.presheaf.germ U x hx).hom r • z = r • z
    rfl
  let : IsLocalization.AtPrime T p := hU.isLocalization_stalk ⟨x, hx⟩
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  let e : S ≃ₐ[Γ(X, U)] T := IsLocalization.algEquiv p.primeCompl S T
  let : Algebra S T := e.toAlgHom.toAlgebra
  let : Module S N := Module.compHom N (algebraMap S T)
  let : IsScalarTower S T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp (r : Γ(X, U)) : algebraMap S T (algebraMap Γ(X, U) S r) = algebraMap Γ(X, U) T r :=
    e.commutes r
  let : IsScalarTower Γ(X, U) S T := .of_algebraMap_eq fun r => (hcomp r).symm
  let : IsScalarTower Γ(X, U) S N := IsScalarTower.of_algebraMap_smul fun r n => by
    show algebraMap S T (algebraMap Γ(X, U) S r) • n = algebraMap Γ(X, U) T r • n
    rw [hcomp]
  have hlocM : IsLocalizedModule p.primeCompl (affineGerm F U x hx) :=
    affineGerm_isLocalized F U hU x hx
  let eM' : LocalizedModule p.primeCompl Γ(F, U) ≃ₗ[S] N :=
    (IsLocalizedModule.linearEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl Γ(F, U))
      (affineGerm F U x hx)).extendScalarsOfIsLocalization p.primeCompl S
  have hdepthM : Module.depth S (IsLocalRing.maximalIdeal S)
      (LocalizedModule p.primeCompl Γ(F, U)) = Module.depth S (IsLocalRing.maximalIdeal S) N :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) eM'
  have hmax : Ideal.map (algebraMap S T) (IsLocalRing.maximalIdeal S) =
      IsLocalRing.maximalIdeal T := by
    show Ideal.map e.toRingHom (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal T
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hdepthST := Module.depth_eq_depth_map_algebraMap
    (A := S) (B := T) e.surjective (IsLocalRing.maximalIdeal S) N
  rw [hmax] at hdepthST
  show Module.depth T (IsLocalRing.maximalIdeal T) N =
    Module.depth S (IsLocalRing.maximalIdeal S) (LocalizedModule p.primeCompl Γ(F, U))
  rw [← hdepthST, ← hdepthM]

/-- At a point `x` of an affine open `U`, the stalk `F_x` has depth at least two over
`𝒪_{X,x}` exactly when the localization of `Γ(F, U)` at the prime of `x` has depth at least two
over the localization of `Γ(X, U)`: the germ map identifies the two, semilinearly over the
canonical isomorphism of the two local rings. -/
theorem two_le_depth_stalk_iff_localizedModule [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x) ↔
      (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
        (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)) := by
  rw [depth_stalk_eq_depth_localizedModule F hU hx]

/-- **Stacks Project, Tag 0AY5.** A coherent module on an integral locally Noetherian scheme is
reflexive if and only if at every point its stalk is either a reflexive module over the local
ring there or has depth at least two. -/
@[stacks 0AY5]
theorem isReflexive_iff_stalk_isReflexive_or_depth_two (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] :
    IsReflexive F ↔
      ∀ x : X, Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) ∨
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x) := by
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  let : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  let : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  let : _root_.SheafOfModules.IsCoherent (dualSheaf F) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf F
  let : (dualSheaf F).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  refine ⟨fun hF x => Or.inl (isReflexive_stalk_of_isReflexive F hF x), fun h => ?_⟩
  refine (isReflexive_iff_sections_isReflexive X F).2 fun U hU => ?_
  by_cases hUne : Nonempty U
  · let : Nonempty U := hUne
    let : IsDomain Γ(X, U) := IsIntegral.component_integral U
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let : Module.Finite Γ(X, U) Γ(F, U) :=
      Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU
    refine isReflexive_iff_localized_isReflexive_or_depth_two.2 fun q hq => ?_
    have hqU : hU.fromSpec ⟨q, hq⟩ ∈ U := (hU.isoSpec.inv ⟨q, hq⟩).2
    have hq' : hU.primeIdealOf ⟨hU.fromSpec ⟨q, hq⟩, hqU⟩ = ⟨q, hq⟩ :=
      hU.fromSpec.isOpenEmbedding.injective
        (hU.fromSpec_primeIdealOf ⟨hU.fromSpec ⟨q, hq⟩, hqU⟩)
    rcases h (hU.fromSpec ⟨q, hq⟩) with hRef | hDepth
    · refine Or.inl ?_
      have hmain := (isReflexive_localizedModule_iff_isReflexive_stalk F hU hqU).mpr hRef
      rwa [hq'] at hmain
    · refine Or.inr ?_
      have hmain := (two_le_depth_stalk_iff_localizedModule F hU hqU).mp hDepth
      rwa [hq'] at hmain
  · have hUbot : U = ⊥ := le_antisymm (fun z hz => (hUne ⟨z, hz⟩).elim) bot_le
    subst hUbot
    have : Subsingleton Γ(F, (⊥ : X.Opens)) := Module.subsingleton Γ(X, (⊥ : X.Opens)) _
    infer_instance

end AlgebraicGeometry

end
