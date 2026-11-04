module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionCriteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étaleness from an isomorphism on completed local rings

A bijective local homomorphism of Noetherian local rings is étale as a homomorphism of local
rings, for trivial reasons: it is flat, formally unramified and essentially of finite type.
Combined with the fact that étaleness of an essentially finite type local homomorphism of
Noetherian local rings is detected on the completions at the maximal ideals, this shows that a
local homomorphism which is essentially of finite type and induces a bijection on completions is
already étale as a homomorphism of local rings.

## Main results

* `RingHom.isEtaleLocalHom_of_bijective`: a bijective local homomorphism of Noetherian local
  rings is étale as a homomorphism of local rings.
* `RingHom.isEtaleLocalHom_of_bijective_adicCompletionMap`: an essentially finite type local
  homomorphism of Noetherian local rings whose induced homomorphism of completions at the
  maximal ideals is bijective is étale as a homomorphism of local rings.

## Implementation notes

Étaleness of a homomorphism of local rings is `RingHom.IsEtaleLocalHom`, which unfolds to
`RingHom.Flat`, `RingHom.FormallyUnramified` and `RingHom.EssFiniteType`. Each of the three is
available for a bijective homomorphism directly from Mathlib, via `RingHom.Flat.of_bijective`,
`RingHom.FormallyUnramified.of_surjective` and `RingHom.FiniteType.of_surjective` followed by
`RingHom.FiniteType.essFiniteType`; no local hypothesis is used, and the Noetherian and local
assumptions are carried only because `RingHom.IsEtaleLocalHom` requires them.

The reduction to the completions is
`RingHom.isEtaleLocalHom_iff_isEtaleLocalHom_adicCompletion`. Its right-hand side is stated
with the locality instance of the completed homomorphism supplied by
`AdicCompletion.isLocalHom_adicCompletionMap`, which is therefore introduced as a local
instance before the bijective case is applied. The completions are Noetherian local rings by
existing instances, so no extra hypotheses are needed.
-/

@[expose] public noncomputable section

universe u v

open AlgebraicGeometry AdicCompletion CategoryTheory IsLocalRing

namespace RingHom

/-- A bijective local homomorphism of Noetherian local rings is étale as a homomorphism of
local rings: it is flat, formally unramified and essentially of finite type. -/
theorem isEtaleLocalHom_of_bijective {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hf : Function.Bijective f) : RingHom.IsEtaleLocalHom f :=
  ⟨.of_bijective hf, .of_surjective hf.surjective,
    (RingHom.FiniteType.of_surjective f hf.surjective).essFiniteType⟩

/-- A local homomorphism of Noetherian local rings which is essentially of finite type and
induces a bijection on the completions at the maximal ideals is étale as a homomorphism of
local rings. -/
@[sga "1 I 4.4" "Sufficiency", sga "3 XI 1.4" "(ii)"]
theorem isEtaleLocalHom_of_bijective_adicCompletionMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType)
    (hbij : Function.Bijective (adicCompletionMap f (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) (IsLocalRing.map_maximalIdeal_le f))) :
    RingHom.IsEtaleLocalHom f := by
  have : IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
    (map_maximalIdeal_le f)) := AdicCompletion.isLocalHom_adicCompletionMap f
  exact (isEtaleLocalHom_iff_isEtaleLocalHom_adicCompletion f hft).mpr
    (isEtaleLocalHom_of_bijective _ hbij)

end RingHom

end
