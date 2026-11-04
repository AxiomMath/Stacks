module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.FormalFibres.Examples
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen--Macaulay fibres of an adic completion, and the depth they compute

Let `B` be a Noetherian ring whose local rings have Cohen--Macaulay formal fibres, let `J ⊆ B`
be an ideal and let `A' = AdicCompletion J B`. The fibres of `B → A'` are Cohen--Macaulay:
Cohen--Macaulayness of fibres is local on the target and descends along faithfully flat maps,
which is exactly what the `RingMapProperty` transfer machinery needs to pass from the formal
fibres to the fibres of an arbitrary adic completion.

Consequently, for a prime `P'` of `A'` lying over a prime `P` of `B`, the local ring
`A'_{P'}/P A'_{P'}` is a local ring of a Cohen--Macaulay ring, so its depth agrees with its
dimension, and that dimension is the height of the image of `P'` in `A'/P A'`.

A Noetherian ring with a dualizing complex has this property: its formal fibres are Gorenstein,
hence Cohen--Macaulay, by Stacks 0AWY. That implication is
`isPRing_cohenMacaulayRingMapProperty` (and `isPRing_cohenMacaulayRingMapProperty_univ` for a
dualizing complex in an arbitrary module universe), so the dualizing complex is not carried by
`depth_fibre_localization_eq_height_of_isPRing`: it assumes only the property the proof of
Stacks 0EHW actually consumes, which is also the hypothesis the source itself uses for this
translation in Stacks 0EHI and Stacks 0BJV.

## Main results

* `Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty`: Cohen--Macaulayness of the target
  of a ring map, the `RingMapProperty` at which `IsPRing` reads "the formal fibres of the local
  rings are Cohen--Macaulay".
* `Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty` and
  `Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_univ`: a dualizing complex
  gives that property.
* `Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_of_isPrecomplete_maximalIdeal`:
  so does completeness of a Noetherian local ring for its maximal ideal (Stacks 0BFR).
* `Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height_of_isPRing`: under that
  property, the depth of `A'_{P'}/P A'_{P'}` over `A'_{P'}` equals the height of the image of
  `P'` in `A'/P A'`.
* `Stacks.AdicCompletionFibre.depth_fibre_localization_eq_height`: the depth of
  `A'_{P'}/P A'_{P'}` over `A'_{P'}` equals the height of the image of `P'` in `A'/P A'`.

## Implementation notes

The Cohen--Macaulay property is packaged as a `RingMapProperty` whose value on a map is
`Module.IsCohenMacaulay` of its target (Definition 0AAH). With that reading the hypothesis of
Stacks 0BJ9 is `Iff.rfl`, and its second and fourth clauses are exactly the "local on the
target" and "faithfully flat descent" clauses that Stacks 0BK9 asks for, once `PrimeSpectrum`
packaging is traded for `(p : Ideal _) [p.IsPrime]`. That the property respects isomorphisms is
proved prime by prime: a ring equivalence matches up the primes and the localizations at
corresponding primes are isomorphic.

The transport of the conclusion to `A'_{P'}/P A'_{P'}` goes through two models of that ring: it
is the localization of the fibre `κ(P) ⊗_B A'` at the prime of the fibre cutting out `P'`
(`Ideal.Fiber.algEquivAux₂`), which is where Cohen--Macaulayness comes from, and it is the
localization of `A'/P A'` at the image of `P'`, which is where the height comes from. The depth
over `A'_{P'}` and the depth over the quotient itself agree because the quotient map is
surjective.

## References

* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0BJ9](https://stacks.math.columbia.edu/tag/0BJ9)
* [Stacks Project, Tag 0BK9](https://stacks.math.columbia.edu/tag/0BK9)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AdicCompletionFibre

universe u v

/-! ### Cohen--Macaulayness of a ring, read prime by prime -/

/-- A Gorenstein ring is Cohen--Macaulay as a module over itself: it is Gorenstein local at every
prime, hence Cohen--Macaulay local there, which is maximal Cohen--Macaulayness of the
localization over itself. -/
private theorem isCohenMacaulay_self_of_isGorensteinRing (T : Type u) [CommRing T]
    [IsNoetherianRing T] (hT : Dualizing.IsGorensteinRing T) : Module.IsCohenMacaulay T T := by
  rw [Stacks.CohenMacaulay.BaseFieldExtension.isCohenMacaulay_self_iff]
  intro P _
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp
    (Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ (hT P))

/-! ### Cohen--Macaulayness as a property of ring maps -/

/-- Being a Cohen--Macaulay ring, viewed as a property of the target of a ring homomorphism.

`IsPRing cohenMacaulayRingMapProperty A` is the property "the formal fibres of the local rings
of `A` are Cohen--Macaulay", which is clause (2) of Stacks 0BJV and the second half of the
hypothesis "universally catenary with Cohen--Macaulay formal fibres" of Stacks 0EHI. -/
public def cohenMacaulayRingMapProperty : RingMapProperty.{u, u} where
  property := fun {_ S} _ _ _ => Module.IsCohenMacaulay S S
  respectsIso := by
    refine ⟨?_, ?_⟩
    · intro A B C _ _ _ f e h
      exact Stacks.CohenMacaulay.BaseFieldExtension.isCohenMacaulay_self_of_ringEquiv e.symm h
    · intro A B C _ _ _ f e h
      exact h

/-- Being a Cohen--Macaulay ring, viewed as a property of the target of a ring homomorphism.
This is `cohenMacaulayRingMapProperty`, under the name the proofs of this file use. -/
private def cohenMacaulayTarget : RingMapProperty.{u, u} :=
  cohenMacaulayRingMapProperty

/-- On a map from a field, `cohenMacaulayTarget` is Cohen--Macaulayness of the target. This is
the hypothesis of Stacks 0BJ9. -/
private theorem cohenMacaulayTarget_algebraMap_iff :
    ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      cohenMacaulayTarget.{u} (algebraMap k R) ↔ Module.IsCohenMacaulay R R := by
  intro k R _ _ _ _
  exact Iff.rfl

/-- **Cohen--Macaulayness of the target is local for localization.** This is clause (B) of
Stacks 0BJ9, repackaged. -/
private theorem cohenMacaulayTarget_isLocalForLocalization :
    IsLocalForLocalization (fun f => cohenMacaulayTarget.{u} f) := by
  intro k S _ _ _ f
  let : Algebra k S := f.toAlgebra
  have h := (cohenMacaulayProperty_satisfies_formalFiberAxioms cohenMacaulayTarget.{u}
    cohenMacaulayTarget_algebraMap_iff).2.1 k S
  exact ⟨fun hf p hp => h.mpr hf ⟨p, hp⟩, fun hp => h.mp fun pp => hp pp.asIdeal⟩

/-- **Cohen--Macaulayness of the fibres descends along a faithfully flat second map.** This is
clause (D) of Stacks 0BJ9, repackaged as Stacks 0BK9 wants it. -/
private theorem cohenMacaulayTarget_descent {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
    [Module.Flat R S] [Module.FaithfullyFlat S T]
    (h : FibersHaveProperty (fun f => cohenMacaulayTarget.{u} f) R T) :
    FibersHaveProperty (fun f => cohenMacaulayTarget.{u} f) R S := by
  intro p hp
  exact (cohenMacaulayProperty_satisfies_formalFiberAxioms cohenMacaulayTarget.{u}
    cohenMacaulayTarget_algebraMap_iff).2.2.2.1 R S T (fun pp => h pp.asIdeal) ⟨p, hp⟩

/-- **A Noetherian ring with a dualizing complex is a Cohen--Macaulay `P`-ring.** Every formal
fibre of a localization of such a ring is Gorenstein by Stacks 0AWY, hence Cohen--Macaulay. -/
public theorem isPRing_cohenMacaulayRingMapProperty (A : Type u) [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) : IsPRing cohenMacaulayRingMapProperty.{u} A := by
  refine ⟨inferInstance, fun p q => ?_⟩
  obtain ⟨hN, hG⟩ := Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex
    (Localization.AtPrime p.asIdeal) _
    (Dualizing.isDualizingComplex_localizationAtPrime.{u, u} K hK p) q.asIdeal
  exact @isCohenMacaulay_self_of_isGorensteinRing _ _ hN hG

/-! ### Cohen--Macaulay formal fibres transport along isomorphisms and localizations -/

/-- Cohen--Macaulayness of the formal fibres of a local ring transports along an isomorphism of
local rings, in any pair of universes: the isomorphism induces one of the adic completions at
the maximal ideals, hence one of the formal fibres over corresponding primes. -/
private theorem formalFibersHave_cohenMacaulayRingMapProperty_of_ringEquiv {A : Type u}
    {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : FormalFibersHave cohenMacaulayRingMapProperty.{u} A) :
    FormalFibersHave cohenMacaulayRingMapProperty.{v} B := by
  intro q
  have _ : (q.asIdeal.comap e.toRingHom).IsPrime := Ideal.IsPrime.comap _
  obtain ⟨E, _⟩ := Stacks.FormalFibres.exists_tensorProduct_ringEquiv e
    (Stacks.FormalFibres.completionRingEquiv e)
    (Ideal.residueFieldRingEquiv (q.asIdeal.comap e.toRingHom) q.asIdeal e rfl)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap e)
    (fun r => Ideal.ResidueField.map_algebraMap (q.asIdeal.comap e.toRingHom) q.asIdeal
      e.toRingHom rfl r)
  exact Stacks.CohenMacaulay.BaseFieldExtension.isCohenMacaulay_self_of_ringEquiv E.symm
    (h ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩)

/-- Being a Cohen--Macaulay `P`-ring transports along an isomorphism of rings, in any pair of
universes. -/
public theorem isPRing_cohenMacaulayRingMapProperty_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) (h : IsPRing cohenMacaulayRingMapProperty.{u} A) :
    IsPRing cohenMacaulayRingMapProperty.{v} B := by
  have _ : IsNoetherianRing A := h.1
  refine ⟨isNoetherianRing_of_ringEquiv A e, fun p => ?_⟩
  have _ : (p.asIdeal.comap e.toRingHom).IsPrime := Ideal.IsPrime.comap _
  exact formalFibersHave_cohenMacaulayRingMapProperty_of_ringEquiv
    (Localization.localRingEquiv (p.asIdeal.comap e.toRingHom) p.asIdeal e rfl)
    (h.2 ⟨p.asIdeal.comap e.toRingHom, inferInstance⟩)

/-- **A Noetherian ring with a dualizing complex in an arbitrary module universe is a
Cohen--Macaulay `P`-ring.** The ring `ULift A` is a localization of `A`, so it inherits a
dualizing complex, now at its own module universe; it is therefore a Cohen--Macaulay `P`-ring
by Stacks 0AWY, and the property transports back along `ULift.ringEquiv`. -/
public theorem isPRing_cohenMacaulayRingMapProperty_univ {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{v} A)} (hK : Dualizing.IsDualizingComplex K) :
    IsPRing cohenMacaulayRingMapProperty.{u} A := by
  let e : A ≃+* ULift.{v} A := ULift.ringEquiv.symm
  let _ : Algebra A (ULift.{v} A) := e.toRingHom.toAlgebra
  let M₀ : Submonoid (ULift.{v} A) := IsUnit.submonoid (ULift.{v} A)
  let M : Submonoid A := M₀.map e.symm.toRingHom
  have : IsLocalization M (ULift.{v} A) :=
    IsLocalization.isLocalization_of_base_ringEquiv M₀ (ULift.{v} A) e.symm
  have : IsNoetherianRing (ULift.{v} A) :=
    IsLocalization.isNoetherianRing M (ULift.{v} A) inferInstance
  exact isPRing_cohenMacaulayRingMapProperty_of_ringEquiv ULift.ringEquiv
    (isPRing_cohenMacaulayRingMapProperty (ULift.{v} A) _
      (Dualizing.isDualizingComplex_localization (B := ULift.{v} A) M K hK))

/-- **A Noetherian complete local ring is a Cohen--Macaulay `P`-ring**: the formal fibres of
all its local rings are Cohen--Macaulay. It has a dualizing complex (Stacks 0BFR, via the Cohen
structure theorem), and a Noetherian ring with a dualizing complex has Gorenstein, hence
Cohen--Macaulay, formal fibres (Stacks 0AWY).

Completeness is precompleteness for the maximal ideal, as in
`Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal`. This is a statement about the
`𝔪`-adic completion; the `I`-adic completion of a local ring at an ideal `I ⊊ 𝔪` is in general
not complete for its maximal ideal, and this lemma says nothing about it. -/
@[ega "IV 7.3.19" "(ii), special case"]
public theorem isPRing_cohenMacaulayRingMapProperty_of_isPrecomplete_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    IsPRing cohenMacaulayRingMapProperty.{u} A := by
  obtain ⟨K, hK⟩ := Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A
  exact isPRing_cohenMacaulayRingMapProperty A K hK

/-- **A localization at a prime of a Cohen--Macaulay `P`-ring is a Cohen--Macaulay `P`-ring.**
A prime of `A_𝔮` is the image of a prime `𝔭 ⊆ 𝔮` of `A`, and localizing `A_𝔮` there gives the
same ring as localizing `A` at `𝔭`. -/
public theorem isPRing_cohenMacaulayRingMapProperty_localizationAtPrime {A : Type u}
    [CommRing A]
    (h : IsPRing cohenMacaulayRingMapProperty.{u} A) (q : Ideal A) [q.IsPrime] :
    IsPRing cohenMacaulayRingMapProperty.{u} (Localization.AtPrime q) := by
  have _ : IsNoetherianRing A := h.1
  refine ⟨inferInstance, fun p => ?_⟩
  have hp : (Ideal.comap (algebraMap A (Localization.AtPrime q)) p.asIdeal).IsPrime :=
    Ideal.IsPrime.comap _
  let e : Localization.AtPrime p.asIdeal ≃+*
      Localization.AtPrime (Ideal.comap (algebraMap A (Localization.AtPrime q)) p.asIdeal) :=
    (IsLocalization.algEquiv
      (Ideal.comap (algebraMap A (Localization.AtPrime q)) p.asIdeal).primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime
        (Ideal.comap (algebraMap A (Localization.AtPrime q)) p.asIdeal))).toRingEquiv
  exact formalFibersHave_cohenMacaulayRingMapProperty_of_ringEquiv e.symm
    (h.2 ⟨Ideal.comap (algebraMap A (Localization.AtPrime q)) p.asIdeal, hp⟩)

/-! ### Two models of the local ring of a fibre -/

/-- The local ring of the fibre of `Spec S → Spec R` over `𝔭` at a prime `𝔔` of the fibre is the
ring `S_𝔮/𝔭S_𝔮`, for `𝔮` the prime of `S` cut out by `𝔔`. So that ring is Cohen--Macaulay as
soon as the fibre is. -/
private theorem isMaximalCohenMacaulay_fibre_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime] (q : Ideal S) [q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)
      (B := S)) = q)
    (hCM : Module.IsCohenMacaulay (p.Fiber S) (p.Fiber S))
    [IsLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))] :
    Module.IsMaximalCohenMacaulay
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
  subst hQ
  refine (Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv
    ((Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv.trans
      (Ideal.quotEquivOfEq ?_))).mp
    (Stacks.CohenMacaulay.BaseFieldExtension.isCohenMacaulay_self_iff.mp hCM Q)
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-! ### The depth of the local rings of the fibres of an adic completion -/

/-- **The depth of a local ring of a fibre of an adic completion is the height of the
corresponding prime of the fibre.** For `B` Noetherian whose local rings have Cohen--Macaulay
formal fibres, `J ⊆ B` an ideal, `A' = AdicCompletion J B` and `P'` a prime of `A'` over a prime
`P` of `B`, the ring `A'_{P'}/P A'_{P'}` is Cohen--Macaulay, so its depth equals its dimension,
which is the height of the image of `P'` in `A'/P A'`.

This is the step of Stacks 0EHW justified there by "the fibres of `A → A'` are
Cohen--Macaulay". The hypothesis is exactly that statement about `B`, rather than the dualizing
complex from which Stacks 0EHW derives it; `isPRing_cohenMacaulayRingMapProperty` and
`isPRing_cohenMacaulayRingMapProperty_univ` discharge it from a dualizing complex, which is
`depth_fibre_localization_eq_height`. -/
theorem depth_fibre_localization_eq_height_of_isPRing
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    (hCM : IsPRing cohenMacaulayRingMapProperty.{u} B)
    (J : Ideal B) (P : Ideal B) [P.IsPrime]
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P] :
    Module.depth (Localization.AtPrime P') (IsLocalRing.maximalIdeal (Localization.AtPrime P'))
        (Localization.AtPrime P' ⧸ P.map (algebraMap B (Localization.AtPrime P'))) =
      (P'.map (Ideal.Quotient.mk (P.map (algebraMap B (AdicCompletion J B))))).height := by
  obtain rfl : P = P'.under B := Ideal.LiesOver.over
  have hCM : Module.IsCohenMacaulay ((P'.under B).Fiber (AdicCompletion J B))
      ((P'.under B).Fiber (AdicCompletion J B)) :=
    fibersHaveProperty_adicCompletion_of_isPRing cohenMacaulayTarget.{u}
      cohenMacaulayTarget_isLocalForLocalization (fun h => cohenMacaulayTarget_descent h) hCM J
      (P'.under B)
  obtain ⟨Q, _, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq P' (P'.under B) rfl
  let eF := fiberRingEquiv B P' (Localization.AtPrime P')
  have _ : IsLocalRing (Localization.AtPrime P' ⧸
      (P'.under B).map (algebraMap B (Localization.AtPrime P'))) := eF.symm.isLocalRing
  have hCMF := isMaximalCohenMacaulay_fibre_localization (P'.under B) Q P' hQ hCM
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime P')
      (Localization.AtPrime P' ⧸ (P'.under B).map (algebraMap B (Localization.AtPrime P')))) :=
    Ideal.Quotient.mk_surjective
  have hmap := Module.depth_eq_depth_map_algebraMap hsurj
    (maximalIdeal (Localization.AtPrime P'))
    (Localization.AtPrime P' ⧸ (P'.under B).map (algebraMap B (Localization.AtPrime P')))
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ hsurj] at hmap
  have hdim : ringKrullDim (Localization.AtPrime P' ⧸
      (P'.under B).map (algebraMap B (Localization.AtPrime P'))) =
      ((P'.map (Ideal.Quotient.mk ((P'.under B).map (algebraMap B (AdicCompletion J B))))).height :
        WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv eF).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  have : ((Module.depth (Localization.AtPrime P')
      (maximalIdeal (Localization.AtPrime P'))
      (Localization.AtPrime P' ⧸ (P'.under B).map (algebraMap B (Localization.AtPrime P'))) : ℕ∞) :
      WithBot ℕ∞) =
      ((P'.map (Ideal.Quotient.mk ((P'.under B).map (algebraMap B (AdicCompletion J B))))).height :
        WithBot ℕ∞) := by
    rw [hmap]
    exact hCMF.trans hdim
  exact_mod_cast this

/-- **The depth of a local ring of a fibre of an adic completion is the height of the
corresponding prime of the fibre.** For `B` Noetherian with a dualizing complex, `J ⊆ B` an
ideal, `A' = AdicCompletion J B` and `P'` a prime of `A'` over a prime `P` of `B`, the ring
`A'_{P'}/P A'_{P'}` is Cohen--Macaulay, so its depth equals its dimension, which is the height
of the image of `P'` in `A'/P A'`.

This is the step of Stacks 0EHW justified there by "the fibres of `A → A'` are
Cohen--Macaulay"; the formal fibres of `B` are Gorenstein by Stacks 0AWY, and
`depth_fibre_localization_eq_height_of_isPRing` does the rest. -/
theorem depth_fibre_localization_eq_height
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    {K : DerivedCategory (ModuleCat.{u} B)} (hK : Dualizing.IsDualizingComplex K)
    (J : Ideal B) (P : Ideal B) [P.IsPrime]
    (P' : Ideal (AdicCompletion J B)) [P'.IsPrime] [P'.LiesOver P] :
    Module.depth (Localization.AtPrime P') (IsLocalRing.maximalIdeal (Localization.AtPrime P'))
        (Localization.AtPrime P' ⧸ P.map (algebraMap B (Localization.AtPrime P'))) =
      (P'.map (Ideal.Quotient.mk (P.map (algebraMap B (AdicCompletion J B))))).height :=
  depth_fibre_localization_eq_height_of_isPRing (isPRing_cohenMacaulayRingMapProperty B K hK)
    J P P'

end Stacks.AdicCompletionFibre

end
