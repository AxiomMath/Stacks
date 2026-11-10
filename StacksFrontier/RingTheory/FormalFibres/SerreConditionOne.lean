module

public import StacksFrontier.RingTheory.Catenary.FormalFibresAssociatedDimension
public import StacksFrontier.RingTheory.FormalFibres.EssFiniteType
public import StacksFrontier.RingTheory.FormalFibres.Examples
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.GRing.Henselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's condition `(S₁)` on formal fibres

Serre's condition `(S₁)` is a property of ring maps in the sense of `RingMapProperty`, and the
rings whose formal fibres satisfy it are closed under passing to algebras essentially of finite
type. In particular a quotient of a Noetherian local ring with `(S₁)` formal fibres again has
`(S₁)` formal fibres.

The condition also holds outright for the local rings of a G-ring: the formal fibres of such a
ring are geometrically regular, hence regular, hence satisfy every `(Sₙ)`.

## Main results

* `serreConditionOneProperty`: `(S₁)` of the target, as a `RingMapProperty`.
* `hasSerreCondition_one_formalFibres_of_essFiniteType`: `(S₁)` of the formal fibres passes from
  a Noetherian local ring to any local algebra essentially of finite type over it.
* `hasSerreCondition_one_formalFibres_of_surjective`: the special case of a surjection.
* `hasSerreCondition_one_formalFibres_of_isGRing_localization`: the formal fibres of a local ring
  presented as a localization of a G-ring satisfy `(S₁)`.
* `hasSerreCondition_one_formalFibres_of_isGRing`: the same for a local G-ring itself.
* `le_ringKrullDim_quotient_adicCompletion_iff_of_surjective`: for a domain `S` that is a local
  quotient of a universally catenary Noetherian local ring with `(S₁)` formal fibres,
  `n ≤ dim(S^∧ / 𝔭)` for every associated prime `𝔭` of `S^∧` exactly when `n ≤ dim(S)`.

## References

* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0BIU](https://stacks.math.columbia.edu/tag/0BIU)
* [Stacks Project, Tag 0BIV](https://stacks.math.columbia.edu/tag/0BIV)
* [Stacks Project, Tag 0BIY](https://stacks.math.columbia.edu/tag/0BIY)
* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

/-- Serre's condition `(S₁)` on the target of a ring map, as a property of ring maps. -/
public def serreConditionOneProperty : RingMapProperty.{u, u} where
  property := fun {A B} _ _ _ => HasSerreCondition B 1
  respectsIso := by
    constructor
    · intro A B C _ _ _ f e h
      exact HasSerreCondition.of_ringEquiv e h
    · intro A B C _ _ _ f e h
      exact h

/-- `serreConditionOneProperty` holds of a ring map exactly when its target satisfies `(S₁)`:
the universe-lifted form of the condition is equivalent to the condition itself. -/
public theorem serreConditionOneProperty_holds_iff {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) :
    serreConditionOneProperty.Holds.{u, u, 0, 0} f ↔ HasSerreCondition B 1 := by
  change HasSerreCondition (ULift B) 1 ↔ HasSerreCondition B 1
  exact ⟨HasSerreCondition.of_ringEquiv ULift.ringEquiv,
    HasSerreCondition.of_ringEquiv ULift.ringEquiv.symm⟩

section Transport

/-- The localization of a local ring at its maximal ideal is the ring itself. -/
private noncomputable def localizationAtMaximalRingEquiv {A : Type u} [CommRing A]
    [IsLocalRing A] : Localization.AtPrime (maximalIdeal A) ≃+* A := by
  have : IsLocalization (maximalIdeal A).primeCompl A := IsLocalization.self (fun x hx => by
    change x ∉ maximalIdeal A at hx
    change IsUnit x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    exact Classical.not_not.mp hx)
  exact (IsLocalization.algEquiv (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A)) A).toRingEquiv

end Transport

/-- Serre's condition `(S₁)` satisfies the axioms (A)--(D) of [Stacks, Tag 0BIV] for a property
of maps out of fields. -/
private theorem serreOneFormalFiberAxioms :
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      serreConditionOneProperty (algebraMap k R) →
        serreConditionOneProperty
          (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom) ∧
    (∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R, serreConditionOneProperty
        (algebraMap k (Localization.AtPrime p.asIdeal))) ↔
        serreConditionOneProperty (algebraMap k R)) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        serreConditionOneProperty.Holds.{u, u, 0, 0}
          (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        serreConditionOneProperty.Holds.{u, u, 0, 0}
          (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        serreConditionOneProperty.Holds.{u, u, 0, 0}
          (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
      ∀ p : PrimeSpectrum A,
        serreConditionOneProperty.Holds.{u, u, 0, 0}
          (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) := by
  have h := serreProperty_satisfies_formalFiberAxioms.{u, u, u} 1 (by decide)
  refine ⟨fun k K R _ _ _ _ _ _ _ hR => h.1 k K R hR, h.2.1, ?_, ?_⟩
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB hreg p
    exact (serreConditionOneProperty_holds_iff _).mpr
      (h.2.2.1 A B C
        (fun q => (serreConditionOneProperty_holds_iff
          (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber B))).mp (hAB q))
        hreg p)
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAC p
    exact (serreConditionOneProperty_holds_iff _).mpr
      (h.2.2.2.1 A B C
        (fun q => (serreConditionOneProperty_holds_iff
          (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber C))).mp (hAC q)) p)

/-- A Noetherian local ring with `(S₁)` formal fibres is an `(S₁)`-ring. -/
private theorem isPRingAt_of_formalFibersHaveAt {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hA : FormalFibersHaveAt.{u, 0, 0} serreConditionOneProperty A) :
    IsPRingAt.{u, 0, 0} serreConditionOneProperty A := by
  have hax := serreOneFormalFiberAxioms.{u}
  refine (isPRing_iff_formalFibersHave_localization_maximal.{u, 0, 0}
    serreConditionOneProperty hax.2.2.1 hax.2.2.2).mpr fun m hm => ?_
  obtain rfl := eq_maximalIdeal hm
  exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, u, 0, 0}
    serreConditionOneProperty localizationAtMaximalRingEquiv.symm hA

/-- Conversely, an `(S₁)`-ring which is local has `(S₁)` formal fibres. -/
private theorem formalFibersHaveAt_of_isPRingAt {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsPRingAt.{u, 0, 0} serreConditionOneProperty A) :
    FormalFibersHaveAt.{u, 0, 0} serreConditionOneProperty A :=
  Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, u, 0, 0}
    serreConditionOneProperty localizationAtMaximalRingEquiv
    (hA.2 ⟨maximalIdeal A, inferInstance⟩)

/-- Let `R → S` be a map of Noetherian local rings making `S` essentially of finite type over
`R`. If every formal fibre of `R` satisfies `(S₁)`, then so does every formal fibre of `S`. -/
public theorem hasSerreCondition_one_formalFibres_of_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (hR : ∀ q : PrimeSpectrum R,
      HasSerreCondition (AdicCompletion (maximalIdeal R) R ⊗[R] q.asIdeal.ResidueField) 1)
    (q : PrimeSpectrum S) :
    HasSerreCondition (AdicCompletion (maximalIdeal S) S ⊗[S] q.asIdeal.ResidueField) 1 := by
  have hax := serreOneFormalFiberAxioms.{u}
  have hsource : FormalFibersHaveAt.{u, 0, 0} serreConditionOneProperty R :=
    fun p => (serreConditionOneProperty_holds_iff _).mpr (hR p)
  have hS : IsPRingAt.{u, 0, 0} serreConditionOneProperty S :=
    isPRing_of_essFiniteType.{u, u} serreConditionOneProperty
      (fun k K T _ _ _ _ _ _ _ _ hT => hax.1 k K T hT)
      hax.2.1 hax.2.2.1 hax.2.2.2 (isPRingAt_of_formalFibersHaveAt hsource)
  exact (serreConditionOneProperty_holds_iff _).mp (formalFibersHaveAt_of_isPRingAt hS q)

/-- A surjection from a Noetherian ring makes the target an essentially finite type Noetherian
algebra. -/
private theorem exists_essFiniteType_isNoetherianRing_of_surjective {R S : Type u} [CommRing R]
    [CommRing S] [IsNoetherianRing R] (f : R →+* S) (hsurj : Function.Surjective f) :
    ∃ _ : Algebra R S, Algebra.EssFiniteType R S ∧ IsNoetherianRing S :=
  letI := f.toAlgebra
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_surjective
    { toRingHom := f, commutes' := fun _ => rfl } hsurj
  ⟨_, this, Algebra.EssFiniteType.isNoetherianRing R S⟩

/-- **`(S₁)` formal fibres pass to a quotient.** If `S` is a Noetherian local ring which is a
quotient of a Noetherian local ring `R` whose formal fibres satisfy `(S₁)`, then the formal
fibres of `S` satisfy `(S₁)`. -/
public theorem hasSerreCondition_one_formalFibres_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] (f : R →+* S) (hsurj : Function.Surjective f)
    (hR : ∀ q : PrimeSpectrum R,
      HasSerreCondition (AdicCompletion (maximalIdeal R) R ⊗[R] q.asIdeal.ResidueField) 1)
    (q : PrimeSpectrum S) :
    HasSerreCondition (AdicCompletion (maximalIdeal S) S ⊗[S] q.asIdeal.ResidueField) 1 := by
  obtain ⟨_, _, _⟩ := exists_essFiniteType_isNoetherianRing_of_surjective f hsurj
  exact hasSerreCondition_one_formalFibres_of_essFiniteType hR q

section GRing

/-- A local ring whose formal fibres are geometrically regular has `(S₁)` formal fibres. -/
private theorem hasSerreCondition_one_of_formalFibersHaveAt_geometricallyRegular
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : FormalFibersHaveAt.{u, u, u}
      (RingMapProperty.geometricallyRegular : RingMapProperty.{u, u}) A)
    (q : PrimeSpectrum A) :
    HasSerreCondition (AdicCompletion (maximalIdeal A) A ⊗[A] q.asIdeal.ResidueField) 1 := by
  let C := AdicCompletion (maximalIdeal A) A
  let : Algebra q.asIdeal.ResidueField (C ⊗[A] q.asIdeal.ResidueField) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsRegularRing (q.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField]
      (C ⊗[A] q.asIdeal.ResidueField)) :=
    ((RingMapProperty.geometricallyRegular_holds_iff _).mp (hA q)).isRegularRing_tensorProduct
      q.asIdeal.ResidueField
  have : IsRegularRing (C ⊗[A] q.asIdeal.ResidueField) := .of_ringEquiv
    (Algebra.TensorProduct.lid q.asIdeal.ResidueField (C ⊗[A] q.asIdeal.ResidueField)).toRingEquiv
  exact HasSerreCondition.of_isRegularRing 1

/-- **The formal fibres of a localization of a G-ring satisfy `(S₁)`.** Let `R` be a G-ring, let
`p` be a prime of `R` and let `A` be a local ring isomorphic to `R_p`. Then every formal fibre of
`A` satisfies `(S₁)`. -/
public theorem hasSerreCondition_one_formalFibres_of_isGRing_localization
    {R : Type u} [CommRing R] (hR : IsGRing R) (p : Ideal R) [p.IsPrime]
    {A : Type u} [CommRing A] [IsLocalRing A] (e : Localization.AtPrime p ≃+* A)
    (q : PrimeSpectrum A) :
    HasSerreCondition (AdicCompletion (maximalIdeal A) A ⊗[A] q.asIdeal.ResidueField) 1 := by
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing (Localization.AtPrime p) := inferInstance
  refine hasSerreCondition_one_of_formalFibersHaveAt_geometricallyRegular
    (Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, u, u, u} _ e
      ((Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom.{u, u}
        (Localization.AtPrime p)).mpr (hR.2 p))) q

/-- **The formal fibres of a local G-ring satisfy `(S₁)`.** -/
public theorem hasSerreCondition_one_formalFibres_of_isGRing
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsGRing A) (q : PrimeSpectrum A) :
    HasSerreCondition (AdicCompletion (maximalIdeal A) A ⊗[A] q.asIdeal.ResidueField) 1 :=
  hasSerreCondition_one_formalFibres_of_isGRing_localization hA (maximalIdeal A)
    localizationAtMaximalRingEquiv q

end GRing

/-- Let `R` be a universally catenary Noetherian local ring whose formal fibres satisfy `(S₁)`
and let `S` be a local quotient of `R` which is a domain. Then a bound `n ≤ dim(S^∧ / 𝔭)` holds
for every associated prime `𝔭` of the completion of `S` exactly when `n ≤ dim(S)`. -/
@[ega "IV 7.2.5" "implication (b) ⇒ (a)", ega "IV 7.8.4" "partial"]
public theorem le_ringKrullDim_quotient_adicCompletion_iff_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsDomain S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (huc : Ring.IsUniversallyCatenary R)
    (hFibres : ∀ q : PrimeSpectrum R,
      HasSerreCondition (AdicCompletion (maximalIdeal R) R ⊗[R] q.asIdeal.ResidueField) 1)
    (n : WithBot ℕ∞) :
    (∀ p : Ideal (AdicCompletion (maximalIdeal S) S),
      IsAssociatedPrimeStacks (AdicCompletion (maximalIdeal S) S)
        (AdicCompletion (maximalIdeal S) S) p →
        n ≤ ringKrullDim (AdicCompletion (maximalIdeal S) S ⧸ p)) ↔
      n ≤ ringKrullDim S := by
  obtain ⟨_, _, _⟩ := exists_essFiniteType_isNoetherianRing_of_surjective f hsurj
  exact le_ringKrullDim_quotient_adicCompletion_iff n
    (Ring.IsUniversallyCatenary.of_surjective hsurj huc)
    (hasSerreCondition_one_formalFibres_of_surjective f hsurj hFibres)

end
