module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatBaseChangeNaive
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeriesNaiveFlat
public import StacksFrontier.RingTheory.Rig.FlatFiniteBaseChange
public import StacksFrontier.RingTheory.Rig.RestrictedPowerSeriesQuotient
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.BaseChangeSurjection

/-!
# The third paragraph of Stacks 0GGR, and the tag

Let `A → B` be rig-flat and `A → C` adic and topologically of finite type, all three rings
Noetherian and adic.  **Stacks 0GGR** says `C → B ⊗̂_A C` is rig-flat.  Everything but the third
paragraph of the proof is already available:

* paragraph 1 reduces the tag to its naive form
  (`AlgebraicGeometry.FormalSpace.rigFlatBaseChangeByAdicFiniteType_of_naive`);
* paragraphs 4 and 5 give naive rig-flatness of `A{σ} → B ⊗̂_A A{σ}`
  (`Rig.isNaivelyRigFlat_completedTensorProduct_restrictedPowerSeries`).

The third paragraph closes the gap between them.  It replaces `C` by a restricted power series
ring it is a topological quotient of (`Rig.exists_restrictedPowerSeriesQuotientMap`, from
condition (8) of Stacks 0GBW), observes that `B ⊗̂_A C` is then the *ordinary* base change
`(B ⊗̂_A A{σ}) ⊗_{A{σ}} (A{σ} ⧸ ker π)`
(`TopologicalRing.exists_ringEquiv_tensorProduct_completedTensorProduct` — the transitivity of
the completed tensor product in the only case it is needed, where the second factor is cyclic
over the base so no completion is required), and applies the usual base change for flatness
(`Rig.flat_atPrime_tensorProduct_of_flat`, Stacks 00HI) over the base `A{σ}`, whose flatness
clause is what paragraphs 4 and 5 supply.

Condition (3) of Stacks 0GGL then upgrades flatness at the primes away from an ideal of
definition to the flatness clause of naive rig-flatness, and paragraph 1 upgrades naive
rig-flatness to rig-flatness.

## Main results

* `AlgebraicGeometry.FormalSpace.flat_atPrime_completedTensorProduct_of_quotient`: the base
  change for flatness of the third paragraph, with the intermediate ring kept abstract.
* `AlgebraicGeometry.FormalSpace.isNaivelyRigFlat_completedTensorProduct_of_adicFiniteType`:
  **the third paragraph of the proof of Stacks 0GGR** — `C → B ⊗̂_A C` is naively rig-flat for
  an arbitrary adic `A → C` of topologically finite type.
* `AlgebraicGeometry.FormalSpace.naiveRigFlatBaseChangeByAdicFiniteType`: the naive form of the
  base-change assertion, quantified over all triples.
* `AlgebraicGeometry.FormalSpace.isRigFlat_completedTensorProduct_baseChange`: **Stacks 0GGR**.
* `AlgebraicGeometry.FormalSpace.rigFlatBaseChangeByAdicFiniteType`: the same in the shape
  Remark 0GBG consumes.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGL](https://stacks.math.columbia.edu/tag/0GGL)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.FormalSpace

universe u

open RestrictedPowerSeries TopologicalRing

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A prime avoiding one ideal of definition avoids every other, the two being cofinal in each
other's powers. -/
private theorem not_le_of_isIdealOfDefinition {S : Type*} [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] {J J' : Ideal S} (hJ : TopologicalRing.IsIdealOfDefinition J)
    (hJ' : TopologicalRing.IsIdealOfDefinition J') {p : Ideal S} (hp : p.IsPrime)
    (h : ¬ J ≤ p) : ¬ J' ≤ p := by
  obtain ⟨m, hJJ', -⟩ := hJ.exists_pow_le_and_pow_le hJ'
  exact fun hle => h fun x hx => hp.mem_of_pow_mem m (hle (hJJ' (Ideal.pow_mem_pow hx m)))

/-- Flatness at a prime transported along an isomorphism of the ring being localized together
with an isomorphism of the ring it is flat over. -/
private theorem flat_atPrime_of_ringEquiv_of_source {T D S S' : Type u} [CommRing T] [CommRing D]
    [CommRing S] [CommRing S'] (e : T ≃+* D) (ε : S ≃+* S') (ι : S →+* T) (ι' : S' →+* D)
    (hcomp : ∀ x : S, e (ι x) = ι' (ε x)) (p : Ideal D) [p.IsPrime]
    (h : letI : (p.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
      _root_.RingHom.Flat
        ((algebraMap T (Localization.AtPrime (p.comap e.toRingHom))).comp ι)) :
    _root_.RingHom.Flat ((algebraMap D (Localization.AtPrime p)).comp ι') := by
  let : (p.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hmon : (p.comap e.toRingHom).primeCompl.map (e : T ≃* D).toMonoidHom = p.primeCompl := by
    refine le_antisymm ?_ fun y hy => ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · change e.symm y ∉ p.comap e.toRingHom
      rw [Ideal.mem_comap, show e.toRingHom (e.symm y) = y from e.apply_symm_apply y]
      exact hy
  let E : Localization.AtPrime (p.comap e.toRingHom) ≃+* Localization.AtPrime p :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (p.comap e.toRingHom))
      (Localization.AtPrime p) e hmon
  have hE : E.toRingHom.comp
        ((algebraMap T (Localization.AtPrime (p.comap e.toRingHom))).comp ι) =
      (algebraMap D (Localization.AtPrime p)).comp (ι'.comp ε.toRingHom) := by
    refine RingHom.ext fun x => ?_
    change E (algebraMap T (Localization.AtPrime (p.comap e.toRingHom)) (ι x)) = _
    rw [IsLocalization.ringEquivOfRingEquiv_eq hmon (ι x)]
    exact congrArg (algebraMap D (Localization.AtPrime p)) (hcomp x)
  have h' : _root_.RingHom.Flat
      ((algebraMap D (Localization.AtPrime p)).comp (ι'.comp ε.toRingHom)) := by
    rw [← hE]
    exact (_root_.RingHom.Flat.comp_iff_of_bijective_left E.bijective).mpr h
  rw [← RingHom.comp_assoc] at h'
  exact (_root_.RingHom.Flat.comp_iff_of_bijective_right ε.bijective).mp h'

/-- Flatness of a localization away from a point, from the ring-homomorphism form to the module
form.  Kept abstract in the two rings: at the concrete `A{σ} → B ⊗̂_A A{σ}` the instance search
for the module structure on the localization does not terminate within the budget, which is why
`AlgebraicGeometry.FormalSpace.flat_atPrime_completedTensorProduct_of_quotient` takes its
flatness clause in the ring-homomorphism form. -/
private theorem module_flat_of_ringHom_flat {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (a : R)
    (h : _root_.RingHom.Flat
      ((algebraMap S (Localization.Away (algebraMap R S a))).comp (algebraMap R S))) :
    Module.Flat R (Localization.Away (algebraMap R S a)) :=
  _root_.RingHom.flat_algebraMap_iff.mp <| by
    rwa [IsScalarTower.algebraMap_eq R S (Localization.Away (algebraMap R S a))]

/-- In `S ⊗[R] (R ⧸ K)`, the two structure maps agree on `R` through the quotient map. -/
private theorem algebraMap_tensorProduct_quotient {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (K : Ideal R) (r : R) :
    algebraMap R (S ⊗[R] (R ⧸ K)) r =
      algebraMap (R ⧸ K) (S ⊗[R] (R ⧸ K)) (Ideal.Quotient.mk K r) := by
  change algebraMap R S r ⊗ₜ[R] (1 : R ⧸ K) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk K r
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    show r • (1 : R ⧸ K) = Ideal.Quotient.mk K r from (Algebra.algebraMap_eq_smul_one r).symm]

/-- **The base change for flatness of the third paragraph of Stacks 0GGR**, with the
intermediate ring `R` kept abstract.  Let `π : R ↠ C` be a continuous open surjection of
linearly topologized `A`-algebras and let `p` be a prime of `B ⊗̂_A C` not containing the
extension of an ideal of definition `I` of `A`.  If `B ⊗̂_A R` is Noetherian and adic and
`R → B ⊗̂_A R` satisfies the flatness clause of naive rig-flatness, then `B ⊗̂_A C` is flat
over `C` after localizing at `p`.

`B ⊗̂_A C` is the ordinary base change of `B ⊗̂_A R` along `R ↠ R ⧸ ker π`
(`TopologicalRing.exists_ringEquiv_tensorProduct_completedTensorProduct`), so the usual base
change for flatness `Rig.flat_atPrime_tensorProduct_of_flat` applies over `R`. -/
public theorem flat_atPrime_completedTensorProduct_of_quotient
    {A B R C : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
    [Algebra A B] [Algebra A R] [Algebra A C]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (π : R →ₐ[A] C) (hsurj : Function.Surjective π) (hcont : Continuous π)
    (hopen : IsOpenMap π) (I : Ideal A) (hIdef : TopologicalRing.IsIdealOfDefinition I)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A R)))
    [IsNoetherianRing (CompletedTensorProduct (R := A) (M := B) (N := R))]
    (hB'adic : ∃ 𝔦 : Ideal (CompletedTensorProduct (R := A) (M := B) (N := R)),
      _root_.IsAdic 𝔦)
    (hflat : Rig.RingHom.IsNaivelyRigFlat
      (algebraMap R (CompletedTensorProduct (R := A) (M := B) (N := R))))
    (p : Ideal (CompletedTensorProduct (R := A) (M := B) (N := C))) (hp : p.IsPrime)
    (hpaway : ¬ I.map (algebraMap A
      (CompletedTensorProduct (R := A) (M := B) (N := C))) ≤ p) :
    letI : p.IsPrime := hp
    _root_.RingHom.Flat
      ((algebraMap (CompletedTensorProduct (R := A) (M := B) (N := C))
        (Localization.AtPrime p)).comp
          (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C)))) := by
  let : p.IsPrime := hp
  set K : Ideal R := RingHom.ker (π : R →+* C)
  set ε : (R ⧸ K) ≃+* C := RingHom.quotientKerEquivOfSurjective hsurj
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorProduct_completedTensorProduct
    (B := B) π hsurj hcont hopen I hJ hK hB'adic
  have hecomp : ∀ x : R ⧸ K,
      e (algebraMap (R ⧸ K) ((CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R]
        (R ⧸ K)) x) =
      algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C)) (ε x) := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (he r).trans (congrArg (algebraMap C
      (CompletedTensorProduct (R := A) (M := B) (N := C)))
        (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj r).symm)
  have : (p.comap e.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hq : ¬ (I.map (algebraMap A R)).map
      (algebraMap R ((CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R] (R ⧸ K)))
      ≤ p.comap e.toRingHom := by
    obtain ⟨a, haI, hap⟩ : ∃ a ∈ I,
        algebraMap A (CompletedTensorProduct (R := A) (M := B) (N := C)) a ∉ p :=
      SetLike.not_le_iff_exists.mp (Ideal.map_le_iff_le_comap.not.mp hpaway)
    refine fun hle => hap ?_
    have hmem := hle (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap A R) haI))
    rw [Ideal.mem_comap] at hmem
    have hval : e.toRingHom (algebraMap R
          ((CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R] (R ⧸ K))
          (algebraMap A R a)) =
        algebraMap A (CompletedTensorProduct (R := A) (M := B) (N := C)) a := by
      change e (algebraMap R _ (algebraMap A R a)) = _
      rw [algebraMap_tensorProduct_quotient K, hecomp,
        show ε (Ideal.Quotient.mk K (algebraMap A R a)) = algebraMap A C a from
          (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj _).trans (π.commutes a),
        ← IsScalarTower.algebraMap_apply A C
          (CompletedTensorProduct (R := A) (M := B) (N := C)) a]
    rwa [hval] at hmem
  exact flat_atPrime_of_ringEquiv_of_source e ε
    (algebraMap (R ⧸ K) ((CompletedTensorProduct (R := A) (M := B) (N := R)) ⊗[R] (R ⧸ K)))
    (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C))) hecomp p
    (Rig.flat_atPrime_tensorProduct_of_flat
      (A := R) (B := CompletedTensorProduct (R := A) (M := B) (N := R)) (C := R ⧸ K)
      (I.map (algebraMap A R)) (isIdealOfDefinition_of_isAdic hK)
      (fun a ha => module_flat_of_ringHom_flat a (hflat.2.2 a ha))
      (p.comap e.toRingHom) hq)

/-- For an ideal `J` defining the topology, `J`-adic completeness is completeness of the ring. -/
private theorem isAdicComplete_iff_isComplete {S : Type*} [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S] {J : Ideal S} (hJ : _root_.IsAdic J) :
    IsAdicComplete J S ↔ TopologicalRing.IsComplete S := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  exact hJ.isAdicComplete_iff.trans and_comm

/-- `A{σ}` is adic: its coefficient ideal defines its topology and it is complete for it. -/
private theorem isAdic_restrictedPowerSeriesRing {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] (I : Ideal A)
    (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)] :
    TopologicalRing.IsAdic (RestrictedPowerSeries I σ) := by
  have hcoef : _root_.IsAdic (coefficientIdeal I σ) :=
    isAdic_coefficientIdeal I (Ideal.fg_of_isNoetherianRing I) σ
  exact ⟨⟨_, isIdealOfDefinition_of_isAdic hcoef, hcoef⟩,
    (isAdicComplete_iff_isComplete hcoef).mp (Rig.isAdicComplete_restrictedPowerSeries I σ)⟩

/-- `B ⊗̂_A A{σ}` is Noetherian: Stacks 0GB4, fed by finite type on the reductions of `A → B`,
which rig-flatness supplies. -/
private theorem isNoetherianRing_completedTensorProduct_restrictedPowerSeries
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [IsNoetherianRing B] [Algebra A B]
    (h₀ : TopologicalRing.IsAdic A) (h₁ : TopologicalRing.IsAdic B)
    (hc₁ : Continuous (algebraMap A B)) (hP : Rig.RingHom.IsRigFlat (algebraMap A B))
    (I : Ideal A) (hIadic : _root_.IsAdic I) (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)] :
    IsNoetherianRing
      (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ)) := by
  obtain ⟨I₀, hI₀def, -⟩ := h₀.1
  let : IsNoetherianRing (RestrictedPowerSeries I σ) :=
    Rig.isNoetherianRing_restrictedPowerSeries I σ
  exact completedTensorProduct_isNoetherianRing hc₁
    (Rig.continuous_coefficientRingHom I hIadic (Ideal.fg_of_isNoetherianRing I) σ) h₁.1
    (isAdic_restrictedPowerSeriesRing I σ).1
    ⟨topologicalNilradical_le_comap _ hc₁,
      Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType (algebraMap A B) hc₁
        ⟨I₀, hI₀def.1, fun x hx =>
          TopologicalRing.CompletionOver.isTopologicallyNilpotent_of_mem_isIdealOfDefinition
            hI₀def hx⟩
        (_root_.RingHom.isTaut_of_isAdic (algebraMap A B) hc₁ hP.1) hP.2.1⟩

/-- `B ⊗̂_A A{σ}` is adic: Stacks 0GB4. -/
private theorem isAdic_completedTensorProduct_restrictedPowerSeries
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [IsNoetherianRing B] [Algebra A B]
    (h₁ : TopologicalRing.IsAdic B) (hc₁ : Continuous (algebraMap A B))
    (I : Ideal A) (hIadic : _root_.IsAdic I) (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)] :
    ∃ 𝔦 : Ideal (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ)),
      _root_.IsAdic 𝔦 := by
  obtain ⟨I₁, hI₁def, -⟩ := h₁.1
  exact (completedTensorProduct_isAdic hc₁
    (Rig.continuous_coefficientRingHom I hIadic (Ideal.fg_of_isNoetherianRing I) σ) h₁.1
    ⟨I₁, hI₁def, Ideal.fg_of_isNoetherianRing I₁⟩ (isAdic_restrictedPowerSeriesRing I σ).1
    ⟨_, isIdealOfDefinition_of_isAdic
      (isAdic_coefficientIdeal I (Ideal.fg_of_isNoetherianRing I) σ),
      (Ideal.fg_of_isNoetherianRing I).map _⟩).1.imp fun _ => And.right

/-- Condition (3) of Stacks 0GGL: flatness at every prime away from an ideal of definition gives
naive rig-flatness. -/
private theorem isNaivelyRigFlat_of_flat_atPrime {C D : Type u} [CommRing C] [CommRing D]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [TopologicalSpace D]
    [IsTopologicalRing D] [IsLinearTopology D D] [Algebra C D]
    (hcont : Continuous (algebraMap C D)) (hCw : TopologicalRing.IsWeaklyAdmissible C)
    (hDw : TopologicalRing.IsWeaklyAdmissible D)
    (hCstar : ∃ I : Ideal C, _root_.IsAdic I ∧ I.FG)
    (hDstar : ∃ J : Ideal D, _root_.IsAdic J ∧ J.FG)
    (hadic : _root_.RingHom.IsAdic (algebraMap C D))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap C D))
    (h : ∀ (p : Ideal D) (hp : p.IsPrime),
      (∃ J : Ideal D, TopologicalRing.IsIdealOfDefinition J ∧ ¬ J ≤ p) →
        letI : p.IsPrime := hp
        _root_.RingHom.Flat ((algebraMap D (Localization.AtPrime p)).comp (algebraMap C D))) :
    Rig.RingHom.IsNaivelyRigFlat (algebraMap C D) :=
  ⟨hadic, hft, ((Rig.naivelyRigFlat_tfae (algebraMap C D) hcont hCw hDw hCstar hDstar
    hadic).out 3 1).mp h⟩

/-- The flatness at one prime that the third paragraph of Stacks 0GGR provides, with the
presentation of `C` and the Stacks 0GB4 facts about `B ⊗̂_A A{σ}` supplied. -/
private theorem flat_atPrime_of_presentation
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (h₁ : TopologicalRing.IsAdic B) (hc₁ : Continuous (algebraMap A B))
    (hP : Rig.RingHom.IsRigFlat (algebraMap A B))
    (hAw : TopologicalRing.IsWeaklyAdmissible A)
    (I : Ideal A) (hIadic : _root_.IsAdic I)
    (hIdef : TopologicalRing.IsIdealOfDefinition I) (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)]
    [IsAdicComplete I A] (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    [IsNoetherianRing
      (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ))]
    (hcoef : _root_.IsAdic (I.map (algebraMap A (RestrictedPowerSeries I σ))))
    (π : RestrictedPowerSeries I σ →+* C) (hsurj : Function.Surjective π)
    (hπcont : Continuous π) (hπopen : IsOpenMap π)
    (hπcomp : π.comp (coefficientRingHom I σ) = algebraMap A C)
    (hIDdef : TopologicalRing.IsIdealOfDefinition
      (I.map (algebraMap A (CompletedTensorProduct (R := A) (M := B) (N := C)))))
    (p : Ideal (CompletedTensorProduct (R := A) (M := B) (N := C))) (hp : p.IsPrime)
    (hpaway : ∃ J : Ideal (CompletedTensorProduct (R := A) (M := B) (N := C)),
      TopologicalRing.IsIdealOfDefinition J ∧ ¬ J ≤ p) :
    letI : p.IsPrime := hp
    _root_.RingHom.Flat
      ((algebraMap (CompletedTensorProduct (R := A) (M := B) (N := C))
        (Localization.AtPrime p)).comp
          (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C)))) := by
  obtain ⟨J, hJdef, hJp⟩ := hpaway
  exact flat_atPrime_completedTensorProduct_of_quotient (A := A) (B := B)
    (R := RestrictedPowerSeries I σ) (C := C)
    { π with commutes' := fun a => DFunLike.congr_fun hπcomp a }
    hsurj hπcont hπopen I hIdef hJ hcoef
    (isAdic_completedTensorProduct_restrictedPowerSeries h₁ hc₁ I hIadic σ)
    (Rig.isNaivelyRigFlat_completedTensorProduct_restrictedPowerSeries
      I hIadic hJ σ hc₁ hP.2.1 hAw hP)
    p hp (not_le_of_isIdealOfDefinition hJdef hIDdef hp hJp)

/-- An adic ring is complete for any ideal defining its topology. -/
private theorem isAdicComplete_of_isAdic {S : Type*} [CommRing S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S] (hS : TopologicalRing.IsAdic S) {J : Ideal S}
    (hJ : _root_.IsAdic J) : IsAdicComplete J S :=
  (isAdicComplete_iff_isComplete hJ).mpr hS.2

/-- The third paragraph of the proof of Stacks 0GGR, from the presentation of `C` onwards. -/
private theorem isNaivelyRigFlat_of_presentation
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (h₀ : TopologicalRing.IsAdic A) (h₁ : TopologicalRing.IsAdic B)
    (hc₁ : Continuous (algebraMap A B)) (hc₂ : Continuous (algebraMap A C))
    (hP : Rig.RingHom.IsRigFlat (algebraMap A B))
    (hQadic : _root_.RingHom.IsAdic (algebraMap A C))
    (hAw : TopologicalRing.IsWeaklyAdmissible A)
    (hCw : TopologicalRing.IsWeaklyAdmissible C)
    (hDw : TopologicalRing.IsWeaklyAdmissible
      (CompletedTensorProduct (R := A) (M := B) (N := C)))
    (hDcont : Continuous (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C))))
    (hDadic : _root_.RingHom.IsAdic
      (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C))))
    (hDft : TopologicalRing.IsTopologicallyOfFiniteType
      (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C))))
    (I₂ : Ideal C) (hI₂adic : _root_.IsAdic I₂)
    (I : Ideal A) (hIadic : _root_.IsAdic I)
    (hIdef : TopologicalRing.IsIdealOfDefinition I) (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)]
    (π : RestrictedPowerSeries I σ →+* C) (hsurj : Function.Surjective π)
    (hπcont : Continuous π) (hπopen : IsOpenMap π)
    (hπcomp : π.comp (coefficientRingHom I σ) = algebraMap A C) :
    Rig.RingHom.IsNaivelyRigFlat (algebraMap C
      (CompletedTensorProduct (R := A) (M := B) (N := C))) := by
  have hJ : _root_.IsAdic (I.map (algebraMap A B)) :=
    _root_.RingHom.isAdic_map_of_isAdic (algebraMap A B) hP.1 hIadic
  have := isAdicComplete_of_isAdic h₀ hIadic
  have := isAdicComplete_of_isAdic h₁ hJ
  let : IsNoetherianRing
      (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ)) :=
    isNoetherianRing_completedTensorProduct_restrictedPowerSeries h₀ h₁ hc₁ hP I hIadic σ
  have hADadic : _root_.RingHom.IsAdic
      (algebraMap A (CompletedTensorProduct (R := A) (M := B) (N := C))) := by
    rw [IsScalarTower.algebraMap_eq A C (CompletedTensorProduct (R := A) (M := B) (N := C))]
    exact _root_.RingHom.isAdic_comp (algebraMap A C)
      (algebraMap C (CompletedTensorProduct (R := A) (M := B) (N := C))) hc₂ hDcont hQadic hDadic
  exact isNaivelyRigFlat_of_flat_atPrime hDcont hCw hDw
    ⟨I₂, hI₂adic, Ideal.fg_of_isNoetherianRing I₂⟩
    ⟨_, _root_.RingHom.isAdic_map_of_isAdic _ hDadic hI₂adic,
      (Ideal.fg_of_isNoetherianRing I₂).map _⟩ hDadic hDft
    (fun p hp hpaway => flat_atPrime_of_presentation h₁ hc₁ hP hAw I hIadic hIdef σ hJ
      (isAdic_coefficientIdeal I (Ideal.fg_of_isNoetherianRing I) σ) π hsurj hπcont hπopen hπcomp
      (isIdealOfDefinition_of_isAdic (_root_.RingHom.isAdic_map_of_isAdic _ hADadic hIadic))
      p hp hpaway)

/-- **The third paragraph of the proof of Stacks 0GGR.**  For `A → B` rig-flat and `A → C` adic
and topologically of finite type between Noetherian adic rings, the base-change arrow
`C → B ⊗̂_A C` is *naively* rig-flat (Stacks 0GGM).

`C` is a topological quotient of a restricted power series ring
(`Rig.exists_restrictedPowerSeriesQuotientMap`), so
`AlgebraicGeometry.FormalSpace.flat_atPrime_completedTensorProduct_of_quotient` applies with
`R = A{σ}`, its flatness clause being
`Rig.isNaivelyRigFlat_completedTensorProduct_restrictedPowerSeries` — the fourth and fifth
paragraphs of the proof.  Condition (3) of Stacks 0GGL turns the resulting flatness at the
primes away from an ideal of definition into the flatness clause of naive rig-flatness, and
adicness and topological finite type of the arrow itself are Stacks 0GB4. -/
public theorem isNaivelyRigFlat_completedTensorProduct_of_adicFiniteType
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (h₀ : TopologicalRing.IsAdic A) (h₁ : TopologicalRing.IsAdic B)
    (h₂ : TopologicalRing.IsAdic C) (hc₁ : Continuous (algebraMap A B))
    (hc₂ : Continuous (algebraMap A C)) (hP : Rig.RingHom.IsRigFlat (algebraMap A B))
    (hQ : _root_.RingHom.IsAdic (algebraMap A C) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C)) :
    Rig.RingHom.IsNaivelyRigFlat (algebraMap C
      (CompletedTensorProduct (R := A) (M := B) (N := C))) := by
  classical
  obtain ⟨I₀, hI₀def, hI₀adic⟩ := h₀.1
  obtain ⟨I₂, hI₂def, hI₂adic⟩ := h₂.1
  have hBw := Rig.weaklyAdmissible_of_isAdicRing h₁
  have hCw := Rig.weaklyAdmissible_of_isAdicRing h₂
  obtain ⟨hDadic, hDft⟩ :=
    isAdic_and_isTopologicallyOfFiniteType_completedTensorProduct_baseChange
      (R := A) (A := B) (C := C) hBw hCw
      ⟨I₂, Ideal.fg_of_isNoetherianRing I₂, hI₂adic⟩ hc₁ hc₂ ⟨hP.1, hP.2.1⟩
  obtain ⟨I, hIdef, σ, _, π, hsurj, hπcont, hπopen, hπcomp⟩ :=
    Rig.exists_restrictedPowerSeriesQuotientMap h₀ h₂
      ⟨I₀, hI₀def, Ideal.fg_of_isNoetherianRing I₀⟩
      ⟨I₂, hI₂def, Ideal.fg_of_isNoetherianRing I₂⟩ hc₂ hQ.1 hQ.2
  have hIadic : _root_.IsAdic I := (Rig.isIdealOfDefinition_iff_isAdic ⟨I₀, hI₀adic⟩ I).1 hIdef
  let : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    isLinearTopology_restrictedPowerSeries I (Ideal.fg_of_isNoetherianRing I) σ
  exact isNaivelyRigFlat_of_presentation h₀ h₁ hc₁ hc₂ hP hQ.1
    (Rig.weaklyAdmissible_of_isAdicRing h₀) hCw
    (completedTensorProduct_isWeaklyAdmissible (B := A) (A := B) (C := C) hBw.1 hCw.1)
    continuous_algebraMap_completedTensorProduct_right hDadic hDft I₂ hI₂adic I hIadic hIdef σ
    π hsurj hπcont hπopen hπcomp

/-- **The naive form of the base-change assertion of Stacks 0GGR**, quantified over all triples
of rings: this is `AlgebraicGeometry.FormalSpace.NaiveRigFlatBaseChangeByAdicFiniteType`, what
the second to fifth paragraphs of the proof establish. -/
public theorem naiveRigFlatBaseChangeByAdicFiniteType :
    NaiveRigFlatBaseChangeByAdicFiniteType.{u} :=
  isNaivelyRigFlat_completedTensorProduct_of_adicFiniteType

/-- **Stacks 0GGR.**  Let `A → B` and `A → C` be arrows of `WAdm^Noeth`.  If `A → B` is rig-flat
and `A → C` is adic and topologically of finite type, then `C → B ⊗̂_A C` is rig-flat.

The naive form is `AlgebraicGeometry.FormalSpace.naiveRigFlatBaseChangeByAdicFiniteType`, the
second to fifth paragraphs of the proof; the first paragraph upgrades it to rig-flatness through
`AlgebraicGeometry.FormalSpace.rigFlat_completedTensorProduct_of_naive`. -/
@[stacks 0GGR]
public theorem isRigFlat_completedTensorProduct_baseChange
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra A B] [Algebra A C] [IsNoetherianRing A]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (h₀ : TopologicalRing.IsAdic A) (h₁ : TopologicalRing.IsAdic B)
    (h₂ : TopologicalRing.IsAdic C) (hc₁ : Continuous (algebraMap A B))
    (hc₂ : Continuous (algebraMap A C)) (hP : Rig.RingHom.IsRigFlat (algebraMap A B))
    (hQ : _root_.RingHom.IsAdic (algebraMap A C) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A C)) :
    Rig.RingHom.IsRigFlat (algebraMap C
      (CompletedTensorProduct (R := A) (M := B) (N := C))) :=
  (rigFlat_completedTensorProduct_of_naive naiveRigFlatBaseChangeByAdicFiniteType
    h₀ h₁ h₂ hc₁ hc₂ hP hQ).2.2

/-- **Stacks 0GGR in the shape Remark 0GBG consumes**, discharging the landing site
`AlgebraicGeometry.FormalSpace.RigFlatBaseChangeByAdicFiniteType`: the naive form
(`AlgebraicGeometry.FormalSpace.naiveRigFlatBaseChangeByAdicFiniteType`) fed through the first
paragraph of the proof. -/
public theorem rigFlatBaseChangeByAdicFiniteType : RigFlatBaseChangeByAdicFiniteType.{u} :=
  rigFlatBaseChangeByAdicFiniteType_of_naive naiveRigFlatBaseChangeByAdicFiniteType

end AlgebraicGeometry.FormalSpace

end
