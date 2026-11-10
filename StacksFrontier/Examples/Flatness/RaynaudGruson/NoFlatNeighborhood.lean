module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksCore.RingTheory.Nakayama
public import StacksFrontier.Examples.Flatness.RaynaudGruson.CurveModel
public import StacksFrontier.Examples.Flatness.RaynaudGruson.FlatAtPrime
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus

/-!
# No flat and no finitely presented neighbourhood in the Raynaud--Gruson example

For the finite type map `A → B` of the Raynaud--Gruson construction, inverting any element of
`B` outside the distinguished prime `q_B` gives an algebra over `A` which is neither flat nor of
finite presentation, although the localization of `B` at `q_B` is flat over `A`.

## Main results

* `Stacks.Examples.RaynaudGruson.not_flat_localizationAway`: no principal neighbourhood of
  `q_B` is flat over `A`.
* `Stacks.Examples.RaynaudGruson.aToB_away_not_finitePresentation`: no principal neighbourhood
  of `q_B` is of finite presentation over `A`.
* `Stacks.Examples.RaynaudGruson.exists_flat_at_prime_not_flat_on_neighborhood`: the whole of
  Stacks 05G2, namely the existence of a local ring `A`, a finite type ring map `A → B` and a
  prime `q` of `B` lying over the maximal ideal of `A` such that `B_q` is flat over `A` while
  `B_g` is neither of finite presentation nor flat over `A` for every `g ∈ B` outside `q`.

The four structural clauses the example needs — that `A` is local, that `A → B` is of finite
type, that `q_B` is prime and that it contracts to the maximal ideal of `A` — are
`Stacks.Examples.RaynaudGruson.ringA_isLocalRing`, `aToB_finiteType`, `idealQB_isPrime` and
`idealQB_comap_eq_maximalIdeal` of
`StacksFrontier.Examples.Flatness.RaynaudGruson.Structure`, and the flat-at-the-prime clause is
`Stacks.Examples.RaynaudGruson.aToB_localization_flat` of
`StacksFrontier.Examples.Flatness.RaynaudGruson.FlatAtPrime`.

## Implementation notes

The kernel of `C_g → B_g` lies in the extension of the square-zero ideal `I`, so flatness of
`B_g` over `A` would force that kernel to vanish; but `ξₙ` lies in it and is nonzero in `C_g` as
soon as `g ∉ qₙ`, which happens for some `n`. Finite presentation is excluded from this: the
relative flat locus of a finitely presented algebra is open, so finite presentation of `B_g`
together with flatness at `q_B` would make some smaller principal neighbourhood flat.

## References

* [Stacks Project, Tag 05G2](https://stacks.math.columbia.edu/tag/05G2)
-/

@[expose] public section

noncomputable section

namespace Stacks.Examples.RaynaudGruson

universe u

variable (k : Type u) [Field k]

/-- The ideal `qₙ` of `C` is prime: the quotient of `C` by it is a field. -/
instance idealQ_isPrime (n : PNat) : (idealQ k n).IsPrime := by
  obtain ⟨e⟩ := quotient_idealQ_equiv_fractionRing k n
  exact (Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField (Field.toIsField (FractionRing (Polynomial k))) e.toMulEquiv)).isPrime

private lemma xi_ne_zero_away (n : PNat) (c : ringC k) (hc : c ∉ idealQ k n) :
    algebraMap (ringC k) (Localization.Away c) (xi k n) ≠ 0 := by
  intro h
  obtain ⟨⟨m, j, rfl⟩, hmz⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers c) (Localization.Away c) _).mp h
  refine hc ((idealQ_isPrime k n).mem_of_pow_mem j ?_)
  rw [← annihilator_xi k n]
  exact (Submodule.mem_annihilator_span_singleton _ _).mpr hmz

private alias idealI_mul_self := Stacks.Examples.RaynaudGruson.idealI_sq

private lemma injective_of_flat_of_ker_le_map
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Flat R T]
    (I : Ideal R) (hI : I * I = ⊥) (φ : S →ₐ[R] T) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.toRingHom ≤ I.map (algebraMap R S)) :
    Function.Injective φ := by
  suffices h : φ.toLinearMap.ker = ⊥ from LinearMap.ker_eq_bot.mp h
  refine Submodule.eq_bot_of_le_smul_of_isNilpotent I _ ⟨2, by simpa [pow_two] using hI⟩ ?_
  rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I φ.toLinearMap hφ]
  refine le_inf le_rfl ?_
  rwa [Ideal.smul_top_eq_map]

private lemma lift_outside_idealQC (g : ringB k) (hg : g ∉ idealQB k) :
    ∃ c : ringC k, cToB k c = g ∧ c ∉ idealQC k := by
  obtain ⟨c, hc⟩ := g.property
  refine ⟨c, Subtype.ext hc, fun h => hg ?_⟩
  rw [← (Subtype.ext hc : cToB k c = g)]
  exact Ideal.mem_map_of_mem (cToB k) h

private lemma injective_awayMap_of_flat (c : ringC k) (hc : c ∉ idealQC k)
    (hflat : RingHom.Flat
      ((algebraMap (ringB k) (Localization.Away (cToB k c))).comp (aToB k))) :
    Function.Injective (Localization.awayMap (cToB k) c) := by
  let S := Localization.Away c
  let T := Localization.Away (cToB k c)
  let aS : ringA k →+* S := (algebraMap (ringC k) S).comp (aToC k)
  let aT : ringA k →+* T := (algebraMap (ringB k) T).comp (aToB k)
  let : Algebra (ringA k) S := aS.toAlgebra
  let : Algebra (ringA k) T := aT.toAlgebra
  have : Module.Flat (ringA k) T := hflat
  let φ : S →ₐ[ringA k] T :=
    { Localization.awayMap (cToB k) c with
      commutes' := fun a => IsLocalization.map_eq _ _ }
  have hsurj : Function.Surjective φ := by
    refine Localization.awayMap_surjective_iff.mpr fun b => ?_
    obtain ⟨a, ha⟩ := b.property
    exact ⟨a, 0, by simpa using (Subtype.ext ha : cToB k a = b)⟩
  have hker : RingHom.ker φ.toRingHom ≤ (idealI k).map aS := by
    change RingHom.ker (Localization.awayMap (cToB k) c) ≤ _
    rw [ker_awayMap_eq_span_xi k c hc]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨n, -, rfl⟩
    change algebraMap (ringC k) S ((zC k - xC k ^ (n.1 : ℕ)) * aToC k (zA k n.1)) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem aS (Ideal.subset_span ⟨n.1, rfl⟩))
  exact injective_of_flat_of_ker_le_map (idealI k) (idealI_mul_self k) φ hsurj hker

/-- No principal neighbourhood of the distinguished prime of `B` is flat over `A`. -/
theorem not_flat_localizationAway : ∀ g ∉ idealQB k,
    ¬ RingHom.Flat ((algebraMap (ringB k) (Localization.Away g)).comp (aToB k)) := by
  intro g hg hflat
  obtain ⟨c, rfl, hc⟩ := lift_outside_idealQC k g hg
  obtain ⟨n, hn⟩ := exists_not_mem_idealQ k c hc
  have hxi : cToB k (xi k n) = 0 := by
    rw [← RingHom.mem_ker, ker_cToB_eq_span_xi]
    exact Ideal.subset_span ⟨n, rfl⟩
  have hmap : Localization.awayMap (cToB k) c
      (algebraMap (ringC k) (Localization.Away c) (xi k n)) = 0 :=
    (IsLocalization.map_eq _ _).trans (by rw [hxi, map_zero])
  exact xi_ne_zero_away k n c hn
    (injective_awayMap_of_flat k c hc hflat (by rw [hmap, map_zero]))

private theorem flat_at_idealQB :
    letI : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
    letI : Algebra (ringA k) (Localization.AtPrime (idealQB k)) := inferInstance
    Module.Flat (ringA k) (Localization.AtPrime (idealQB k)) := by
  classical
  let : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
  let : Algebra (ringA k) (Localization.AtPrime (idealQB k)) := inferInstance
  let T := bAtQB k
  have hT : Submonoid.closure {b : ringB k | b ∉ idealQB k} = (idealQB k).primeCompl :=
    le_antisymm (Submonoid.closure_le.2 fun _ hb => hb) fun _ hb => Submonoid.subset_closure hb
  have : IsLocalization (idealQB k).primeCompl T := by
    change IsLocalization (idealQB k).primeCompl
      (Localization (Submonoid.closure {b : ringB k | b ∉ idealQB k}))
    rw [← hT]
    infer_instance
  let : Algebra (ringA k) T := ((algebraMap (ringB k) T).comp (aToB k)).toAlgebra
  let : Module (ringA k) T := Algebra.toModule
  let e : Localization.AtPrime (idealQB k) ≃ₐ[ringB k] T :=
    IsLocalization.algEquiv (idealQB k).primeCompl (Localization.AtPrime (idealQB k)) T
  let eA : Localization.AtPrime (idealQB k) ≃ₐ[ringA k] T :=
    { e.toRingEquiv with
      commutes' := fun x => e.commutes (aToB k x) }
  have : @Module.Flat (ringA k) T _ _ Algebra.toModule :=
    RingHom.flat_algebraMap_iff.mp (aToB_localization_flat k)
  exact Module.Flat.of_linearEquiv eA.toLinearEquiv

private theorem flat_at_localized_prime (g : ringB k)
    (pG : PrimeSpectrum (Localization.Away g))
    (hpG : pG.asIdeal.under (ringB k) = idealQB k) :
    letI : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
    letI : Algebra (ringA k) (Localization.AtPrime pG.asIdeal) := inferInstance
    Module.Flat (ringA k) (Localization.AtPrime pG.asIdeal) := by
  classical
  let : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
  let : Algebra (ringA k) (Localization.AtPrime (idealQB k)) := inferInstance
  let : Algebra (ringA k) (Localization.AtPrime pG.asIdeal) := inferInstance
  have hflatQ : Module.Flat (ringA k) (Localization.AtPrime (idealQB k)) := flat_at_idealQB k
  have hcomap : pG.asIdeal.comap (algebraMap (ringB k)
      (Localization (Submonoid.powers g))) = idealQB k := hpG
  let : (pG.asIdeal.comap (algebraMap (ringB k)
      (Localization (Submonoid.powers g)))).IsPrime := hcomap.symm ▸ idealQB_isPrime k
  have hprimeCompl : (idealQB k).primeCompl =
      (pG.asIdeal.comap (algebraMap (ringB k)
        (Localization (Submonoid.powers g)))).primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff]
    rw [hcomap]
  let hlocComap : IsLocalization
      (pG.asIdeal.comap (algebraMap (ringB k)
        (Localization (Submonoid.powers g)))).primeCompl
      (Localization.AtPrime pG.asIdeal) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime
      (M := Submonoid.powers g) pG.asIdeal
  let : IsLocalization (idealQB k).primeCompl
      (Localization.AtPrime pG.asIdeal) := hprimeCompl.symm ▸ hlocComap
  let eB : Localization.AtPrime (idealQB k) ≃ₐ[ringB k] Localization.AtPrime pG.asIdeal :=
    IsLocalization.algEquiv (idealQB k).primeCompl
      (Localization.AtPrime (idealQB k)) (Localization.AtPrime pG.asIdeal)
  let eA : Localization.AtPrime (idealQB k) ≃ₐ[ringA k] Localization.AtPrime pG.asIdeal :=
    { eB.toRingEquiv with
      commutes' := fun x => eB.commutes (aToB k x) }
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflatQ eA.symm.toLinearEquiv

/-- Every principal neighbourhood of the distinguished prime `q_B` of `B` has a prime lying
over `q_B`. -/
theorem exists_prime_away_under_eq_idealQB (g : ringB k) (hg : g ∉ idealQB k) :
    ∃ pG : PrimeSpectrum (Localization.Away g), pG.asIdeal.under (ringB k) = idealQB k := by
  have hdisj : Disjoint (Submonoid.powers g : Set (ringB k)) (idealQB k : Set (ringB k)) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hg ((idealQB_isPrime k).mem_of_pow_mem n hx)
  exact ⟨(IsLocalization.primeSpectrumOrderIso (Submonoid.powers g) (Localization.Away g)).symm
      ⟨⟨idealQB k, inferInstance⟩, hdisj⟩,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g)
      (Localization.Away g) (idealQB_isPrime k) hdisj⟩

/-- No principal neighbourhood of the distinguished prime of `B` is of finite presentation
over `A`. -/
theorem aToB_away_not_finitePresentation : ∀ g ∉ idealQB k,
    ¬ ((algebraMap (ringB k) (Localization.Away g)).comp (aToB k)).FinitePresentation := by
  classical
  intro g hg hfp
  let : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
  let : Algebra (ringA k) (Localization.Away g) := inferInstance
  have : Algebra.FinitePresentation (ringA k) (Localization.Away g) := by
    rwa [← RingHom.finitePresentation_algebraMap]
  obtain ⟨pG, hpG⟩ := exists_prime_away_under_eq_idealQB k g hg
  have hflatAt : Module.Flat (ringA k)
      (LocalizedModule.AtPrime pG.asIdeal (Localization.Away g)) := by
    change Module.Flat (ringA k) (Localization.AtPrime pG.asIdeal)
    exact flat_at_localized_prime k g pG hpG
  obtain ⟨h, hh, hflatAway⟩ :=
    Module.exists_away_flat_of_flat_atPrime (R := ringA k) (S := Localization.Away g)
      (N := Localization.Away g) pG hflatAt
  let fAway : Localization.Away g →ₗ[Localization.Away g] Localization.Away h :=
    Algebra.linearMap (Localization.Away g) (Localization.Away h)
  have hfAway : IsLocalizedModule (Submonoid.powers h) fAway :=
    (isLocalizedModule_iff_isLocalization' (Submonoid.powers h) _).mpr inferInstance
  have : Module.Flat (ringA k) (LocalizedModule.Away h (Localization.Away g)) := hflatAway
  have : Module.Flat (ringA k) (Localization.Away h) :=
    Module.Flat.of_linearEquiv
      ((IsLocalizedModule.iso (Submonoid.powers h) fAway).symm.restrictScalars (ringA k))
  let b : ringB k := (IsLocalization.Away.sec g h).1
  have hb : b ∉ idealQB k := by
    intro hbq
    have hb' : b ∈ pG.asIdeal.comap (algebraMap (ringB k) (Localization.Away g)) := by
      simpa only [Ideal.under] using (hpG ▸ hbq : b ∈ pG.asIdeal.under (ringB k))
    obtain ⟨u, hu⟩ := IsLocalization.Away.associated_sec_fst g h
    exact hh (hu ▸ Ideal.mul_mem_right (↑u) pG.asIdeal (Ideal.mem_comap.mp hb'))
  have : IsLocalization.Away (g * b) (Localization.Away h) :=
    IsLocalization.Away.mul_of_associated g b h (IsLocalization.Away.associated_sec_fst g h)
  let : Algebra (ringA k) (Localization.Away (g * b)) := inferInstance
  refine not_flat_localizationAway k (g * b)
    (fun hgbq => ((idealQB_isPrime k).mul_mem_iff_mem_or_mem.mp hgbq).elim hg hb) ?_
  change (algebraMap (ringA k) (Localization.Away (g * b))).Flat
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_linearEquiv ((IsLocalization.algEquiv (Submonoid.powers (g * b))
      (Localization.Away (g * b)) (Localization.Away h)).toLinearEquiv.restrictScalars (ringA k)))

private theorem aToB_atPrime_flat :
    ((algebraMap (ringB k) (Localization.AtPrime (idealQB k))).comp (aToB k)).Flat := by
  let : Algebra (ringA k) (ringB k) := (aToB k).toAlgebra
  let : Algebra (ringA k) (Localization.AtPrime (idealQB k)) := inferInstance
  have heq : algebraMap (ringA k) (Localization.AtPrime (idealQB k)) =
      (algebraMap (ringB k) (Localization.AtPrime (idealQB k))).comp (aToB k) := by
    rw [IsScalarTower.algebraMap_eq (ringA k) (ringB k) (Localization.AtPrime (idealQB k))]
    rfl
  rw [← heq]
  exact RingHom.flat_algebraMap_iff.mpr (flat_at_idealQB k)

/-- **The Raynaud--Gruson example.** There is a local ring `A`, a finite type ring map `A → B`
and a prime `q` of `B` over the maximal ideal of `A` such that `B_q` is flat over `A` while for
every `g ∈ B` outside `q` the ring `B_g` is neither of finite presentation nor flat over `A`. -/
@[stacks 05G2]
theorem exists_flat_at_prime_not_flat_on_neighborhood :
    ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A) (φ : A →+* B)
      (q : Ideal B) (_ : q.IsPrime),
      φ.FiniteType ∧ q.comap φ = IsLocalRing.maximalIdeal A ∧
        ((algebraMap B (Localization.AtPrime q)).comp φ).Flat ∧
        ∀ g : B, g ∉ q →
          ¬ ((algebraMap B (Localization.Away g)).comp φ).FinitePresentation ∧
          ¬ ((algebraMap B (Localization.Away g)).comp φ).Flat :=
  ⟨ringA ℚ, ringB ℚ, inferInstance, inferInstance, inferInstance, aToB ℚ, idealQB ℚ,
    inferInstance, aToB_finiteType ℚ, idealQB_comap_eq_maximalIdeal ℚ, aToB_atPrime_flat ℚ,
    fun g hg => ⟨aToB_away_not_finitePresentation ℚ g hg, not_flat_localizationAway ℚ g hg⟩⟩

end Stacks.Examples.RaynaudGruson

end
