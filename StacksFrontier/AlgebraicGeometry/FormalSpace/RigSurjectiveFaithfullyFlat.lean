module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap

/-!
# Rig-surjectivity of a flat affine formal morphism is faithful flatness of its closed fibre

Let `A` be a Noetherian ring complete with respect to an ideal `I` whose `I`-torsion vanishes,
and let `C` be an `I`-adically complete `A`-algebra with `A/Iⁿ → C/IⁿC` flat and of finite type
for every `n`. Then `Spf C → Spf A` is rig-surjective if and only if `A/I → C/IC` is faithfully
flat (Stacks 0AQY).

One direction is Stacks 0AQX, already available as
`AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap`. For the converse one
produces, from a maximal ideal `I ⊆ 𝔪 ⊆ A`, an adic point of `Spf A` whose closed point lies
over `𝔪`: the vanishing of the `I`-torsion makes `I` contain an `A`-regular element `a`
(Stacks 00LL, which is how Stacks 05EA and 00L6 enter), so a prime `𝔮` of `A_𝔪` avoiding `a`
and closed in the punctured spectrum exists (Stacks 02IM), the one-dimensional local domain
`A_𝔪/𝔮` is dominated by a discrete valuation ring `V` (Stacks 00PH), and the completion
`R = V^∧` is a complete discrete valuation ring (Stacks 0AP1). Rig-surjectivity lifts this
point to `Spf C` after an extension `R ⊆ R'`, and the lift is `Spf` of a ring map `C → R'`
(Stacks 0AN0) whose kernel pulls back to a prime of `C` lying over `𝔪`. So `Spec(C/IC) →
Spec(A/I)` hits every closed point, and flatness turns that into faithful flatness
(Stacks 00HQ).

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap_iff_faithfullyFlat`:
  **Stacks 0AQY**.
* `AlgebraicGeometry.FormalSpace.exists_isPrime_comap_eq_of_isRigSurjective`: the geometric
  half of Stacks 0AQY, that rig-surjectivity makes every maximal ideal of `A` containing `I`
  a contraction of a prime of `C`.
* `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`: a quotient system on a ring
  smaller than the cutoff of the site has a large enough site.

## Implementation notes

No largeness hypothesis on the quotient systems is carried. Where one is wanted — to make a
formal spectrum an affine formal algebraic space, which is what the set-theoretic condition of
Stacks 0AIS needs — `hasLargeSite_of_mk_lt_cutoff` derives
`QuotientSystem.HasLargeSite` from a cardinality bound on the ring, and
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` supplies that bound for a
complete adic ring already carrying a quotient system. Stacks 0AN0 itself asks for no such
condition.

The one hypothesis that is carried is `hAdicRepresentable`: a continuous homomorphism out of
`A` which is adic induces a morphism of formal spectra representable by algebraic spaces,
*for a weakly admissible target*. Since an adic homomorphism is taut
(`RingHom.isTaut_of_isAdic`, Stacks 0GBS part (1)), that statement is an instance of the
implication (3) ⟹ (1) of **Stacks 0AN5**, which identifies representability of a morphism of
affine formal spectra with tautness of the ring map; the weak admissibility of the target is
carried for exactly that reason, since 0AN5 is stated for weakly admissible topological rings
and without it `formalSpectrum DR` is not known to be an affine formal algebraic space at all.
It is the single missing input: `AlgebraicGeometry.FormalSpace.IsRigSurjective` renders
adicness of its quantified point as representability, and the adicness itself, which is what
the source proof produces and all this proof needs, is established here as `RingHom.IsAdic`.
Everything else in the source argument is proved.

Towards 0AN5 (3) ⟹ (1) the library has the cartesian square it rests on, namely
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`: for a taut
homomorphism the stage `Spec (C ⧸ K)` cut out by the closure of the extended ideal *is* the
fibre product `Spf C ×_{Spf A} Spec (A ⧸ I)`. What is missing is the passage from that, which
represents the base change of `Spf φ` along a quasi-compact point of `Spf A` (Stacks 0AIA), to
the base change along an arbitrary one; in the source this is the unexplained "we conclude"
at the end of the proof of 0AN5.

## References

* [Stacks Project, Tag 0AQY](https://stacks.math.columbia.edu/tag/0AQY)
* [Stacks Project, Tag 0AQX](https://stacks.math.columbia.edu/tag/0AQX)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 00HQ](https://stacks.math.columbia.edu/tag/00HQ)
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Cardinality

/-- A quotient system on a ring smaller than the cutoff of the site is automatically carried by
the site: the atlas `∐_J Spec (A ⧸ J)` is indexed by a set of ideals, so by at most `2 ^ #A`
many, and each component is the spectrum of a quotient of `A`. -/
theorem hasLargeSite_of_mk_lt_cutoff {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A) (hA : #A < B.cutoff) : D.HasLargeSite := by
  classical
  set κ : Cardinal.{u} := max ℵ₀ (2 ^ #A) with hκdef
  have hκ : κ < B.cutoff := max_lt B.aleph0_lt_cutoff (B.cutoff_isStrongPrelimit hA)
  have hι : #{ J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J } ≤ κ := by
    calc #{ J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }
        ≤ #(Ideal A) := mk_subtype_le _
      _ ≤ #(Set A) := mk_le_of_injective (f := fun J : Ideal A => (J : Set A))
          SetLike.coe_injective
      _ = 2 ^ #A := mk_set
      _ ≤ κ := le_max_right _ _
  refine lt_of_le_of_lt (schemeSize_coproduct_le _ κ (le_max_left _ _) hι fun J => ?_) hκ
  rw [Scheme.size_Spec]
  exact max_le (le_max_left _ _)
    (mk_quotient_le.trans ((Cardinal.cantor _).le.trans (le_max_right _ _)))

/-- The `J`-adic completion of a ring smaller than the cutoff of the site is again smaller than
the cutoff: it injects into the product of the quotients `V ⧸ Jⁿ`, each no larger than `V`, and
the cutoff is a strong prelimit of uncountable cofinality. -/
theorem mk_adicCompletion_lt_cutoff {V : Type u} [CommRing V] (J : Ideal V)
    (hV : #V < B.cutoff) : #(AdicCompletion J V) < B.cutoff := by
  set Q : ℕ → Type u := fun n => V ⧸ (J ^ n • (⊤ : Submodule V V)) with hQdef
  have hQ : ∀ n : ℕ, #(Q n) < B.cutoff := fun _ => mk_quotient_le.trans_lt hV
  have hsup : (⨆ n : ℕ, #(Q n)) < B.cutoff :=
    lift_iSup_lt_of_lt_cof_ord
      (by rw [mk_nat, lift_aleph0, lift_id']; exact B.aleph0_lt_cutoff_cof) hQ
  set b : Cardinal.{u} := max ℵ₀ (⨆ n : ℕ, #(Q n)) with hbdef
  have hb : b < B.cutoff := max_lt B.aleph0_lt_cutoff hsup
  calc
    #(AdicCompletion J V) ≤ #(∀ n : ℕ, Q n) :=
      mk_le_of_injective (f := fun x : AdicCompletion J V => x.val) Subtype.val_injective
    _ = Cardinal.prod (fun n : ℕ => #(Q n)) := mk_pi _
    _ ≤ Cardinal.prod (fun _ : ℕ => b) :=
      prod_le_prod _ _ fun n => le_max_of_le_right (le_ciSup bddAbove_of_small n)
    _ = b ^ ℵ₀ := by simp
    _ < B.cutoff := Cardinal.power_aleph0_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit hb

end Cardinality

section Points

/-- **Stacks 00LL, applied.** An ideal whose torsion submodule vanishes contains a regular
element: no associated prime of the ring contains it, since an element killed by the whole
ideal would be a nonzero element of the torsion submodule. -/
private theorem exists_isSMulRegular_mem_of_torsionBySet_eq_bot {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥) :
    ∃ a ∈ I, IsSMulRegular A a := by
  refine (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le I A
    (associatedPrimes.finite A A)).mpr fun q hq hIq => ?_
  obtain ⟨hqprime, x, hx⟩ := (isAssociatedPrime_iff (I := q) (M := A)).mp hq
  have hxt : x ∈ Submodule.torsionBySet A A (I : Set A) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have hqa : (a : A) ∈ q := hIq a.property
    rw [hx, Submodule.mem_colon] at hqa
    simpa using hqa x (by simp)
  have hx0 : x = 0 := by
    have hxbot : x ∈ (⊥ : Submodule A A) := by simpa [hTorsion] using hxt
    simpa using hxbot
  exact hqprime.ne_top (hx.trans (by simp [hx0] : (⊥ : Submodule A A).colon {x} = ⊤))

/-- From a maximal ideal `I ⊆ 𝔪 ⊆ A` of a Noetherian ring with no `I`-torsion, a prime `𝔮` of
`A_𝔪` not containing `I A_𝔪` together with a discrete valuation ring dominating the
one-dimensional local domain `A_𝔪 ⧸ 𝔮`.

A regular element `a ∈ I` is a nonzerodivisor in the flat localization `A_𝔪`, so some prime
`𝔮` avoids all its powers (Stacks 02IM is what makes the corresponding point closed in the
punctured spectrum; here the avoidance of `a` is what is needed). Such a `𝔮` is not the
maximal ideal, because `a` lies in the latter, so `A_𝔪 ⧸ 𝔮` is not a field and
Stacks 00PH dominates it by a discrete valuation ring inside its fraction field. -/
private theorem exists_prime_not_le_map_of_torsionBySet_eq_bot {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥) :
    ∃ q : Ideal (Localization.AtPrime m), ∃ _ : q.IsPrime,
      ¬ I.map (algebraMap A (Localization.AtPrime m)) ≤ q ∧
      ∃ V : Subalgebra (Localization.AtPrime m ⧸ q)
          (FractionRing (Localization.AtPrime m ⧸ q)),
        IsDiscreteValuationRing V ∧
        IsFractionRing V (FractionRing (Localization.AtPrime m ⧸ q)) ∧
        IsLocalHom (algebraMap (Localization.AtPrime m ⧸ q) V) := by
  obtain ⟨a, haI, hregA⟩ := exists_isSMulRegular_mem_of_torsionBySet_eq_bot I hTorsion
  set L := Localization.AtPrime m with hLdef
  set aL : L := algebraMap A L a with haLdef
  have hregRing : IsRegular a :=
    isRegular_iff.mpr ⟨hregA, fun x y hxy => hregA (by simpa [mul_comm] using hxy)⟩
  have : Module.Flat A L := IsLocalization.flat L m.primeCompl
  have hregRingL : IsRegular aL :=
    (Commute.isRegular_iff fun b => Commute.all _ b).2
      (by simpa only [IsLeftRegular, IsSMulRegular, Algebra.smul_def] using
        (Module.Flat.isSMulRegular_of_isRegular (M := L) hregRing))
  have hregL : IsSMulRegular L aL := hregRingL.1
  have haMax : aL ∈ IsLocalRing.maximalIdeal L := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m L]
    exact Ideal.mem_map_of_mem (algebraMap A L) (hIm haI)
  have hdisj : Disjoint ((⊥ : Ideal L) : Set L) (Submonoid.powers aL : Set L) := by
    rw [Set.disjoint_left]
    intro z hz0 hzpow
    have hz0' : z = 0 := by simpa using hz0
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hzpow
    exact one_ne_zero ((hregL.pow n).right_eq_zero_of_smul (by simpa using hz0'))
  obtain ⟨q, hqprime, -, hqdisj⟩ :=
    Ideal.exists_le_prime_disjoint (⊥ : Ideal L) (Submonoid.powers aL) hdisj
  have haq : aL ∉ q := fun h => (Set.disjoint_left.mp hqdisj) h ⟨1, by simp⟩
  have hqne : q ≠ IsLocalRing.maximalIdeal L := fun he => haq (he ▸ haMax)
  have hIavoid : ¬ I.map (algebraMap A L) ≤ q := fun hle =>
    haq (hle (Ideal.mem_map_of_mem (algebraMap A L) haI))
  set R₀ := L ⧸ q with hR₀def
  have : q.IsPrime := hqprime
  have : IsDomain R₀ := Ideal.Quotient.isDomain q
  have : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have hR₀field : ¬ IsField R₀ := fun hfield =>
    hqne ((IsLocalRing.isMaximal_iff L).mp (Ideal.Quotient.maximal_of_isField q hfield))
  obtain ⟨V, hVdvr, hVfrac, hVlocal⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField
      (R := R₀) (FractionRing R₀) (L := FractionRing R₀) hR₀field
  exact ⟨q, hqprime, hIavoid, V, hVdvr, hVfrac, hVlocal⟩

/-- A maximal ideal of `A ⧸ I` is the image of a maximal ideal of `A` containing `I`. -/
private theorem exists_isMaximal_map_eq {A : Type u} [CommRing A] (I : Ideal A)
    (x : Ideal (A ⧸ I)) (hx : x.IsMaximal) :
    ∃ m : Ideal A, m.IsMaximal ∧ I ≤ m ∧ m.map (Ideal.Quotient.mk I) = x := by
  refine ⟨Ideal.comap (Ideal.Quotient.mk I) x,
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, fun a ha => ?_,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective x⟩
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact Ideal.zero_mem _

/-- A nonzero proper ideal of a discrete valuation ring carrying its maximal-adic topology
defines that same topology: it is a positive power of the maximal ideal. -/
private theorem isAdic_of_ne_bot_of_ne_top {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (htop : IsAdic (IsLocalRing.maximalIdeal R)) (J : Ideal R) (hne : J ≠ ⊥) (hproper : J ≠ ⊤) :
    IsAdic J := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hπ
  have heq : J = IsLocalRing.maximalIdeal R ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.span_singleton_pow]
    exact hn
  have hnpos : 0 < n := by
    by_contra! h
    exact hproper (by simpa [Nat.eq_zero_of_le_zero h] using heq)
  rw [heq]
  exact is_ideal_adic_pow htop hnpos

end Points
section Criterion

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing A]

/-- The geometric step of Stacks 0AQY: if `Spf C → Spf A` is rig-surjective then every maximal
ideal `I ⊆ 𝔪 ⊆ A` is the contraction of a prime of `C`.

The vanishing `I`-torsion yields a prime `𝔮` of `A_𝔪` missing a regular element of `I`, hence a
one-dimensional local domain `A_𝔪 ⧸ 𝔮` dominated by a discrete valuation ring `V`
(Stacks 00PH); its completion `R` is a complete discrete valuation ring (Stacks 0AP1) and
`A → R` is adic because the image of `I` is a nonzero proper ideal of `R`. Rig-surjectivity
lifts `Spf R → Spf A` to `Spf C` over an extension `R ⊆ R'`, the lift is `Spf` of a ring map
`g : C → R'` (Stacks 0AN0), and full faithfulness identifies `g ∘ (A → C)` with `A → R → R'`.
So `g⁻¹ 𝔪_{R'}` contracts to `𝔪`. -/
theorem exists_isPrime_comap_eq_of_isRigSurjective (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C)
    (hAdicRepresentable : ∀ (R : Type u) [CommRing R] [TopologicalSpace R]
      [IsTopologicalRing R] [IsLinearTopology R R], TopologicalRing.IsWeaklyAdmissible R →
      ∀ (DR : QuotientSystem B S hS R)
      (q : ContinuousHom D DR), RingHom.IsAdic q.toRingHom →
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
          (formalSpectrumMap
            (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) q).hom)
    (hrig : IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f))
    (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m) :
    ∃ n : Ideal C, n.IsPrime ∧ n.comap (algebraMap A C) = m := by
  classical
  set hAweak := TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete with hAweakdef
  have hCweak : TopologicalRing.IsWeaklyAdmissible C :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hCadic hCcomplete
  have hAcard : #A < B.cutoff := mk_lt_cutoff_of_quotientSystem hAadic hAcomplete D
  obtain ⟨q, hqprime, hIavoid, V, hVdvr, hVfrac, hVlocal⟩ :=
    exists_prime_not_le_map_of_torsionBySet_eq_bot I m hIm hTorsion
  set L := Localization.AtPrime m with hLdef
  set R₀ := L ⧸ q with hR₀def
  have : q.IsPrime := hqprime
  have : IsDomain R₀ := Ideal.Quotient.isDomain q
  have : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have : IsDiscreteValuationRing V := hVdvr
  have : IsFractionRing V (FractionRing R₀) := hVfrac
  have : IsLocalRing V := hVdvr.toIsLocalRing
  -- `R` is the completion of `V`, a complete discrete valuation ring
  set R : Type u := AdicCompletion (IsLocalRing.maximalIdeal V) V with hRdef
  obtain ⟨hRdom, hRdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := V)).mp ⟨inferInstance, hVdvr⟩
  have : IsDomain R := hRdom
  have : IsDiscreteValuationRing R := hRdvr
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  have hRtopring : IsTopologicalRing R :=
    (IsLocalRing.maximalIdeal R).ringFilterBasis.isTopologicalRing
  have hRlin : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  have hRtop : IsAdic (IsLocalRing.maximalIdeal R) := rfl
  have hRcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := inferInstance
  have hRweak : TopologicalRing.IsWeaklyAdmissible R :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hRtop hRcomplete
  -- `R` is small enough to carry a quotient system over `S`
  have hLcard : #L < B.cutoff :=
    (Cardinal.mk_le_of_isLocalization m.primeCompl L).trans_lt
      (max_lt B.aleph0_lt_cutoff hAcard)
  have hR₀card : #R₀ < B.cutoff := mk_quotient_le.trans_lt hLcard
  have hVcard : #V < B.cutoff :=
    (mk_le_of_injective (f := fun z : V => (z : FractionRing R₀)) Subtype.val_injective).trans_lt
      ((Cardinal.mk_le_of_isLocalization (nonZeroDivisors R₀) (FractionRing R₀)).trans_lt
        (max_lt B.aleph0_lt_cutoff hR₀card))
  have hRcard : #R < B.cutoff := mk_adicCompletion_lt_cutoff _ hVcard
  -- the adic ring map `r : A → R`
  have : IsLocalHom (algebraMap R₀ V) := hVlocal
  have : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  set b : R₀ →+* R := (algebraMap V R).comp (algebraMap R₀ V) with hbdef
  set r : A →+* R := (b.comp (Ideal.Quotient.mk q)).comp (algebraMap A L) with hrdef
  have hbinj : Function.Injective b :=
    (AdicCompletion.of_injective (IsLocalRing.maximalIdeal V) V).comp fun x y h =>
      IsFractionRing.injective R₀ (FractionRing R₀)
        (congrArg (fun z : V => (z : FractionRing R₀)) h)
  have hrmax : (IsLocalRing.maximalIdeal R).comap r = m := by
    rw [hrdef, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal L m
  have hIr : I.map r ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, hrmax]; exact hIm
  have hIrne : I.map r ≠ ⊥ := by
    intro hbot
    apply hIavoid
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    have hrz : r z = 0 := by
      have hmem : r z ∈ I.map r := Ideal.mem_map_of_mem r hz
      rw [hbot] at hmem
      exact Ideal.mem_bot.mp hmem
    change algebraMap A L z ∈ q
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hbinj
    rw [map_zero]
    exact hrz
  have hrcont : Continuous r := continuous_of_isAdic_of_map_le hAadic hRtop r hIr
  have hradic : RingHom.IsAdic r :=
    ⟨I, hAadic, isAdic_of_ne_bot_of_ne_top hRtop _ hIrne
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIr)⟩
  -- the adic point `Spf R → Spf A`, and the lift supplied by rig-surjectivity
  obtain ⟨DR, p, hp⟩ := exists_quotientSystem_continuousHom hAweak D r hrcont hRcard
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin,
    hR'adic, hR'complete, DR', e, y, he, hy⟩ :=
    hrig R hRtop hRcomplete hRweak DR (formalSpectrumMap hAweak p)
      (hAdicRepresentable R hRweak DR p (by rw [hp]; exact hradic))
  let : CommRing R' := hR'ring
  have : IsDomain R' := hR'dom
  have : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : TopologicalSpace R' := hR'top
  have : IsTopologicalRing R' := hR'topring
  have : IsLinearTopology R' R' := hR'lin
  have : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  -- the lift is `Spf` of a ring map `g : C → R'`
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hCweak hR'weak y
  obtain ⟨fg, hfg⟩ := exists_continuousHom_comp hAweak f g hCweak
  obtain ⟨pe, hpe⟩ := exists_continuousHom_comp hAweak p e hRweak
  have hhom : fg = pe := by
    obtain ⟨k, hk, huniq⟩ :=
      existsUnique_continuousHom_formalSpectrumMap_eq hAweak hR'weak
        (formalSpectrumMap hAweak pe)
    clear hk
    refine (huniq fg ?_).trans (huniq pe rfl).symm
    change formalSpectrumMap hAweak fg = formalSpectrumMap hAweak pe
    rw [← formalSpectrumMap_comp hAweak hCweak f g fg hfg,
      ← formalSpectrumMap_comp hAweak hRweak p e pe hpe, hg]
    exact hy
  have hring : g.toRingHom.comp (algebraMap A C) = (algebraMap R R').comp r := by
    have hh := congrArg ContinuousHom.toRingHom hhom
    rw [hfg, hpe, hf, he, hp] at hh
    exact hh
  -- the preimage of the maximal ideal of `R'` is a prime of `C` over `m`
  refine ⟨(IsLocalRing.maximalIdeal R').comap g.toRingHom,
    Ideal.comap_isPrime g.toRingHom _, ?_⟩
  rw [Ideal.comap_comap, hring, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, hrmax]

/-- **Stacks 0AQY.** Let `A` be a Noetherian ring complete with respect to an ideal `I` whose
`I`-torsion vanishes, and let `C` be an `I`-adically complete `A`-algebra such that
`A/Iⁿ → C/IⁿC` is flat and of finite type for every `n`. Then `Spf C → Spf A` is rig-surjective
if and only if `A/I → C/IC` is faithfully flat.

Faithful flatness gives rig-surjectivity by Stacks 0AQX. Conversely, a closed point of
`Spec(A/I)` is a maximal ideal `I ⊆ 𝔪 ⊆ A`, and
`exists_isPrime_comap_eq_of_isRigSurjective` contracts a prime of `C` onto it; so
`Spec(C/IC) → Spec(A/I)` meets every closed point, which for a flat map is faithful flatness
(Stacks 00HQ). -/
@[stacks 0AQY "modulo Stacks 0AN5 part (3) implies part (1) for the adic point, carried as
  `hAdicRepresentable`"]
theorem isRigSurjective_formalSpectrumMap_iff_faithfullyFlat (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥)
    (hfinite : ∀ n : ℕ, Algebra.FiniteType (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C)
    (hAdicRepresentable : ∀ (R : Type u) [CommRing R] [TopologicalSpace R]
      [IsTopologicalRing R] [IsLinearTopology R R], TopologicalRing.IsWeaklyAdmissible R →
      ∀ (DR : QuotientSystem B S hS R)
      (q : ContinuousHom D DR), RingHom.IsAdic q.toRingHom →
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
          (formalSpectrumMap
            (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) q).hom) :
    IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f) ↔
      Module.FaithfullyFlat (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := by
  classical
  refine ⟨fun hrig => ?_, fun hff =>
    isRigSurjective_formalSpectrumMap I hAadic hAcomplete hCadic hCcomplete hfinite hflat hff
      D E f hf⟩
  have hflat1 : Module.Flat (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := by
    convert hflat 1 using 2 <;> rw [pow_one]
  set φ := algebraMap (A ⧸ I) (C ⧸ I.map (algebraMap A C)) with hφdef
  have hflatRH : RingHom.Flat φ := RingHom.flat_algebraMap_iff.mpr hflat1
  refine RingHom.faithfullyFlat_algebraMap_iff.mp
    (((faithfullyFlat_tfae00HQ φ hflatRH).out 3 1).mp fun x hx => ?_)
  -- a closed point of `Spec (A ⧸ I)` is a maximal ideal `I ≤ m` of `A`
  obtain ⟨m, hmmax, hIm, hmap⟩ := exists_isMaximal_map_eq I x.asIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx)
  have : m.IsMaximal := hmmax
  obtain ⟨n, hnprime, hncomap⟩ := exists_isPrime_comap_eq_of_isRigSurjective I hAadic
    hAcomplete hCadic hCcomplete hTorsion f hf hAdicRepresentable hrig m hIm
  have hIn : I.map (algebraMap A C) ≤ n := by
    rw [Ideal.map_le_iff_le_comap, hncomap]; exact hIm
  set n' := n.map (Ideal.Quotient.mk (I.map (algebraMap A C)))
  have hn' : n'.IsPrime := by
    have := hnprime
    exact Ideal.isPrime_map_quotientMk_of_isPrime hIn
  have hn'comap : n'.comap (Ideal.Quotient.mk (I.map (algebraMap A C))) = n := by
    exact Ideal.comap_map_mk hIn
  refine ⟨⟨n', hn'⟩, PrimeSpectrum.ext ?_⟩
  change n'.comap φ = x.asIdeal
  rw [← hmap]
  refine Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective ?_
  rw [Ideal.comap_map_mk hIm, Ideal.comap_comap,
    show φ.comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap A C))).comp (algebraMap A C) from rfl,
    ← Ideal.comap_comap, hn'comap, hncomap]

end Criterion

end AlgebraicGeometry.FormalSpace

end
