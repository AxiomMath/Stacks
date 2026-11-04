module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

@[expose] public section

/-!
# Elementary operations on henselian pairs

The characterizations in `StacksFrontier.RingTheory.Henselian.Pair.Criteria` make the henselian
condition on a pair `(A, I)` depend only on coarse data, and this file collects the resulting
closure properties. Being a henselian pair depends only on the closed subset `V(I)` of the prime
spectrum, it is inherited by integral extensions along the extended ideal, it can be tested on a
nested pair of ideals one step at a time, and it is closed under sums of ideals. As an
application, `V(𝔭 + I)` is connected for every prime `𝔭` of a henselian pair.

## Main results

* `henselianPair_map_of_isIntegral`: an integral extension of a henselian pair is henselian along
  the extended ideal.
* `henselianPair_iff_of_zeroLocus_eq`: two ideals with the same vanishing locus define henselian
  pairs simultaneously.
* `henselianPair_iff_of_le`: for `I ≤ J`, the pair `(A, J)` is henselian if and only if `(A, I)`
  and `(A ⧸ I, J / I)` are.
* `henselianPair_sup`: a sum of two henselian ideals is henselian.
* `isConnected_zeroLocus_add`: `V(𝔭 + I)` is connected for a prime `𝔭` of a henselian pair.

## Implementation notes

The extension of `I` along an algebra `B` is `I.map (algebraMap A B)`, the quotient ideal `J / I`
is the image of `J` under `Ideal.Quotient.mk I`, the sum of two ideals is their supremum in the
ideal lattice, and `V(I)` is `PrimeSpectrum.zeroLocus (I : Set A)`.

## References

* [Stacks: Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
-/

open Function PrimeSpectrum Topology

universe u v w

section

/-- An integral extension of a henselian pair is henselian along the extended ideal. -/
@[stacks 09XK]
theorem henselianPair_map_of_isIntegral {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal A)
    (hI : HenselianPair A I) :
    HenselianPair B (I.map (algebraMap A B)) := by
  apply ((henselianPair_tfae.{v, u} B (I.map (algebraMap A B))).out 4 1).mp
  intro C _ _ hC
  let _ : Algebra A C := (algebraMap B C).comp (algebraMap A B) |>.toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
  have hA : ∀ (D : Type (max u v)) [CommRing D] [Algebra A D] [Algebra.IsIntegral A D],
      InducesBijectionOnIdempotents (I.map (algebraMap A D)) :=
    ((henselianPair_tfae.{u, v} A I).out 1 4).mp hI
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  exact hA C

end

section

private def mapIdempotents {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    {e : R // IsIdempotentElem e} → {e : S // IsIdempotentElem e} :=
  fun e ↦ ⟨f e, e.2.map f⟩

private lemma mapIdempotents_bijective_of_surjective_of_ker_isNilpotent
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Bijective (mapIdempotents f) := by
  constructor
  · rintro ⟨e, he⟩ ⟨e', he'⟩ h
    exact Subtype.ext <| eq_of_isNilpotent_sub_of_isIdempotentElem he he'
      (hnil _ (by
        simpa [RingHom.mem_ker, mapIdempotents, sub_eq_zero] using congrArg Subtype.val h))
  · rintro ⟨e, he⟩
    obtain ⟨e', he', hfe'⟩ :=
      exists_isIdempotentElem_eq_of_ker_isNilpotent f hnil e (hf e) he
    exact ⟨⟨e', he'⟩, Subtype.ext hfe'⟩

private lemma factor_ker_isNilpotent {R : Type*} [CommRing R] {I K : Ideal R}
    (hIK : I ≤ K) (hKI : K ≤ I.radical) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factor hIK), IsNilpotent x := by
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hxK : x ∈ K := by
    rwa [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hKI hxK)
  exact ⟨n, Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hn)⟩

private lemma inducesBijectionOnIdempotents_iff_of_radical_eq
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I.radical = J.radical) :
    InducesBijectionOnIdempotents I ↔ InducesBijectionOnIdempotents J := by
  let K := I.radical
  have key (L : Ideal R) (hL : L ≤ K) (hLK : K ≤ L.radical) :
      InducesBijectionOnIdempotents L ↔ Function.Bijective (idemMap K) := by
    have hq := mapIdempotents_bijective_of_surjective_of_ker_isNilpotent
      (Ideal.Quotient.factor hL) (Ideal.Quotient.factor_surjective hL)
      (factor_ker_isNilpotent hL hLK)
    have comp : mapIdempotents (Ideal.Quotient.factor hL) ∘ idemMap L = idemMap K :=
      funext fun e => Subtype.ext (Ideal.Quotient.factor_mk hL e)
    unfold InducesBijectionOnIdempotents
    rw [← hq.of_comp_iff' (idemMap L), comp]
  exact (key I Ideal.le_radical le_rfl).trans
    (key J (Ideal.le_radical.trans_eq h.symm) h.le).symm

/-- Two ideals with the same vanishing locus define henselian pairs simultaneously. -/
@[stacks 09XJ]
theorem henselianPair_iff_of_zeroLocus_eq
    {A : Type u} [CommRing A] (I J : Ideal A)
    (hIJ : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)) :
    HenselianPair A I ↔ HenselianPair A J := by
  have hrad : I.radical = J.radical := (PrimeSpectrum.zeroLocus_eq_iff).mp hIJ
  have hcharI := (@henselianPair_tfae.{u, u} A _ I).out 1 4
  have hcharJ := (@henselianPair_tfae.{u, u} A _ J).out 1 4
  rw [hcharI, hcharJ]
  have mappedRadical (B : Type u) [CommRing B] [Algebra A B] :
      (I.map (algebraMap A B)).radical = (J.map (algebraMap A B)).radical := by
    have step {I J : Ideal A} (h : I ≤ J.radical) :
        (I.map (algebraMap A B)).radical ≤ (J.map (algebraMap A B)).radical :=
      Ideal.radical_le_radical_iff.mpr
        ((Ideal.map_mono h).trans (Ideal.map_radical_le (f := algebraMap A B) (I := J)))
    exact le_antisymm (step (Ideal.le_radical.trans hrad.le))
      (step (Ideal.le_radical.trans hrad.ge))
  constructor
  · intro H B _ _ _
    exact (inducesBijectionOnIdempotents_iff_of_radical_eq _ _ (mappedRadical B)).mp (H B)
  · intro H B _ _ _
    exact (inducesBijectionOnIdempotents_iff_of_radical_eq _ _ (mappedRadical B)).mpr (H B)

end

section

private def idemEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    {x : R // IsIdempotentElem x} ≃ {x : S // IsIdempotentElem x} where
  toFun x := ⟨e x, by
    unfold IsIdempotentElem at x ⊢
    rw [← map_mul, x.2]⟩
  invFun x := ⟨e.symm x, by
    unfold IsIdempotentElem at x ⊢
    rw [← map_mul, x.2]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

private lemma inducesBijectionOnIdempotents_trans {R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) :
    (InducesBijectionOnIdempotents I →
        InducesBijectionOnIdempotents (J.map (Ideal.Quotient.mk I)) →
          InducesBijectionOnIdempotents J) ∧
      (InducesBijectionOnIdempotents J →
        InducesBijectionOnIdempotents (J.map (Ideal.Quotient.mk I)) →
          InducesBijectionOnIdempotents I) := by
  let q : R ⧸ I →+* R ⧸ J := Ideal.Quotient.factor hIJ
  have hqker : RingHom.ker q = J.map (Ideal.Quotient.mk I) :=
    Ideal.Quotient.factor_ker hIJ
  let e₀ : (R ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I)) ≃+* (R ⧸ I) ⧸ RingHom.ker q :=
    Ideal.quotientEquiv _ _ (RingEquiv.refl _) (by simp [hqker])
  let e : (R ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I)) ≃+* R ⧸ J :=
    e₀.trans (q.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective hIJ))
  have he (x : {x : R // IsIdempotentElem x}) :
      idemEquiv e (idemMap (J.map (Ideal.Quotient.mk I)) (idemMap I x)) = idemMap J x := by
    apply Subtype.ext
    show e (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x.1)) = Ideal.Quotient.mk J x.1
    simp [e, e₀, q]
  have hfun : (idemEquiv e : _ → _) ∘ idemMap (J.map (Ideal.Quotient.mk I)) ∘ idemMap I =
      idemMap J := funext he
  have key (hJ : InducesBijectionOnIdempotents (J.map (Ideal.Quotient.mk I))) :
      InducesBijectionOnIdempotents J ↔ InducesBijectionOnIdempotents I := by
    unfold InducesBijectionOnIdempotents
    rw [← hfun, ← Function.comp_assoc]
    exact ((idemEquiv e).bijective.comp hJ).of_comp_iff' _
  exact ⟨fun hI hJ => (key hJ).mpr hI, fun h hJ => (key hJ).mp h⟩

private lemma quotientMap_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal A) :
    Algebra.IsIntegral (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  let IB := I.map (algebraMap A B)
  have : Algebra.IsIntegral A (B ⧸ IB) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ A IB)
      Ideal.Quotient.mk_surjective
  exact Algebra.IsIntegral.tower_top A

private lemma map_quotientMap_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I J : Ideal A) :
    (J.map (Ideal.Quotient.mk I)).map
        (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) =
      (J.map (algebraMap A B)).map
        (Ideal.Quotient.mk (I.map (algebraMap A B))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

private lemma henselianPair_iff_induces {A : Type w} [CommRing A] (I : Ideal A) :
    HenselianPair A I ↔
      ∀ (B : Type w) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
        InducesBijectionOnIdempotents (I.map (algebraMap A B)) :=
  (henselianPair_tfae A I).out 1 4

/-- For nested ideals `I ⊆ J`, the pair `(A, J)` is henselian if and only if `(A, I)` and
the induced pair `(A / I, J / I)` are henselian. -/
@[stacks 0DYD]
theorem henselianPair_iff_of_le {A : Type w} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J) :
    (HenselianPair A I ∧
      HenselianPair (A ⧸ I) (J.map (Ideal.Quotient.mk I))) ↔
      HenselianPair A J := by
  have hbijQ (hQ : HenselianPair (A ⧸ I) (J.map (Ideal.Quotient.mk I))) (B : Type w)
      [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] :
      InducesBijectionOnIdempotents
        ((J.map (algebraMap A B)).map (Ideal.Quotient.mk (I.map (algebraMap A B)))) := by
    let : Algebra.IsIntegral (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := quotientMap_isIntegral I
    simpa only [map_quotientMap_eq] using
      (henselianPair_iff_induces (J.map (Ideal.Quotient.mk I))).mp hQ (B ⧸ I.map (algebraMap A B))
  constructor
  · rintro ⟨hI, hQ⟩
    apply (henselianPair_iff_induces J).mpr
    intro B _ _ _
    exact (inducesBijectionOnIdempotents_trans (Ideal.map_mono hIJ)).1
      ((henselianPair_iff_induces I).mp hI B) (hbijQ hQ B)
  · intro hJ
    have hQ : HenselianPair (A ⧸ I) (J.map (Ideal.Quotient.mk I)) := by
      simpa only [Ideal.Quotient.algebraMap_eq] using
        (henselianPair_map_of_isIntegral (B := A ⧸ I) J hJ)
    refine ⟨?_, hQ⟩
    apply (henselianPair_iff_induces I).mpr
    intro B _ _ _
    exact (inducesBijectionOnIdempotents_trans (Ideal.map_mono hIJ)).2
      ((henselianPair_iff_induces J).mp hJ B) (hbijQ hQ B)

end

section

/-- The sum of two ideals defining henselian pairs also defines a henselian pair. -/
@[stacks 0G1R]
theorem henselianPair_sup {A : Type u} [CommRing A] {I J : Ideal A}
    (hI : HenselianPair A I) (hJ : HenselianPair A J) :
    HenselianPair A (I ⊔ J) := by
  apply (henselianPair_iff_of_le le_sup_left).mp
  refine ⟨hI, ?_⟩
  simpa [Ideal.map_sup] using
    (henselianPair_map_of_isIntegral J hJ :
      HenselianPair (A ⧸ I) (J.map (Ideal.Quotient.mk I)))

end

section

private theorem connectedSpace_primeSpectrum_of_idempotents
    (R : Type*) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen, and_iff_right (inferInstance : Nonempty (PrimeSpectrum R))]
  intro U hU
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hU
  rcases h e he with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

/-- For a henselian pair `(A, I)` and a prime ideal `p` of `A`, the closed subset
`V(p + I)` of `Spec(A)` is connected. -/
@[stacks 09Y6]
theorem isConnected_zeroLocus_add {A : Type u} [CommRing A] (I p : Ideal A)
    (hI : HenselianPair A I) (hp : p.IsPrime) :
    IsConnected (zeroLocus ((p + I : Ideal A) : Set A) : Set (PrimeSpectrum A)) := by
  let B := A ⧸ p
  let J : Ideal B := I.map (Ideal.Quotient.mk p)
  let C := B ⧸ J
  let q₁ : A →+* B := Ideal.Quotient.mk p
  let q₂ : B →+* C := Ideal.Quotient.mk J
  let q : A →+* C := q₂.comp q₁
  let : Algebra A B := q₁.toAlgebra
  let : Algebra.IsIntegral A B :=
    ⟨q₁.isIntegral_of_surjective Ideal.Quotient.mk_surjective⟩
  have hB : HenselianPair B J := henselianPair_map_of_isIntegral I hI
  have hbij : InducesBijectionOnIdempotents J := by
    have hchar := ((henselianPair_tfae.{u, u} B J).out 1 4).mp hB
    simpa using hchar B
  have hCidem : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨d, hd⟩ := hbij.2 ⟨e, he⟩
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp d.2 with hd0 | hd1
    · left
      simpa [idemMap, hd0] using (congrArg Subtype.val hd).symm
    · right
      simpa [idemMap, hd1] using (congrArg Subtype.val hd).symm
  have hJ : J ≠ ⊤ := by
    intro htop
    have hjac : (⊥ : Ideal B).jacobson = ⊤ := top_unique (htop ▸ hB.1)
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hjac)
  let : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr hJ
  let : ConnectedSpace (PrimeSpectrum C) :=
    connectedSpace_primeSpectrum_of_idempotents C hCidem
  have hq : Surjective q := q₂.surjective.comp q₁.surjective
  have hker : RingHom.ker q = p + I := by
    ext x
    show q₂ (q₁ x) = 0 ↔ x ∈ p + I
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show q₁ x ∈ J ↔ x ∈ p + I
    simpa [J, q₁] using
      (show x ∈ (J.comap q₁) ↔ x ∈ p + I by
        rw [Ideal.comap_map_quotientMk, Ideal.add_eq_sup])
  have hRange : Set.range (comap q) = zeroLocus ((p + I : Ideal A) : Set A) := by
    rw [range_comap_of_surjective C q hq, hker]
  have hEmb : IsClosedEmbedding (comap q) :=
    isClosedEmbedding_comap_of_surjective C q hq
  have hpre : IsPreconnected (Set.range (comap q)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ hEmb.continuous.continuousOn
  have hne : (Set.range (comap q)).Nonempty := Set.range_nonempty _
  rw [hRange] at hpre hne
  exact ⟨hne, hpre⟩

end

end
