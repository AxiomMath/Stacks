module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two local algebras over a purely inseparable residue extension

All rings are commutative with unit. Let `A → B` and `A → C` be local homomorphisms of local
rings, with `A → C` integral and at least one of the induced residue field extensions
`κ(m_C)/κ(m_A)` or `κ(m_B)/κ(m_A)` purely inseparable. Then `D = B ⊗_A C` is a local ring and
the canonical maps `B → D` and `C → D` are local homomorphisms. This is Stacks tag 092Y,
Lemma 10.156.5.

## The encoding

A *local ring* is a ring `R` with a unique maximal ideal `m_R`, i.e. `IsLocalRing R`, with
maximal ideal `IsLocalRing.maximalIdeal R`; a local ring is nonzero by convention. Its
*residue field* is `κ(m_R) = R / m_R`, i.e. `IsLocalRing.ResidueField R`, with quotient map
`IsLocalRing.residue R`. A *local homomorphism* is a ring map `f : A → B` of local rings with
`f(m_A) ⊆ m_B`, equivalently `f⁻¹(m_B) = m_A`, i.e. `IsLocalHom f`; it induces
`IsLocalRing.ResidueField.map f : κ(m_A) → κ(m_B)`. A ring map is *integral* when every element
of the target satisfies a monic polynomial over the image, i.e. `Algebra.IsIntegral A C`. A
field extension `L/K` is *purely inseparable* when for every `α ∈ L` there is `n ≥ 0` with
`α^(p^n) ∈ K` for `p` the characteristic exponent, i.e. `IsPurelyInseparable K L`; in
characteristic `0` this forces `L = K`. For `A`-algebras `B` and `C`, the tensor product
`D = B ⊗_A C` is `TensorProduct A B C`, with canonical maps `B → D`, `b ↦ b ⊗ 1`
(`Algebra.TensorProduct.includeLeftRingHom`) and `C → D`, `c ↦ 1 ⊗ c`
(`Algebra.TensorProduct.includeRight`).

The two local homomorphisms are encoded as `Algebra A B`, `Algebra A C` with
`IsLocalHom (algebraMap A B)` and `IsLocalHom (algebraMap A C)`. The induced residue field
extension `κ(m_A) → κ(m_C)` is `IsLocalRing.ResidueField.map (algebraMap A C)`, given an
algebra structure via `.toAlgebra` so that pure inseparability can be stated, and likewise for
`B`. The hypothesis is a disjunction: *either* `κ(m_C)/κ(m_A)` or `κ(m_B)/κ(m_A)` is purely
inseparable.

## The argument

Write `D = B ⊗[A] C`, with `m_A, m_B, m_C` the maximal ideals and `κ(m_A) = ResidueField A`,
and so on.

1. The base-changed map `B → D` is integral, integrality of `A → C` being stable under the
   base change `A → B` (Stacks 02JK).
2. An integral extension satisfies going-up and lying-over, so `Spec D → Spec B` is surjective
   and the maximal ideals of `D` map onto those of `B`; moreover every maximal ideal of `D`
   contracts to a maximal ideal of `B`, i.e. to `m_B` (Stacks 00GU/00GQ). Hence the maximal
   ideals of `D` are exactly those of the fibre ring `D / m_B·D = D ⊗_B κ(m_B)`.
3. The fibre ring is identified as
   `D / m_B·D  ≅  κ(m_B) ⊗_A C  ≅  κ(m_B) ⊗_{κ(m_A)} (C / m_A·C)`.
4. `C / m_A·C` is local with residue field `κ(m_C)` and integral over the field `κ(m_A)`, so
   `Spec (C / m_A·C)` is the single point `{m_C}`; therefore
   `Spec (D / m_B·D) ≅ Spec (κ(m_B) ⊗_{κ(m_A)} κ(m_C))` (Stacks 00E5: nilpotents do not
   change `Spec`).
5. `κ(m_B) ⊗_{κ(m_A)} κ(m_C)` has a unique prime ideal because one of the two field extensions
   is purely inseparable: for a purely inseparable `N/K` and any field extension `L/K`, the
   ring `L ⊗_K N` is local with nilpotent maximal ideal, so its `Spec` is one point.

Combining (2), (4) and (5): `D` has a unique maximal ideal, so `IsLocalRing D`, and the
contraction of `m_D` is `m_B` along `B → D` and `m_C` along `C → D`, i.e. both canonical maps
are local. The reusable analytic kernel (5) is
`tensorField_isPurelyInseparable_unique_prime`.
-/

@[expose] public section

open IsLocalRing TensorProduct

/-! ### The analytic kernel: step 5

If `L/K` and `M/K` are field extensions and at least one of them is purely inseparable, then
the tensor product `L ⊗[K] M` has a unique prime ideal, i.e. its `Spec` is a single point.

Without loss of generality `M/K` is purely inseparable, the other case being symmetric by
`Algebra.TensorProduct.comm`. Let `p` be the characteristic exponent of `K`. For every `x ∈ M`
there is `n` with `x^{p^n} ∈ K`, so in `R := L ⊗[K] M` the element `1 ⊗ x` satisfies
`(1 ⊗ x)^{p^n} = (x^{p^n}) • 1` in the image of `L`, and `1 ⊗ x - a` is nilpotent for a
suitable scalar `a`. Consequently `R / nilradical R` is generated over the image of `L` by
elements already in `L`, i.e. the reduction of `R` is a field, a quotient of `L`; and a ring
whose reduction is a field has a unique prime ideal. In characteristic `0`, purely inseparable
means `M = K`, so `R ≅ L` is itself a field.
-/

/-- Transport `∃! prime` along a ring isomorphism (primes correspond via `comap`). -/
private lemma uniquePrime_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : ∃! P : Ideal S, P.IsPrime) : ∃! P : Ideal R, P.IsPrime := by
  obtain ⟨P, hP, huniq⟩ := h
  refine ⟨Ideal.comap e P, Ideal.comap_isPrime e P, fun Q hQ => ?_⟩
  have heq : Ideal.comap (e.symm : S →+* R) Q = P := huniq _ (Ideal.comap_isPrime _ _)
  have hback : Ideal.comap (e : R →+* S) (Ideal.comap (e.symm : S →+* R) Q) = Q := by
    rw [Ideal.comap_comap, e.symm_comp, Ideal.comap_id]
  rw [← heq]
  exact hback.symm

/-- Helper for `tensorField_isPurelyInseparable_unique_prime`: the case where the
*right* factor `M/K` is purely inseparable. Every element of `L ⊗[K] M` has a
`p^n`-th power lying in the image of `L` (Frobenius additivity plus
`IsPurelyInseparable.pow_mem`); hence every prime ideal is contained in the
nilradical, so the nilradical is the unique prime. -/
@[ega "0 22.5.5" "locality of K⊗k k′"]
private lemma tensorField_isPurelyInseparable_unique_prime_aux
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (hins : IsPurelyInseparable K M) :
    ∃! P : Ideal (L ⊗[K] M), P.IsPrime := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have : ExpChar (L ⊗[K] M) p :=
    expChar_of_injective_algebraMap (algebraMap K (L ⊗[K] M)).injective p
  have hmono : ∀ (w : L ⊗[K] M) (a b : ℕ), a ≤ b → w ^ p ^ a ∈ (algebraMap L (L ⊗[K] M)).range →
      w ^ p ^ b ∈ (algebraMap L (L ⊗[K] M)).range := by
    rintro w a b hab ⟨e, he⟩
    refine ⟨e ^ p ^ (b - a), ?_⟩
    rw [map_pow, he, ← pow_mul, ← pow_add, Nat.add_sub_of_le hab]
  have hpow : ∀ z : L ⊗[K] M, ∃ n : ℕ, z ^ p ^ n ∈ (algebraMap L (L ⊗[K] M)).range := by
    have key : ∀ (l : L) (c : K),
        (l ⊗ₜ[K] (algebraMap K M c) : L ⊗[K] M) = (algebraMap K L c * l) ⊗ₜ[K] 1 := by
      intro l c
      rw [Algebra.algebraMap_eq_smul_one (R := K) (A := M),
        Algebra.algebraMap_eq_smul_one (R := K) (A := L), TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      congr 1
      rw [smul_mul_assoc, one_mul]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l m =>
        obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K p m
        refine ⟨n, ?_⟩
        rw [Algebra.TensorProduct.tmul_pow, ← hc, key]
        exact ⟨algebraMap K L c * l ^ p ^ n, rfl⟩
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        refine ⟨max a b, ?_⟩
        rw [add_pow_expChar_pow x y p (max a b)]
        exact Subring.add_mem _ (hmono x a _ (le_max_left a b) ha)
          (hmono y b _ (le_max_right a b) hb)
  have hQnil : ∀ Q : Ideal (L ⊗[K] M), Q.IsPrime → Q = nilradical (L ⊗[K] M) := by
    intro Q hQ
    refine le_antisymm (fun z hz => ?_) (nilradical_le_prime Q)
    obtain ⟨n, a, ha⟩ := hpow z
    have hmem : a ∈ Ideal.comap (algebraMap L (L ⊗[K] M)) Q := by
      rw [Ideal.mem_comap, ha]
      exact Ideal.pow_mem_of_mem Q hz _ (pow_pos (expChar_pos K p) n)
    rw [(Ideal.comap (algebraMap L (L ⊗[K] M)) Q).eq_bot_of_prime, Ideal.mem_bot] at hmem
    exact mem_nilradical.mpr ⟨p ^ n, by rw [← ha, hmem, map_zero]⟩
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (L ⊗[K] M)
  refine ⟨nilradical (L ⊗[K] M), ?_, hQnil⟩
  rw [← hQnil Q hQ.isPrime]
  exact hQ.isPrime

/-- If `L/K` and `M/K` are field extensions and at least one of them is purely inseparable,
then `L ⊗[K] M` has a unique prime ideal. -/
@[ega "0 22.5.5" "locality of K⊗k k′",
  ega "IV 4.3.2" "special case",
  ega "IV 4.3.7" "Purely inseparable K"]
lemma tensorField_isPurelyInseparable_unique_prime
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : IsPurelyInseparable K M ∨ IsPurelyInseparable K L) :
    ∃! P : Ideal (L ⊗[K] M), P.IsPrime := by
  rcases h with hM | hL
  · exact tensorField_isPurelyInseparable_unique_prime_aux hM
  · exact uniquePrime_of_ringEquiv (Algebra.TensorProduct.comm K L M).toRingEquiv
      (tensorField_isPurelyInseparable_unique_prime_aux (K := K) (L := M) (M := L) hL)

/-- **Assembly lemma for Stacks 092Y part (a).** If `B` is local, `B → D` is an
integral algebra map, and the fibre ring `D / (m_B · D)` has a unique prime ideal,
then `D` is a local ring.

Proof: every maximal ideal `I` of `D` contracts along the integral map to a maximal
ideal of `B` (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`), hence to `m_B`
(B local), so `I ⊇ m_B·D = J`. The quotient map `q : D → D/J` then sends each
maximal `I` to a maximal — in particular prime — ideal of the fibre, which by the
unique-prime hypothesis is the SAME ideal `P`; since `I ⊇ ker q = J` we recover
`I = comap q P`. Thus every maximal ideal of `D` equals `comap q P`, giving a unique
maximal ideal (`IsLocalRing.of_unique_max_ideal`). `D` is nontrivial because the
fibre has a prime, hence is nontrivial, and `q` is surjective.

This is reusable for parts (b)/(c): it pins every maximal ideal of `D` to a single
`comap q P`, and shows each contracts to `m_B` along `algebraMap B D`. -/
@[ega "0 22.5.2" "(iii)", sga "3 V 4.1.2" "locality of A[T]/(F)"]
lemma isLocalRing_of_integral_fibre_unique_prime
    {B D : Type*} [CommRing B] [CommRing D] [IsLocalRing B]
    [Algebra B D] [Algebra.IsIntegral B D]
    (hfib : ∃! P : Ideal (D ⧸ Ideal.map (algebraMap B D) (maximalIdeal B)), P.IsPrime) :
    IsLocalRing D := by
  set J : Ideal D := Ideal.map (algebraMap B D) (maximalIdeal B) with hJ
  obtain ⟨P, hPprime, hPuniq⟩ := hfib
  have : Nontrivial (D ⧸ J) := by
    rcases subsingleton_or_nontrivial (D ⧸ J) with hs | hn
    · exact absurd (Subsingleton.elim P ⊤) hPprime.ne_top
    · exact hn
  have : Nontrivial D := (Ideal.Quotient.mk J).domain_nontrivial
  have hcontract : ∀ I : Ideal D, I.IsMaximal → J ≤ I := by
    intro I hI
    rw [hJ, ← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)]
    exact Ideal.map_comap_le
  set q : D →+* (D ⧸ J) := Ideal.Quotient.mk J
  have hqsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hkerq : RingHom.ker q = J := Ideal.mk_ker
  have hkey : ∀ I : Ideal D, I.IsMaximal → I = Ideal.comap q P := by
    intro I hI
    have hJI : J ≤ I := hcontract I hI
    have heqP : Ideal.map q I = P := hPuniq _
      (Ideal.IsMaximal.map_of_surjective_of_ker_le hqsurj (hkerq.le.trans hJI)).isPrime
    rw [← heqP, Ideal.comap_map_of_surjective' q hqsurj I, hkerq, sup_eq_left.mpr hJI]
  obtain ⟨M, hM⟩ := Ideal.exists_maximal D
  exact .of_unique_max_ideal ⟨M, hM, fun N hN => by rw [hkey N hN, hkey M hM]⟩

/- Transport `∃! prime` along a `PrimeSpectrum.comap`-bijection `f : R →+* S`
(the unique prime of `S` is the contraction of the unique prime of `R`). -/
private lemma uniquePrime_of_specBijective' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hbij : Function.Bijective (PrimeSpectrum.comap f))
    (h : ∃! P : Ideal S, P.IsPrime) : ∃! P : Ideal R, P.IsPrime := by
  obtain ⟨P, hP, hu⟩ := h
  have huniqS : ∀ x y : PrimeSpectrum S, x = y := by
    intro x y; apply PrimeSpectrum.ext
    rw [hu x.asIdeal x.isPrime, hu y.asIdeal y.isPrime]
  refine ⟨(PrimeSpectrum.comap f ⟨P, hP⟩).asIdeal,
    (PrimeSpectrum.comap f ⟨P, hP⟩).isPrime, ?_⟩
  intro Q hQ
  obtain ⟨xS, hxS⟩ := hbij.surjective ⟨Q, hQ⟩
  have : (⟨Q, hQ⟩ : PrimeSpectrum R) = PrimeSpectrum.comap f ⟨P, hP⟩ := by
    rw [← hxS, huniqS xS ⟨P, hP⟩]
  exact congrArg PrimeSpectrum.asIdeal this

/-- A surjective ring hom with kernel contained in the nilradical induces a
bijection of prime spectra. -/
private lemma specComap_bijective_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hk : RingHom.ker f ≤ nilradical R) :
    Function.Bijective (PrimeSpectrum.comap f) := by
  refine ⟨fun x y hxy => PrimeSpectrum.comap_injective_of_surjective f hf hxy, fun x => ?_⟩
  have := x.isPrime
  have hkx : RingHom.ker f ≤ x.asIdeal := hk.trans (nilradical_le_prime x.asIdeal)
  refine ⟨⟨Ideal.map f x.asIdeal, Ideal.map_isPrime_of_surjective hf hkx⟩, PrimeSpectrum.ext ?_⟩
  show Ideal.comap f (Ideal.map f x.asIdeal) = x.asIdeal
  rw [Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hkx]

-- large elaboration; raise heartbeats
/-- **Fibre over the residue field (Stacks 092Y, step 4+5 core).** Let `RA`, `RB`,
`F` be fields and `Cb` a commutative ring with `RA`-algebra structures, and let
`ψ : Cb →ₐ[RA] F` be a surjective map whose kernel is contained in the nilradical
of `Cb`. If one of `F / RA` or `RB / RA` is purely inseparable, then
`RB ⊗[RA] Cb` has a unique prime ideal.

Proof: base-changing `ψ` gives a surjection `g : Cb ⊗[RA] RB → F ⊗[RA] RB` with
nil kernel, hence a bijection on prime spectra. The target `F ⊗[RA] RB` has a
unique prime by `tensorField_isPurelyInseparable_unique_prime` (transported
across `Algebra.TensorProduct.comm`). -/
@[ega "0 22.5.5" "locality of K⊗k k′"]
private lemma fibre_unique_prime_core
    {RA RB Cb F : Type*} [Field RA] [Field RB] [CommRing Cb] [Field F]
    [Algebra RA RB] [Algebra RA Cb] [Algebra RA F]
    (ψ : Cb →ₐ[RA] F) (hψsurj : Function.Surjective ψ)
    (hψker : RingHom.ker (ψ : Cb →+* F) ≤ nilradical Cb)
    (hins : IsPurelyInseparable RA F ∨ IsPurelyInseparable RA RB) :
    ∃! P : Ideal (RB ⊗[RA] Cb), P.IsPrime := by
  have hstep : ∃! P : Ideal (RB ⊗[RA] F), P.IsPrime :=
    tensorField_isPurelyInseparable_unique_prime hins
  have hcomm1 : ∃! P : Ideal (F ⊗[RA] RB), P.IsPrime :=
    uniquePrime_of_ringEquiv (Algebra.TensorProduct.comm RA F RB).toRingEquiv hstep
  let g : (Cb ⊗[RA] RB) →ₐ[RA] (F ⊗[RA] RB) :=
    Algebra.TensorProduct.map ψ (AlgHom.id RA RB)
  have hgsurj : Function.Surjective g :=
    Algebra.TensorProduct.map_surjective ψ (AlgHom.id RA RB) hψsurj Function.surjective_id
  have hkerg : RingHom.ker (g.toRingHom : (Cb ⊗[RA] RB) →+* _) ≤ nilradical (Cb ⊗[RA] RB) := by
    have hke := Algebra.TensorProduct.map_ker ψ (AlgHom.id RA RB) hψsurj Function.surjective_id
    have hkereq : RingHom.ker (g.toRingHom : (Cb ⊗[RA] RB) →+* _)
        = Ideal.map Algebra.TensorProduct.includeLeft (RingHom.ker ψ) ⊔
          Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker (AlgHom.id RA RB)) := hke
    rw [hkereq]
    have hkid : Ideal.map (Algebra.TensorProduct.includeRight (R := RA) (A := Cb) (B := RB))
        (RingHom.ker (AlgHom.id RA RB)) = ⊥ := by
      have : RingHom.ker (AlgHom.id RA RB) = ⊥ := by
        rw [RingHom.ker_eq_bot_iff_eq_zero]; intro x hx; simpa using hx
      rw [this, Ideal.map_bot]
    rw [hkid, sup_bot_eq]
    rw [Ideal.map_le_iff_le_comap]
    intro n hn
    have hn' : n ∈ nilradical Cb := hψker hn
    rw [Ideal.mem_comap, mem_nilradical]
    rw [mem_nilradical] at hn'
    obtain ⟨k, hk⟩ := hn'
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hbij : Function.Bijective (PrimeSpectrum.comap (g.toRingHom : (Cb ⊗[RA] RB) →+* _)) :=
    specComap_bijective_of_surjective_of_ker_le_nilradical _ hgsurj hkerg
  have htens : ∃! P : Ideal (Cb ⊗[RA] RB), P.IsPrime :=
    uniquePrime_of_specBijective' _ hbij hcomm1
  exact uniquePrime_of_ringEquiv (Algebra.TensorProduct.comm RA RB Cb).toRingEquiv htens

-- large elaboration; raise heartbeats
/-- **Fibre uniqueness (Stacks 092Y, steps 3+4+5).** The fibre ring
`D / (m_B · D)` of `D = B ⊗[A] C` over `B` has a unique prime ideal.

The argument:
1. Quotient-base-change: `(B ⊗[A] C) / (m_B·D) ≅ κ(m_B) ⊗[A] C` via
   `Algebra.TensorProduct.quotientTensorEquiv` (or `quotIdealMapEquivTensorQuot`),
   where `J = Ideal.map (algebraMap B D) (maximalIdeal B)` and `κ(m_B) = B/m_B`.
2. Base-change transitivity over the tower `A → κ(m_A) → κ(m_B)`:
   `κ(m_B) ⊗[A] C ≅ κ(m_B) ⊗[κ(m_A)] (κ(m_A) ⊗[A] C) = κ(m_B) ⊗[κ(m_A)] (C/m_A·C)`
   (`Algebra.TensorProduct.cancelBaseChange` + `quotIdealMapEquivTensorQuot` for
   `C/m_A·C ≅ κ(m_A) ⊗[A] C`).
3. `C̄ := C/(m_A·C)` is Artinian local over the field `κ(m_A)` (integral via
   `Algebra.IsIntegral.tensorProduct`/`tower_top`); its only prime is `m_C/(m_A·C)`,
   so `C̄ / nilradical = κ(m_C)` (a field). `nilradical C̄` is nilpotent
   (`IsArtinianRing.isNilpotent_nilradical`).
4. The induced ideal `(nilradical C̄)·(κ(m_B) ⊗ C̄)` is nil, so by
   `PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical` primes of
   `κ(m_B) ⊗ C̄` biject with primes of the quotient
   `κ(m_B) ⊗[κ(m_A)] (C̄/nilradical) = κ(m_B) ⊗[κ(m_A)] κ(m_C)`.
5. `κ(m_B) ⊗[κ(m_A)] κ(m_C)` has a unique prime by
   `tensorField_isPurelyInseparable_unique_prime` applied to `hins` (the two residue
   field extensions, one purely inseparable).
Transport `∃! prime` back along the ring isomorphisms (primes correspond by
`Ideal.comap`/`RingEquiv`). -/
@[ega "0 22.5.5" "partial"]
lemma existsUnique_isPrime_fibre
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    [Algebra.IsIntegral A C]
    (hins :
      @IsPurelyInseparable (ResidueField A) (ResidueField C) _ _
        (IsLocalRing.ResidueField.map (algebraMap A C)).toAlgebra ∨
      @IsPurelyInseparable (ResidueField A) (ResidueField B) _ _
        (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra) :
    ∃! P : Ideal ((TensorProduct A B C) ⧸
        Ideal.map (algebraMap B (TensorProduct A B C)) (maximalIdeal B)), P.IsPrime := by
  -- The residue-field algebra instances `Algebra (ResidueField A) (ResidueField B/C)` are now
  -- supplied canonically by Mathlib (from `[IsLocalHom (algebraMap A B/C)]`); re-introducing
  -- them via `letI` would create an instance diamond that breaks tensor-algebra synthesis.
  -- Use the CANONICAL `Algebra A (ResidueField B)` / `Algebra A (ResidueField C)` instances
  -- (synthesized from `Algebra A B` + the quotient algebra structure) so that the tensor
  -- products `ResidueField B ⊗[A] C` match `quotientTensorEquiv`'s canonical module instance.
  have hcore : ∃! P : Ideal ((ResidueField B) ⊗[ResidueField A] ((ResidueField A) ⊗[A] C)),
      P.IsPrime := by
    have : Algebra.IsIntegral (ResidueField A) ((ResidueField A) ⊗[A] C) :=
      Algebra.IsIntegral.tensorProduct A (ResidueField A) C
    have : Nontrivial (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top (map_maximalIdeal_le _))
    have : IsLocalRing (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) :=
      .of_surjective' _ Ideal.Quotient.mk_surjective
    have eqCb : (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) ≃+* ((ResidueField A) ⊗[A] C) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal A)).toRingEquiv
    have : Nontrivial ((ResidueField A) ⊗[A] C) :=
      ⟨eqCb 0, eqCb 1, fun h => by simpa using eqCb.injective h⟩
    have : IsLocalRing ((ResidueField A) ⊗[A] C) :=
      .of_surjective' (eqCb : (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) →+* _)
        eqCb.surjective
    let gC : C →ₐ[A] ResidueField C := { residue C with commutes' := fun r => rfl }
    let fRA : ResidueField A →ₐ[ResidueField A] ResidueField C := Algebra.ofId _ _
    have hcomm : ∀ (x : ResidueField A) (y : C), Commute (fRA x) (gC y) := fun _ _ => mul_comm _ _
    let ψ : ((ResidueField A) ⊗[A] C) →ₐ[ResidueField A] ResidueField C :=
      Algebra.TensorProduct.lift fRA gC hcomm
    have hψsurj : Function.Surjective ψ := by
      intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      refine ⟨(1 : ResidueField A) ⊗ₜ c, ?_⟩
      simp only [ψ, Algebra.TensorProduct.lift_tmul]
      simp [fRA, gC]
      rfl
    have hψker : RingHom.ker (ψ : ((ResidueField A) ⊗[A] C) →+* ResidueField C)
        ≤ nilradical ((ResidueField A) ⊗[A] C) := by
      have hnil : nilradical ((ResidueField A) ⊗[A] C) =
          maximalIdeal ((ResidueField A) ⊗[A] C) := by
        refine le_antisymm (nilradical_le_prime _) ?_
        rw [nilradical_eq_sInf]
        refine le_sInf fun P (hP : P.IsPrime) => (IsLocalRing.eq_maximalIdeal ?_).ge
        refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ResidueField A) P ?_
        rw [(Ideal.comap (algebraMap (ResidueField A) ((ResidueField A) ⊗[A] C)) P).eq_bot_of_prime]
        exact Ideal.bot_isMaximal
      rw [hnil, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective
        (ψ : ((ResidueField A) ⊗[A] C) →+* ResidueField C) hψsurj)]
    apply fibre_unique_prime_core ψ hψsurj hψker
    -- `hins` is stated with the `ResidueField.map …` algebra instance; the ambient one is
    -- Mathlib's canonical `ResidueField` algebra.  These algebras have the same `algebraMap`
    -- (both are the induced residue-field map), so `IsPurelyInseparable` transports across them.
    have halgB : (ResidueField.map (algebraMap A B)).toAlgebra
        = (inferInstance : Algebra (ResidueField A) (ResidueField B)) :=
      Algebra.algebra_ext _ _ (fun r => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r; rfl)
    have halgC : (ResidueField.map (algebraMap A C)).toAlgebra
        = (inferInstance : Algebra (ResidueField A) (ResidueField C)) :=
      Algebra.algebra_ext _ _ (fun r => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r; rfl)
    rcases hins with h | h
    · refine Or.inl ?_
      convert h using 2 <;> first | rfl | exact halgC.symm
    · refine Or.inr ?_
      convert h using 2 <;> first | rfl | exact halgB.symm
  -- κ(m_B) ⊗[κ(m_A)] (κ(m_A) ⊗[A] C) ≅ κ(m_B) ⊗[A] C  (cancelBaseChange)
  have eBC : (ResidueField B) ⊗[ResidueField A] ((ResidueField A) ⊗[A] C) ≃ₐ[ResidueField B]
      (ResidueField B) ⊗[A] C :=
    Algebra.TensorProduct.cancelBaseChange A (ResidueField A) (ResidueField B) (ResidueField B) C
  -- κ(m_B) ⊗[A] C ≅ D / (m_B · D)  (quotientTensorEquiv)
  have eDJ := (Algebra.TensorProduct.quotientTensorEquiv (R := A) A C B (maximalIdeal
      B)).toRingEquiv
  have hBC : ∃! P : Ideal ((ResidueField B) ⊗[A] C), P.IsPrime :=
    uniquePrime_of_ringEquiv
      (R := (ResidueField B) ⊗[A] C)
      (S := (ResidueField B) ⊗[ResidueField A] ((ResidueField A) ⊗[A] C))
      eBC.symm.toRingEquiv hcore
  -- Transport `∃! prime` to the fibre `D/(m_B·D)`.  With the canonical
  -- `Algebra A (ResidueField B)` instance, `hBC`'s tensor product carries the same module
  -- instance as `eDJ.symm`'s codomain; the unfolding `ResidueField B = B ⧸ maximalIdeal B` is
  -- bridged with a propositional cast, valid by `rfl` under full transparency.
  have hBC' : ∃! P : Ideal ((B ⧸ maximalIdeal B) ⊗[A] C), P.IsPrime := by
    have hprop : (∃! P : Ideal ((ResidueField B) ⊗[A] C), P.IsPrime)
        = (∃! P : Ideal ((B ⧸ maximalIdeal B) ⊗[A] C), P.IsPrime) := by
      set_option backward.isDefEq.respectTransparency true in rfl
    exact hprop ▸ hBC
  -- Final transport along `eDJ.symm : D/(m_B·D) ≃+* (B ⧸ m_B) ⊗[A] C`, inlined so that the goal's
  -- `Ideal` instance on `D/(m_B·D)` drives elaboration (avoiding the `Ideal.Quotient.semiring`
  -- vs `CommRing`-derived instance clash that blocks `uniquePrime_of_ringEquiv` here).
  obtain ⟨P, hP, hu⟩ := hBC'
  refine ⟨Ideal.comap (eDJ.symm : _ →+* _) P, Ideal.comap_isPrime _ _, fun Q hQ => ?_⟩
  have heq : Ideal.comap
      (eDJ : ((B ⧸ maximalIdeal B) ⊗[A] C) →+*
        (B ⊗[A] C) ⧸ Ideal.map (algebraMap B (B ⊗[A] C)) (maximalIdeal B)) Q = P :=
    hu _ (Ideal.comap_isPrime _ _)
  have hbk : Ideal.comap
        (eDJ.symm : ((B ⊗[A] C) ⧸ Ideal.map (algebraMap B (B ⊗[A] C)) (maximalIdeal B)) →+*
          ((B ⧸ maximalIdeal B) ⊗[A] C))
        (Ideal.comap
          (eDJ : ((B ⧸ maximalIdeal B) ⊗[A] C) →+*
            (B ⊗[A] C) ⧸ Ideal.map (algebraMap B (B ⊗[A] C)) (maximalIdeal B)) Q) = Q := by
    rw [Ideal.comap_comap]
    have hid : (eDJ : ((B ⧸ maximalIdeal B) ⊗[A] C) →+*
          (B ⊗[A] C) ⧸ Ideal.map (algebraMap B (B ⊗[A] C)) (maximalIdeal B)).comp
        (eDJ.symm : ((B ⊗[A] C) ⧸ Ideal.map (algebraMap B (B ⊗[A] C)) (maximalIdeal B)) →+*
          ((B ⧸ maximalIdeal B) ⊗[A] C)) = RingHom.id _ :=
      RingHom.ext (fun x => eDJ.apply_symm_apply x)
    rw [hid, Ideal.comap_id]
  rw [← heq]
  exact hbk.symm

-- large elaboration; raise heartbeats
/-- Helper for Stacks 092Y part (c): if `A → C` is an integral local homomorphism of
local rings, then every element `x` of the maximal ideal of `C` becomes nilpotent in
`C / (m_A · C)`, i.e. `x ^ k ∈ m_A · C` for some `k`. (The fibre `C / m_A·C` is local
and integral over the field `κ(m_A)`, hence has a unique prime equal to its nilradical;
the image of `x` lies in that maximal ideal, so it is nilpotent.) -/
private lemma mc_pow_mem {A C : Type*} [CommRing A] [CommRing C] [IsLocalRing A] [IsLocalRing C]
    [Algebra A C] [IsLocalHom (algebraMap A C)] [Algebra.IsIntegral A C]
    (x : C) (hx : x ∈ maximalIdeal C) :
    ∃ k, x ^ k ∈ Ideal.map (algebraMap A C) (maximalIdeal A) := by
  have hNle := map_maximalIdeal_le (algebraMap A C)
  set N : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A) with hN
  have : Nontrivial (C ⧸ N) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hNle)
  have : IsLocalRing (C ⧸ N) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsScalarTower A C (C ⧸ N) := .of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral A (C ⧸ N) := Algebra.IsIntegral.trans C
  have hmAN : ∀ a ∈ maximalIdeal A, (algebraMap A (C ⧸ N)) a = 0 := by
    intro a ha
    have hh : (algebraMap A (C ⧸ N)) a = (Ideal.Quotient.mk N) (algebraMap A C a) := rfl
    rw [hh, Ideal.Quotient.eq_zero_iff_mem, hN]
    exact Ideal.mem_map_of_mem _ ha
  have hnil : nilradical (C ⧸ N) = maximalIdeal (C ⧸ N) := by
    refine le_antisymm (nilradical_le_prime _) ?_
    rw [nilradical_eq_sInf]
    refine le_sInf fun P (hP : P.IsPrime) => (IsLocalRing.eq_maximalIdeal ?_).ge
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) P ?_
    have hmle : maximalIdeal A ≤ Ideal.comap (algebraMap A (C ⧸ N)) P := fun a ha => by
      rw [Ideal.mem_comap, hmAN a ha]
      exact P.zero_mem
    rw [le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ P).ne_top) hmle]
    exact maximalIdeal.isMaximal A
  have hxmem : (Ideal.Quotient.mk N) x ∈ maximalIdeal (C ⧸ N) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk N), Ideal.Quotient.eq] at hy
    have h2 := (maximalIdeal C).sub_mem (Ideal.mul_mem_right z _ hx) (hNle hy)
    simp only [sub_sub_cancel, mem_maximalIdeal, one_notMem_nonunits] at h2
  rw [← hnil, mem_nilradical] at hxmem
  obtain ⟨k, hk⟩ := hxmem
  exact ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ((map_pow (Ideal.Quotient.mk N) x k).trans hk)⟩

-- large elaboration; raise heartbeats
/-- **Stacks Tag 092Y.** Let `A → B` and `A → C` be local homomorphisms of local
rings, with `A → C` integral and at least one of the induced residue field
extensions `κ(m_C)/κ(m_A)`, `κ(m_B)/κ(m_A)` purely inseparable. Then
`D = B ⊗_A C` is a local ring and the canonical maps `B → D`, `C → D` are
local homomorphisms. -/
@[stacks 092Y, ega "0 22.5.5" "partial"]
theorem isLocalRing_tensorProduct_of_isIntegral
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    [Algebra.IsIntegral A C]
    (hins :
      @IsPurelyInseparable (ResidueField A) (ResidueField C) _ _
        (IsLocalRing.ResidueField.map (algebraMap A C)).toAlgebra ∨
      @IsPurelyInseparable (ResidueField A) (ResidueField B) _ _
        (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra) :
    IsLocalRing (TensorProduct A B C) ∧
      IsLocalHom (Algebra.TensorProduct.includeLeftRingHom : B →+* TensorProduct A B C) ∧
      IsLocalHom ((Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A B
          C).toRingHom) := by
  have : Algebra.IsIntegral B (TensorProduct A B C) := Algebra.IsIntegral.tensorProduct A B C
  have hloc : IsLocalRing (TensorProduct A B C) :=
    isLocalRing_of_integral_fibre_unique_prime (existsUnique_isPrime_fibre A B C hins)
  have hB : IsLocalHom (algebraMap B (TensorProduct A B C)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap B (TensorProduct A B C))).out 1 5).mpr
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal (TensorProduct A B C))))
  refine ⟨hloc, hB, ?_⟩
  set D := TensorProduct A B C
  set ir : C →+* D := (Algebra.TensorProduct.includeRight : C →ₐ[A] D).toRingHom with hir
  apply (IsLocalRing.local_hom_TFAE ir).out 4 1 |>.mp
  have hcomp : ir.comp (algebraMap A C) = algebraMap A D := by ext a; simp [hir]
  have hcomp2 : algebraMap A D = (algebraMap B D).comp (algebraMap A B) := by
    ext a
    show (algebraMap A D) a = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hmapN : Ideal.map ir (Ideal.map (algebraMap A C) (maximalIdeal A)) ≤ maximalIdeal D := by
    rw [Ideal.map_map, hcomp, hcomp2, ← Ideal.map_map]
    exact (Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)
  intro x hx
  obtain ⟨k, hk⟩ := mc_pow_mem (A := A) x hx
  refine Ideal.mem_comap.mpr ((maximalIdeal.isMaximal D).isPrime.mem_of_pow_mem k ?_)
  rw [← map_pow]
  exact hmapN (Ideal.mem_map_of_mem _ hk)
