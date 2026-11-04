module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.LocalProperties.Submodule
import StacksCore.Tactic.StacksAttribute

/-!
# Normal rings and integral closedness

Normality is defined by integral closedness and the domain property at every prime localization.
We prove that normal rings are integrally closed in their total rings of fractions and that
directed colimits of normal rings are normal.
-/

@[expose] public section

-- A normal domain is an integrally closed domain.
add_to_stacks 0309 IsIntegrallyClosed
add_to_ega "IV 14.5.5" IsIntegrallyClosed
add_to_ega "IV 7.5.3" "(vi), partial" IsIntegrallyClosed
add_to_stacks 0309 "identified with the Stacks wording" isIntegrallyClosed_iff

/-- A commutative ring `R` is *normal* if for every prime ideal `p` the localization `R_p` is an
integrally closed integral domain. -/
@[stacks 00GV, ega "IV 5.13.5", ega "IV 5.13.6"]
def IsNormalRing (R : Type*) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)

/-- A ring is normal exactly when its localizations at primes are integrally closed domains. -/
theorem isNormalRing_iff {R : Type*} [CommRing R] :
    IsNormalRing R ↔ ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
  Iff.rfl

/-! ### Basic API for normal rings -/

/-- Being an integrally closed domain transfers along a ring isomorphism. -/
private theorem isDomain_and_isIntegrallyClosed_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) [IsDomain A] [IsIntegrallyClosed A] :
    IsDomain B ∧ IsIntegrallyClosed B :=
  ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

/-- A localization of `R` at a prime `p` is a normal domain when `R` is a normal ring. -/
theorem IsNormalRing.atPrime {R : Type*} [CommRing R] (h : IsNormalRing R) (p : Ideal R)
    [p.IsPrime] (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.AtPrime T p] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  obtain ⟨_, _⟩ := isNormalRing_iff.mp h p
  exact isDomain_and_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) T).toRingEquiv

/-- Normality transports along a ring isomorphism. -/
theorem IsNormalRing.congr {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : IsNormalRing A) : IsNormalRing B := by
  refine isNormalRing_iff.mpr @fun q hq => ?_
  have hp : (q.comap (e : A →+* B)).IsPrime := hq.comap _
  have hmap : (q.comap (e : A →+* B)).primeCompl.map (e : A ≃+* B).toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, Ideal.mem_comap, Subsemigroup.mem_mk]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · exact fun hx => ⟨e.symm x, by simpa using hx, by simp⟩
  obtain ⟨_, _⟩ := isNormalRing_iff.mp h (q.comap (e : A →+* B))
  exact isDomain_and_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap (e : A →+* B)))
      (Localization.AtPrime q) e hmap)

/-- A localization of a normal ring is a normal ring. -/
@[stacks 037C]
theorem IsNormalRing.isLocalization {R : Type*} [CommRing R] (h : IsNormalRing R)
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsNormalRing S := by
  refine isNormalRing_iff.mpr @fun q hq => ?_
  have : (q.comap (algebraMap R S)).IsPrime := hq.comap _
  have : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ _
  exact h.atPrime (q.comap (algebraMap R S)) (Localization.AtPrime q)

/-- A normal ring which is local is a normal domain. -/
theorem IsNormalRing.of_isLocalRing {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsNormalRing R) : IsDomain R ∧ IsIntegrallyClosed R := by
  have : IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) :=
    IsLocalization.self fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx
  exact h.atPrime (IsLocalRing.maximalIdeal R) R

/-- A normal domain is a normal ring: Definition 0309 implies Definition 00GV. -/
theorem IsNormalRing.of_isIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsNormalRing R := isNormalRing_iff.mpr fun p _ =>
  ⟨IsLocalization.isDomain_of_local_atPrime ‹p.IsPrime›,
    isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p) (M := p.primeCompl)
      p.primeCompl_le_nonZeroDivisors⟩

/-- A normal ring is reduced. -/
@[ega "IV 5.13.5"]
theorem IsNormalRing.isReduced {R : Type*} [CommRing R] (h : IsNormalRing R) : IsReduced R := by
  apply isReduced_ofLocalizationMaximal
  intro m hm
  have := (isNormalRing_iff.mp h m).1
  infer_instance

/-- A *normal domain* is a (commutative) integral domain that is integrally closed in
its field of fractions. -/
@[ega "IV 7.5.3"]
class IsNormalDomain (R : Type*) [CommRing R] : Prop where
  isDomain : IsDomain R
  isIntegrallyClosed : IsIntegrallyClosed R

attribute [instance] IsNormalDomain.isDomain IsNormalDomain.isIntegrallyClosed

/-! ### Stacks 00GY

Stacks 00GY — any localization of a normal domain is normal — is Mathlib's, one declaration
per field of `IsNormalDomain`: `IsLocalization.isDomain_of_le_nonZeroDivisors` for the domain
half and `isIntegrallyClosed_of_isLocalization` for the integrally closed half. (Both take the
submonoid to consist of nonzerodivisors, which for a domain is `0 ∉ M`.) -/

add_to_stacks 00GY "the localization is a domain"
  IsLocalization.isDomain_of_le_nonZeroDivisors
add_to_stacks 00GY "the localization is integrally closed" isIntegrallyClosed_of_isLocalization
add_to_ega "II 8.11.8" "partial" isIntegrallyClosed_of_isLocalization

/-! ## Integral closedness is local at maximal ideals

The local-to-global argument uses integral closedness of the localizations, without any domain
hypothesis. In particular it applies to normal rings (tag 034M).
-/

/-- If `R_P` is integrally closed, every integral element of the total ring of fractions of `R`
has a denominator outside `P` that puts it in the image of `R`. -/
theorem exists_mem_primeCompl_mul_eq_algebraMap
    (R : Type*) [CommRing R] (P : Ideal R) [P.IsPrime]
    [IsIntegrallyClosed (Localization.AtPrime P)]
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ t ∈ P.primeCompl, ∃ r : R, algebraMap R (FractionRing R) t * x
        = algebraMap R (FractionRing R) r := by
  let K := FractionRing R
  let Rp := Localization.AtPrime P
  let Kp := FractionRing Rp
  have hf (y : nonZeroDivisors R) : IsUnit ((algebraMap Rp Kp).comp (algebraMap R Rp) y) :=
    IsLocalization.map_units Kp (⟨_, Submonoid.mem_comap.mp
      (IsLocalization.nonZeroDivisors_le_comap P.primeCompl Rp y.2)⟩ : nonZeroDivisors Rp)
  let g : K →+* Kp := IsLocalization.lift hf
  have hg (a : R) : g (algebraMap R K a) = algebraMap Rp Kp (algebraMap R Rp a) :=
    IsLocalization.lift_eq hf a
  obtain ⟨ρ, hρ⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (hx.map_of_comp_eq (algebraMap R Rp) g (IsLocalization.lift_comp hf).symm)
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj P.primeCompl ρ
  have hz : g (algebraMap R K s * x - algebraMap R K a) = 0 := by
    have h := congrArg (algebraMap Rp Kp) has
    rw [map_mul] at h
    rw [map_sub, map_mul, hg, hg, ← hρ]
    linear_combination h
  obtain ⟨⟨b, d⟩, hbd⟩ := IsLocalization.surj (nonZeroDivisors R)
    (algebraMap R K s * x - algebraMap R K a)
  have hb : algebraMap R Rp b = 0 := by
    rw [← IsFractionRing.to_map_eq_zero_iff (K := Kp), ← hg, ← hbd, map_mul, hz, zero_mul]
  obtain ⟨w, hw⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl Rp b).mp hb
  refine ⟨w * s, P.primeCompl.mul_mem w.2 s.2, w * a, ?_⟩
  have hwz : algebraMap R K w * (algebraMap R K s * x - algebraMap R K a) = 0 := by
    rw [← (IsLocalization.map_units K d).mul_left_eq_zero, mul_assoc, hbd, ← map_mul, hw,
      map_zero]
  rw [map_mul, map_mul]
  linear_combination hwz

/-- If all maximal localizations of `R` are integrally closed, every integral element of its
total ring of fractions lies in the image of `R`. -/
theorem exists_algebraMap_eq_of_isIntegral_of_forall_localization_maximal
    (R : Type*) [CommRing R]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsIntegrallyClosed (Localization.AtPrime P))
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R (FractionRing R) r = x := by
  refine Submodule.mem_one.mp <| Submodule.mem_of_localization_maximal
    (fun P _ => LocalizedModule P.primeCompl (FractionRing R))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (FractionRing R)) x 1 fun P _ => ?_
  have := h P
  obtain ⟨t, htP, r, heq⟩ := exists_mem_primeCompl_mul_eq_algebraMap R P x hx
  rw [Submodule.mem_localized₀]
  refine ⟨algebraMap R (FractionRing R) r, Submodule.algebraMap_mem r, ⟨t, htP⟩, ?_⟩
  rw [← IsLocalizedModule.mk_eq_mk', LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.mk_smul]
  rw [Algebra.smul_def, ← heq]

/-- A commutative ring whose localizations at all maximal ideals are integrally closed is
integrally closed in its total ring of fractions; no domain hypothesis is needed. -/
theorem IsIntegrallyClosed.of_forall_localization_maximal {R : Type*} [CommRing R]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed R := by
  refine ⟨IsFractionRing.injective R (FractionRing R), fun {x} =>
    ⟨exists_algebraMap_eq_of_isIntegral_of_forall_localization_maximal R h x, ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact isIntegral_algebraMap

/-- A normal ring `R` is integrally closed in its total ring of fractions
`Q(R) = FractionRing R`. -/
@[stacks 034M, ega "IV 6.14.1.1" "(i) necessity"]
theorem IsNormalRing.isIntegrallyClosed
    {R : Type*} [CommRing R] (hR : IsNormalRing R) :
    IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_forall_localization_maximal fun P _ => (isNormalRing_iff.mp hR P).2

/-!
# A directed colimit of normal rings is a normal ring

Let `(ι, ≤)` be a directed nonempty preorder, let `(R_i)_{i ∈ ι}` be a family of
commutative rings, and let `φ_{ij} : R_i → R_j` for `i ≤ j` be ring homomorphisms
forming a directed system. If every `R_i` is a normal ring, then so is the colimit
`R = colim_i R_i`. This is Stacks Tag 037D (Lemma 10.37.17).

An integral domain is *normal* when it is integrally closed in its field of
fractions, which in Mathlib is `IsDomain` together with `IsIntegrallyClosed`. A
commutative ring `R` is *normal* when the localization `R_p` is a normal domain for
every prime ideal `p ⊆ R` (Stacks Definition 10.37.11, Tag 00GV). A normal ring need
not itself be a domain — a finite product of normal domains is normal — which is why
the definition is phrased through the localizations rather than as "integrally
closed domain".

A directed system of rings is a directed nonempty preorder `(ι, ≤)`, a family of
commutative rings `(R_i)`, and ring homomorphisms `φ_{ij} : R_i → R_j` for `i ≤ j`
with `φ_{ii} = id` and `φ_{jk} ∘ φ_{ij} = φ_{ik}`; the last two conditions are
Mathlib's `DirectedSystem`. The colimit is `Ring.DirectLimit R φ`.

## Main results

* `directLimit_isNormalRing`: a directed colimit of normal rings is a normal ring.
* `Ring.DirectLimit.isDomain`: a directed colimit of domains is a domain.
* `Ring.DirectLimit.isIntegrallyClosed`: a directed colimit of integrally closed domains
  is integrally closed.
* `Ring.DirectLimit.exists_of_finset`: any finite set of elements of a directed colimit
  descends to a single stage.
-/

@[expose] public section

/-- Taking the complement of a prime ideal commutes with pullback. -/
theorem Ideal.primeCompl_comap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal S) [p.IsPrime] : (p.comap f).primeCompl = p.primeCompl.comap f := by
  ext x
  simp [Ideal.mem_primeCompl_iff]

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (G : ι → Type*) [(i : ι) → CommRing (G i)]
variable (φ : (i j : ι) → i ≤ j → G i →+* G j)

/-- A directed colimit of integral domains is an integral domain. No injectivity of the
transition maps is needed. -/
@[ega "IV 5.13.3"]
theorem Ring.DirectLimit.isDomain
    (H : ι → Type*) [(i : ι) → CommRing (H i)]
    (ψ : (i j : ι) → i ≤ j → H i →+* H j)
    (hdir : DirectedSystem H (fun i j h => ψ i j h))
    (hdom : ∀ i, IsDomain (H i)) :
    IsDomain (Ring.DirectLimit H (fun i j h => ψ i j h)) := by
  classical
  have : Nontrivial (Ring.DirectLimit H (fun i j h => ψ i j h)) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    refine ⟨Ring.DirectLimit.of H (fun i j h => ψ i j h) i 1,
      Ring.DirectLimit.of H (fun i j h => ψ i j h) i 0, fun h => ?_⟩
    rw [map_zero] at h
    obtain ⟨l, hil, hl⟩ := Ring.DirectLimit.of.zero_exact h
    exact one_ne_zero (by rwa [map_one] at hl)
  have : NoZeroDivisors (Ring.DirectLimit H (fun i j h => ψ i j h)) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨j, b, rfl⟩ := Ring.DirectLimit.exists_of y
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    rw [← Ring.DirectLimit.of_f hik a,
        ← Ring.DirectLimit.of_f hjk b] at hxy ⊢
    rw [← map_mul] at hxy
    obtain ⟨l, hkl, hl0⟩ := Ring.DirectLimit.of.zero_exact hxy
    rw [map_mul] at hl0
    rcases mul_eq_zero.mp hl0 with h | h <;> [left; right] <;>
      rw [← Ring.DirectLimit.of_f hkl, h, map_zero]
  exact NoZeroDivisors.to_isDomain _

/-- Any finite set of elements of a directed colimit of rings descends to a
single stage. Given a `Finset` `s` of elements of `Ring.DirectLimit G f`, there is an
index `i` and a (set-theoretic) section `g` such that `of i (g z) = z` for every
`z ∈ s`. -/
theorem Ring.DirectLimit.exists_of_finset
    (G : ι → Type*) [(i : ι) → CommRing (G i)]
    (f : ∀ i j, i ≤ j → G i → G j)
    (s : Finset (Ring.DirectLimit G (fun i j h => f i j h))) :
    ∃ (i : ι) (g : Ring.DirectLimit G (fun i j h => f i j h) → G i),
      ∀ z ∈ s, Ring.DirectLimit.of G (fun i j h => f i j h) i (g z) = z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨Classical.arbitrary ι, fun _ => 0, by simp⟩
  | @insert z s hzs ih =>
    obtain ⟨i, g, hg⟩ := ih
    obtain ⟨j, w, hw⟩ := Ring.DirectLimit.exists_of (f := f) z
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y => if y = z then f j k hjk w else f i k hik (g y), fun y hy => ?_⟩
    by_cases hyz : y = z
    · subst hyz
      simpa using hw
    · simpa [hyz] using hg y ((Finset.mem_insert.mp hy).resolve_left hyz)

/-- In an integrally closed commutative ring `A`, if `a` is a root of `q.scaleRoots b` for a monic
`q` and a nonzerodivisor `b`, then `b` divides `a`. -/
theorem exists_mul_eq_of_scaleRoots_eval_eq_zero {A : Type*} [CommRing A]
    [IsIntegrallyClosed A] {q : Polynomial A} (hq : q.Monic) {a b : A}
    (hb : b ∈ nonZeroDivisors A)
    (h : (q.scaleRoots b).eval a = 0) : ∃ y, y * b = a := by
  set K := FractionRing A
  set μ := IsLocalization.mk' K a ⟨b, hb⟩ with hμ
  have hkey := Polynomial.scaleRoots_eval₂_mul (p := q) (algebraMap A K) μ b
  rw [show algebraMap A K b * μ = algebraMap A K a by
      rw [hμ, mul_comm, IsLocalization.mk'_spec],
    Polynomial.eval₂_at_apply, h, map_zero] at hkey
  have hbK : IsUnit (algebraMap A K b) := IsLocalization.map_units K ⟨b, hb⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (⟨q, hq, ((hbK.pow _).mul_right_eq_zero).mp hkey.symm⟩ : IsIntegral A μ)
  exact ⟨y, (IsFractionRing.injective A K).eq_iff.mp <| by
    rw [map_mul, hy, hμ, IsLocalization.mk'_spec]⟩

/-- A directed colimit of integrally closed domains is integrally closed in its field
of fractions. -/
@[ega "IV 5.13.4" "more general"]
theorem Ring.DirectLimit.isIntegrallyClosed
    (H : ι → Type*) [(i : ι) → CommRing (H i)]
    (ψ : (i j : ι) → i ≤ j → H i →+* H j)
    (hdir : DirectedSystem H (fun i j h => ψ i j h))
    (hdom : ∀ i, IsDomain (H i))
    (hic : ∀ i, IsIntegrallyClosed (H i)) :
    IsIntegrallyClosed (Ring.DirectLimit H (fun i j h => ψ i j h)) := by
  have := Ring.DirectLimit.isDomain H ψ hdir hdom
  classical
  rw [isIntegrallyClosed_iff (FractionRing (Ring.DirectLimit H (fun i j h => ψ i j h)))]
  rintro x ⟨p, hpmonic, hpeval⟩
  obtain ⟨a, b, hb, hxab⟩ := IsFractionRing.div_surjective
    (A := Ring.DirectLimit H (fun i j h => ψ i j h)) x
  have hq0 : (p.scaleRoots b).eval a = 0 := by
    have hinj := IsFractionRing.injective (Ring.DirectLimit H (fun i j h => ψ i j h))
      (FractionRing (Ring.DirectLimit H (fun i j h => ψ i j h)))
    have := Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero hinj (hxab ▸ hpeval) hb
    rwa [Polynomial.eval₂_at_apply, map_eq_zero_iff _ hinj] at this
  obtain ⟨i, g, hg⟩ := Ring.DirectLimit.exists_of_finset H (fun i j h => ψ i j h)
    (insert a (insert b (p.support.image p.coeff)))
  have hga : Ring.DirectLimit.of H (fun i j h => ψ i j h) i (g a) = a :=
    hg a (Finset.mem_insert_self _ _)
  have hgb : Ring.DirectLimit.of H (fun i j h => ψ i j h) i (g b) = b :=
    hg b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hplift : p ∈ Polynomial.lifts (Ring.DirectLimit.of H (fun i j h => ψ i j h) i) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr fun k => if hk : k ∈ p.support then
      ⟨g (p.coeff k), hg _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨k, hk, rfl⟩)))⟩
    else ⟨0, by rw [map_zero, Polynomial.notMem_support_iff.mp hk]⟩
  obtain ⟨pi, hpimap, -, hpimonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hplift hpmonic
  have hqieval0 : Ring.DirectLimit.of H (fun i j h => ψ i j h) i
      ((pi.scaleRoots (g b)).eval (g a)) = 0 := by
    rwa [← Polynomial.eval_map_apply,
      Polynomial.map_scaleRoots _ _ _ (by simp [hpimonic.leadingCoeff]), hpimap, hgb, hga]
  obtain ⟨l, hil, hl0⟩ := Ring.DirectLimit.of.zero_exact hqieval0
  have hofbl : Ring.DirectLimit.of H (fun i j h => ψ i j h) l (ψ i l hil (g b)) = b := by
    rw [Ring.DirectLimit.of_f, hgb]
  have hqleval0 :
      ((pi.map (ψ i l hil)).scaleRoots (ψ i l hil (g b))).eval (ψ i l hil (g a)) = 0 := by
    rw [← Polynomial.map_scaleRoots _ _ _ (by simp [hpimonic.leadingCoeff]),
      Polynomial.eval_map_apply, hl0]
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨yl, hyl⟩ := exists_mul_eq_of_scaleRoots_eval_eq_zero (hpimonic.map _)
    (mem_nonZeroDivisors_of_ne_zero fun h => hbne (by rw [← hofbl, h, map_zero])) hqleval0
  refine ⟨Ring.DirectLimit.of H (fun i j h => ψ i j h) l yl, ?_⟩
  have hbK : algebraMap (Ring.DirectLimit H (fun i j h => ψ i j h))
      (FractionRing (Ring.DirectLimit H (fun i j h => ψ i j h))) b ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← hxab, ← hga, ← Ring.DirectLimit.of_f hil, ← hyl,
    map_mul, hofbl, map_mul, mul_div_cancel_right₀ _ hbK]

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- The pullback of an ideal `p` of a directed colimit to the stage `G i` is the pullback
along `φ i j` of its pullback to any later stage `G j`. -/
@[ega "IV 5.13.1" "Clause (ii)"]
theorem Ring.DirectLimit.comap_of_eq_comap_comap_of
    (p : Ideal (Ring.DirectLimit G (fun i j h => φ i j h)))
    (i j : ι) (h : i ≤ j) :
    p.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i)
      = (p.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) j)).comap (φ i j h) := by
  rw [Ideal.comap_comap]
  congr 1
  ext x
  simp

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- Localizing a directed system of rings at a compatible family of primes gives a
directed system of local rings, with transition maps `Localization.localRingHom`. -/
private theorem directedSystem_localRingHom (hdir : DirectedSystem G (fun i j h => φ i j h))
    (P : (i : ι) → Ideal (G i)) [∀ i, (P i).IsPrime]
    (hP : ∀ i j (h : i ≤ j), P i = (P j).comap (φ i j h)) :
    DirectedSystem (fun i => Localization.AtPrime (P i))
      (fun i j h => Localization.localRingHom (P i) (P j) (φ i j h) (hP i j h)) := by
  refine ⟨fun i x => ?_, fun k j i hij hjk x => ?_⟩
  · rw [Localization.localRingHom_unique (P i) (P i) (φ i i le_rfl) (hP i i le_rfl)
      (j := RingHom.id _) fun y => by rw [hdir.map_self y]; rfl]
    rfl
  · rw [← RingHom.comp_apply, ← Localization.localRingHom_comp]
    refine DFunLike.congr_fun (Localization.localRingHom_unique _ _ _ _ fun y => ?_) x
    rw [Localization.localRingHom_to_map, RingHom.comp_apply, hdir.map_map hij hjk y]

section Localization

variable (H : ι → Type*) [(i : ι) → CommRing (H i)] [(i : ι) → Algebra (G i) (H i)]
variable (ψ : (i j : ι) → i ≤ j → H i →+* H j)

omit [IsDirectedOrder ι] [Nonempty ι] in
/-- Compatible structure maps `G i → H i` induce a ring homomorphism between the directed
colimits. -/
private theorem exists_directLimit_hom_of_algebraMap
    (hψ : ∀ i j (h : i ≤ j) x,
      ψ i j h (algebraMap (G i) (H i) x) = algebraMap (G j) (H j) (φ i j h x)) :
    ∃ Φ : Ring.DirectLimit G (fun i j h => φ i j h) →+* Ring.DirectLimit H (fun i j h => ψ i j h),
      ∀ i a, Φ (Ring.DirectLimit.of G (fun i j h => φ i j h) i a)
        = Ring.DirectLimit.of H (fun i j h => ψ i j h) i (algebraMap (G i) (H i) a) :=
  ⟨Ring.DirectLimit.lift G (fun i j h => φ i j h) _
    (fun i => (Ring.DirectLimit.of H (fun i j h => ψ i j h) i).comp (algebraMap (G i) (H i)))
    (fun i j h x => by
      rw [RingHom.comp_apply, RingHom.comp_apply, ← hψ, Ring.DirectLimit.of_f]),
    fun i a => by rw [Ring.DirectLimit.lift_of]; rfl⟩

variable (M : Submonoid (Ring.DirectLimit G (fun i j h => φ i j h)))
  [∀ i, IsLocalization (M.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i)) (H i)]
  (Φ : Ring.DirectLimit G (fun i j h => φ i j h) →+* Ring.DirectLimit H (fun i j h => ψ i j h))
  (hΦ : ∀ i a, Φ (Ring.DirectLimit.of G (fun i j h => φ i j h) i a)
    = Ring.DirectLimit.of H (fun i j h => ψ i j h) i (algebraMap (G i) (H i) a))
include hΦ

/-- Two elements of a directed colimit identified in the colimit of the localizations at
the pullbacks of a submonoid `M` are identified after multiplying by an element of `M`. -/
private theorem exists_mul_eq_mul_of_directLimit_hom_eq
    (hdirH : DirectedSystem H (fun i j h => ψ i j h))
    (hψ : ∀ i j (h : i ≤ j) x,
      ψ i j h (algebraMap (G i) (H i) x) = algebraMap (G j) (H j) (φ i j h x))
    {x y : Ring.DirectLimit G (fun i j h => φ i j h)} (hxy : Φ x = Φ y) :
    ∃ c : M, c * x = c * y := by
  obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨j, b, rfl⟩ := Ring.DirectLimit.exists_of y
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  rw [← Ring.DirectLimit.of_f hik a,
    ← Ring.DirectLimit.of_f hjk b] at hxy ⊢
  rw [hΦ, hΦ, ← sub_eq_zero, ← map_sub] at hxy
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hxy
  rw [map_sub, sub_eq_zero, hψ, hψ] at hl
  obtain ⟨⟨d, hd⟩, hdeq⟩ := IsLocalization.exists_of_eq
    (M := M.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) l)) (S := H l) hl
  refine ⟨⟨Ring.DirectLimit.of G (fun i j h => φ i j h) l d, Submonoid.mem_comap.mp hd⟩, ?_⟩
  rw [Subtype.coe_mk, ← Ring.DirectLimit.of_f hkl (φ i k hik a),
    ← Ring.DirectLimit.of_f hkl (φ j k hjk b),
    ← map_mul, ← map_mul]
  exact congrArg _ hdeq

/-- Localization commutes with directed colimits: the colimit of the localizations of the
stages at the pullbacks of a submonoid `M` is a localization of the colimit at `M`. -/
theorem Ring.DirectLimit.isLocalization (hdirH : DirectedSystem H (fun i j h => ψ i j h))
    (hψ : ∀ i j (h : i ≤ j) x,
      ψ i j h (algebraMap (G i) (H i) x) = algebraMap (G j) (H j) (φ i j h x)) :
    letI := Φ.toAlgebra
    IsLocalization M (Ring.DirectLimit H (fun i j h => ψ i j h)) := by
  let := Φ.toAlgebra
  refine ⟨⟨?_, fun z => ?_,
    fun hxy => exists_mul_eq_mul_of_directLimit_hom_eq G φ H ψ M Φ hΦ hdirH hψ hxy⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of y
    rw [RingHom.algebraMap_toAlgebra, hΦ]
    exact (IsLocalization.map_units (H i)
      (⟨a, Submonoid.mem_comap.mpr hy⟩ :
        M.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i))).map
        (Ring.DirectLimit.of H (fun i j h => ψ i j h) i)
  · obtain ⟨i, w, rfl⟩ := Ring.DirectLimit.exists_of z
    obtain ⟨⟨b, c, hc⟩, hbc⟩ := IsLocalization.surj
      (M.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i)) w
    refine ⟨⟨Ring.DirectLimit.of G (fun i j h => φ i j h) i b,
      ⟨Ring.DirectLimit.of G (fun i j h => φ i j h) i c, Submonoid.mem_comap.mp hc⟩⟩, ?_⟩
    rw [Subtype.coe_mk, RingHom.algebraMap_toAlgebra, hΦ, hΦ, ← map_mul]
    exact congrArg _ hbc

end Localization

/-- Let `(ι, ≤)` be a directed nonempty preorder, let `(G_i)` be a family of commutative rings,
and let `φ_{ij} : G_i →+* G_j` (for `i ≤ j`) be ring homomorphisms forming a directed system of
rings. If every `G_i` is a normal ring, then the directed colimit `Ring.DirectLimit G φ` is a
normal ring. -/
@[stacks 037D, ega "IV 5.13.6" "more general"]
theorem directLimit_isNormalRing
    (hdir : DirectedSystem G (fun i j h => φ i j h))
    (hnormal : ∀ i, IsNormalRing (G i)) :
    IsNormalRing (Ring.DirectLimit G (fun i j h => φ i j h)) := by
  refine isNormalRing_iff.mpr @fun p hp => ?_
  let P i := p.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i)
  let ψ i j h :=
    Localization.localRingHom (P i) (P j) (φ i j h)
      (Ring.DirectLimit.comap_of_eq_comap_comap_of G φ p i j h)
  have hψ i j h x := Localization.localRingHom_to_map (P i) (P j) (φ i j h)
    (Ring.DirectLimit.comap_of_eq_comap_comap_of G φ p i j h) x
  have hdirH := directedSystem_localRingHom G φ hdir P
    (Ring.DirectLimit.comap_of_eq_comap_comap_of G φ p)
  obtain ⟨Φ, hΦ⟩ := exists_directLimit_hom_of_algebraMap G φ _ ψ hψ
  let := Φ.toAlgebra
  have : ∀ i, IsLocalization
      (p.primeCompl.comap (Ring.DirectLimit.of G (fun i j h => φ i j h) i))
      (Localization.AtPrime (P i)) := fun i => by
    rw [← Ideal.primeCompl_comap]
    exact Localization.isLocalization
  have := Ring.DirectLimit.isLocalization G φ _ ψ p.primeCompl Φ hΦ hdirH hψ
  let e := (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Ring.DirectLimit _ (fun i j h => ψ i j h))).toRingEquiv
  have hN i := isNormalRing_iff.mp (hnormal i) (P i)
  have := Ring.DirectLimit.isDomain _ ψ hdirH fun i => (hN i).1
  have := Ring.DirectLimit.isIntegrallyClosed _ ψ hdirH (fun i => (hN i).1) fun i => (hN i).2
  exact isDomain_and_isIntegrallyClosed_of_ringEquiv e.symm
