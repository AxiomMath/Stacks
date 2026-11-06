module

public import StacksFrontier.RingTheory.Flat.UniversalInjectivity05U9
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import Mathlib.RingTheory.Noetherian.Nilpotent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zero divisors of local rings of a tensor product of zero-dimensional local algebras

Let `k` be a field of characteristic zero and let `K`, `L` be local `k`-algebras of Krull
dimension zero.  Every zero divisor of every local ring `(K ⊗[k] L)_𝔮` is nilpotent
(Perrin, thèse, I Proposition 1.8).

## Implementation notes

Perrin's proof writes `K`, `L` as filtered unions of Artinian local subalgebras essentially of
finite type and uses that the tensor product of two such is Cohen–Macaulay (EGA IV 6.3.5,
6.7.1), together with the irreducibility of the local rings of a tensor product of field
extensions.  In characteristic zero a shorter route is available, and it is the one taken here.

* The tensor product `λ ⊗[k] κ` of the residue fields is a normal ring, every field extension
  being separable in characteristic zero (`Algebra.isSeparableExtension_of_charZero_and_tfae`),
  hence geometrically normal (Stacks 0C30), and the base change of a geometrically normal algebra
  to a field being normal (`Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_field`).
  So its local rings are domains.
* The kernel of `K ⊗[k] L → λ ⊗[k] κ` is nil, so an element of `(K ⊗[k] L)_𝔮` which is not
  nilpotent has nonzero image in the domain `(λ ⊗[k] κ)_𝔮̄`.
* A non-zero-divisor lifts along a reduction by a nilpotent ideal `I` of a base ring `A` with
  `A/I` a field, for a flat `A`-algebra
  (`TensorProduct.ZeroDimLocal.regularAt_bot_of_regularAt_map`): this is the local criterion in
  the form `Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent`.  It is applied
  once over `K` and once over `L`, when their maximal ideals are nilpotent.
* Finally a zero-dimensional local `k`-algebra is the directed union of the localizations of its
  finitely generated subalgebras at their maximal ideals, which are local with nilpotent maximal
  ideal, and the statement only involves finitely many elements at a time.

## References

* L. Perrin, *Approximation des schémas en groupes, quasi-compacts sur un corps*, thèse,
  I §1.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct.ZeroDimLocal

universe u v w

/-! ### The local criterion: injectivity modulo a nilpotent maximal ideal -/

open Stacks.NilpotentReduction in
/-- **Injectivity lifts along a nilpotent maximal ideal**, for an endomorphism of a flat module:
if `I ⊆ A` is a nilpotent maximal ideal, `M` is a flat `A`-module and `f : M → M` is injective
modulo `I`, then `f` is injective.  Over the field `A ⧸ I` the reduction is universally
injective, and universal injectivity lifts along a nilpotent ideal into a flat module
(`Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent`). -/
@[ega "IV 11.9.15" "special case"]
theorem injective_of_injective_mapQ {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Flat A M] (I : Ideal A) [I.IsMaximal] (hI : IsNilpotent I)
    (f : M →ₗ[A] M)
    (hf : Function.Injective (Submodule.mapQ (I • ⊤ : Submodule A M) (I • ⊤) f
      (Submodule.smul_top_le_comap_smul_top I f))) :
    Function.Injective f := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  have hUI : UniversallyInjectivePoly.{_, u} (mapQSMulTop I f) := fun Q _ _ =>
    Module.Flat.rTensor_preserves_injective_linearMap (mapQSMulTop I f) hf
  have h := (universallyInjectivePoly_iff_mapQSMulTop_of_isNilpotent I f hI).2 hUI A
  intro x y hxy
  have h' : f.rTensor A (x ⊗ₜ[A] (1 : A)) = f.rTensor A (y ⊗ₜ[A] (1 : A)) := by
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hxy]
  have := congrArg (TensorProduct.rid A M) (h h')
  simpa using this

/-! ### Regularity of an element at a multiplicative set, modulo an ideal -/

section Regular

variable {R : Type*} [CommRing R]

/-- `a` is a non-zero-divisor modulo `J` after localization at `T`, stated on elements of `R`:
if `t a b ∈ J` with `t ∈ T`, then `t' b ∈ J` for some `t' ∈ T`. -/
def RegularAt (J : Ideal R) (T : Submonoid R) (a : R) : Prop :=
  ∀ b : R, ∀ t ∈ T, t * (a * b) ∈ J → ∃ t' ∈ T, t' * b ∈ J

/-- Regularity modulo the kernel of a ring map can be tested after the ring map. -/
theorem regularAt_of_map {R' : Type*} [CommRing R'] (π : R →+* R') {J : Ideal R}
    (hJ : RingHom.ker π = J) {T : Submonoid R} {a : R}
    (h : RegularAt ⊥ (T.map π) (π a)) : RegularAt J T a := by
  intro b t ht hab
  rw [← hJ, RingHom.mem_ker, map_mul, map_mul] at hab
  obtain ⟨t', ⟨t₀, ht₀, rfl⟩, h'⟩ := h (π b) (π t) ⟨t, ht, rfl⟩ (by rw [hab]; rfl)
  refine ⟨t₀, ht₀, ?_⟩
  rw [← hJ, RingHom.mem_ker, map_mul]
  exact h'

/-- **A non-zero-divisor lifts along a nilpotent maximal ideal of a base ring**, for a flat
algebra: if `R` is flat over `A`, `I ⊆ A` is a nilpotent maximal ideal and `a ∈ R` is regular
modulo `IR` after localization at `T`, then `a` is regular after localization at `T`. -/
theorem regularAt_bot_of_regularAt_map {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [Algebra A R] [Module.Flat A R] (I : Ideal A) [I.IsMaximal] (hI : IsNilpotent I)
    (T : Submonoid R) (a : R) (h : RegularAt (I.map (algebraMap A R)) T a) :
    RegularAt ⊥ T a := by
  let S := Localization T
  have : Module.Flat R S := IsLocalization.flat S T
  have : Module.Flat A S := Module.Flat.trans A R S
  let f : S →ₗ[A] S := (LinearMap.mulLeft R (algebraMap R S a)).restrictScalars A
  have hmap : (I • ⊤ : Submodule A S) =
      ((I.map (algebraMap A R)).map (algebraMap R S)).restrictScalars A := by
    rw [Ideal.smul_top_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmem : ∀ y : S, y ∈ (I • ⊤ : Submodule A S) ↔
      y ∈ (I.map (algebraMap A R)).map (algebraMap R S) := fun y => by
    rw [hmap, Submodule.restrictScalars_mem]
  have hf : Function.Injective (Submodule.mapQ (I • ⊤ : Submodule A S) (I • ⊤) f
      (Submodule.smul_top_le_comap_smul_top I f)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero, hmem]
    rw [hmem] at hq
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq T y
    have hfy : f (IsLocalization.mk' S b t) = IsLocalization.mk' S (a * b) t := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
    rw [hfy, IsLocalization.mk'_mem_map_algebraMap_iff] at hq
    obtain ⟨t₀, ht₀, h₀⟩ := hq
    obtain ⟨t', ht', h'⟩ := h b t₀ ht₀ h₀
    exact (IsLocalization.mk'_mem_map_algebraMap_iff T S _ b t).2 ⟨t', ht', h'⟩
  have hinj := injective_of_injective_mapQ I hI f hf
  intro b t ht hab
  rw [Ideal.mem_bot] at hab
  have h0 : algebraMap R S b = 0 := by
    apply hinj
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, map_zero]
    have h1 : algebraMap R S t * (algebraMap R S a * algebraMap R S b) = 0 := by
      rw [← map_mul, ← map_mul, hab, map_zero]
    exact (IsLocalization.map_units S ⟨t, ht⟩).mul_right_eq_zero.mp h1
  obtain ⟨⟨t', ht'⟩, h'⟩ := (IsLocalization.map_eq_zero_iff T S b).1 h0
  exact ⟨t', ht', by rw [Ideal.mem_bot]; exact h'⟩

/-- Regularity at `⊥` and a submonoid makes the image in the localization a non-zero-divisor. -/
theorem algebraMap_mem_nonZeroDivisors_of_regularAt {T : Submonoid R} {a : R}
    (h : RegularAt ⊥ T a) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S] :
    algebraMap R S a ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq T y
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hy
  obtain ⟨⟨m, hm⟩, hmb⟩ := hy
  obtain ⟨t', ht', h'⟩ := h b m hm (by rw [Ideal.mem_bot]; exact hmb)
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨t', ht'⟩, by rw [Ideal.mem_bot] at h'; exact h'⟩

end Regular

/-! ### Nil ideals -/

/-- The image of a nil ideal generates a nil ideal. -/
theorem map_le_nilradical {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} (hI : I ≤ nilradical R) : I.map f ≤ nilradical R' := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨n, hn⟩ := (mem_nilradical).1 (hI hx)
  exact (mem_nilradical).2 ⟨n, by rw [← map_pow, hn, map_zero]⟩

/-- A nilpotent ideal is nil. -/
theorem le_nilradical_of_isNilpotent {R : Type*} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) : I ≤ nilradical R := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  refine (mem_nilradical).2 ⟨n, ?_⟩
  have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at this
  exact this

/-- A fraction whose numerator has a nilpotent image in the localization is nilpotent. -/
private theorem isNilpotent_mk'_of_pow_eq_zero {R : Type*} [CommRing R] {M : Submonoid R}
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] (a : R) (s : M) {n : ℕ}
    (h : algebraMap R S a ^ n = 0) : IsNilpotent (IsLocalization.mk' S a s) :=
  ⟨n, by rw [IsLocalization.mk'_eq_mul_mk'_one, mul_pow, h, zero_mul]⟩

/-! ### Local algebras with nilpotent maximal ideal -/

section NilpotentMaximal

variable (k : Type u) [Field k] [CharZero k] (K : Type v) (L : Type w) [CommRing K] [CommRing L]
  [Algebra k K] [Algebra k L] [IsLocalRing K] [IsLocalRing L]

open IsLocalRing

/-- The reduction `K ⊗[k] L → L ⊗[k] κ` of the first factor to its residue field. -/
noncomputable def firstReduction : K ⊗[k] L →ₐ[k] L ⊗[k] (K ⧸ maximalIdeal K) :=
  (Algebra.TensorProduct.comm k (K ⧸ maximalIdeal K) L).toAlgHom.comp
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (maximalIdeal K)) (AlgHom.id k L))

/-- The reduction `L ⊗[k] κ → λ ⊗[k] κ` of the first factor to its residue field. -/
noncomputable def secondReduction :
    L ⊗[k] (K ⧸ maximalIdeal K) →ₐ[k] (L ⧸ maximalIdeal L) ⊗[k] (K ⧸ maximalIdeal K) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (maximalIdeal L)) (AlgHom.id k _)

omit [CharZero k] [IsLocalRing L] in
/-- The kernel of `firstReduction` is generated by the maximal ideal of `K`. -/
theorem ker_firstReduction :
    RingHom.ker (firstReduction k K L) =
      (maximalIdeal K).map (algebraMap K (K ⊗[k] L)) := by
  have h1 : RingHom.ker (firstReduction k K L) = RingHom.ker
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (maximalIdeal K)) (AlgHom.id k L)) := by
    ext x
    simp only [RingHom.mem_ker, firstReduction, AlgHom.coe_comp, Function.comp_apply]
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  rw [h1, Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective k _)]
  have : RingHom.ker (Ideal.Quotient.mkₐ k (maximalIdeal K)) = maximalIdeal K :=
    Ideal.Quotient.mkₐ_ker k _
  rw [this]
  rfl

omit [CharZero k] in
/-- The kernel of `secondReduction` is generated by the maximal ideal of `L`. -/
theorem ker_secondReduction :
    RingHom.ker (secondReduction k K L) =
      (maximalIdeal L).map (algebraMap L (L ⊗[k] (K ⧸ maximalIdeal K))) := by
  rw [secondReduction, Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective k _)]
  have : RingHom.ker (Ideal.Quotient.mkₐ k (maximalIdeal L)) = maximalIdeal L :=
    Ideal.Quotient.mkₐ_ker k _
  rw [this]
  rfl

omit [CharZero k] [IsLocalRing L] in
/-- `firstReduction` is surjective. -/
theorem firstReduction_surjective : Function.Surjective (firstReduction k K L) := by
  rw [firstReduction, AlgHom.coe_comp]
  exact (AlgEquiv.surjective _).comp (Algebra.TensorProduct.map_surjective _ _
    (Ideal.Quotient.mkₐ_surjective k _) Function.surjective_id)

omit [CharZero k] in
/-- `secondReduction` is surjective. -/
theorem secondReduction_surjective : Function.Surjective (secondReduction k K L) :=
  Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective k _)
    Function.surjective_id

variable {k K L}

omit [CharZero k] in
/-- The kernel of the reduction `K ⊗[k] L → λ ⊗[k] κ` is nil, when the maximal ideals are. -/
theorem ker_reduction_le_nilradical (hK : IsNilpotent (maximalIdeal K))
    (hL : IsNilpotent (maximalIdeal L)) :
    RingHom.ker ((secondReduction k K L).toRingHom.comp (firstReduction k K L).toRingHom) ≤
      nilradical (K ⊗[k] L) := by
  intro z hz
  rw [RingHom.mem_ker, RingHom.comp_apply] at hz
  have h2 : (firstReduction k K L) z ∈ nilradical _ := by
    refine map_le_nilradical (algebraMap L (L ⊗[k] (K ⧸ maximalIdeal K)))
      (le_nilradical_of_isNilpotent hL) ?_
    rw [← ker_secondReduction]
    exact hz
  obtain ⟨n, hn⟩ := (mem_nilradical).1 h2
  have h1 : z ^ n ∈ nilradical _ := by
    refine map_le_nilradical (algebraMap K (K ⊗[k] L)) (le_nilradical_of_isNilpotent hK) ?_
    rw [← ker_firstReduction, RingHom.mem_ker, map_pow]
    exact hn
  obtain ⟨m, hm⟩ := (mem_nilradical).1 h1
  exact (mem_nilradical).2 ⟨n * m, by rw [pow_mul, hm]⟩

/-- **Zero divisors of the local rings of `K ⊗[k] L` are nilpotent**, for local `k`-algebras
`K`, `L` with nilpotent maximal ideals over a field `k` of characteristic zero. -/
theorem isNilpotent_of_not_mem_nonZeroDivisors_of_isNilpotent_maximalIdeal
    (hK : IsNilpotent (maximalIdeal K)) (hL : IsNilpotent (maximalIdeal L))
    (q : Ideal (K ⊗[k] L)) [q.IsPrime] (x : Localization.AtPrime q)
    (hx : x ∉ nonZeroDivisors (Localization.AtPrime q)) : IsNilpotent x := by
  classical
  let : Field (K ⧸ maximalIdeal K) := Ideal.Quotient.field _
  let : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
  have : Algebra.IsSeparableExtension k (K ⧸ maximalIdeal K) :=
    (Algebra.isSeparableExtension_of_charZero_and_tfae k (K ⧸ maximalIdeal K)).1 inferInstance
  have : Algebra.IsGeometricallyNormal k (K ⧸ maximalIdeal K) :=
    Algebra.IsGeometricallyNormal.of_isSeparableExtension
  have hnorm : IsNormalRing ((L ⧸ maximalIdeal L) ⊗[k] (K ⧸ maximalIdeal K)) :=
    Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_field
      (A := K ⧸ maximalIdeal K) (L ⧸ maximalIdeal L)
  set π₁ := (firstReduction k K L).toRingHom with hπ₁
  set π₂ := (secondReduction k K L).toRingHom with hπ₂
  set π := π₂.comp π₁ with hπ
  have hπs : Function.Surjective π :=
    (secondReduction_surjective k K L).comp (firstReduction_surjective k K L)
  have hker : RingHom.ker π ≤ nilradical _ := ker_reduction_le_nilradical hK hL
  have hkerq : RingHom.ker π ≤ q := hker.trans (nilradical_le_prime q)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  by_contra hn
  apply hx
  set q₂ := q.map π with hq₂
  have : q₂.IsPrime := Ideal.map_isPrime_of_surjective hπs hkerq
  have hcomap : q₂.comap π = q := by
    rw [hq₂, Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hkerq
  have : IsDomain (Localization.AtPrime q₂) := (hnorm q₂).1
  have hlift : ∀ y, algebraMap _ (Localization.AtPrime q₂) y = 0 → ∃ m₀ ∉ q, π m₀ * y = 0 := by
    intro y hy
    obtain ⟨⟨m, hm⟩, hmy⟩ := (IsLocalization.map_eq_zero_iff q₂.primeCompl _ _).1 hy
    obtain ⟨m₀, rfl⟩ := hπs m
    exact ⟨m₀, fun h => hm (Ideal.mem_map_of_mem _ h), hmy⟩
  -- the image of `a` in the local ring of `λ ⊗[k] κ` is nonzero
  have ha₂ : algebraMap _ (Localization.AtPrime q₂) (π a) ≠ 0 := by
    intro h0
    obtain ⟨m₀, hm₀, hma⟩ := hlift _ h0
    have hz : m₀ * a ∈ nilradical _ := hker (by rw [RingHom.mem_ker, map_mul]; exact hma)
    obtain ⟨N, hN⟩ := (mem_nilradical).1 hz
    apply hn
    have hu : IsUnit (algebraMap _ (Localization.AtPrime q) m₀) :=
      IsLocalization.map_units _ (⟨m₀, hm₀⟩ : q.primeCompl)
    have haN : (algebraMap _ (Localization.AtPrime q) a) ^ N = 0 := by
      have := congrArg (algebraMap _ (Localization.AtPrime q)) hN
      rw [map_pow, map_mul, mul_pow, map_zero] at this
      exact (hu.pow N).mul_right_eq_zero.mp this
    exact isNilpotent_mk'_of_pow_eq_zero _ a s haN
  -- regularity in `λ ⊗[k] κ`
  have key : RegularAt ⊥ ((q.primeCompl.map π₁).map π₂) (π₂ (π₁ a)) := by
    intro b t ht hab
    obtain ⟨t₁, ⟨t₀, ht₀, rfl⟩, rfl⟩ := ht
    rw [Ideal.mem_bot] at hab
    have hu : IsUnit (algebraMap _ (Localization.AtPrime q₂) (π t₀)) :=
      IsLocalization.map_units _ (⟨π t₀, fun h => ht₀ (by
        rw [← hcomap]; exact h)⟩ : q₂.primeCompl)
    have hb : algebraMap _ (Localization.AtPrime q₂) b = 0 := by
      have := congrArg (algebraMap _ (Localization.AtPrime q₂)) hab
      rw [map_mul, map_mul, map_zero] at this
      have := hu.mul_right_eq_zero.mp this
      exact (mul_eq_zero.mp this).resolve_left ha₂
    obtain ⟨m₀, hm₀, hmb⟩ := hlift _ hb
    exact ⟨π m₀, ⟨π₁ m₀, ⟨m₀, hm₀, rfl⟩, rfl⟩, by rw [Ideal.mem_bot]; exact hmb⟩
  have hreg : RegularAt ⊥ q.primeCompl a := by
    refine regularAt_bot_of_regularAt_map (A := K) (maximalIdeal K) hK _ a ?_
    refine regularAt_of_map π₁ (ker_firstReduction k K L) ?_
    refine regularAt_bot_of_regularAt_map (A := L) (maximalIdeal L) hL _ _ ?_
    exact regularAt_of_map π₂ (ker_secondReduction k K L) key
  have ha : algebraMap _ (Localization.AtPrime q) a ∈ nonZeroDivisors _ :=
    algebraMap_mem_nonZeroDivisors_of_regularAt hreg _
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  refine mul_mem ha ?_
  refine IsUnit.mem_nonZeroDivisors ?_
  rw [isUnit_iff_exists_inv]
  refine ⟨algebraMap _ _ (s : K ⊗[k] L), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]

end NilpotentMaximal

/-! ### Zero-dimensional local algebras as unions of local algebras with nilpotent maximal ideal -/

section Approximation

variable (k : Type u) [Field k] {K : Type v} [CommRing K] [Algebra k K] [IsLocalRing K]

open IsLocalRing

/-- The finitely generated subalgebra of `K` generated by a finite set. -/
abbrev adjoinFinset (F : Finset K) : Subalgebra k K := Algebra.adjoin k (F : Set K)

/-- The contraction of the maximal ideal of `K` to the subalgebra generated by `F`. -/
abbrev adjoinPrime (F : Finset K) : Ideal (adjoinFinset k F) :=
  (maximalIdeal K).comap (adjoinFinset k F).val.toRingHom

/-- The local ring of the subalgebra generated by `F` at the contraction of the maximal ideal
of `K`. -/
abbrev localAdjoin (F : Finset K) : Type v :=
  Localization.AtPrime (adjoinPrime k F)

/-- The embedding of `localAdjoin k F` into `K`: an element outside the maximal ideal is a unit
of the local ring `K`. -/
noncomputable def localAdjoinHom (F : Finset K) : localAdjoin k F →ₐ[k] K :=
  IsLocalization.liftAlgHom (M := (adjoinPrime k F).primeCompl)
    (f := (adjoinFinset k F).val) fun y => by
      by_contra h
      exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)

/-- `localAdjoinHom` restricts to the inclusion of the subalgebra. -/
theorem localAdjoinHom_algebraMap (F : Finset K) (a : adjoinFinset k F) :
    localAdjoinHom k F (algebraMap _ _ a) = a := by
  rw [localAdjoinHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- `localAdjoinHom` is injective. -/
theorem localAdjoinHom_injective (F : Finset K) : Function.Injective (localAdjoinHom k F) := by
  rw [localAdjoinHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
  intro x y
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (localAdjoinHom k F) h
    rwa [localAdjoinHom_algebraMap, localAdjoinHom_algebraMap] at this
  · rw [Subtype.val_injective h]

/-- The maximal ideal of `localAdjoin k F` is nilpotent when `K` is zero-dimensional: it is a
nil ideal of a Noetherian ring. -/
theorem isNilpotent_maximalIdeal_localAdjoin [Ring.KrullDimLE 0 K] (F : Finset K) :
    IsNilpotent (maximalIdeal (localAdjoin k F)) := by
  have : Algebra.FiniteType k (adjoinFinset k F) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset F)
  have : IsNoetherianRing (adjoinFinset k F) := Algebra.FiniteType.isNoetherianRing k _
  have hnil : maximalIdeal (localAdjoin k F) ≤ nilradical (localAdjoin k F) := by
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (adjoinPrime k F).primeCompl x
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (localAdjoin k F) (adjoinPrime k F)] at hx
    have hm : maximalIdeal K ≤ nilradical K :=
      (Ring.KrullDimLE.nilradical_eq_maximalIdeal (R := K)).ge
    obtain ⟨n, hn⟩ := (mem_nilradical).1 (hm hx)
    refine (mem_nilradical).2 ⟨n, ?_⟩
    have ha : a ^ n = 0 := Subtype.val_injective (by simpa using hn)
    rw [← IsLocalization.mk'_pow, ha, IsLocalization.mk'_zero]
  obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical (localAdjoin k F)
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← Ideal.zero_eq_bot, ← hN]
  exact Ideal.pow_right_mono hnil N

end Approximation

section Main

variable {k : Type u} [Field k] {K : Type v} {L : Type w} [CommRing K] [CommRing L]
  [Algebra k K] [Algebra k L]

/-- Every element of `K ⊗[k] L` comes from the tensor product of two finitely generated
subalgebras, and from any larger such. -/
theorem exists_finset_mem_range (x : K ⊗[k] L) :
    ∃ (FK : Finset K) (FL : Finset L), ∀ (FK' : Finset K) (FL' : Finset L), FK ⊆ FK' →
      FL ⊆ FL' → x ∈ (Algebra.TensorProduct.map (adjoinFinset k FK').val
        (adjoinFinset k FL').val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, ∅, fun _ _ _ _ => Subalgebra.zero_mem _⟩
  | tmul a b =>
    refine ⟨{a}, {b}, fun FK' FL' hK hL => ?_⟩
    have ha : a ∈ adjoinFinset k FK' :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (hK (Finset.mem_singleton_self a)))
    have hb : b ∈ adjoinFinset k FL' :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (hL (Finset.mem_singleton_self b)))
    exact ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨FK₁, FL₁, h₁⟩ := hx
    obtain ⟨FK₂, FL₂, h₂⟩ := hy
    refine ⟨FK₁ ∪ FK₂, FL₁ ∪ FL₂, fun FK' FL' hK hL => Subalgebra.add_mem _
      (h₁ FK' FL' (Finset.union_subset_left hK) (Finset.union_subset_left hL))
      (h₂ FK' FL' (Finset.union_subset_right hK) (Finset.union_subset_right hL))⟩

variable [IsLocalRing K] [IsLocalRing L]

variable (k) in
/-- The embedding of the tensor product of two local subalgebras. -/
noncomputable def localAdjoinTensorHom (FK : Finset K) (FL : Finset L) :
    localAdjoin k FK ⊗[k] localAdjoin k FL →ₐ[k] K ⊗[k] L :=
  Algebra.TensorProduct.map (localAdjoinHom k FK) (localAdjoinHom k FL)

/-- `localAdjoinTensorHom` is injective, `k` being a field. -/
theorem localAdjoinTensorHom_injective (FK : Finset K) (FL : Finset L) :
    Function.Injective (localAdjoinTensorHom k FK FL) :=
  TensorProduct.map_injective_of_flat_flat (localAdjoinHom k FK).toLinearMap
    (localAdjoinHom k FL).toLinearMap (localAdjoinHom_injective k FK)
    (localAdjoinHom_injective k FL)

/-- The tensor product of the subalgebras lands in the image of `localAdjoinTensorHom`. -/
theorem range_map_le_range_localAdjoinTensorHom (FK : Finset K) (FL : Finset L) :
    (Algebra.TensorProduct.map (adjoinFinset k FK).val (adjoinFinset k FL).val).range ≤
      (localAdjoinTensorHom k FK FL).range := by
  have h : Algebra.TensorProduct.map (adjoinFinset k FK).val (adjoinFinset k FL).val =
      (localAdjoinTensorHom k FK FL).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k _ (localAdjoin k FK))
        (IsScalarTower.toAlgHom k _ (localAdjoin k FL))) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, localAdjoinTensorHom,
      IsScalarTower.coe_toAlgHom', localAdjoinHom_algebraMap]
    rfl
  rw [h, AlgHom.range_comp]
  exact Subalgebra.map_le.2 fun _ _ => ⟨_, rfl⟩

omit [IsLocalRing K] [IsLocalRing L] in
/-- Nilpotence of zero divisors transfers along an injective ring map, one zero divisor at a
time: if `c₀ z₀ x₀ = 0` downstairs with `c₀` outside the contracted prime and no multiple of
`z₀` outside `q` vanishing upstairs, then a multiple of a power of `x₀` outside `q` vanishes. -/
theorem exists_mul_pow_eq_zero_of_injective {R₀ R : Type*} [CommRing R₀] [CommRing R]
    (j : R₀ →+* R) (hj : Function.Injective j) (q : Ideal R) [q.IsPrime]
    (hP : ∀ y : Localization.AtPrime (q.comap j), y ∉ nonZeroDivisors _ → IsNilpotent y)
    (x₀ z₀ c₀ : R₀) (hc : j c₀ ∉ q) (hczx : j c₀ * (j z₀ * j x₀) = 0)
    (hz : ∀ c' ∉ q, c' * j z₀ ≠ 0) :
    ∃ n : ℕ, ∃ d ∉ q, d * j x₀ ^ n = 0 := by
  have hc₀ : c₀ ∈ (q.comap j).primeCompl := hc
  have hczx₀ : c₀ * (z₀ * x₀) = 0 := hj (by rw [map_mul, map_mul, map_zero]; exact hczx)
  obtain ⟨n, hn⟩ := hP (algebraMap _ _ x₀) (by
    intro hreg
    have hzx : algebraMap R₀ (Localization.AtPrime (q.comap j)) z₀ *
        algebraMap _ (Localization.AtPrime (q.comap j)) x₀ = 0 := by
      rw [← map_mul]
      exact (IsLocalization.map_eq_zero_iff (q.comap j).primeCompl _ _).2 ⟨⟨c₀, hc₀⟩, hczx₀⟩
    have h0 := (mem_nonZeroDivisors_iff_right.1 hreg) _ hzx
    obtain ⟨⟨c', hc'⟩, hcz⟩ := (IsLocalization.map_eq_zero_iff (q.comap j).primeCompl _ _).1 h0
    exact hz (j c') hc' (by rw [← map_mul, hcz, map_zero]))
  rw [← map_pow] at hn
  obtain ⟨⟨d, hd⟩, hdx⟩ := (IsLocalization.map_eq_zero_iff (q.comap j).primeCompl _ _).1 hn
  exact ⟨n, j d, hd, by rw [← map_pow, ← map_mul, hdx, map_zero]⟩

variable [CharZero k] [Ring.KrullDimLE 0 K] [Ring.KrullDimLE 0 L]

variable (k K L) in
/-- **Perrin, I Proposition 1.8, in characteristic zero.**  Let `k` be a field of characteristic
zero and `K`, `L` local `k`-algebras of Krull dimension zero.  Every zero divisor of every local
ring of `K ⊗[k] L` is nilpotent.

The statement involves finitely many elements at a time, so it reduces to the local
subalgebras `localAdjoin` generated by them, whose maximal ideals are nilpotent, and there it is
`TensorProduct.ZeroDimLocal.isNilpotent_of_not_mem_nonZeroDivisors_of_isNilpotent_maximalIdeal`. -/
theorem _root_.TensorProduct.isNilpotent_of_not_mem_nonZeroDivisors_localization
    (q : Ideal (K ⊗[k] L)) [q.IsPrime]
    (r : Localization.AtPrime q) (hr : r ∉ nonZeroDivisors (Localization.AtPrime q)) :
    IsNilpotent r := by
  classical
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl r
  rw [mem_nonZeroDivisors_iff_right] at hr
  obtain ⟨y, hyr, hy⟩ : ∃ y, y * IsLocalization.mk' (Localization.AtPrime q) x s = 0 ∧ y ≠ 0 := by
    by_contra h
    exact hr fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩
  obtain ⟨z, t, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl y
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hyr
  obtain ⟨⟨c, hc⟩, hczx⟩ := hyr
  have hz : ∀ c' ∉ q, c' * z ≠ 0 := fun c' hc' h0 =>
    hy ((IsLocalization.mk'_eq_zero_iff _ _).2 ⟨⟨c', hc'⟩, h0⟩)
  -- finitely many elements
  obtain ⟨FK₁, FL₁, h₁⟩ := exists_finset_mem_range (k := k) x
  obtain ⟨FK₂, FL₂, h₂⟩ := exists_finset_mem_range (k := k) z
  obtain ⟨FK₃, FL₃, h₃⟩ := exists_finset_mem_range (k := k) c
  set FK := FK₁ ∪ FK₂ ∪ FK₃
  set FL := FL₁ ∪ FL₂ ∪ FL₃
  set j := localAdjoinTensorHom k FK FL
  have hj := localAdjoinTensorHom_injective (k := k) FK FL
  have hrange : ∀ w : K ⊗[k] L, w ∈ (Algebra.TensorProduct.map (adjoinFinset k FK).val
      (adjoinFinset k FL).val).range → ∃ w₀, j w₀ = w := fun w hw => by
    obtain ⟨w₀, hw₀⟩ := range_map_le_range_localAdjoinTensorHom (k := k) FK FL hw
    exact ⟨w₀, hw₀⟩
  obtain ⟨x₀, rfl⟩ := hrange x (h₁ FK FL
    (Finset.subset_union_left.trans Finset.subset_union_left)
    (Finset.subset_union_left.trans Finset.subset_union_left))
  obtain ⟨z₀, rfl⟩ := hrange z (h₂ FK FL
    (Finset.subset_union_right.trans Finset.subset_union_left)
    (Finset.subset_union_right.trans Finset.subset_union_left))
  obtain ⟨c₀, rfl⟩ := hrange c (h₃ FK FL Finset.subset_union_right Finset.subset_union_right)
  obtain ⟨n, d, hd, hdx⟩ := exists_mul_pow_eq_zero_of_injective j.toRingHom hj q
    (isNilpotent_of_not_mem_nonZeroDivisors_of_isNilpotent_maximalIdeal
      (isNilpotent_maximalIdeal_localAdjoin k FK) (isNilpotent_maximalIdeal_localAdjoin k FL) _)
    x₀ z₀ c₀ hc hczx hz
  refine isNilpotent_mk'_of_pow_eq_zero _ _ _ (n := n) ?_
  rw [← map_pow]
  exact (IsLocalization.map_eq_zero_iff q.primeCompl _ _).2 ⟨⟨d, hd⟩, hdx⟩

end Main

end TensorProduct.ZeroDimLocal

end
