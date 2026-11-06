module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GroupActionsIntegral.ResidueFields
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.InfiniteInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer

/-!
# Decomposition and inertia at a separable closure

Let `A` be a discrete valuation ring, `K` its fraction field and `L` a separable closure of `K`.
At a maximal ideal of the integral closure of `A` in `L` the residue field is algebraically
closed.  The residue action of the decomposition group has inertia as its kernel, and the tame
inertia character takes values in the full inverse limit of the roots of unity of orders prime
to the residue characteristic.

## Main results

* `Stacks.FundamentalGroup.isAlgClosed_quotient_integralClosure`: algebraic closedness of the
  residue field.
* `Stacks.FundamentalGroup.primeToChar_divides_tameRamificationIndex`: every allowed order
  occurs at a finite Galois level.
* `Stacks.FundamentalGroup.exists_primeToChar_tameInertiaCharacter`: the canonical wild-tame
  sequence and its equivariant character.

## Implementation notes

The first exact sequence is registered from the general surjectivity and kernel theorems for the
residue action.  The target of the tame character is represented by compatible families of units
at every positive order prime to the residue characteristic; in characteristic zero every
positive order is included.  Its wild subgroup is the kernel, and the tame quotient identifies
with the subgroup of compatible families by the first isomorphism theorem.

## References

* [Stacks Project, Tag 0BUB](https://stacks.math.columbia.edu/tag/0BUB)
-/

@[expose] public noncomputable section

open scoped Pointwise
open Polynomial

universe u v w z

namespace Stacks.FundamentalGroup

add_to_stacks 0BUB "the kernel in the decomposition exact sequence"
  Ideal.Quotient.ker_stabilizerHom

add_to_stacks 0BUB "surjectivity in the decomposition exact sequence"
  Ideal.Quotient.stabilizerHom_surjective_of_profinite

/-- The residue field of the integral closure in a separable closure is
algebraically closed. -/
@[stacks 0BUB "the algebraically closed residue field"]
public theorem isAlgClosed_quotient_integralClosure
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI : Field (integralClosure A L ⧸ P) := Ideal.Quotient.field P
    IsAlgClosed (integralClosure A L ⧸ P) := by
  let B := integralClosure A L
  let : IsSepClosed L := IsSepClosure.sep_closed K
  have hAlgKL : Algebra.IsAlgebraic K L := IsSepClosure.separable.isAlgebraic
  let : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr hAlgKL
  let : IsFractionRing B L := integralClosure.isFractionRing_of_algebraic fun x hx => by
      apply (IsFractionRing.injective A K)
      apply (algebraMap K L).injective
      simpa only [map_zero, ← IsScalarTower.algebraMap_apply A K L] using hx
  let : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr Subtype.val_injective
  have hinjAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr fun x y h =>
      hinjAL (congrArg Subtype.val h)
  let : P.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  have hPne : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) P
  let : IsAlgClosed P.ResidueField :=
    IsLocalRing.isAlgClosed_residueField_of_normal B L
      (IsIntegrallyClosed.of_isIntegrallyClosedIn B L) P hPne
  let e : (B ⧸ P) ≃ₐ[B ⧸ P] P.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      (Ideal.bijective_algebraMap_quotient_residueField P)
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  exact IsAlgClosed.of_ringEquiv P.ResidueField (B ⧸ P) e.symm.toRingEquiv

/-- If an `n`-th power in a Dedekind extension `C` of a discrete valuation ring `A` is the image
of a uniformizer, then `n` divides the ramification index of every nonzero prime of `C` over the
maximal ideal of `A`. -/
public theorem dvd_ramificationIdx_of_pow_eq_algebraMap
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Type v} [CommRing C] [IsDedekindDomain C] [Algebra A C] [FaithfulSMul A C]
    {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) {a : C}
    (ha : a ^ n = algebraMap A C π) (q : Ideal C) [hq : q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal A)] :
    n ∣ q.ramificationIdx A := by
  have hpAne : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hqprime := Ideal.prime_of_isPrime (Ideal.ne_bot_of_liesOver_of_ne_bot hpAne q) hq
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hπ.ne_zero (FaithfulSMul.algebraMap_injective A C (by simpa [hn.ne'] using ha.symm))
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A C) = Ideal.span {a} ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, ← ha,
      ← Ideal.span_singleton_pow]
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ q
      (Ideal.map_ne_bot_of_ne_bot hpAne), hmap,
    FiniteMultiplicity.multiplicity_pow hqprime (FiniteMultiplicity.of_prime_left hqprime
      (by simpa [Ideal.span_singleton_eq_bot] using ha0))]
  exact dvd_mul_right _ _

/-- If `n` is prime to `p` and `w` is a power of `p` (or `w = 1` when `p = 0`), then `n ∣ w * t`
implies `n ∣ t`. -/
private lemma dvd_of_dvd_primePow_mul {n p r w t : ℕ} (hr : r = w * t) (hw₀ : p = 0 → w = 1)
    (hwp : 0 < p → ∃ a, w = p ^ a) (hn : p = 0 ∨ n.Coprime p) (h : n ∣ r) : n ∣ t := by
  subst hr
  rcases Nat.eq_zero_or_pos p with hp | hp
  · simpa [hw₀ hp] using h
  · obtain ⟨a, rfl⟩ := hwp hp
    exact ((hn.resolve_left hp.ne').pow_right a).dvd_mul_left.mp h

/-- Every positive order prime to the residue characteristic divides a tame
ramification index at a finite Galois subextension. -/
@[stacks 0BUB "cofinality of prime-to-characteristic orders"]
public theorem primeToChar_divides_tameRamificationIndex
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (n : ℕ) (hn : 0 < n)
    (hcoprime : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime n (ringChar (IsLocalRing.ResidueField A))) :
    ∃ (F : FiniteGaloisIntermediateField K L),
      let C := integralClosure A F
      letI : IsScalarTower A F L :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      let f : C →ₐ[A] integralClosure A L :=
        (IsScalarTower.toAlgHom A F L).mapIntegralClosure
      let q := P.comap f.toRingHom
      ∃ hq : q.IsMaximal,
        letI : q.IsMaximal := hq
        n ∣ IsDiscreteValuationRing.tameRamificationIndex A F q := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hunit : IsUnit (n : A) :=
    Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar n hn.ne'
      (hcoprime.imp_right Nat.Coprime.symm)
  have : NeZero (n : L) := ⟨by simpa using (hunit.map (algebraMap A L)).ne_zero⟩
  let : IsSepClosed L := IsSepClosure.sep_closed K
  obtain ⟨α, hαpow⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap A L π) n
  let F : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K ({α} : Set L)
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let αF : F := ⟨α, FiniteGaloisIntermediateField.subset_adjoin K ({α} : Set L)
    (Set.mem_singleton_iff.mpr rfl)⟩
  have hαFpow : (αF : F) ^ n = algebraMap A F π := by
    apply Subtype.ext
    show α ^ n = algebraMap F L (algebraMap A F π)
    rw [← IsScalarTower.algebraMap_apply A F L]
    exact hαpow
  have hαFint : IsIntegral A αF := by
    refine ⟨X ^ n - C π, monic_X_pow_sub_C π hn.ne', ?_⟩
    simp [hαFpow]
  refine ⟨F, ?_⟩
  dsimp only
  let C := integralClosure A F
  let f : C →ₐ[A] integralClosure A L :=
    (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let a : C := ⟨αF, hαFint⟩
  have hpowC : a ^ n = algebraMap A C π := by
    apply Subtype.ext
    simpa [a, ← IsScalarTower.algebraMap_apply A C F] using hαFpow
  let : Algebra C (integralClosure A L) := f.toRingHom.toAlgebra
  let : IsScalarTower A C (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let : Algebra.IsIntegral A (integralClosure A L) := inferInstance
  let : Algebra.IsIntegral C (integralClosure A L) :=
    ⟨fun x : integralClosure A L ↦
      (Algebra.IsIntegral.isIntegral (R := A) (A := integralClosure A L) x).tower_top⟩
  have hq : q.IsMaximal := by
    show (Ideal.comap (algebraMap C (integralClosure A L)) P).IsMaximal
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) P
  refine ⟨hq, ?_⟩
  let : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain A K F C
  let : P.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  let : P.LiesOver q := ⟨rfl⟩
  let : q.LiesOver (IsLocalRing.maximalIdeal A) := Ideal.LiesOver.tower_bot P q _
  let : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr fun x y h => by
    apply IsFractionRing.injective A K
    apply (algebraMap K F).injective
    simpa [← IsScalarTower.algebraMap_apply A K F] using congrArg Subtype.val h
  have hspec := IsDiscreteValuationRing.canonicalInertiaCharacter_spec.{u, v, w, w} A K F q
  exact dvd_of_dvd_primePow_mul hspec.1 hspec.2.1 hspec.2.2.1 hcoprime
    (dvd_ramificationIdx_of_pow_eq_algebraMap hπ hn hpowC q)

/-- Division telescopes along a divisibility chain `c ∣ a ∣ b`. -/
private lemma nat_div_mul_div {a b c : ℕ} (hab : a ∣ b) (hca : c ∣ a) :
    b / a * (a / c) = b / c := by
  rw [← Nat.mul_div_assoc (b / a) hca, Nat.div_mul_cancel hab]

/-- Reindexing a compatible family of characters along a cofinal choice of levels.  If `theta` is
computed from `thetaS` by raising the value at a level divisible by the index to the quotient of
the two, then `theta` again has the stated orders and compatibilities, its image is exactly the
compatible families, and its kernel is that of `thetaS`. -/
private lemma reindexed_character_spec
    {G : Type*} [Group G] {U : Type*} [CommGroup U] {V : Type*} [CommMonoid V]
    {Sx Nx : Type*}
    (dS : Sx → ℕ) (dN : Nx → ℕ)
    (hSpos : ∀ t : Sx, 0 < dS t)
    (hSdir : ∀ t s : Sx, ∃ k : Sx, dS t ∣ dS k ∧ dS s ∣ dS k)
    (θS : G →* (Sx → U))
    (hSorder : ∀ (σ : G) (t : Sx), θS σ t ^ dS t = 1)
    (hSsurj : ∀ g : Sx → U, (∀ t : Sx, g t ^ dS t = 1) →
      (∀ t s : Sx, dS t ∣ dS s → g s ^ (dS s / dS t) = g t) → ∃ σ : G, θS σ = g)
    (θ : G →* (Nx → U))
    (asN : Sx → Nx) (hasN : ∀ t : Sx, dN (asN t) = dS t)
    (lev : Nx → Sx) (hlev : ∀ n : Nx, dN n ∣ dS (lev n))
    (hcoord : ∀ (σ : G) (n : Nx) (t : Sx), dN n ∣ dS t →
      θ σ n = θS σ t ^ (dS t / dN n)) :
    (∀ (σ : G) (n : Nx), θ σ n ^ dN n = 1) ∧
    (∀ (σ : G) (n m : Nx), dN n ∣ dN m → θ σ m ^ (dN m / dN n) = θ σ n) ∧
    (∀ g : Nx → U, g ∈ θ.range ↔
      ((∀ n : Nx, g n ^ dN n = 1) ∧
        ∀ n m : Nx, dN n ∣ dN m → g m ^ (dN m / dN n) = g n)) ∧
    θ.ker = θS.ker ∧
    (∀ (v : U →* V) (e : V ≃* V) (σ ρ : G),
      (∀ t : Sx, v (θS ρ t) = e (v (θS σ t))) →
      ∀ n : Nx, v (θ ρ n) = e (v (θ σ n))) := by
  have hlevcoord (σ : G) (n : Nx) : θ σ n = θS σ (lev n) ^ (dS (lev n) / dN n) :=
    hcoord σ n (lev n) (hlev n)
  have horder (σ : G) (n : Nx) : θ σ n ^ dN n = 1 := by
    rw [hlevcoord σ n, ← pow_mul, Nat.div_mul_cancel (hlev n)]
    exact hSorder σ (lev n)
  have hcompat (σ : G) (n m : Nx) (hnm : dN n ∣ dN m) :
      θ σ m ^ (dN m / dN n) = θ σ n := by
    obtain ⟨k, hnk, hmk⟩ := hSdir (lev n) (lev m)
    have hkn : dN n ∣ dS k := (hlev n).trans hnk
    have hkm : dN m ∣ dS k := (hlev m).trans hmk
    rw [hcoord σ m k hkm, ← pow_mul, nat_div_mul_div hkm hnm, (hcoord σ n k hkn).symm]
  have hequiv (v : U →* V) (e : V ≃* V) (σ ρ : G)
      (h : ∀ t : Sx, v (θS ρ t) = e (v (θS σ t))) (n : Nx) :
      v (θ ρ n) = e (v (θ σ n)) := by
    rw [hlevcoord ρ n, hlevcoord σ n]
    simp only [map_pow, h (lev n)]
  refine ⟨horder, hcompat, ?_, ?_, hequiv⟩
  · intro g
    show (∃ σ : G, θ σ = g) ↔ _
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨horder σ, hcompat σ⟩
    · rintro ⟨hroot, hcompatN⟩
      obtain ⟨σ, hσ⟩ := hSsurj (fun t => g (asN t))
        (fun t => by have h := hroot (asN t); rwa [hasN t] at h)
        (fun t s hts => by
          have h := hcompatN (asN t) (asN s) (by rwa [hasN t, hasN s])
          rwa [hasN t, hasN s] at h)
      refine ⟨σ, ?_⟩
      funext n
      calc
        θ σ n = θS σ (lev n) ^ (dS (lev n) / dN n) := hlevcoord σ n
        _ = g (asN (lev n)) ^ (dS (lev n) / dN n) := by rw [congrFun hσ (lev n)]
        _ = g n := by
            have h := hcompatN n (asN (lev n)) (by rw [hasN (lev n)]; exact hlev n)
            rwa [hasN (lev n)] at h
  · ext σ
    show (θ σ = 1) ↔ (θS σ = 1)
    constructor
    · intro h
      funext t
      have ht := congrFun h (asN t)
      rw [hcoord σ (asN t) t (by rw [hasN t]), hasN t, Nat.div_self (hSpos t)] at ht
      simpa using ht
    · intro h
      funext n
      rw [hlevcoord σ n]
      simp [congrFun h (lev n)]

/-- The pro-`p` property of a subgroup of a topological group transports along an equality of
subgroups. -/
private lemma isPGroup_of_subgroup_eq {G : Type*} [Group G] [TopologicalSpace G]
    {W W' : Subgroup G} (hWW : W = W') (p : ℕ)
    (hpro : ∀ (H : Type z) [Group H] [Finite H] (f : W' →* H),
      IsOpen (f.ker : Set W') → Function.Surjective f → IsPGroup p H)
    (H : Type z) [Group H] [Finite H] (f : W →* H)
    (hopen : IsOpen (f.ker : Set W)) (hsurj : Function.Surjective f) :
    IsPGroup p H := by
  subst hWW
  exact hpro H f hopen hsurj

/-- The character obtained from `θS` by evaluating at the level `lev n` and raising to the
index `dS (lev n) / dN n`. -/
private def reindexCharacter {G U Sx Nx : Type*} [Monoid G] [CommMonoid U]
    (dS : Sx → ℕ) (dN : Nx → ℕ) (θS : G →* (Sx → U)) (lev : Nx → Sx) : G →* (Nx → U) where
  toFun σ n := θS σ (lev n) ^ (dS (lev n) / dN n)
  map_one' := by funext n; simp
  map_mul' σ τ := by funext n; simp [mul_pow]

/-- In a compatible family over a directed set of levels, raising to the index from any level
divisible by `d` gives the same value. -/
private lemma pow_div_eq_of_compatible {U Sx : Type*} [Monoid U] (dS : Sx → ℕ) (χ : Sx → U)
    (hdir : ∀ t s : Sx, ∃ k : Sx, dS t ∣ dS k ∧ dS s ∣ dS k)
    (hcompat : ∀ t s : Sx, dS t ∣ dS s → χ s ^ (dS s / dS t) = χ t)
    {d : ℕ} {t s : Sx} (ht : d ∣ dS t) (hs : d ∣ dS s) :
    χ t ^ (dS t / d) = χ s ^ (dS s / d) := by
  obtain ⟨k, htk, hsk⟩ := hdir t s
  rw [← hcompat t k htk, ← hcompat s k hsk, ← pow_mul, ← pow_mul, nat_div_mul_div htk ht,
    nat_div_mul_div hsk hs]

/-- The canonical tame inertia character at a separable closure has wild kernel
and reaches every compatible family of prime-to-characteristic roots of unity.
Its finite-level formula specifies the character independently of choices. -/
@[stacks 0BUB "the wild–tame exact sequence and canonical character",
  sga "1 XIII 2.0" "inertia structure",
  sga "7 I 0.3" "I/P ≅ Ẑ(1), P pro-p",
  sga "7 XV 2.2.5" "partial"]
public theorem exists_primeToChar_tameInertiaCharacter
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let I := P.inertia Gal(L/K)
    let D := MulAction.stabilizer Gal(L/K) P
    let p := ringChar (IsLocalRing.ResidueField A)
    let N := {n : ℕ // 0 < n ∧ (p = 0 ∨ Nat.Coprime n p)}
    ∃ θ : I →* (∀ _ : N, (B ⧸ P)ˣ),
      (∀ σ : I, ∀ n : N, (θ σ n) ^ n.1 = 1) ∧
      (∀ σ : I, ∀ n m : N, n.1 ∣ m.1 →
        (θ σ m) ^ (m.1 / n.1) = θ σ n) ∧
      (∀ f : ∀ _ : N, (B ⧸ P)ˣ,
        (f ∈ θ.range ↔
          ((∀ n : N, (f n) ^ n.1 = 1) ∧
           (∀ n m : N, n.1 ∣ m.1 → (f m) ^ (m.1 / n.1) = f n)))) ∧
      (∀ τ : D, ∀ σ : I,
        ∃ ρ : I,
          (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
            (τ : Gal(L/K))⁻¹ ∧
          (∀ n : N, θ ρ n =
            (Ideal.quotientEquiv P P
              ((MulSemiringAction.toRingEquiv Gal(L/K) B) (τ : Gal(L/K)))
              τ.property.symm).toMulEquiv (θ σ n))) ∧
      (∀ τ : D, ∀ σ : I, σ ∈ θ.ker →
        ∃ ρ : I,
          (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
            (τ : Gal(L/K))⁻¹ ∧ ρ ∈ θ.ker) ∧
      (∀ (F : FiniteGaloisIntermediateField K L),
        let C := integralClosure A F
        letI : IsScalarTower A F L :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI : MulSemiringAction Gal(F/K) C :=
          IsIntegralClosure.MulSemiringAction A K F C
        let f : C →ₐ[A] B :=
          (IsScalarTower.toAlgHom A F L).mapIntegralClosure
        let q := P.comap f.toRingHom
        ∀ [q.IsMaximal], ∀ n : N,
          n.1 ∣ IsDiscreteValuationRing.tameRamificationIndex A F q →
          ∀ σ : I,
            ∃ σF : q.inertia Gal(F/K),
              (σF : Gal(F/K)) =
                AlgEquiv.restrictNormal (σ : Gal(L/K))
                  (F : IntermediateField K L) ∧
              ((θ σ n : (B ⧸ P)ˣ) : B ⧸ P) =
                (Ideal.quotientMap P f.toRingHom le_rfl)
                  (((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1) ^
                    (IsDiscreteValuationRing.tameRamificationIndex A F q / n.1))) ∧
      (p = 0 → θ.ker = ⊥) ∧
      (0 < p →
        ∀ (H : Type*) [Group H] [Finite H] (f : θ.ker →* H),
          IsOpen (f.ker : Set θ.ker) → Function.Surjective f → IsPGroup p H) := by
  classical
  let : IsGalois K L := inferInstance
  obtain ⟨S, hSone, hSpos, hScoprime, hSroots, hSdir, hSlevels, θS,
      hSorder, hScompat, hSsurj, hSconj, hSkerconj, hSfinite, _, hSzero, hSpro⟩ :=
    exists_tameInertiaCharacter.{u, v, w, u_1} A K L P
  intro B I D p N
  let := IsIntegralClosure.MulSemiringAction A K L B
  have hcofinal (n : N) : ∃ m : S, n.1 ∣ m.1 := by
    obtain ⟨F, hq, hdiv⟩ := primeToChar_divides_tameRamificationIndex A K L P n.1 n.2.1 n.2.2
    let C := integralClosure A F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f : C →ₐ[A] integralClosure A L := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let q := P.comap f.toRingHom
    let : q.IsMaximal := hq
    exact ⟨⟨_, (hSfinite F).choose⟩, hdiv⟩
  let lev (n : N) : S := Classical.choose (hcofinal n)
  have hlev (n : N) : n.1 ∣ (lev n).1 := Classical.choose_spec (hcofinal n)
  have hSdir' (t s : S) : ∃ k : S, t.1 ∣ k.1 ∧ s.1 ∣ k.1 := by
    obtain ⟨k, hk, htk, hsk⟩ := hSdir t.1 t.2 s.1 s.2
    exact ⟨⟨k, hk⟩, htk, hsk⟩
  let θ : I →* (∀ _ : N, (B ⧸ P)ˣ) := reindexCharacter (fun t : S => t.1) (fun n : N => n.1) θS lev
  have hcoord (σ : I) (n : N) (t : S) (hnt : n.1 ∣ t.1) : θ σ n = θS σ t ^ (t.1 / n.1) :=
    pow_div_eq_of_compatible (fun t : S => t.1) (θS σ) hSdir' (hScompat σ) (hlev n) hnt
  let asN (t : S) : N :=
    ⟨t.1, hSpos t.1 t.2, or_iff_not_imp_left.mpr fun hp => hScoprime hp t.1 t.2⟩
  obtain ⟨horder, hcompat, hrange, hkerEq, hequiv⟩ :=
    reindexed_character_spec (G := I) (U := (B ⧸ P)ˣ) (V := B ⧸ P)
      (fun t : S => t.1) (fun n : N => n.1) (fun t => hSpos t.1 t.2) hSdir'
      θS hSorder hSsurj θ asN (fun _ => rfl) lev hlev hcoord
  refine ⟨θ, horder, hcompat, hrange, fun τ σ => ?_, fun τ σ hσ => ?_, fun F => ?_,
    fun hp => hkerEq.trans (hSzero hp), fun hp => isPGroup_of_subgroup_eq hkerEq p (hSpro hp)⟩
  · obtain ⟨ρ, hρ, hρact⟩ := hSconj τ σ
    let eτ := (Ideal.quotientEquiv P P
      ((MulSemiringAction.toRingEquiv Gal(L/K) B) (τ : Gal(L/K))) τ.property.symm).toMulEquiv
    exact ⟨ρ, hρ, hequiv (Units.coeHom (B ⧸ P)) eτ σ ρ hρact⟩
  · obtain ⟨ρ, hρ, hρker⟩ := hSkerconj τ σ (by simpa [hkerEq] using hσ)
    exact ⟨ρ, hρ, by simpa [hkerEq] using hρker⟩
  · dsimp only
    let C := integralClosure A F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f : C →ₐ[A] B := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let q := P.comap f.toRingHom
    intro hq n hdiv σ
    let : q.IsMaximal := hq
    have hL := hSfinite F
    let σF := (hL.choose_spec σ).choose
    let t : S := ⟨IsDiscreteValuationRing.tameRamificationIndex A F q, hL.choose⟩
    refine ⟨σF, (hL.choose_spec σ).choose_spec.1, ?_⟩
    calc
      ↑(θ σ n) = ↑(θS σ t ^ (t.1 / n.1)) := congrArg Units.val (hcoord σ n t hdiv)
      _ = ((Ideal.quotientMap P f.toRingHom le_rfl)
          (((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1)) ^
            (t.1 / n.1)) := by
        rw [Units.val_pow_eq_pow_val]
        exact congrArg (fun z : B ⧸ P => z ^ (t.1 / n.1)) (hL.choose_spec σ).choose_spec.2
      _ = _ := (map_pow _ _ _).symm

end Stacks.FundamentalGroup
