module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksFrontier.RingTheory.Flat.ClosedSubset
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Flat.QuotientInf
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus

/-!
# Flattening over a Noetherian complete local ring

Let `R → S` be a map of Noetherian rings with `R` local and complete, and let `M` be a finite
`S`-module. There is a smallest ideal `I ⊆ R` such that, after quotienting by `I`, the module
becomes flat over `R/I` at every prime of `S/IS` lying over the closed point. This *flattening
ideal* detects flatness of base changes: a local map from `R` to a local ring `R'` makes the base
change of `M` flat along the closed point of `R'` exactly when it annihilates `I`.

## Main results

* `Module.FlatAfterQuotientAlong`: flatness along a closed locus after quotienting the base
  ring, the algebra and the module by an ideal of the base.
* `Module.exists_least_flattening_ideal`: existence of the least flattening ideal.
* `Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot`: the criterion for a Noetherian local
  target.
* `Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot_of_finiteType`: the criterion for an
  arbitrary local target, for a finite-type algebra.

## References

* [The Stacks Project, Tag 0526](https://stacks.math.columbia.edu/tag/0526)
* [The Stacks Project, Tag 0527](https://stacks.math.columbia.edu/tag/0527)
* [The Stacks Project, Tag 0528](https://stacks.math.columbia.edu/tag/0528)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Flatness along the inverse image of `V(m)` after quotienting `R`, `S` and `M` by the ideal
`I` of `R`. Here `(S / IS) ⊗[S] M` is the canonical model of `M / IM`. -/
@[stacks 0526 "the property (15.20.1) quantified over in the statement"]
abbrev Module.FlatAfterQuotientAlong
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] (m I : Ideal R) : Prop :=
  Module.FlatAlongZeroLocus
    (R ⧸ I) (S ⧸ I.map (algebraMap R S))
    (m.map (Ideal.Quotient.mk I))
    ((S ⧸ I.map (algebraMap R S)) ⊗[S] M)

/-! ### Elementary transport lemmas -/

/-- Flatness along a closed subset only depends on the module up to a linear equivalence over
the source ring. -/
private theorem flatAlongZeroLocus_of_linearEquiv
    (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A)
    (P Q : Type*) [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup Q] [Module A Q] [Module B Q] [IsScalarTower A B Q]
    (e : P ≃ₗ[B] Q)
    (h : Module.FlatAlongZeroLocus A B J P) :
    Module.FlatAlongZeroLocus A B J Q := by
  intro q hq hJ
  let eLoc := IsLocalizedModule.mapEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl P)
    (LocalizedModule.mkLinearMap q.primeCompl Q)
    (Localization q.primeCompl) e
  exact (Module.Flat.equiv_iff (eLoc.restrictScalars A)).mp (h q hJ)

/-- Flatness along a closed subset is invariant under a linear equivalence over the source
ring. -/
private theorem flatAlongZeroLocus_iff_of_linearEquiv
    (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A)
    (P Q : Type*) [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup Q] [Module A Q] [Module B Q] [IsScalarTower A B Q]
    (e : P ≃ₗ[B] Q) :
    Module.FlatAlongZeroLocus A B J P ↔ Module.FlatAlongZeroLocus A B J Q :=
  ⟨flatAlongZeroLocus_of_linearEquiv A B J P Q e,
    flatAlongZeroLocus_of_linearEquiv A B J Q P e.symm⟩

/-- Flatness along the inverse image of the zero locus of a nilpotent ideal is flatness. -/
private theorem flat_of_flatAlongZeroLocus_of_isNilpotent
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (hI : IsNilpotent I)
    (hflat : Module.FlatAlongZeroLocus R S I M) : Module.Flat R M := by
  obtain ⟨n, hn⟩ := hI
  refine Module.flat_of_isLocalized_maximal S M
    (fun q _ => LocalizedModule.AtPrime q M)
    (fun q _ => LocalizedModule.mkLinearMap q.primeCompl M) ?_
  intro q hq
  apply hflat q
  apply Ideal.IsPrime.le_of_pow_le (n := n) (hP := hq.isPrime)
  rw [← Ideal.map_pow, hn]
  simp

/-- The canonical model `(S / IS) ⊗[S] M` of `M / IM` agrees with `(R / I) ⊗[R] M`. -/
private noncomputable def quotientCancelBaseChange
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) :
    ((S ⧸ I.map (algebraMap R S)) ⊗[S] M) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) := by
  letI := Algebra.isPushout_quotient R S I
  exact Algebra.IsPushout.cancelBaseChange R (R ⧸ I) S
    (S ⧸ I.map (algebraMap R S)) M

/-- Base changing the model `(S / IS) ⊗[S] M` of `M / IM` along `R / I → C` gives `C ⊗[R] M`. -/
private noncomputable def tensorQuotientCancelBaseChange
    (R S M C : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) [CommRing C] [Algebra R C] [Algebra (R ⧸ I) C] [IsScalarTower R (R ⧸ I) C] :
    (C ⊗[R ⧸ I] ((S ⧸ I.map (algebraMap R S)) ⊗[S] M)) ≃ₗ[C] (C ⊗[R] M) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
    (quotientCancelBaseChange R S M I) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) C C M

/-- The two models `M / IM` and `(R/I) ⊗[R] M` of the reduction of `M` modulo `I` have the same
flatness over `R / I`. -/
private theorem flat_quotient_iff_flat_tensor {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) :
    Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) ↔
      Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
  (Module.Flat.equiv_iff (isBaseChange_mkQ_smul_top (M := M) I).equiv).symm

/-- Flatness of the reduction modulo `I` passes to any algebra killing `I`. -/
private theorem flat_tensor_of_flat_quotient {R A M : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I ≤ RingHom.ker (algebraMap R A))
    (hflat : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    Module.Flat A (A ⊗[R] M) := by
  let f : (R ⧸ I) →ₐ[R] A := Ideal.Quotient.liftₐ I (Algebra.ofId R A) hI
  let : Algebra (R ⧸ I) A := f.toAlgebra
  let : IsScalarTower R (R ⧸ I) A := IsScalarTower.of_algHom f
  let := hflat
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) A A M).symm

/-! ### The least flattening ideal over a complete Noetherian local ring -/

/-- In a ring which is precomplete for the `m`-adic topology, a decreasing family of ideals
`K n` squeezed between `m ^ n` and `K (n+1) ⊔ m ^ n` satisfies `(⨅ k, K k) ⊔ m ^ n = K n`. -/
private theorem iInf_sup_pow_eq {R : Type*} [CommRing R] (m : Ideal R)
    [IsPrecomplete m R] (K : ℕ → Ideal R) (hanti : Antitone K)
    (hpow : ∀ n, m ^ n ≤ K n) (hstep : ∀ n, K n ≤ K (n + 1) ⊔ m ^ n) (n : ℕ) :
    (⨅ k, K k) ⊔ m ^ n = K n := by
  classical
  apply le_antisymm (sup_le (iInf_le K n) (hpow n))
  intro z hz
  have step (k : ℕ) (y : K (k + n)) :
      ∃ t : K (k + 1 + n), (y : R) - t ∈ m ^ (k + n) := by
    obtain ⟨t, ht, e, he, hy⟩ := Submodule.mem_sup.mp (hstep (k + n) y.property)
    refine ⟨⟨t, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht⟩, ?_⟩
    simpa [← hy] using he
  let f : (k : ℕ) → K (k + n) := fun k => Nat.rec (motive := fun k => K (k + n))
    ⟨z, by simpa using hz⟩ (fun k y => (step k y).choose) k
  have hf (k : ℕ) : (f k).val - (f (k + 1)).val ∈ m ^ (k + n) := by
    simpa only [f] using (step k (f k)).choose_spec
  have hc {a b : ℕ} (hab : a ≤ b) :
      (f a).val - (f b).val ∈ m ^ (a + n) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h := (m ^ (a + n)).add_mem ih
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hab n) (hf b))
      simpa only [sub_add_sub_cancel] using h
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := m) (fun k => (f k).val) (by
    intro a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_add_right a n) (hc hab))
  have hLm (k : ℕ) : (f k).val - L ∈ m ^ k := by
    simpa only [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] using hL k
  have hLK : L ∈ ⨅ k, K k := by
    rw [Submodule.mem_iInf]
    intro k
    have hfk : (f k).val ∈ K k := hanti (Nat.le_add_right k n) (f k).property
    simpa only [sub_sub_cancel] using (K k).sub_mem hfk (hpow k (hLm k))
  have hzL : z - L ∈ m ^ n := by
    have hh := (m ^ n).add_mem (by simpa using hc (Nat.zero_le n)) (hLm n)
    simpa only [sub_add_sub_cancel, f, Nat.rec_zero] using hh
  exact Submodule.mem_sup.mpr ⟨L, hLK, z - L, hzL, add_sub_cancel _ _⟩

/-- A property of ideals which holds for `⊤` and is stable under intersection has a least
element among the ideals containing a fixed ideal with Artinian quotient. -/
private theorem exists_least_above_of_isArtinian_quotient {R : Type*} [CommRing R]
    (A : Ideal R) [IsArtinianRing (R ⧸ A)] (P : Ideal R → Prop)
    (htop : P ⊤) (hinf : ∀ I J, P I → P J → P (I ⊓ J)) :
    ∃ I, A ≤ I ∧ P I ∧ ∀ J, A ≤ J → P J → I ≤ J := by
  classical
  let π := Ideal.Quotient.mk A
  have hc (J : Ideal R) (hJ : A ≤ J) : (J.map π).comap π = J := by
    rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective]
    change J ⊔ RingHom.ker π = J
    rw [show RingHom.ker π = A from Ideal.mk_ker]
    exact sup_eq_left.mpr hJ
  obtain ⟨L, hL, hmin⟩ := IsArtinian.set_has_minimal
    {L : Ideal (R ⧸ A) | P (Ideal.comap π L)} ⟨⊤, by simpa using htop⟩
  refine ⟨Ideal.comap π L, ?_, hL, ?_⟩
  · intro z hz
    change π z ∈ L
    simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
  · intro J hAJ hJ
    have hcap : P (Ideal.comap π (L ⊓ J.map π)) := by
      rw [Ideal.comap_inf, hc J hAJ]
      exact hinf _ _ hL hJ
    have heq : L ⊓ J.map π = L :=
      eq_of_le_of_not_lt inf_le_left (hmin _ hcap)
    have hle : L ≤ J.map π := by rw [← heq]; exact inf_le_right
    simpa only [hc J hAJ] using Ideal.comap_mono (f := π) hle

/-- The quotient of a Noetherian local ring by a power of its maximal ideal is Artinian. -/
private theorem quotient_maximalIdeal_pow_isArtinian {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ IsLocalRing.maximalIdeal R ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    infer_instance
  refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ⟨⟨?_, ?_⟩, ?_⟩
  · infer_instance
  · exact Ideal.pow_le_self hn
  · intro q hq _
    rw [← (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical,
      ← Ideal.radical_pow _ hn]
    exact hq.1.radical_le_iff.mpr hq.2

/-- Over a complete Noetherian local ring, a monotone property of ideals which holds for `⊤` and
for the maximal ideal and is stable under intersection has a least ideal whose sups with the
positive powers of the maximal ideal all satisfy it. -/
private theorem exists_least_adic_ideal {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    (P : Ideal R → Prop) (htop : P ⊤) (hm : P (IsLocalRing.maximalIdeal R))
    (hmono : ∀ I J, I ≤ J → P I → P J)
    (hinf : ∀ I J, P I → P J → P (I ⊓ J)) :
    ∃ I, I ≤ IsLocalRing.maximalIdeal R ∧
      (∀ n : ℕ, P (I ⊔ IsLocalRing.maximalIdeal R ^ (n + 1))) ∧
      ∀ J, (∀ n : ℕ, P (J ⊔ IsLocalRing.maximalIdeal R ^ (n + 1))) → I ≤ J := by
  classical
  let m := IsLocalRing.maximalIdeal R
  have hex (n : ℕ) : ∃ I, m ^ n ≤ I ∧ P I ∧ ∀ J, m ^ n ≤ J → P J → I ≤ J := by
    have := quotient_maximalIdeal_pow_isArtinian (R := R) n
    exact exists_least_above_of_isArtinian_quotient (m ^ n) P htop hinf
  choose K hpow hP hmin using hex
  have hanti : Antitone K := by
    intro a b hab
    exact hmin b (K a) ((Ideal.pow_le_pow_right hab).trans (hpow a)) (hP a)
  have hstep (n : ℕ) : K n ≤ K (n + 1) ⊔ m ^ n :=
    hmin n _ le_sup_right (hmono _ _ le_sup_left (hP (n + 1)))
  have heq (n : ℕ) : (⨅ k, K k) ⊔ m ^ n = K n :=
    iInf_sup_pow_eq m K hanti hpow hstep n
  refine ⟨⨅ k, K k, ?_, ?_, ?_⟩
  · exact (iInf_le K 1).trans (hmin 1 m (by simp) hm)
  · intro n
    rw [heq]
    exact hP (n + 1)
  · intro J hJ z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsHausdorff.haus' (I := m)
    intro n
    rw [SModEq.zero]
    change z ∈ Submodule.comap J.mkQ (m ^ n • (⊤ : Submodule R (R ⧸ J)))
    rw [Submodule.comap_smul_top_of_surjective _ _ J.mkQ_surjective,
      Submodule.ker_mkQ, Ideal.smul_eq_mul, Ideal.mul_top, sup_comm]
    cases n with
    | zero => simp
    | succ n =>
      exact hmin (n + 1) _ le_sup_right (hJ n) ((iInf_le K (n + 1)) hz)

/-- The quotient property (15.20.1) follows from flatness of the reductions modulo the ideals
`I ⊔ m ^ (n+1)`. -/
private theorem flatAfterQuotientAlong_of_flat_tensor_sup_pow
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] (m I : Ideal R)
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ (I ⊔ m ^ (n + 1)))
      ((R ⧸ (I ⊔ m ^ (n + 1))) ⊗[R] M)) :
    Module.FlatAfterQuotientAlong R S M m I := by
  let A := R ⧸ I
  let B := S ⧸ I.map (algebraMap R S)
  let N := B ⊗[S] M
  let mA := m.map (Ideal.Quotient.mk I)
  have hn (n : ℕ) : Module.Flat (A ⧸ mA ^ (n + 1))
      (N ⧸ (mA ^ (n + 1) • (⊤ : Submodule A N))) := by
    let L := mA ^ (n + 1)
    let C := A ⧸ L
    have hker : I ⊔ m ^ (n + 1) ≤ RingHom.ker (algebraMap R C) := by
      refine sup_le ?_ ?_
      · intro z hz
        change Ideal.Quotient.mk L (Ideal.Quotient.mk I z) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
      · intro z hz
        change Ideal.Quotient.mk L (Ideal.Quotient.mk I z) = 0
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        dsimp [L, mA]
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hz
    have hc : Module.Flat C (C ⊗[R] M) :=
      flat_tensor_of_flat_quotient _ hker (hflat n)
    exact (flat_quotient_iff_flat_tensor L).mpr
      ((Module.Flat.equiv_iff (tensorQuotientCancelBaseChange R S M C I)).mpr hc)
  intro q hq hmq
  exact Module.Flat.of_flat_quotient_pow mA N hn q hmq
    (LocalizedModule.AtPrime q N) (LocalizedModule.mkLinearMap q.primeCompl N)

/-- The quotient property (15.20.1) implies flatness of the reductions modulo `I ⊔ m ^ n`. -/
private theorem flat_tensor_sup_pow_of_flatAfterQuotientAlong
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (m I : Ideal R) (hflat : Module.FlatAfterQuotientAlong R S M m I) (n : ℕ) :
    Module.Flat (R ⧸ (I ⊔ m ^ n)) ((R ⧸ (I ⊔ m ^ n)) ⊗[R] M) := by
  let A := R ⧸ I
  let B := S ⧸ I.map (algebraMap R S)
  let N := B ⊗[S] M
  let C := R ⧸ (I ⊔ m ^ n)
  let f : A →ₐ[R] C := Ideal.Quotient.factorₐ R le_sup_left
  let : Algebra A C := f.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algHom f
  let D := C ⊗[A] B
  let mA := m.map (Ideal.Quotient.mk I)
  let mC := m.map (Ideal.Quotient.mk (I ⊔ m ^ n))
  have hmap : mA.map (algebraMap A C) = mC := by
    rw [Ideal.map_map]
    rfl
  have hnil : IsNilpotent mC := by
    refine ⟨n, ?_⟩
    change (m.map (Ideal.Quotient.mk (I ⊔ m ^ n))) ^ n = ⊥
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have hD : Module.FlatAlongZeroLocus C D mC (D ⊗[B] N) :=
    Module.FlatAlongZeroLocus.baseChange A B C D mA mC N hmap.le hflat
  have hDflat : Module.Flat C (D ⊗[B] N) :=
    flat_of_flatAlongZeroLocus_of_isNilpotent mC hnil hD
  let e : (D ⊗[B] N) ≃ₗ[C] (C ⊗[R] M) :=
    Algebra.IsPushout.cancelBaseChange A C B D N ≪≫ₗ
      tensorQuotientCancelBaseChange R S M C I
  exact (Module.Flat.equiv_iff e).mp hDflat

-- The iterated quotient base changes in this proof exceed the default elaboration budget.
/-- Over a complete Noetherian local ring, there is a least ideal contained in the maximal ideal
such that the quotient module is flat at every prime lying over the maximal ideal. -/
@[stacks 0526]
theorem Module.exists_least_flattening_ideal
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (M : Type w) [AddCommGroup M] [Module S M] [Module.Finite S M]
    [IsNoetherianRing S] :
    ∃ I : Ideal R,
      I ≤ IsLocalRing.maximalIdeal R ∧
        Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) I ∧
          ∀ J : Ideal R,
            Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) J → I ≤ J := by
  let : Module R M := Module.compHom M (algebraMap R S)
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let P : Ideal R → Prop := fun I => Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)
  have htop : P ⊤ := by
    dsimp [P]
    infer_instance
  have hm : P (IsLocalRing.maximalIdeal R) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    dsimp [P]
    infer_instance
  have hmono (I J : Ideal R) (hIJ : I ≤ J) (hI : P I) : P J :=
    flat_tensor_of_flat_quotient I (by simpa using hIJ) hI
  have hinf (I J : Ideal R) (hI : P I) (hJ : P J) : P (I ⊓ J) :=
    (flat_quotient_iff_flat_tensor (I ⊓ J)).mp
      (Module.Flat.quotient_inf I J
        ((flat_quotient_iff_flat_tensor I).mpr hI)
        ((flat_quotient_iff_flat_tensor J).mpr hJ))
  obtain ⟨I, hIm, hI, hmin⟩ := exists_least_adic_ideal P htop hm hmono hinf
  refine ⟨I, hIm, flatAfterQuotientAlong_of_flat_tensor_sup_pow _ _ hI, ?_⟩
  intro J hJ
  exact hmin J fun n => flat_tensor_sup_pow_of_flatAfterQuotientAlong _ _ hJ (n + 1)

/-! ### Detecting flatness of a base change by the flattening ideal -/

/-- Over an Artinian local ring, flatness along the closed point is flatness. -/
private lemma flat_of_flatAlongZeroLocus_of_isArtinian
    (A : Type*) (T : Type*) [CommRing A] [CommRing T] [Algebra A T]
    [IsLocalRing A] [IsArtinianRing A]
    (N : Type*) [AddCommGroup N] [Module A N] [Module T N] [IsScalarTower A T N]
    (h : Module.FlatAlongZeroLocus A T (IsLocalRing.maximalIdeal A) N) :
    Module.Flat A N :=
  flat_of_flatAlongZeroLocus_of_isNilpotent _
    ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance) h

/-- The quotient of a Noetherian local ring by the kernel of a local map to an Artinian local
ring is Artinian. -/
private lemma isArtinianRing_quotient_ker
    (R : Type*) (A : Type*) [CommRing R] [CommRing A]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing A] [IsArtinianRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)] :
    IsArtinianRing (R ⧸ RingHom.ker (algebraMap R A)) := by
  let : Nontrivial (R ⧸ RingHom.ker (algebraMap R A)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  let : IsLocalRing (R ⧸ RingHom.ker (algebraMap R A)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  refine ⟨n, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    change IsLocalRing.maximalIdeal R ^ n ≤
      RingHom.ker (Ideal.Quotient.mk (RingHom.ker (algebraMap R A)))
    rw [Ideal.mk_ker]
    intro z hz
    have hz' : algebraMap R A z ∈
        (IsLocalRing.maximalIdeal R).map (algebraMap R A) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap R A) hz
    have hz'' := (Ideal.pow_right_mono
      (IsLocalRing.map_maximalIdeal_le (algebraMap R A)) n) hz'
    rw [hn] at hz''
    exact hz''
  · exact bot_le

/-- If the base change of `M` to an Artinian local `R`-algebra `A` is flat along the closed
point, then the kernel of `R → A` satisfies the flattening property (15.20.1). -/
private lemma flatAfterQuotientAlong_ker_of_isArtinian
    (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (A : Type*) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (T : Type*) [CommRing T] [Algebra A T]
    (N : Type*) [AddCommGroup N] [Module A N] [Module T N] [IsScalarTower A T N]
    (hN : Module.FlatAlongZeroLocus A T (IsLocalRing.maximalIdeal A) N)
    (eN : N ≃ₗ[A] (A ⊗[R] M)) :
    Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R)
      (RingHom.ker (algebraMap R A)) := by
  let K := RingHom.ker (algebraMap R A)
  let Rbar := R ⧸ K
  let Sbar := S ⧸ K.map (algebraMap R S)
  let Nbar := Sbar ⊗[S] M
  let : Nontrivial Rbar := Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  let : IsLocalRing Rbar := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsArtinianRing Rbar := isArtinianRing_quotient_ker R A
  let : Algebra Rbar A := (RingHom.kerLift (algebraMap R A)).toAlgebra
  let : IsScalarTower R Rbar A := IsScalarTower.of_algebraMap_eq fun r => by
    exact (RingHom.kerLift_mk (algebraMap R A) r).symm
  have hflatN : Module.Flat A N := flat_of_flatAlongZeroLocus_of_isArtinian A T N hN
  let : Module.Flat A N := hflatN
  have hflatARM : Module.Flat A (A ⊗[R] M) := Module.Flat.of_linearEquiv eN.symm
  let : Module.Flat A (A ⊗[R] M) := hflatARM
  have hflatBase : Module.Flat A (A ⊗[Rbar] Nbar) :=
    Module.Flat.of_linearEquiv (tensorQuotientCancelBaseChange R S M A K)
  have hflatBar : Module.Flat Rbar Nbar :=
    Module.Flat.of_flat_baseChange_of_injective A (A ⊗[Rbar] Nbar)
      (TensorProduct.isBaseChange Rbar Nbar A)
      (RingHom.kerLift_injective (algebraMap R A))
  let : Module.Flat Rbar Nbar := hflatBar
  intro q hq _
  exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl Nbar)

-- The tower of quotient and localization base changes exceeds the default elaboration budget.
/-- For the least ideal making the indicated quotient of `M` flat along the closed point, a local
map from `R` to a Noetherian local ring `R'` annihilates that ideal exactly when the base change
of `M` is flat along the closed point of `R'`. -/
@[stacks 0527]
lemma Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R]
    (M : Type w) [AddCommGroup M] [Module S M]
    (I : Ideal R)
    (hI_flat : Module.FlatAfterQuotientAlong
      R S M (IsLocalRing.maximalIdeal R) I)
    (hI_min : ∀ J : Ideal R,
      Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) J → I ≤ J)
    (R' : Type x) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')] :
    Module.FlatAlongZeroLocus R' (S ⊗[R] R')
        (IsLocalRing.maximalIdeal R') ((S ⊗[R] R') ⊗[S] M) ↔
      I.map (algebraMap R R') = ⊥ := by
  let : Module R M := Module.compHom M (algebraMap R S)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  constructor
  · intro h
    apply le_antisymm
    · rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing
          (IsLocalRing.maximalIdeal R') (IsLocalRing.maximalIdeal.isMaximal R').ne_top]
      refine le_iInf fun n => ?_
      let A := R' ⧸ IsLocalRing.maximalIdeal R' ^ (n + 1)
      let : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr (by
        intro htop
        exact (IsLocalRing.maximalIdeal.isMaximal R').ne_top
          (top_le_iff.mp (htop ▸ Ideal.pow_le_self (Nat.succ_ne_zero n))))
      let : IsLocalRing A :=
        IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      let : IsLocalHom (algebraMap R' A) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let : IsLocalHom (algebraMap R A) := by
        change IsLocalHom ((algebraMap R' A).comp (algebraMap R R'))
        infer_instance
      let : IsArtinianRing A := by
        rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
        refine ⟨n + 1, ?_⟩
        rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
          ← Ideal.map_pow]
        refine le_antisymm ?_ bot_le
        rw [Ideal.map_le_iff_le_comap]
        change IsLocalRing.maximalIdeal R' ^ (n + 1) ≤
          RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R' ^ (n + 1)))
        rw [Ideal.mk_ker]
      let T := (S ⊗[R] R') ⊗[R'] A
      let N := T ⊗[(S ⊗[R] R')] ((S ⊗[R] R') ⊗[S] M)
      have hmap : (IsLocalRing.maximalIdeal R').map (algebraMap R' A) ≤
          IsLocalRing.maximalIdeal A := IsLocalRing.map_maximalIdeal_le _
      have hN := Module.FlatAlongZeroLocus.baseChange R' (S ⊗[R] R') A T
        (IsLocalRing.maximalIdeal R') (IsLocalRing.maximalIdeal A)
        ((S ⊗[R] R') ⊗[S] M) hmap h
      let e₁ : N ≃ₗ[A] (A ⊗[R'] ((S ⊗[R] R') ⊗[S] M)) :=
        Algebra.IsPushout.cancelBaseChange R' A (S ⊗[R] R') T _
      let e₂ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
        (Algebra.IsPushout.cancelBaseChange R R' S (S ⊗[R] R') M)
      let e₃ : (A ⊗[R'] (R' ⊗[R] M)) ≃ₗ[A] (A ⊗[R] M) :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange R R' A A M
      have hK := hI_min _ (flatAfterQuotientAlong_ker_of_isArtinian
        R S M A T N hN (e₁ ≪≫ₗ e₂ ≪≫ₗ e₃))
      rw [Ideal.map_le_iff_le_comap]
      exact hK.trans (by
        intro z hz
        change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R' ^ (n + 1)))
          (algebraMap R R' z) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz
        exact (Ideal.pow_le_pow_right (Nat.le_succ n)) hz)
    · exact bot_le
  · intro h
    let Rbar := R ⧸ I
    let Sbar := S ⧸ I.map (algebraMap R S)
    let T := S ⊗[R] R'
    have hIK : I ≤ RingHom.ker (algebraMap R R') := by
      rw [RingHom.ker_eq_comap_bot]
      exact (Ideal.map_le_iff_le_comap).mp (le_of_eq h)
    have hIS : I.map (algebraMap R S) ≤ RingHom.ker (algebraMap S T) := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      change algebraMap S T (algebraMap R S z) = 0
      calc
        algebraMap S T (algebraMap R S z) = algebraMap R T z :=
          (IsScalarTower.algebraMap_apply R S T z).symm
        _ = algebraMap R' T (algebraMap R R' z) := IsScalarTower.algebraMap_apply R R' T z
        _ = 0 := by rw [hIK hz, map_zero]
    let : Algebra Rbar R' :=
      (Ideal.Quotient.lift I (algebraMap R R') (fun z hz => hIK hz)).toAlgebra
    let : Algebra Sbar T :=
      (Ideal.Quotient.lift (I.map (algebraMap R S)) (algebraMap S T)
        (fun z hz => hIS hz)).toAlgebra
    let : Algebra Rbar T := Algebra.compHom T (algebraMap Rbar R')
    let : IsScalarTower R Rbar R' := IsScalarTower.of_algebraMap_eq fun z => by
      exact (Ideal.Quotient.lift_mk I (algebraMap R R')
        (fun y hy => hIK hy)).symm
    let : IsScalarTower S Sbar T := IsScalarTower.of_algebraMap_eq fun z => by
      exact (Ideal.Quotient.lift_mk (I.map (algebraMap R S)) (algebraMap S T)
        (fun y hy => hIS hy)).symm
    let : IsScalarTower R Rbar T := IsScalarTower.of_algebraMap_eq fun z => by
      change algebraMap R T z =
        algebraMap R' T (algebraMap Rbar R' (algebraMap R Rbar z))
      rw [← IsScalarTower.algebraMap_apply R Rbar R' z]
      exact IsScalarTower.algebraMap_apply R R' T z
    let : IsScalarTower R Sbar T := IsScalarTower.of_algebraMap_eq fun z => by
      change algebraMap R T z =
        algebraMap Sbar T (algebraMap R Sbar z)
      rw [IsScalarTower.algebraMap_apply R S Sbar z]
      rw [← IsScalarTower.algebraMap_apply S Sbar T (algebraMap R S z)]
      exact IsScalarTower.algebraMap_apply R S T z
    let : IsScalarTower Rbar R' T :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsScalarTower Rbar Sbar T := IsScalarTower.of_algebraMap_eq fun z => by
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective z
      subst z
      change algebraMap Rbar T ((Ideal.Quotient.mk I) y) =
        algebraMap Sbar T (algebraMap Rbar Sbar ((Ideal.Quotient.mk I) y))
      have hleft : algebraMap Rbar R' ((Ideal.Quotient.mk I) y) =
          algebraMap R R' y :=
        Ideal.Quotient.lift_mk I (algebraMap R R') (fun t ht => hIK ht)
      have hright : algebraMap Sbar T
          ((Ideal.Quotient.mk (I.map (algebraMap R S))) (algebraMap R S y)) =
          algebraMap S T (algebraMap R S y) :=
        Ideal.Quotient.lift_mk (I.map (algebraMap R S)) (algebraMap S T)
          (fun t ht => hIS ht)
      rw [Algebra.compHom_algebraMap_apply, hleft,
        Ideal.Quotient.algebraMap_quotient_map_quotient, hright]
      exact (IsScalarTower.algebraMap_apply R R' T y).symm.trans
        (IsScalarTower.algebraMap_apply R S T y)
    let : Algebra.IsPushout R Rbar S Sbar := Algebra.isPushout_quotient R S I
    have hp : Algebra.IsPushout Rbar R' Sbar T :=
      (Algebra.IsPushout.comp_iff R Rbar S Sbar).mp (by infer_instance)
    let : Algebra.IsPushout Rbar R' Sbar T := hp
    have hmap : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)).map
        (algebraMap Rbar R') ≤ IsLocalRing.maximalIdeal R' := by
      calc
        _ = (IsLocalRing.maximalIdeal R).map (algebraMap R R') := by
          rw [Ideal.map_map]
          congr 1
        _ ≤ IsLocalRing.maximalIdeal R' := IsLocalRing.map_maximalIdeal_le _
    have hN := Module.FlatAlongZeroLocus.baseChange
      Rbar Sbar R' T
      ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I))
      (IsLocalRing.maximalIdeal R')
      (Sbar ⊗[S] M) hmap hI_flat
    let e : (T ⊗[Sbar] (Sbar ⊗[S] M)) ≃ₗ[T] (T ⊗[S] M) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange S Sbar T T M
    exact flatAlongZeroLocus_of_linearEquiv R' T (IsLocalRing.maximalIdeal R')
      _ _ e hN

/-! ### Detecting flatness of a base change over an arbitrary local ring

For a finite-type algebra the Noetherian hypothesis on the target local ring in Tag 0527 can be
dropped: an arbitrary local ring is the directed union of the localizations at the induced prime
of its finitely generated subalgebras over the Noetherian base, and these are Noetherian local.
-/

open CategoryTheory Limits

/-- Transport of flatness along a closed subset through a tower `A → B` of `R`-algebras: if
`M ⊗[R] A` is flat over `A` along the zero locus of `J`, then `M ⊗[R] B` is flat over `B` along
the zero locus of any ideal `K` containing the extension of `J`. Here `(S ⊗[R] A) ⊗[S] M` is the
canonical model of `M ⊗[R] A`. -/
private theorem flatAlongZeroLocus_baseChange_of_tower
    {R S A B M : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup M] [Module S M]
    (J : Ideal A) (K : Ideal B) (hJK : J.map (algebraMap A B) ≤ K)
    (h : Module.FlatAlongZeroLocus A (S ⊗[R] A) J ((S ⊗[R] A) ⊗[S] M)) :
    Module.FlatAlongZeroLocus B (S ⊗[R] B) K ((S ⊗[R] B) ⊗[S] M) := by
  let f : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R A B)
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) := f.toRingHom.toAlgebra
  let : Algebra A (S ⊗[R] B) := (algebraMap B (S ⊗[R] B)).comp
    (algebraMap A B) |>.toAlgebra
  let : IsScalarTower A B (S ⊗[R] B) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change (1 : S) ⊗ₜ[R] algebraMap A B a = f (1 ⊗ₜ[R] a)
      simp [f])
  let : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq' (f.restrictScalars R).comp_algebraMap.symm
  let : Algebra.IsPushout A B (S ⊗[R] A) (S ⊗[R] B) := by
    apply (Algebra.IsPushout.comp_iff R A S (S ⊗[R] A)).mp
    infer_instance
  have h' := Module.FlatAlongZeroLocus.baseChange
    A (S ⊗[R] A) B (S ⊗[R] B) J K ((S ⊗[R] A) ⊗[S] M) hJK h
  exact (flatAlongZeroLocus_iff_of_linearEquiv B (S ⊗[R] B) K _ _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      S (S ⊗[R] A) (S ⊗[R] B) (S ⊗[R] B) M)).mp h'

/-- The localization of a subalgebra `B` of a local ring `A` at the prime induced by the maximal
ideal of `A`. -/
private abbrev localizationAtComap
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal A).comap B.val)

/-- The canonical map from the localization of `B` at the induced prime into `A`, obtained by
inverting the elements of `B` which are units in `A`. -/
private noncomputable def localizationAtComapHom
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : localizationAtComap B →ₐ[R] A :=
  IsLocalization.liftAlgHom (M := ((IsLocalRing.maximalIdeal A).comap B.val).primeCompl)
    (f := B.val) fun s ↦
    IsLocalRing.notMem_maximalIdeal.mp s.property

/-- The canonical map out of the localization extends the inclusion of `B`. -/
private theorem localizationAtComapHom_algebraMap
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) (x : B) :
    localizationAtComapHom B (algebraMap B (localizationAtComap B) x) = x :=
  IsLocalization.lift_eq _ _

/-- The canonical map out of the localization is injective. -/
private theorem localizationAtComapHom_injective
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : Function.Injective (localizationAtComapHom B) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    ((IsLocalRing.maximalIdeal A).comap B.val).primeCompl
    (localizationAtComapHom B).toRingHom).mpr
  intro x y
  constructor
  · exact congrArg (localizationAtComapHom B)
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      localizationAtComapHom_algebraMap]
    intro h
    exact congrArg (algebraMap B (localizationAtComap B)) (Subtype.ext h)

/-- The canonical map out of the localization is a local ring homomorphism. -/
private theorem localizationAtComapHom_isLocalHom
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : IsLocalHom (localizationAtComapHom B).toRingHom := by
  constructor
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    ((IsLocalRing.maximalIdeal A).comap B.val).primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff _ _ a s).mpr
  change (a : A) ∉ IsLocalRing.maximalIdeal A
  apply IsLocalRing.notMem_maximalIdeal.mpr
  have hs : IsUnit (localizationAtComapHom B
      (algebraMap B (localizationAtComap B) s)) := by
    rw [localizationAtComapHom_algebraMap]
    exact IsLocalRing.notMem_maximalIdeal.mp s.property
  have he := congrArg (localizationAtComapHom B)
    (IsLocalization.mk'_spec (localizationAtComap B) a s)
  simp only [map_mul, localizationAtComapHom_algebraMap] at he hs
  exact he ▸ hx.mul hs

/-- The image in `A` of the localization of a subalgebra `B` at the induced prime: a subalgebra
of `A` containing `B` which is local with local inclusion into `A`. -/
private noncomputable def localSubalgebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : Subalgebra R A :=
  (localizationAtComapHom B).range

/-- The localization of `B` at the induced prime is isomorphic to its image in `A`. -/
private noncomputable def localSubalgebraEquiv
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : localizationAtComap B ≃ₐ[R] localSubalgebra B :=
  AlgEquiv.ofBijective (localizationAtComapHom B).rangeRestrict
    ⟨fun _ _ h ↦ localizationAtComapHom_injective B (congrArg Subtype.val h),
      Set.rangeFactorization_surjective⟩

/-- A subalgebra is contained in its localization at the induced prime. -/
private theorem le_localSubalgebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : B ≤ localSubalgebra B := by
  intro x hx
  exact ⟨algebraMap B (localizationAtComap B) ⟨x, hx⟩,
    localizationAtComapHom_algebraMap B _⟩

/-- Localizing at the induced prime is monotone in the subalgebra. -/
private theorem localSubalgebra_mono
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A] :
    Monotone (localSubalgebra : Subalgebra R A → Subalgebra R A) := by
  intro B C hBC x hx
  obtain ⟨x, rfl⟩ := hx
  let f := Localization.localRingHom
    ((IsLocalRing.maximalIdeal A).comap B.val)
    ((IsLocalRing.maximalIdeal A).comap C.val)
    (Subalgebra.inclusion hBC).toRingHom (by ext; rfl)
  refine ⟨f x, ?_⟩
  have he : (localizationAtComapHom C).toRingHom.comp f =
      (localizationAtComapHom B).toRingHom := by
    apply IsLocalization.ringHom_ext
      (M := ((IsLocalRing.maximalIdeal A).comap B.val).primeCompl)
    ext b
    simp [f, localizationAtComapHom_algebraMap]
  exact DFunLike.congr_fun he x

/-- The localization of a subalgebra at the induced prime is a local ring. -/
private theorem localSubalgebra_isLocalRing
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : IsLocalRing (localSubalgebra B) :=
  (localSubalgebraEquiv B).toRingEquiv.isLocalRing

/-- The inclusion of the localization of a subalgebra at the induced prime into `A` is a local
ring homomorphism. -/
private theorem localSubalgebra_isLocalHom
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    (B : Subalgebra R A) : IsLocalHom (localSubalgebra B).val := by
  constructor
  intro x hx
  obtain ⟨y, rfl⟩ := (localSubalgebraEquiv B).surjective x
  let := localizationAtComapHom_isLocalHom B
  exact (isUnit_of_map_unit (localizationAtComapHom B).toRingHom y hx).map
    (localSubalgebraEquiv B).toRingHom

/-- The localization of a finitely generated subalgebra over a Noetherian ring at the induced
prime is Noetherian. -/
private theorem localSubalgebra_isNoetherianRing
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsNoetherianRing R] (B : Subalgebra R A) (hB : B.FG) :
    IsNoetherianRing (localSubalgebra B) := by
  let : Algebra.FiniteType R B := B.fg_iff_finiteType.mp hB
  let := Algebra.FiniteType.isNoetherianRing R B
  let := IsLocalization.isNoetherianRing
    ((IsLocalRing.maximalIdeal A).comap B.val).primeCompl
    (localizationAtComap B) inferInstance
  exact isNoetherianRing_of_ringEquiv _ (localSubalgebraEquiv B).toRingEquiv

/-- A set of subalgebras of `A`, viewed as a diagram of `R`-algebras indexed by the inclusion
order. -/
private abbrev subalgebraDiagram
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (s : Set (Subalgebra R A)) : s ⥤ CommAlgCat R where
  obj B := CommAlgCat.of R B.val
  map f := CommAlgCat.ofHom (Subalgebra.inclusion (leOfHom f))

/-- The cocone on `subalgebraDiagram s` given by the inclusions into `A`. -/
private abbrev subalgebraCocone
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (s : Set (Subalgebra R A)) : Cocone (subalgebraDiagram s) where
  pt := CommAlgCat.of R A
  ι.app B := CommAlgCat.ofHom B.val.val

/-- A directed set of subalgebras with supremum `⊤` exhibits `A` as the colimit of the diagram
of its members. -/
private noncomputable def subalgebraCoconeIsColimit
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (s : Set (Subalgebra R A)) [Nonempty s] [IsDirected s (· ≤ ·)]
    (hs : (⨆ B : s, B.val) = ⊤) : IsColimit (subalgebraCocone s) := by
  have hd : Directed (· ≤ ·) (fun B : s ↦ B.val) := fun i j ↦ exists_ge_ge i j
  let f (d : Cocone (subalgebraDiagram s)) : A →ₐ[R] d.pt :=
    (@Subalgebra.iSupLift R A d.pt _ _ _
      (inferInstance : Semiring d.pt) (inferInstance : Algebra R d.pt)
      s inferInstance (fun B : s ↦ B.val) hd
      (fun B ↦ (d.ι.app B).hom)
      (by
        intro i j hij
        simpa using (congrArg CommAlgCat.Hom.hom (d.w (homOfLE hij))).symm)
      ⊤ hs.ge).comp Subalgebra.topEquiv.symm.toAlgHom
  have hf (d : Cocone (subalgebraDiagram s)) (i : s) (x : i.val) :
      f d x = d.ι.app i x := by
    dsimp only [f, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_mk _ (T := ⊤) x trivial
  refine ⟨fun d ↦ CommAlgCat.ofHom (f d), ?_, ?_⟩
  · intro d i
    ext x
    exact hf d i x
  · intro d g hg
    ext x
    have hx : x ∈ ⨆ B : s, B.val := by rw [hs]; trivial
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hd, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact (ConcreteCategory.congr_hom (hg i) ⟨x, hi⟩).trans (hf d i ⟨x, hi⟩).symm

/-- A local ring which is an algebra over a Noetherian ring `R` is the directed union of a family
of Noetherian local `R`-subalgebras whose inclusions are local. -/
private theorem exists_directed_noetherian_local_subalgebras
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing A] :
    ∃ s : Set (Subalgebra R A),
      Nonempty s ∧ IsDirected s (· ≤ ·) ∧
      (⨆ B : s, B.val) = ⊤ ∧
      ∀ B : s, IsLocalRing B.val ∧ IsNoetherianRing B.val ∧ IsLocalHom B.val.val := by
  classical
  let s : Set (Subalgebra R A) :=
    Set.range (fun t : Finset A ↦ localSubalgebra (Algebra.adjoin R (t : Set A)))
  have hm : Monotone (fun t : Finset A ↦ localSubalgebra (Algebra.adjoin R (t : Set A))) :=
    fun _ _ h ↦ localSubalgebra_mono (Algebra.adjoin_mono h)
  have hn : Nonempty s := ⟨⟨_, ⟨∅, rfl⟩⟩⟩
  let := hn
  refine ⟨s, hn, ?_, ?_, ?_⟩
  · constructor
    intro i j
    obtain ⟨t, ht⟩ := i.property
    obtain ⟨u, hu⟩ := j.property
    refine ⟨⟨_, ⟨t ∪ u, rfl⟩⟩, ?_, ?_⟩
    · change i.val ≤ _
      rw [← ht]
      exact hm Finset.subset_union_left
    · change j.val ≤ _
      rw [← hu]
      exact hm Finset.subset_union_right
  · apply top_unique
    intro x _
    apply (le_iSup (fun B : s ↦ B.val)
      ⟨_, ⟨{x}, rfl⟩⟩)
    exact le_localSubalgebra _ (Algebra.subset_adjoin (by simp))
  · rintro ⟨B, t, rfl⟩
    exact ⟨localSubalgebra_isLocalRing _,
      localSubalgebra_isNoetherianRing _ (Subalgebra.fg_adjoin_finset _),
      localSubalgebra_isLocalHom _⟩

/-- If the base change of a finite module along a finite-type algebra to a local `R`-algebra `A`
is flat along the closed point, then it is already flat along the closed point over some
Noetherian local `R`-subalgebra of `A` with local inclusion. This is the descent step supplied by
Tag 05LM. -/
private theorem exists_noetherian_subalgebra_flatAlongZeroLocus_baseChange
    (R A : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing A] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hflat : Module.FlatAlongZeroLocus A (S ⊗[R] A)
      (IsLocalRing.maximalIdeal A) ((S ⊗[R] A) ⊗[S] M)) :
    ∃ B : Subalgebra R A, ∃ (_ : IsLocalRing B),
      IsNoetherianRing B ∧ IsLocalHom B.val ∧
      Module.FlatAlongZeroLocus B (S ⊗[R] B)
        (IsLocalRing.maximalIdeal B) ((S ⊗[R] B) ⊗[S] M) := by
  obtain ⟨s, hn, hd, hs, hB⟩ := exists_directed_noetherian_local_subalgebras R A
  let := hn
  let := hd
  let : ∀ B : s, IsLocalRing B.val := fun B ↦ (hB B).1
  let : ∀ B : s, IsLocalHom B.val.val := fun B ↦ (hB B).2.2
  let F := subalgebraDiagram s
  let E := (colimit F : CommAlgCat R)
  let e : E ≃ₐ[R] A := CommAlgCat.algEquivOfIso
    ((colimit.isColimit F).coconePointUniqueUpToIso (subalgebraCoconeIsColimit s hs))
  have he (B : s) (x : B.val) : e ((colimit.ι F B).hom x) = x :=
    ConcreteCategory.congr_hom (colimit.ι_desc (subalgebraCocone s) B) x
  let : IsLocalRing E := e.symm.toRingEquiv.isLocalRing
  let : Algebra A E := e.symm.toRingHom.toAlgebra
  have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
  let : IsScalarTower R A E :=
    IsScalarTower.of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have hι (B : s) : IsLocalHom (colimit.ι F B).hom.toRingHom := by
    have hcomp : e.toRingHom.comp (colimit.ι F B).hom.toRingHom = B.val.val := by
      ext x
      exact he B x
    have : IsLocalHom (e.toRingHom.comp (colimit.ι F B).hom.toRingHom) := hcomp ▸ inferInstance
    exact isLocalHom_of_comp _ e.toRingHom
  have hJ : (⨆ B : s, (IsLocalRing.maximalIdeal B.val).map
      (colimit.ι F B).hom.toRingHom) = IsLocalRing.maximalIdeal E := by
    apply le_antisymm
    · apply iSup_le
      intro B
      let := hι B
      exact IsLocalRing.map_maximalIdeal_le _
    · intro x hx
      have hmem : e x ∈ ⨆ B : s, B.val := by rw [hs]; trivial
      have hdir : Directed (· ≤ ·) (fun B : s ↦ B.val) := fun i j ↦ exists_ge_ge i j
      rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hmem
      obtain ⟨B, hmem⟩ := hmem
      let y : B.val := ⟨e x, hmem⟩
      have hxy : (colimit.ι F B).hom y = x := e.injective (he B y)
      apply (le_iSup (fun B : s ↦ (IsLocalRing.maximalIdeal B.val).map
        (colimit.ι F B).hom.toRingHom) B)
      rw [← hxy]
      apply Ideal.mem_map_of_mem
      intro hy
      exact hx (hxy ▸ hy.map (colimit.ι F B).hom)
  have hE : Module.FlatAlongZeroLocus E (S ⊗[R] E)
      (⨆ B : s, (IsLocalRing.maximalIdeal B.val).map (colimit.ι F B).hom.toRingHom)
      ((S ⊗[R] E) ⊗[S] M) := by
    rw [hJ]
    exact flatAlongZeroLocus_baseChange_of_tower _ _
      (IsLocalRing.map_maximalIdeal_le e.symm.toRingHom) hflat
  let : Module R M := Module.compHom M (algebraMap R S)
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let := Algebra.FiniteType.isNoetherianRing R S
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.FinitePresentation S M := Module.finitePresentation_of_finite S M
  obtain ⟨B, hflatB⟩ := Module.exists_flatAlongZeroLocus_baseChange_of_colimit
    R S M s F (fun B ↦ IsLocalRing.maximalIdeal B.val) (by
      intro i j hij
      have hc : j.val.val.toRingHom.comp (Subalgebra.inclusion hij).toRingHom =
          i.val.val.toRingHom := rfl
      have : IsLocalHom (j.val.val.toRingHom.comp (Subalgebra.inclusion hij).toRingHom) :=
        hc ▸ ⟨(hB i).2.2.map_nonunit⟩
      let := isLocalHom_of_comp (Subalgebra.inclusion hij).toRingHom j.val.val.toRingHom
      exact IsLocalRing.map_maximalIdeal_le _) hE
  exact ⟨B.val, inferInstance, (hB B).2.1, (hB B).2.2, hflatB⟩

/-- If a local map to a local ring `A` annihilates the flattening ideal, then the base change of
`M` to `A` is flat along the closed point: the map factors through `R / I`, for which Tag 0527
applies, and flatness along the closed point is stable under the further base change to `A`. -/
private theorem flatAlongZeroLocus_baseChange_of_map_eq_bot
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R]
    (M : Type w) [AddCommGroup M] [Module S M]
    (I : Ideal R)
    (hI_flat : Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) I)
    (hI_min : ∀ J : Ideal R,
      Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) J → I ≤ J)
    (A : Type x) [CommRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (hI : I.map (algebraMap R A) = ⊥) :
    Module.FlatAlongZeroLocus A (S ⊗[R] A)
      (IsLocalRing.maximalIdeal A) ((S ⊗[R] A) ⊗[S] M) := by
  have hker := (Ideal.map_eq_bot_iff_le_ker (algebraMap R A)).mp hI
  let f : R ⧸ I →ₐ[R] A := Ideal.Quotient.liftₐ I (Algebra.ofId R A) hker
  have : Nontrivial (R ⧸ I) := f.toRingHom.domain_nontrivial
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap R (R ⧸ I)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : Algebra (R ⧸ I) A := f.toRingHom.toAlgebra
  have : IsScalarTower R (R ⧸ I) A :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalHom (algebraMap (R ⧸ I) A) := by
    constructor
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (isUnit_of_map_unit (algebraMap R A) x hx).map (Ideal.Quotient.mk I)
  have hQ := (Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot
    R S M I hI_flat hI_min (R ⧸ I)).mpr (Ideal.map_quotient_self I)
  exact flatAlongZeroLocus_baseChange_of_tower _ _
    (IsLocalRing.map_maximalIdeal_le (algebraMap (R ⧸ I) A)) hQ

/-- Flatness along a closed subset transported along an isomorphism of the algebra which is
compatible with the base. -/
private theorem flatAlongZeroLocus_tensor_of_algEquiv
    {A S T U M : Type*} [CommRing A] [CommRing S] [CommRing T] [CommRing U]
    [Algebra A T] [Algebra A U] [Algebra S T] [Algebra S U]
    [AddCommGroup M] [Module S M]
    (J : Ideal A) (e : T ≃ₐ[S] U)
    (he : e.toRingHom.comp (algebraMap A T) = algebraMap A U)
    (h : Module.FlatAlongZeroLocus A T J (T ⊗[S] M)) :
    Module.FlatAlongZeroLocus A U J (U ⊗[S] M) := by
  let : Algebra T U := e.toRingHom.toAlgebra
  have : IsScalarTower A T U := IsScalarTower.of_algebraMap_eq' he.symm
  have : IsScalarTower S T U := IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  let eA : T ≃ₐ[A] U := { __ := e.toRingEquiv, commutes' a := DFunLike.congr_fun he a }
  have : Algebra.IsPushout A A T U := Algebra.IsPushout.of_equiv eA (by ext; rfl)
  have h' := Module.FlatAlongZeroLocus.baseChange A T A U J J
    (T ⊗[S] M) (by simp) h
  exact (flatAlongZeroLocus_iff_of_linearEquiv A U J _ _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S T U U M)).mp h'

/-- Base change of the algebra along a surjection `R → R₀` of bases does not change flatness
along a closed subset, because the two tensor products `S ⊗[R] A` and `S ⊗[R₀] A` agree. -/
private theorem flatAlongZeroLocus_baseChange_iff_of_surjective_algebraMap
    {R R₀ S A M : Type*} [CommRing R] [CommRing R₀] [CommRing S] [CommRing A]
    [Algebra R R₀] [Algebra R S] [Algebra R₀ S] [IsScalarTower R R₀ S]
    [Algebra R A] [Algebra R₀ A] [IsScalarTower R R₀ A]
    [AddCommGroup M] [Module S M]
    (hR : Function.Surjective (algebraMap R R₀)) (J : Ideal A) :
    Module.FlatAlongZeroLocus A (S ⊗[R] A) J ((S ⊗[R] A) ⊗[S] M) ↔
      Module.FlatAlongZeroLocus A (S ⊗[R₀] A) J ((S ⊗[R₀] A) ⊗[S] M) := by
  have : TensorProduct.CompatibleSMul R R₀ S A :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S A hR
  let e := Algebra.TensorProduct.equivOfCompatibleSMul R R₀ S S A
  exact ⟨flatAlongZeroLocus_tensor_of_algEquiv J e.symm (by ext; rfl),
    flatAlongZeroLocus_tensor_of_algEquiv J e (by ext; rfl)⟩

/-- If the base change of `M` to a local ring `A` is flat along the closed point, then the
flattening ideal maps to zero. The two rings live in independent universes, so `R` and `A` are
first replaced by the `ULift`s `ULift.{x} R` and `ULift.{u} A`, which share a universe; the
statement is then descended to a Noetherian local subalgebra by Tag 05LM and Tag 0527 applies
there. -/
private theorem map_eq_bot_of_flatAlongZeroLocus_baseChange
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (M : Type w) [AddCommGroup M] [Module S M] [Module.Finite S M]
    (I : Ideal R)
    (hI_flat : Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) I)
    (hI_min : ∀ J : Ideal R,
      Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) J → I ≤ J)
    (A : Type x) [CommRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (hflat : Module.FlatAlongZeroLocus A (S ⊗[R] A)
      (IsLocalRing.maximalIdeal A) ((S ⊗[R] A) ⊗[S] M)) :
    I.map (algebraMap R A) = ⊥ := by
  let R₀ := ULift.{x} R
  let A₀ := ULift.{u} A
  let : Algebra R₀ S := ULift.algebra' R S
  let : Algebra R₀ A₀ := ULift.algebra' R A₀
  have : IsNoetherianRing R₀ := isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  have : IsLocalRing A₀ := (ULift.ringEquiv : A₀ ≃+* A).symm.isLocalRing
  have : Algebra.FiniteType R₀ S := Algebra.FiniteType.of_restrictScalars_finiteType R R₀ S
  have hR : Function.Surjective (algebraMap R R₀) := fun x ↦ ⟨x.down, rfl⟩
  have : IsLocalHom (algebraMap A A₀) :=
    IsLocalHom.of_surjective _ (fun x ↦ ⟨x.down, rfl⟩)
  have hA₀ : Module.FlatAlongZeroLocus A₀ (S ⊗[R₀] A₀)
      (IsLocalRing.maximalIdeal A₀) ((S ⊗[R₀] A₀) ⊗[S] M) :=
    (flatAlongZeroLocus_baseChange_iff_of_surjective_algebraMap hR _).mp
      (flatAlongZeroLocus_baseChange_of_tower _ _
        (IsLocalRing.map_maximalIdeal_le (algebraMap A A₀)) hflat)
  obtain ⟨B, hBl, hBn, hBm, hBflat⟩ :=
    exists_noetherian_subalgebra_flatAlongZeroLocus_baseChange R₀ A₀ S M hA₀
  let := hBl
  let := hBn
  let : Algebra R B := (B.restrictScalars R).algebra
  have : IsScalarTower R R₀ B := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hBflat' : Module.FlatAlongZeroLocus B (S ⊗[R] B)
      (IsLocalRing.maximalIdeal B) ((S ⊗[R] B) ⊗[S] M) :=
    (flatAlongZeroLocus_baseChange_iff_of_surjective_algebraMap hR _).mpr hBflat
  let f : B →ₐ[R] A := ULift.algEquiv.toAlgHom.comp (B.val.restrictScalars R)
  have : IsLocalHom (f.toRingHom.comp (algebraMap R B)) :=
    f.comp_algebraMap ▸ inferInstance
  have : IsLocalHom (algebraMap R B) := isLocalHom_of_comp _ f.toRingHom
  have hIB := (Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot
    R S M I hI_flat hI_min B).mp hBflat'
  rw [← f.comp_algebraMap, ← Ideal.map_map, hIB, Ideal.map_bot]

/-- For the least ideal making the indicated quotient of `M` flat along the closed point, a local
map from `R` to an arbitrary local ring `R'` annihilates that ideal exactly when the base change
of `M` is flat along the closed point, provided `S` is of finite type over the Noetherian local
ring `R` and `M` is finite over `S`. No Noetherian hypothesis is imposed on `R'`. -/
@[stacks 0528]
lemma Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot_of_finiteType
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (M : Type w) [AddCommGroup M] [Module S M] [Module.Finite S M]
    (I : Ideal R)
    (hI_flat : Module.FlatAfterQuotientAlong
      R S M (IsLocalRing.maximalIdeal R) I)
    (hI_min : ∀ J : Ideal R,
      Module.FlatAfterQuotientAlong R S M (IsLocalRing.maximalIdeal R) J → I ≤ J)
    (R' : Type x) [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')] :
    Module.FlatAlongZeroLocus R' (S ⊗[R] R')
        (IsLocalRing.maximalIdeal R') ((S ⊗[R] R') ⊗[S] M) ↔
      I.map (algebraMap R R') = ⊥ :=
  ⟨map_eq_bot_of_flatAlongZeroLocus_baseChange R S M I hI_flat hI_min R',
    flatAlongZeroLocus_baseChange_of_map_eq_bot R S M I hI_flat hI_min R'⟩
