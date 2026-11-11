module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization

/-!
# Irreducibility of `Spec` from irreducible fibres
-/

/-!
# Spec of a flat finitely presented algebra is irreducible from irreducible
fibres on a dense subset (Tag 00I6)

Let `R → S` be a ring map with `Spec R` irreducible. If the structure map
`Spec S → Spec R` is open (e.g. if `R → S` is flat and of finite presentation)
and the topological fibres of `Spec S → Spec R` are irreducible over a dense
subset of `Spec R`, then `Spec S` is irreducible.

The headline `irreducibleSpace_of_isOpenMap_dense_irreducible_fibres` is the
purely topological version of the Stacks lemma, formulated directly in terms of
fibres of the structure map (this is the *more general* form noted in the
Stacks statement, with `(b) + (c)` replaced by openness of the map on spectra).
The flat + finite presentation specialization follows by combining it with
`primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation`.
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `Y` is irreducible and `f : X → Y` is an open map whose topological
fibres `{x // f x = y}` are irreducible for `y` in a dense subset `D ⊆ Y`,
then `X` is nonempty. -/
private lemma nonempty_of_dense_irreducible_fibres
    [IrreducibleSpace Y] (f : X → Y) (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    Nonempty X :=
  let ⟨y, hy⟩ := hD.nonempty
  ⟨(hfib y hy).toNonempty.some.1⟩

/-- If `Y` is irreducible and `f : X → Y` is a continuous open map whose
topological fibres are irreducible for `y` in a dense subset, then `X` is
preirreducible. -/
private lemma preirreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    [IrreducibleSpace Y]
    (f : X → Y) (hf : IsOpenMap f)
    (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    PreirreducibleSpace X := by
  refine ⟨fun U V hU hV ⟨xU, _, hxU⟩ ⟨xV, _, hxV⟩ => ?_⟩
  obtain ⟨y, _, hyU, hyV⟩ := (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible _ _
    (hf U hU) (hf V hV) ⟨f xU, trivial, xU, hxU, rfl⟩ ⟨f xV, trivial, xV, hxV, rfl⟩
  obtain ⟨y₀, ⟨⟨xU, hxU, hfxU⟩, ⟨xV, hxV, hfxV⟩⟩, hy₀D⟩ :=
    hD.inter_open_nonempty _ ((hf U hU).inter (hf V hV)) ⟨y, hyU, hyV⟩
  have := hfib y₀ hy₀D
  obtain ⟨⟨x₀, _⟩, _, hx₀U, hx₀V⟩ :=
    (IrreducibleSpace.isIrreducible_univ {x : X // f x = y₀}).isPreirreducible _ _
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      ⟨⟨xU, hfxU⟩, trivial, hxU⟩ ⟨⟨xV, hfxV⟩, trivial, hxV⟩
  exact ⟨x₀, trivial, hx₀U, hx₀V⟩

/-- **Topological core of Stacks 00I6.** Let `f : X → Y` be a continuous open
map between topological spaces with `Y` irreducible. If the fibres
`{x // f x = y}` of `f` are irreducible spaces for `y` in a dense subset of
`Y`, then `X` is irreducible.

This is the *more general* form of Stacks tag 00I6 (Algebra, Lemma 10.130.4)
indicated in the statement, with the flatness and finite-presentation
hypotheses replaced by openness of the structure map on spectra. -/
@[ega "IV 2.3.5" "(iii), special case", ega "IV 4.4.2" "irreducibility clause"]
theorem irreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    [IrreducibleSpace Y]
    (f : X → Y) (hf : IsOpenMap f)
    (D : Set Y) (hD : Dense D)
    (hfib : ∀ y ∈ D, IrreducibleSpace {x : X // f x = y}) :
    IrreducibleSpace X :=
  have : Nonempty X := nonempty_of_dense_irreducible_fibres f D hD hfib
  have : PreirreducibleSpace X :=
    preirreducibleSpace_of_isOpenMap_dense_irreducible_fibres f hf D hD hfib
  ⟨inferInstance⟩

/-- **Stacks 00I6** (algebraic form, more general statement). Let `R → S` be a
ring map. Assume:
* `Spec R` is irreducible;
* the induced map `Spec S → Spec R` is open;
* the topological fibres of `Spec S → Spec R` are irreducible for `p` in a
  dense subset of `Spec R`.

Then `Spec S` is irreducible. -/
@[stacks 00I6 "general form", ega "IV 2.3.5" "(iii), special case", ega "IV 4.4.2" "special case"]
theorem irreducibleSpace_primeSpectrum_of_isOpenMap_comap
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IrreducibleSpace (PrimeSpectrum R)]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)))
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hfib : ∀ p ∈ D,
      IrreducibleSpace
        {q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) q = p}) :
    IrreducibleSpace (PrimeSpectrum S) :=
  irreducibleSpace_of_isOpenMap_dense_irreducible_fibres
    (PrimeSpectrum.comap (algebraMap R S)) hopen
    D hD hfib

/-- **Stacks 00I6** (flat + finite-presentation form). Let `R → S` be a flat
ring map of finite presentation. If `Spec R` is irreducible and the
topological fibres of `Spec S → Spec R` are irreducible for `p` in a dense
subset of `Spec R`, then `Spec S` is irreducible. -/
@[stacks 00I6]
theorem irreducibleSpace_primeSpectrum_of_flat_finitePresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IrreducibleSpace (PrimeSpectrum R)]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hfib : ∀ p ∈ D,
      IrreducibleSpace
        {q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) q = p}) :
    IrreducibleSpace (PrimeSpectrum S) :=
  irreducibleSpace_primeSpectrum_of_isOpenMap_comap R S
    (primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation R S)
    D hD hfib

end

/-!
# Tensor products over a separably closed field (Tag 00I7)

Stacks lemma 00I7 says: if `k` is a separably closed field and `R`, `S` are
`k`-algebras each with a unique minimal prime, then so does `R ⊗_k S`.
The statement of 00I7 is `existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed`;
`irreducibleSpace_primeSpectrum_tensorProduct_of_isSepClosed` is the same statement phrased as
irreducibility of spectra. Both carry the tag.

The proof follows Stacks. Let `K` be an algebraic closure of `k`; since `k` is
separably closed, `K / k` is purely inseparable, so `Spec (T ⊗_k K) → Spec T` is a
homeomorphism for every `k`-algebra `T`
(`PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`).
Together with `K ⊗_k (R ⊗_k S) ≅ (K ⊗_k R) ⊗_K (K ⊗_k S)` this reduces the lemma to
the algebraically closed case. There one passes to the reductions, which are domains,
and shows that the tensor product of two domains over an algebraically closed field
is a domain: after reducing to a finite type left factor, the Hilbert Nullstellensatz
gives enough `K`-points, and the Jacobson property shows that a product of
coefficients vanishing at every point is zero.

We also record the trivial cases in which one of the two factors is `k` itself,
together with `unique_minimalPrime_of_ringEquiv`: any ring isomorphism transports
the property of having a unique minimal prime.
-/

@[expose] public section

open scoped TensorProduct

/-- A ring isomorphism transports the property of having a unique minimal prime. -/
theorem unique_minimalPrime_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : ∃! p, p ∈ minimalPrimes S) : ∃! p, p ∈ minimalPrimes R := by
  have hcomap : minimalPrimes R =
      Ideal.comap (e : R →+* S) '' minimalPrimes S := by
    have := Ideal.comap_minimalPrimes_eq_of_surjective
      (f := (e : R →+* S)) e.surjective (I := (⊥ : Ideal S))
    have hbot : (⊥ : Ideal S).comap (e : R →+* S) = ⊥ :=
      Ideal.comap_bot_of_injective _ e.injective
    simpa [minimalPrimes, hbot] using this
  obtain ⟨q, hq, huniq⟩ := h
  refine ⟨Ideal.comap (e : R →+* S) q, ?_, ?_⟩
  · rw [hcomap]; exact ⟨q, hq, rfl⟩
  · intro p hp
    rw [hcomap] at hp
    obtain ⟨q', hq', rfl⟩ := hp
    rw [huniq q' hq']

/-- The right-factor trivial case of Stacks 00I7: if the right factor is the
base field `k` itself, then `R ⊗[k] k` has a unique minimal prime whenever
`R` does. -/
theorem tensorProduct_rid_unique_minimalPrime (k : Type*) [Field k] (R : Type*) [CommRing R]
    [Algebra k R] (hR : ∃! p, p ∈ minimalPrimes R) : ∃! p, p ∈ minimalPrimes (R ⊗[k] k) :=
  unique_minimalPrime_of_ringEquiv (Algebra.TensorProduct.rid k k R).toRingEquiv hR

/-- The left-factor trivial case of Stacks 00I7: if the left factor is the
base field `k` itself, then `k ⊗[k] S` has a unique minimal prime whenever
`S` does. -/
theorem tensorProduct_lid_unique_minimalPrime (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] (hS : ∃! p, p ∈ minimalPrimes S) : ∃! p, p ∈ minimalPrimes (k ⊗[k] S) :=
  unique_minimalPrime_of_ringEquiv (Algebra.TensorProduct.lid k S).toRingEquiv hS

/-- The right-factor trivial case of Stacks 00I7, under the name used by earlier
references: `R ⊗_k k` has a unique minimal prime whenever `R` does. The general
statement is `existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed`. -/
alias tensorProduct_unique_minimalPrime_of_isSepClosed_right_base :=
  tensorProduct_rid_unique_minimalPrime

/-- A ring has a unique minimal prime if and only if its nilradical is prime. -/
private lemma existsUnique_mem_minimalPrimes_iff_isPrime_nilradical (R : Type*) [CommRing R] :
    (∃! p : Ideal R, p ∈ minimalPrimes R) ↔ (nilradical R).IsPrime := by
  constructor
  · rintro ⟨p, hp, hpu⟩
    have hnil : nilradical R = p := by
      rw [nilradical, ← Ideal.sInf_minimalPrimes]
      exact le_antisymm (sInf_le hp) (le_sInf fun q hq => (hpu q hq).symm ▸ le_rfl)
    exact hnil ▸ hp.isPrime
  · intro hnil
    refine ⟨nilradical R, ⟨⟨hnil, bot_le⟩, fun q hq _ => @nilradical_le_prime R _ q hq.1⟩,
      fun p hp => le_antisymm (hp.2 ⟨hnil, bot_le⟩ (@nilradical_le_prime R _ p hp.isPrime))
        (@nilradical_le_prime R _ p hp.isPrime)⟩

/-- A ring map inducing a homeomorphism on spectra preserves and reflects irreducibility
of the spectrum. -/
private lemma irreducibleSpace_primeSpectrum_iff_of_isHomeomorph {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : IsHomeomorph (PrimeSpectrum.comap f)) :
    IrreducibleSpace (PrimeSpectrum A) ↔ IrreducibleSpace (PrimeSpectrum B) :=
  ⟨fun _ => Function.Surjective.irreducibleSpace (hf.homeomorph _).symm.continuous
      (hf.homeomorph _).symm.surjective,
    fun _ => Function.Surjective.irreducibleSpace hf.continuous hf.surjective⟩

/-- A ring isomorphism preserves irreducibility of the spectrum. -/
private lemma irreducibleSpace_primeSpectrum_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) [IrreducibleSpace (PrimeSpectrum A)] :
    IrreducibleSpace (PrimeSpectrum B) :=
  (irreducibleSpace_primeSpectrum_iff_of_isHomeomorph (e : A →+* B)
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective)).mp inferInstance

/-- The finite type case of `isDomain_tensorProduct_of_isAlgClosed`: if `K` is algebraically
closed, `A` is a domain of finite type over `K` and `B` is a domain over `K`, then `A ⊗_K B`
has no zero divisors. -/
private lemma eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType (K A B : Type*) [Field K]
    [IsAlgClosed K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [IsDomain A]
    [IsDomain B] [Algebra.FiniteType K A] {x y : A ⊗[K] B} (hxy : x * y = 0) :
    x = 0 ∨ y = 0 := by
  classical
  let b := Module.Free.chooseBasis K B
  let bA := Algebra.TensorProduct.basis A b
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hφ : ∀ m : Ideal A, m.IsMaximal → ∃ φ : A →ₐ[K] K, ∀ a, φ a = 0 → a ∈ m := by
    intro m hm
    let _ : Field (A ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType K (A ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m)
        (Ideal.Quotient.mkₐ_surjective K m)
    have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
    have hb : Function.Bijective (algebraMap K (A ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m)) hb
    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m), fun a ha => ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hcoef : ∀ (φ : A →ₐ[K] K) (z : A ⊗[K] B) (i : Module.Free.ChooseBasisIndex K B),
      b.repr (Algebra.TensorProduct.lid K B
        (Algebra.TensorProduct.map φ (AlgHom.id K B) z)) i = φ (bA.repr z i) := by
    intro φ z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [bA, Algebra.TensorProduct.basis_repr_tmul]
    | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]
  have key : ∀ i j, bA.repr x i * bA.repr y j = 0 := by
    intro i j
    have hrad : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' ⊥ (Ideal.radical_eq_iff.mp (by simp))
    rw [← Ideal.mem_bot, ← hrad, Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφm⟩ := hφ m hm
    let Ψ : A ⊗[K] B →ₐ[K] B :=
      (Algebra.TensorProduct.lid K B).toAlgHom.comp
        (Algebra.TensorProduct.map φ (AlgHom.id K B))
    have hΨ : Ψ x * Ψ y = 0 := by rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp hΨ with h | h
    · refine m.mul_mem_right _ (hφm _ ?_)
      rw [← hcoef]
      exact (congrArg (fun z => b.repr z i) h).trans (by simp)
    · refine m.mul_mem_left _ (hφm _ ?_)
      rw [← hcoef]
      exact (congrArg (fun z => b.repr z j) h).trans (by simp)
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hx' : bA.repr x ≠ 0 := by simpa using hx
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hx'
    have hy : bA.repr y = 0 := by
      ext j
      exact (mul_eq_zero.mp (key i j)).resolve_left hi
    simpa using hy

/-- If `K` is an algebraically closed field and `A`, `B` are `K`-algebras which are domains,
then `A ⊗_K B` is a domain. This is the core of the proof of Stacks 00I7. -/
theorem isDomain_tensorProduct_of_isAlgClosed (K A B : Type*) [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [IsDomain A] [IsDomain B] :
    IsDomain (A ⊗[K] B) := by
  classical
  have : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right K A B
      (algebraMap K A).injective
  suffices NoZeroDivisors (A ⊗[K] B) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let b := Module.Free.chooseBasis K B
  let bA := Algebra.TensorProduct.basis A b
  let s : Finset A :=
    (bA.repr x).support.image (bA.repr x) ∪ (bA.repr y).support.image (bA.repr y)
  let A₀ : Subalgebra K A := Algebra.adjoin K (s : Set A)
  have : Algebra.FiniteType K A₀ := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  let ι₀ : A₀ ⊗[K] B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.map A₀.val (AlgHom.id K B)
  have hinj : Function.Injective ι₀ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) A₀.val.toLinearMap
      Subtype.val_injective
  have hrange : ∀ z : A ⊗[K] B, (∀ i, bA.repr z i ∈ A₀) → z ∈ ι₀.range := by
    intro z hz
    rw [← bA.linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun i _ => ⟨⟨_, hz i⟩ ⊗ₜ b i, ?_⟩
    simp [ι₀, bA, TensorProduct.smul_tmul']
  have hx₀ : ∀ i, bA.repr x i ∈ A₀ := fun i => by
    by_cases hi : bA.repr x i = 0
    · rw [hi]; exact zero_mem _
    · exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hi))))
  have hy₀ : ∀ i, bA.repr y i ∈ A₀ := fun i => by
    by_cases hi : bA.repr y i = 0
    · rw [hi]; exact zero_mem _
    · exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hi))))
  obtain ⟨x₀, hx₀'⟩ := ι₀.mem_range.mp (hrange x hx₀)
  obtain ⟨y₀, hy₀'⟩ := ι₀.mem_range.mp (hrange y hy₀)
  have h0 : x₀ * y₀ = 0 := hinj (by rw [map_mul, hx₀', hy₀', hxy, map_zero])
  rcases eq_zero_or_eq_zero_of_mul_eq_zero_of_finiteType K A₀ B h0 with h | h
  · exact Or.inl (by rw [← hx₀', h, map_zero])
  · exact Or.inr (by rw [← hy₀', h, map_zero])

/-- The algebraically closed case of Stacks 00I7: if `K` is algebraically closed and the
spectra of the `K`-algebras `A` and `B` are irreducible, so is the spectrum of `A ⊗_K B`. -/
theorem irreducibleSpace_primeSpectrum_tensorProduct_of_isAlgClosed (K A B : Type*) [Field K]
    [IsAlgClosed K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [IrreducibleSpace (PrimeSpectrum A)] [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum (A ⊗[K] B)) := by
  have hA : (nilradical A).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have hB : (nilradical B).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have : IsDomain (A ⧸ nilradical A) := (Ideal.Quotient.isDomain_iff_prime _).mpr hA
  have : IsDomain (B ⧸ nilradical B) := (Ideal.Quotient.isDomain_iff_prime _).mpr hB
  have := isDomain_tensorProduct_of_isAlgClosed K (A ⧸ nilradical A) (B ⧸ nilradical B)
  let f := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (nilradical A))
    (Ideal.Quotient.mkₐ K (nilradical B))
  have hfA := Ideal.Quotient.mkₐ_surjective K (nilradical A)
  have hfB := Ideal.Quotient.mkₐ_surjective K (nilradical B)
  have hf : Function.Surjective f := Algebra.TensorProduct.map_surjective _ _ hfA hfB
  have hker : RingHom.ker f.toRingHom ≤ nilradical (A ⊗[K] B) := by
    have : RingHom.ker f.toRingHom = RingHom.ker f := rfl
    rw [this, Algebra.TensorProduct.map_ker _ _ hfA hfB]
    refine sup_le ?_ ?_ <;> rw [Ideal.map_le_iff_le_comap] <;> intro a ha <;>
      simp only [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
        mem_nilradical] at ha <;>
      exact IsNilpotent.map ha _
  have h := PrimeSpectrum.isHomeomorph_comap f.toRingHom
    (fun z => ⟨1, one_pos, by simpa using hf z⟩) hker
  exact Function.Surjective.irreducibleSpace h.continuous h.surjective

/-- If `k` is separably closed, base change to an algebraic closure of `k` preserves and
reflects irreducibility of the spectrum: `Spec (K ⊗_k T) → Spec T` is a homeomorphism since
`K / k` is purely inseparable. -/
private lemma irreducibleSpace_primeSpectrum_iff_tensorProduct_algebraicClosure (k T : Type*)
    [Field k] [IsSepClosed k] [CommRing T] [Algebra k T] :
    IrreducibleSpace (PrimeSpectrum T) ↔
      IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] T)) := by
  rw [irreducibleSpace_primeSpectrum_iff_of_isHomeomorph _
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k (AlgebraicClosure k) T)]
  exact irreducibleSpace_primeSpectrum_iff_of_isHomeomorph _
    (PrimeSpectrum.isHomeomorph_comap_of_bijective
      (f := (Algebra.TensorProduct.comm k (AlgebraicClosure k) T).symm.toRingEquiv.toRingHom)
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) T).symm.bijective)

/-- **Stacks Tag 00I7.** Let `k` be a separably closed field and let `R`, `S` be
`k`-algebras. If `R` and `S` each have a unique minimal prime, then so does `R ⊗_k S`. -/
@[stacks 00I7]
theorem existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed (k : Type*) [Field k]
    [IsSepClosed k] (R S : Type*) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (hR : ∃! p : Ideal R, p ∈ minimalPrimes R) (hS : ∃! p : Ideal S, p ∈ minimalPrimes S) :
    ∃! p : Ideal (R ⊗[k] S), p ∈ minimalPrimes (R ⊗[k] S) := by
  simp only [existsUnique_mem_minimalPrimes_iff_isPrime_nilradical,
    ← PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR hS ⊢
  let K := AlgebraicClosure k
  have : IrreducibleSpace (PrimeSpectrum (K ⊗[k] R)) := 
    (irreducibleSpace_primeSpectrum_iff_tensorProduct_algebraicClosure k R).mp hR
  have : IrreducibleSpace (PrimeSpectrum (K ⊗[k] S)) := 
    (irreducibleSpace_primeSpectrum_iff_tensorProduct_algebraicClosure k S).mp hS
  have := irreducibleSpace_primeSpectrum_tensorProduct_of_isAlgClosed K (K ⊗[k] R) (K ⊗[k] S)
  let e : (K ⊗[k] R) ⊗[K] (K ⊗[k] S) ≃+* K ⊗[k] (R ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k K K (K ⊗[k] R) S).toRingEquiv.trans
      (Algebra.TensorProduct.assoc k k k K R S).toRingEquiv
  have := irreducibleSpace_primeSpectrum_of_ringEquiv e
  exact
    (irreducibleSpace_primeSpectrum_iff_tensorProduct_algebraicClosure k (R ⊗[k] S)).mpr this


/-- **Stacks Tag 00I7**, in terms of spectra. Let `k` be a separably closed field and let `R`,
`S` be `k`-algebras whose spectra are irreducible. Then the spectrum of `R ⊗_k S` is
irreducible. -/
@[stacks 00I7 "in terms of irreducibility of spectra"]
theorem irreducibleSpace_primeSpectrum_tensorProduct_of_isSepClosed (k : Type*) [Field k]
    [IsSepClosed k] (R S : Type*) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [IrreducibleSpace (PrimeSpectrum R)] [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  have h := existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed k R S
    ((existsUnique_mem_minimalPrimes_iff_isPrime_nilradical R).mpr
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance))
    ((existsUnique_mem_minimalPrimes_iff_isPrime_nilradical S).mpr
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance))
  exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr
    ((existsUnique_mem_minimalPrimes_iff_isPrime_nilradical _).mp h)

end
