module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute

/-!
# The Galois group acts transitively on the primes of `kbar ⊗[k] K`

Let `K/k` be an extension of fields and let `kbar/k` be a Galois extension. Then
`Gal(kbar/k)` acts transitively on the primes of `kbar ⊗[k] K`. The same holds for a normal
extension `kbar/k`, which need not be separable; a separable algebraic closure of `k` is the
case the source states.

Throughout, `k` is the base field, `K` a field with a `k`-algebra structure, and `kbar` a
field with a `k`-algebra structure that is Galois over `k`.

## Conventions

That `kbar/k` is Galois means it is algebraic, separable and normal, the typeclass
`IsGalois k kbar`; a separable algebraic closure of `k` is Galois over `k`. A normal extension,
the typeclass `Normal k kbar`, is algebraic with every minimal polynomial splitting, and the
transitivity statement for it is reduced to the Galois case by passing to the separable closure
of `k` in `kbar`, over which `kbar` is purely inseparable: a purely inseparable extension is a
universal homeomorphism on spectra, so it changes neither the primes nor the automorphisms.

The Galois group of `kbar/k` is the group of `k`-algebra automorphisms of `kbar`, the type
`kbar ≃ₐ[k] kbar`. The ring `kbar ⊗[k] K` is the tensor product of `k`-algebras with its
canonical commutative-ring and `k`-algebra structure. For `σ ∈ Gal(kbar/k)` the induced
`k`-algebra automorphism of `kbar ⊗[k] K` is `σ ⊗ id_K : x ⊗ y ↦ σ x ⊗ y`, realized as
`Algebra.TensorProduct.congr σ AlgEquiv.refl`; it induces a self-map of the prime spectrum
`Spec (kbar ⊗[k] K)` by pullback of prime ideals.

The primes of `kbar ⊗[k] K` are the prime ideals of that commutative ring, that is, the
points of its `PrimeSpectrum`. Acting transitively has its standard meaning for a group
action on a set: any element can be sent to any other by some group element, with no claim
of uniqueness. The geometric action of a ring automorphism `φ` on `Spec` is by pullback
`PrimeSpectrum.comap φ`; since `comap` of an automorphism is bijective, the choice of
direction does not affect the transitivity claim.
-/

@[expose] public section

open scoped TensorProduct

/-! ## Shape of the argument

Write `B = kbar ⊗[k] K` and `G = Gal(kbar/k) = (kbar ≃ₐ[k] kbar)`.

The classical proof is a profinite compactness reduction to the finite Galois case, and that
compactness step is `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`: for a group
`G` acting on `B` over `A`, compact, totally disconnected and topological, with `B` discrete,
the action continuous and `B` invariant over `A`, two primes with the same contraction to `A`
differ by an element of `G`. The whole proof therefore reduces to supplying its hypotheses
with `A = K`, `B = kbar ⊗[k] K` and `G = kbar ≃ₐ[k] kbar`, and converting the conclusion
`Q = σ • P`, an equality of ideals with `•` the pushforward, into the `comap` form used in
`gal_acts_transitively_on_primes_of_isGalois`.

Those hypotheses split into the following pieces.

1. The `MulSemiringAction G B` instance, in which `σ` acts by
   `Algebra.TensorProduct.congr σ AlgEquiv.refl`, that is, by `σ ⊗ id_K`. This is a group
   homomorphism `G →* RingAut B`, hence a `MulSemiringAction` via
   `MulSemiringAction.compHom`.
2. `SMulCommClass G K B`: the `G`-action and the `K`-scalar action commute, because
   `σ ⊗ id_K` fixes the right tensor factor `K`.
3. The topology on `G` is the Krull topology, under which `G` is compact, totally
   disconnected and a topological group. `B` is given the discrete topology, and
   `ContinuousSMul G B` holds because every `x ∈ B` lies in `L ⊗[k] K` for a finite
   subextension `L`, and the open subgroup `Gal(kbar/L)` fixes it.
4. `Algebra.IsInvariant K B G`: a `G`-invariant element of `kbar ⊗[k] K` lies in the image of
   `K`. This is the substantive algebraic content, the statement that
   `K = (kbar ⊗ K)^{Gal}`.
5. `Ideal.under K P = Ideal.under K Q` for any two primes: `K` is a field, so its only prime
   ideal is `⊥`, and both contractions equal `⊥`.
6. The conversion from `Q = σ • P` to `comap (σ ⊗ id) Q = P` in `PrimeSpectrum`: for the
   `MulSemiringAction` of a group, `σ • P = comap σ⁻¹ P = map σ P`, and `comap` of the
   automorphism `σ ⊗ id` is a bijection inverse to `comap (σ⁻¹ ⊗ id)`.
-/

-- The `K`-algebra structure on `kbar ⊗[k] K` used in this file is the one coming from the
-- RIGHT tensor factor (`includeRight : K → kbar ⊗[k] K`), since the profinite transitivity
-- theorem is applied with base ring `A := K`. Mathlib provides it as
-- `Algebra.TensorProduct.rightAlgebra` but does not register it globally: on `A ⊗[R] A` it
-- would be a second `Algebra A` structure beside the global `Algebra.TensorProduct.leftAlgebra`
-- (`a ↦ a ⊗ 1`), and the two are different. It is activated here for the whole file, the
-- theorems after the namespace included, and only locally: importers keep `leftAlgebra` as the
-- default and activate `rightAlgebra` themselves where they want it.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Stacks.GaloisTensorAction

variable {k K kbar : Type*} [Field k] [Field K] [Field kbar]
  [Algebra k K] [Algebra k kbar] [IsGalois k kbar]

/-- The action of `σ ∈ Gal(kbar/k)` on `kbar ⊗[k] K` by `σ ⊗ id_K`, packaged as
a monoid homomorphism into the ring automorphism group of the tensor product.

SANITY CHECK PASSED (statement is a routine functoriality fact).
Proof strategy: `map_one'` and `map_mul'` are proved by `ext` + tensor-product
induction (`TensorProduct.induction_on` / the `tmul`/`add`/`zero` cases), where
each `tmul` case reduces to `AlgEquiv.refl`/composition of `AlgEquiv`s; close
with `simp [Algebra.TensorProduct.congr, Algebra.TensorProduct.map_tmul]` and
`rfl`.  (Verified in scratch that the `tmul` cases close by `simp; rfl` and the
`zero/add` cases by `simp`.) -/
noncomputable def galTensorAut :
    (kbar ≃ₐ[k] kbar) →* RingAut (kbar ⊗[k] K) where
  toFun σ := (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K))).toRingEquiv
  map_one' := by
    have h : Algebra.TensorProduct.congr (1 : kbar ≃ₐ[k] kbar) (AlgEquiv.refl (R := k) (A₁ := K))
        = AlgEquiv.refl := by
      rw [show (1 : kbar ≃ₐ[k] kbar) = AlgEquiv.refl from rfl]
      exact Algebra.TensorProduct.congr_refl
    rw [h]
    rfl
  map_mul' σ τ := by
    have h : Algebra.TensorProduct.congr (σ * τ) (AlgEquiv.refl (R := k) (A₁ := K))
        = (Algebra.TensorProduct.congr τ (AlgEquiv.refl (R := k) (A₁ := K))).trans
            (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K))) := by
      rw [← Algebra.TensorProduct.congr_trans]
      rfl
    rw [h]
    rfl

/-- The `MulSemiringAction` of `Gal(kbar/k)` on `kbar ⊗[k] K` induced by
`galTensorAut` (compose the canonical action of `RingAut` with `galTensorAut`).

SANITY CHECK PASSED (definitional / standard builder).
Proof strategy: `MulSemiringAction.compHom (kbar ⊗[k] K) galTensorAut`, using the
canonical `MulSemiringAction (RingAut (kbar ⊗[k] K)) (kbar ⊗[k] K)`. -/
noncomputable instance galTensorAction :
    MulSemiringAction (kbar ≃ₐ[k] kbar) (kbar ⊗[k] K) :=
  MulSemiringAction.compHom (kbar ⊗[k] K) (galTensorAut (k := k) (K := K) (kbar := kbar))

omit [IsGalois k kbar] in
/-- Unfolding lemma: the `galTensorAction` smul is `σ ⊗ id_K`.

SANITY CHECK PASSED (definitional unfolding of `compHom`/`galTensorAut`).
Proof strategy: `rfl` after unfolding `galTensorAction`, `MulSemiringAction.compHom`,
`galTensorAut`; equivalently `simp [galTensorAction, MulSemiringAction.compHom, galTensorAut]`. -/
theorem galTensorAction_smul (σ : kbar ≃ₐ[k] kbar) (x : kbar ⊗[k] K) :
    σ • x = Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K)) x :=
  rfl

/-- The Galois action and the `K`-scalar action on `kbar ⊗[k] K` commute, because
`σ ⊗ id_K` fixes the right (`K`) tensor factor.

SANITY CHECK PASSED (`σ ⊗ id` is `K`-linear by construction).
Proof strategy: `constructor; intro a σ x`; rewrite both smuls with
`galTensorAction_smul`, note `a • x = (1 ⊗ a) * x` (the `K`-algebra structure on
`kbar ⊗[k] K` is via the right factor: `algebraMap K _ a = 1 ⊗ₜ a`), use
`map_mul` of the ring hom `σ ⊗ id` and that it fixes `1 ⊗ₜ a`
(`Algebra.TensorProduct.congr_tmul` with `AlgEquiv.refl`). -/
instance smulCommClass_K : SMulCommClass (kbar ≃ₐ[k] kbar) K (kbar ⊗[k] K) := by
  constructor
  intro σ a x
  simp only [galTensorAction_smul, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- The invariant subring of `kbar ⊗[k] K` under `Gal(kbar/k)` is `K`: every
`G`-invariant element comes from `K`.  This is the substantive algebraic content
of Stacks 04KP (the statement `K = (kbar ⊗[k] K)^{Gal(kbar/k)}`).

SANITY CHECK PASSED (true: this is the Galois-descent fixed-point statement).
Rigorous argument: Let `t ∈ kbar ⊗[k] K` be `G`-invariant.  Choosing a `k`-basis
`(eᵢ)` of `K`, write `t = Σ xᵢ ⊗ eᵢ` uniquely with `xᵢ ∈ kbar` (almost all `0`);
`σ • t = Σ σ(xᵢ) ⊗ eᵢ`, and by uniqueness of the representation `σ • t = t` for
all `σ ∈ G` forces `σ(xᵢ) = xᵢ` for all `σ, i`.  Since `kbar/k` is a (separable
algebraic) closure with `IsGalois k kbar`, the fixed field `(kbar)^{Gal} = k`
(`IsGalois`/`fixedField` is `⊥`); hence each `xᵢ ∈ k`, so
`t = Σ xᵢ ⊗ eᵢ = 1 ⊗ (Σ xᵢ eᵢ) ∈ algebraMap K (kbar ⊗[k] K) '' K` (using
`xᵢ ⊗ eᵢ = 1 ⊗ (xᵢ • eᵢ)` for `xᵢ ∈ k`).  Thus `t` is in the image of `K`.
Mathlib ingredients: `IsGalois.tower_top_intermediateField_fixedField` /
`IsGalois.fixedField_bot` (fixed field of the whole group is `k`),
`Algebra.TensorProduct.basis`/`Basis.tensorProduct` for the unique
representation, and `Algebra.TensorProduct` left/right factor lemmas. -/
instance tensor_isInvariant :
    Algebra.IsInvariant K (kbar ⊗[k] K) (kbar ≃ₐ[k] kbar) := by
  rw [Algebra.isInvariant_iff]
  intro t ht
  set ι := Module.Basis.ofVectorSpaceIndex k K
  set b : Module.Basis ι k K := Module.Basis.ofVectorSpace k K
  set B := Algebra.TensorProduct.basis kbar (R := k) (M := K) b
  have hBapply : ∀ i, B i = 1 ⊗ₜ[k] b i := fun i => Algebra.TensorProduct.basis_apply b i
  set c := B.repr t
  -- For each `σ` and basis index `i`, the `i`-th coordinate of `σ ⊗ id` applied
  -- to `t` is `σ` applied to the `i`-th coordinate of `t`.
  have key : ∀ (σ : kbar ≃ₐ[k] kbar) (i : ι),
      B.repr (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K)) t) i = σ (c i) := by
    intro σ i
    have h1 : ∀ (j : ι) (a : kbar),
        Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K)) (a • B j) = σ a • B j := by
      intro j a
      rw [hBapply, ← TensorProduct.tmul_eq_smul_one_tmul]
      simp [← TensorProduct.tmul_eq_smul_one_tmul]
    conv_lhs =>
      rw [← B.linearCombination_repr t, Finsupp.linearCombination_apply, map_finsuppSum]
    simp_rw [h1]
    rw [map_finsuppSum]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single i]
    · rw [Finsupp.single_eq_same]
    · exact fun j _ hj ↦ Finsupp.single_eq_of_ne (Ne.symm hj)
    · intro _
      simp
  -- Invariance forces every coordinate to be fixed by all of `Gal(kbar/k)`.
  have hfixed : ∀ i, ∀ σ : kbar ≃ₐ[k] kbar, σ (c i) = c i := by
    intro i σ
    have heq : Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K)) t = t := by
      rw [← galTensorAction_smul]
      exact ht σ
    rw [← key σ i, heq]
  -- A fully-fixed element of `kbar` lies in `k` (Galois descent on the closure).
  have hmem : ∀ i, ∃ y : k, algebraMap k kbar y = c i := by
    intro i
    have hbot : c i ∈ (⊥ : IntermediateField k kbar) :=
      (InfiniteGalois.mem_bot_iff_fixed (c i)).mpr (hfixed i)
    rwa [IntermediateField.mem_bot, Set.mem_range] at hbot
  choose y hy using hmem
  -- The descent: `t = 1 ⊗ₜ (Σ yᵢ • bᵢ)` is in the image of `K`.
  refine ⟨c.sum (fun i _ => y i • b i), ?_⟩
  rw [Algebra.TensorProduct.right_algebraMap_apply,
    show (1 : kbar) ⊗ₜ[k] (c.sum (fun i _ => y i • b i))
      = c.sum (fun i _ => (1 : kbar) ⊗ₜ[k] (y i • b i)) from ?_]
  · rw [← B.linearCombination_repr t, Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro i _
    rw [hBapply, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        ← Algebra.algebraMap_eq_smul_one, hy i, smul_eq_mul, mul_one]
  · rw [Finsupp.sum, TensorProduct.tmul_sum]
    rfl

/-- `kbar ⊗[k] K` carries the discrete topology (chosen, as required by the
profinite transitivity lemma). -/
instance : TopologicalSpace (kbar ⊗[k] K) := ⊥

/-- The topology chosen on `kbar ⊗[k] K` is indeed discrete. -/
instance : DiscreteTopology (kbar ⊗[k] K) := ⟨rfl⟩

/-- The Galois action of `Gal(kbar/k)` (Krull topology) on the discrete ring
`kbar ⊗[k] K` is continuous.

SANITY CHECK PASSED (standard: continuity of a profinite action on a discrete
module/ring whose elements have open stabilizers).
Rigorous argument: With `B` discrete, `ContinuousSMul G B` is equivalent to: for
each `x ∈ B` the stabilizer `{σ | σ • x = x}` is open in `G` (then `(σ,x) ↦ σ•x`
is locally constant).  Every `x ∈ kbar ⊗[k] K` is a finite sum of pure tensors
`Σ aⱼ ⊗ bⱼ`, hence lies in `L ⊗[k] K` for a finite subextension
`L = k(a₁,…,aₙ) ⊆ kbar` (finite since `kbar/k` is algebraic).  The open subgroup
`Gal(kbar/L)` (a basic open of the Krull topology, `krullTopology`) fixes `L`
pointwise, hence fixes each `aⱼ ⊗ bⱼ` and so fixes `x`; thus the stabilizer of
`x` contains an open subgroup and is open.  Mathlib ingredients: the Krull
topology's neighborhood basis of `1` by `Gal(kbar/L)` for finite `L`
(`krullTopology`, `IntermediateField.fixingSubgroup`,
`IntermediateField.fixingSubgroup_isOpen`), `continuousSMul_of_...` / the
discrete-codomain criterion (`continuous_of_discreteTopology`-style:
`ContinuousSMul` via `IsOpen` stabilizers). -/
instance continuousSMul_gal :
    ContinuousSMul (kbar ≃ₐ[k] kbar) (kbar ⊗[k] K) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  -- It suffices to show each stabilizer is open.  We induct on the tensor `x`.
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      -- `a` is integral over `k`, so `L = k(a)` is a finite intermediate field,
      -- whose fixing subgroup is open and contained in the stabilizer.
      set L : IntermediateField k kbar := IntermediateField.adjoin k {a}
      have : FiniteDimensional k L :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral k a)
      have hsub : (L.fixingSubgroup : Set (kbar ≃ₐ[k] kbar))
          ⊆ (MulAction.stabilizer (kbar ≃ₐ[k] kbar) (a ⊗ₜ[k] b) : Set (kbar ≃ₐ[k] kbar)) := by
        intro σ hσ
        rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
        have ha : σ a = a := hσ a (IntermediateField.mem_adjoin_simple_self k a)
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, galTensorAction_smul]
        simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        congr 1
      exact Subgroup.isOpen_of_openSubgroup _
        (U := ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩) hsub
  | add x y hx hy =>
      -- The stabilizer of `x + y` contains `stab x ⊓ stab y`, an open subgroup.
      have hsub : ((MulAction.stabilizer (kbar ≃ₐ[k] kbar) x
            ⊓ MulAction.stabilizer (kbar ≃ₐ[k] kbar) y : Subgroup (kbar ≃ₐ[k] kbar)) :
            Set (kbar ≃ₐ[k] kbar))
          ⊆ (MulAction.stabilizer (kbar ≃ₐ[k] kbar) (x + y) : Set (kbar ≃ₐ[k] kbar)) := by
        intro σ hσ
        rw [SetLike.mem_coe, Subgroup.mem_inf] at hσ
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_add,
          (MulAction.mem_stabilizer_iff).mp hσ.left, (MulAction.mem_stabilizer_iff).mp hσ.right]
      refine Subgroup.isOpen_of_openSubgroup _
        (U := ⟨_, ?_⟩) hsub
      exact (⟨_, hx⟩ : OpenSubgroup _).isOpen.inter (⟨_, hy⟩ : OpenSubgroup _).isOpen

end Stacks.GaloisTensorAction

open Stacks.GaloisTensorAction in
-- needed: this proof's `obtain`/`rcases` on
-- `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` needs the `MulSemiringAction`
-- instance found up to non-transparent unfolding of `kbar ⊗[k] K`.
set_option backward.isDefEq.respectTransparency false in
/-- Statement 1 (Stacks Tag 04KP). The Galois group `Gal(kbar/k)` of a Galois extension
`kbar/k` acts transitively on the primes of `kbar ⊗[k] K`: for every pair of prime ideals
`P, Q` there exists `σ ∈ Gal(kbar/k)` whose induced map on the prime spectrum
(via `comap` of `σ ⊗ id_K`) carries `Q` to `P`. A separable algebraic closure of `k`, the case
the source states, is Galois over `k`. -/
@[stacks 04KP, sga "1 V 1.1" "(ii), special case"]
theorem gal_acts_transitively_on_primes_of_isGalois
    {k K kbar : Type*}
    [Field k] [Field K] [Field kbar]
    [Algebra k K] [Algebra k kbar] [IsGalois k kbar] :
    ∀ (P Q : PrimeSpectrum (kbar ⊗[k] K)),
      ∃ σ : kbar ≃ₐ[k] kbar,
        PrimeSpectrum.comap
          (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ :=
              K))).toAlgHom.toRingHom Q = P := by
  -- `kbar/k` is Galois, giving the compact, totally-disconnected, topological-group
  -- Krull topology on `G := kbar ≃ₐ[k] kbar`.
  intro P Q
  -- Both primes of `kbar ⊗[k] K` contract to the unique prime `⊥` of the field `K`.
  -- Proof strategy: `Ideal.under K P` and `Ideal.under K Q` are prime ideals of the
  -- field `K`; the only prime ideal of a field is `⊥` (`Ideal.IsPrime` on a field ⇒
  -- `= ⊥`, e.g. via `Ideal.eq_bot_of_prime`/`Subsingleton`-of-`maximalIdeal`); hence
  -- both equal `⊥`.  Provide as a `have`.
  have hunder : Ideal.under K P.asIdeal = Ideal.under K Q.asIdeal :=
    (Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm
  -- Apply the Mathlib profinite transitivity theorem with `A := K`, `G := Gal(kbar/k)`.
  -- It yields `σ` with `Q.asIdeal = σ • P.asIdeal`.
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := K) (G := kbar ≃ₐ[k] kbar) P.asIdeal Q.asIdeal hunder
  refine ⟨σ, ?_⟩
  -- Convert `Q.asIdeal = σ • P.asIdeal` into the `comap`-form goal.
  -- `comap`/`map` of the underlying ring automorphism).
  -- Rigorous argument: by `Ideal.pointwise_smul_eq_comap`,
  --   `σ • P.asIdeal = Ideal.comap (RingEquiv.symm (galTensorAut σ)) P.asIdeal`,
  -- and `galTensorAut σ = (congr σ refl).toRingEquiv`, whose `comap` (as a
  -- `PrimeSpectrum.comap`) is the bijection induced by `σ ⊗ id`.  Unfolding
  -- `PrimeSpectrum.comap` to ideal `comap`, the goal
  --   `PrimeSpectrum.comap (congr σ refl).toRingHom Q = P`
  -- is `Ideal.comap (congr σ refl) Q.asIdeal = P.asIdeal`.  Rewriting `Q.asIdeal`
  -- with `hσ` and `galTensorAction_smul`, this becomes
  --   `Ideal.comap (congr σ refl) (Ideal.comap (congr σ refl).symm P.asIdeal) = P.asIdeal`,
  -- which is `Ideal.comap_comap` + `RingEquiv`-`symm` cancellation
  -- (`Ideal.comap_coe_symm_comp`/`RingHom.comp` with `RingEquiv.symm_comp`), i.e.
  -- `comap (e ∘ e.symm) = comap id = id`.  Conclude with `PrimeSpectrum.ext`.
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, hσ]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hφ : (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ := K))).toAlgHom.toRingHom x
      = σ • x := (galTensorAction_smul σ x).symm
  rw [hφ, inv_smul_smul]

/-- The automorphism group of a normal algebraic extension `kbar/k` acts transitively on the
primes of `kbar ⊗[k] K`, for an arbitrary extension of fields `K/k`: for every pair of prime
ideals `P, Q` there is a `k`-automorphism `σ` of `kbar` whose induced map on the prime spectrum
(via `comap` of `σ ⊗ id_K`) carries `Q` to `P`.

Normality is not a convenience of the proof. For `k = ℚ`, `kbar = K = ℚ(2 ^ (1 / 3))` the group
`kbar ≃ₐ[k] kbar` is trivial while `kbar ⊗[k] K` has two primes, with residue fields of degrees
`1` and `2` over `K`, so no group of automorphisms of `kbar` over `k` can be transitive on them.

Separability, on the other hand, is not needed: `kbar` is purely inseparable over the separable
closure `ks` of `k` in it, so `Spec (kbar ⊗[k] K) ⟶ Spec (ks ⊗[k] K)` is a homeomorphism, and
every `k`-automorphism of `ks` extends to one of `kbar` because `kbar/k` is normal. -/
@[sga "1 V 1.1" "(ii), special case"]
theorem gal_acts_transitively_on_primes_of_normal
    {k K kbar : Type*}
    [Field k] [Field K] [Field kbar]
    [Algebra k K] [Algebra k kbar] [Normal k kbar] :
    ∀ (P Q : PrimeSpectrum (kbar ⊗[k] K)),
      ∃ σ : kbar ≃ₐ[k] kbar,
        PrimeSpectrum.comap
          (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := k) (A₁ :=
              K))).toAlgHom.toRingHom Q = P := by
  intro P Q
  -- The structure map of `kbar ⊗[k] K` over `ks ⊗[k] K`, for `ks` the separable closure of
  -- `k` in `kbar`.
  let u : (↥(separableClosure k kbar) ⊗[k] K) →ₐ[↥(separableClosure k kbar)] (kbar ⊗[k] K) :=
    Algebra.TensorProduct.map
      (Algebra.ofId ↥(separableClosure k kbar) kbar) (AlgHom.id k K)
  have hu : IsHomeomorph (PrimeSpectrum.comap u.toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      ↥(separableClosure k kbar) k K kbar
  obtain ⟨σ₀, hσ₀⟩ :=
    gal_acts_transitively_on_primes_of_isGalois (k := k) (K := K)
      (kbar := ↥(separableClosure k kbar))
      (PrimeSpectrum.comap u.toRingHom P) (PrimeSpectrum.comap u.toRingHom Q)
  refine ⟨σ₀.liftNormal kbar, hu.bijective.injective ?_⟩
  -- `σ₀ ⊗ id_K` and its extension `(σ₀.liftNormal kbar) ⊗ id_K` agree through `u`.
  have hcomm :
      (Algebra.TensorProduct.congr (σ₀.liftNormal kbar)
            (AlgEquiv.refl (R := k) (A₁ := K))).toAlgHom.toRingHom.comp u.toRingHom =
        u.toRingHom.comp (Algebra.TensorProduct.congr σ₀
          (AlgEquiv.refl (R := k) (A₁ := K))).toAlgHom.toRingHom := by
    refine RingHom.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
        simpa [u, Algebra.ofId_apply] using
          congrArg (fun y : kbar ↦ y ⊗ₜ[k] b)
            (AlgEquiv.liftNormal_commutes σ₀ kbar a)
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (congrArg (fun f => PrimeSpectrum.comap f Q) hcomm).trans hσ₀
