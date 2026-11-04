module

import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat

public import StacksFrontier.RingTheory.Spectrum.Prime.Codimension

@[expose] public section

/-!
# Krull dimension is unchanged by base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type and let `K/k` be a field extension.
This file proves that `S` and its base change `T = K ⊗_k S` have the same Krull dimension
(Stacks 00P3).

The argument is the source's. Noether normalization (Lemma 00OY) produces a natural number
`r = dim S`, elements `y : Fin r → S` and an injective finite `k`-algebra map
`k[Y_1, …, Y_r] → S`, `Y_i ↦ y_i`. Base changing along `k → K` turns the polynomial ring into
`K[Y_1, …, Y_r]` and `S` into `T`, and the base changed map `K[Y_1, …, Y_r] → T` is again
injective and integral, so Krull dimension is invariant along it (Lemma 00OK) and
`dim T = dim K[Y_1, …, Y_r] = r = dim S`.

## Main results

* `Stacks.KrullDimension.FieldBaseChange.solution`: the statement of Stacks 00P3.

## Implementation notes

Three properties of a ring map ascend along a base change `S' = S ⊗_R R'`, and Mathlib has only the
first: integrality (`Algebra.IsPushout.isIntegral'`), flatness
(`Stacks.KrullDimension.FieldBaseChange.flat_of_isPushout`, which is `Module.Flat.isBaseChange`
read through `Algebra.IsPushout.out`) and injectivity
(`Stacks.KrullDimension.FieldBaseChange.faithfulSMul_of_isPushout`, which needs `S` flat over `R`;
this is where the source's "since `K` is flat over `k`" is used). The last two together with Lemma
00OK give `Stacks.KrullDimension.FieldBaseChange.ringKrullDim_eq_of_isPushout`: `dim S = dim S'`
when `R → R'` is injective and integral and `S` is flat over `R`.

The mathematics of the source's proof is
`Stacks.KrullDimension.FieldBaseChange.ringKrullDim_eq_natCard_of_aeval_injective_finite`: if
`y : σ → S` normalizes `S` over `k`, in the sense that `k[X_i : i ∈ σ] → S`, `X_i ↦ y i`, is
injective and finite, then any base change `T = K ⊗_k S` along a flat map to a field has
`dim T = #σ`. Neither `k` a field (only `K` flat over `k`) nor `S` of finite type is needed, and
this is stronger than the equality `dim S = dim T` on its own, since Lemma 00OY delivers
`dim S = #σ` outright.

Pushout squares are used rather than `TensorProduct`, so that the polynomial ring
`K[X_i : i ∈ σ]` need not be transported across the isomorphism `k[X_i] ⊗_k K`: the square
`k[X_i] → S`, `K[X_i] → T` is a pushout square by `Algebra.IsPushout.comp_iff` applied to the
square `k → K`, `k[X_i] → K[X_i]`, which is an instance in
`Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`. The only step of that identification with
content is that the two ways around the square `k[X_i] → S → T`, `k[X_i] → K[X_i] → T` agree,
which is `MvPolynomial.aeval_map_algebraMap` followed by `MvPolynomial.aeval_algebraMap_apply`.

The degenerate case `S = 0` is not covered by Lemma 00OY, which needs `Nontrivial S`, and is
treated separately: `S = 0` forces `T = 0` and both dimensions are `⊥`.

## References

* [StacksProject 00P3](https://stacks.math.columbia.edu/tag/00P3)
* [StacksProject 00OY](https://stacks.math.columbia.edu/tag/00OY)
* [StacksProject 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/


namespace Stacks.KrullDimension.FieldBaseChange

open MvPolynomial

section IsPushout

/- A pushout square of commutative rings
```
R  →  S
↓     ↓
R' →  S'
```
that is, `S' = S ⊗[R] R'`. -/
variable (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
  [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'] [IsScalarTower R S S']
  [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S']

/-- Flatness ascends along a base change: if `S' = S ⊗[R] R'` and `R'` is flat over `R`, then
`S'` is flat over `S`. -/
private theorem flat_of_isPushout [Module.Flat R R'] : Module.Flat S S' :=
  Module.Flat.isBaseChange R S R' S' Algebra.IsPushout.out

/-- Injectivity ascends along a flat base change: if `S' = S ⊗[R] R'` with `R → R'` injective
and `S` flat over `R`, then `S → S'` is injective. -/
private theorem faithfulSMul_of_isPushout [Module.Flat R S] [FaithfulSMul R R'] :
    FaithfulSMul S S' :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr fun a b hab ↦
    Algebra.TensorProduct.includeLeft_injective (S := R)
        (FaithfulSMul.algebraMap_injective R R') <| by
      simpa using congrArg (Algebra.IsPushout.equiv R S R' S').symm hab

/-- Krull dimension is unchanged by a flat base change of an injective integral ring map: if
`S' = S ⊗[R] R'` with `R → R'` injective and integral and `S` flat over `R`, then `S` and `S'`
have the same Krull dimension. -/
private theorem ringKrullDim_eq_of_isPushout [Module.Flat R S] [FaithfulSMul R R']
    [Algebra.IsIntegral R R'] :
    ringKrullDim S = ringKrullDim S' :=
  have : Algebra.IsIntegral S S' :=
    Algebra.IsPushout.isIntegral' (R := R) (A := S) (S := R') (SA := S')
  have : FaithfulSMul S S' := faithfulSMul_of_isPushout R S R' S'
  Algebra.IsIntegral.ringKrullDim_eq S S'

end IsPushout

/-- **Base change of a Noether normalization.** Let `K` be a field, flat over a commutative ring
`k`, let `S` be a `k`-algebra and let `T = K ⊗_k S` be its base change. If finitely many elements
`y : σ → S` normalize `S`, that is, the `k`-algebra map `k[X_i : i ∈ σ] → S`, `X_i ↦ y i`, is
injective and makes `S` a finite module, then `T` has Krull dimension the number of variables. -/
private theorem ringKrullDim_eq_natCard_of_aeval_injective_finite {σ : Type*} [Finite σ]
    (k K S T : Type*) [CommRing k] [Field K] [CommRing S] [CommRing T] [Algebra k K] [Algebra k S]
    [Algebra k T] [Algebra K T] [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T]
    [Algebra.IsPushout k K S T] [Module.Flat k K] {y : σ → S}
    (hinj : Function.Injective (aeval y : MvPolynomial σ k →ₐ[k] S))
    (hfin : (aeval y : MvPolynomial σ k →ₐ[k] S).Finite) :
    ringKrullDim T = Nat.card σ := by
  -- the normalization of `S` and its base change to `K`, as algebra structures
  let _ : Algebra (MvPolynomial σ k) (MvPolynomial σ K) := MvPolynomial.algebraMvPolynomial
  let _ : Algebra (MvPolynomial σ k) S := (aeval y : MvPolynomial σ k →ₐ[k] S).toRingHom.toAlgebra
  let _ : Algebra (MvPolynomial σ K) T :=
    (aeval fun i ↦ algebraMap S T (y i) : MvPolynomial σ K →ₐ[K] T).toRingHom.toAlgebra
  let _ : Algebra (MvPolynomial σ k) T :=
    ((algebraMap (MvPolynomial σ K) T).comp
      (algebraMap (MvPolynomial σ k) (MvPolynomial σ K))).toAlgebra
  have : IsScalarTower (MvPolynomial σ k) (MvPolynomial σ K) T := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K (MvPolynomial σ K) T :=
    .of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k (MvPolynomial σ K) T :=
    .of_algebraMap_eq fun a ↦ by
      simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  -- the two ways round the square `k[X_i] → S → T`, `k[X_i] → K[X_i] → T` agree
  have : IsScalarTower (MvPolynomial σ k) S T := .of_algebraMap_eq fun x ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact (aeval_map_algebraMap K _ x).trans (aeval_algebraMap_apply (B := T) y x)
  -- so the right-hand square of `k → k[X_i] → S`, `K → K[X_i] → T` is again a pushout square
  have : Algebra.IsPushout (MvPolynomial σ k) (MvPolynomial σ K) S T :=
    .symm ((Algebra.IsPushout.comp_iff k (MvPolynomial σ k) K (MvPolynomial σ K)).mp
      (Algebra.IsPushout.symm ‹Algebra.IsPushout k K S T›))
  have : Module.Finite (MvPolynomial σ k) S := hfin
  have : Algebra.IsIntegral (MvPolynomial σ k) S := .of_finite _ _
  have : FaithfulSMul (MvPolynomial σ k) S :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr
      (by simpa [RingHom.algebraMap_toAlgebra] using hinj)
  have : Module.Flat (MvPolynomial σ k) (MvPolynomial σ K) :=
    flat_of_isPushout k (MvPolynomial σ k) K (MvPolynomial σ K)
  rw [← ringKrullDim_eq_of_isPushout (MvPolynomial σ k) (MvPolynomial σ K) S T,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- **Stacks 00P3.** Let `k` be a field, let `S` be a `k`-algebra of finite type and let `K/k` be
a field extension. Then `S` and its base change `T = K ⊗_k S` have the same Krull dimension. -/
public theorem solution (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] :
    ringKrullDim S = ringKrullDim T := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have := Module.subsingleton S T
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k S).FG)
  obtain ⟨r, y, -, hinj, hfin, hdim⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top k (s := (s : Set S))
      s.finite_toSet hs
  rw [hdim, ringKrullDim_eq_natCard_of_aeval_injective_finite k K S T hinj hfin]
  simp

end Stacks.KrullDimension.FieldBaseChange

end

/-!
# Krull dimension is unchanged by base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type and let `K/k` be a field extension.
Then `dim S = dim (K ⊗_k S)`, where `dim` is the Krull dimension, the supremum of the lengths of
chains of prime ideals (Stacks 00P3).

The source's proof: Noether normalization (Lemma 00OY) produces `d = dim S` and a finite injective
`k`-algebra map `k[y_1, …, y_d] → S`. Since `K` is flat over `k` — every module over a field is
free — base change preserves both injectivity and module-finiteness, so
`K[y_1, …, y_d] → K ⊗_k S` is again finite and injective, and Krull dimension is invariant along an
injective integral map (Lemma 00OK). Hence `dim (K ⊗_k S) = dim K[y_1, …, y_d] = d = dim S`.

## Main results

* `Algebra.IsPushout.ringKrullDim_eq`: a finite type algebra over a field and its base change
  along a field extension have the same Krull dimension.

## Implementation notes

The base change is an arbitrary pushout square of `k`-algebras, `Algebra.IsPushout k K S T`, rather
than the construction `K ⊗[k] S`. The source's literal form is recovered by `inferInstance` once
`Algebra.TensorProduct.rightAlgebra` is a local instance, and a base change already presented in
another shape — a quotient `K[x_1, …, x_n]/(I · K[x_1, …, x_n])` of a polynomial ring, as the
neighbouring Lemma 00P4 and the proof of Lemma 00SS present it — is covered with no intermediate
isomorphism. What the instance asserts is exactly that the canonical `K`-algebra map `K ⊗_k S → T`
built from `algebraMap K T` and `algebraMap S T` is an isomorphism, so `T` is the source's
`K ⊗_k S` together with its two structure maps.

A field extension `K/k` is `[Field K] [Algebra k K]`; no injectivity hypothesis on `algebraMap k K`
is needed, since a ring map out of a field into a nonzero ring is injective.

`ringKrullDim` takes values in `WithBot ℕ∞`, with `⊥` for the zero ring and `⊤` for infinite
dimension, so neither a nontriviality nor a finiteness hypothesis is needed and the degenerate case
is covered: `S = 0` forces `T = 0` and both sides are `⊥`. The equality is oriented as in the
source, `dim S = dim (K ⊗_k S)`.

Faithfulness. (1) No hypothesis is idle. `Algebra.FiniteType k S` is essential: for `k = ℚ` and
`K = S = ℚ(t)` one has `dim S = 0` while `dim (ℚ(t) ⊗_ℚ ℚ(t)) = 1`, the kernel of the
multiplication map being a nonzero prime. `Field K` is essential: for `K = k[t]` the base change is
`S[t]`, of dimension `dim S + 1`. `Field k` is essential — it is what makes `K` flat over `k` and
Noether normalization available: over `k = ℤ` with `K = ℚ` and `S = ℤ`, `dim S = 1` while
`ℚ ⊗_ℤ ℤ = ℚ` has dimension `0`. (2) The scalars and the base are the source's: the pushout square
is taken over `k`, both scalar towers are over `k`, the finite type hypothesis is on `S` over `k`
and not over `K`, and the two dimensions are those of `S` and of `T` themselves. (3) The object the
source names, `K ⊗_k S`, is pinned by the pushout instance, which fixes `T` together with the two
structure maps `algebraMap K T` and `algebraMap S T` up to the unique `k`-algebra isomorphism
compatible with them; the conclusion is an equality of dimensions, not an existence statement.
(4) The instantiation is not degenerate: for `k = ℚ`, `K = ℂ` and `S = ℚ[x, y]/(x ^ 2 + y ^ 2)` the
base change is `T = ℂ[x, y]/(x ^ 2 + y ^ 2)`, and `dim S = dim T = 1` with both sides a natural
number rather than `⊥` or `⊤`, even though `x ^ 2 + y ^ 2` is irreducible over `ℚ` and factors as
`(x + i y)(x - i y)` over `ℂ`, so that the base change genuinely changes the ring.

## References

* [StacksProject 00P3](https://stacks.math.columbia.edu/tag/00P3)
* [StacksProject 00OY](https://stacks.math.columbia.edu/tag/00OY)
* [StacksProject 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/


/-- **Stacks 00P3.** Let `k` be a field, let `S` be a `k`-algebra of finite type and let `K/k` be a
field extension. Then `S` and its base change `T = K ⊗_k S` have the same Krull dimension. -/
@[stacks 00P3 "The base change `K ⊗_k S` is an arbitrary pushout square of `k`-algebras
`Algebra.IsPushout k K S T`; the source's literal form is `inferInstance` once
`Algebra.TensorProduct.rightAlgebra` is a local instance. See the module docstring."]
public theorem Algebra.IsPushout.ringKrullDim_eq (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] :
    ringKrullDim S = ringKrullDim T :=
  Stacks.KrullDimension.FieldBaseChange.solution k K S T


/-!
# Local dimension is unchanged by base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, let `K/k` be a
field extension, let `T = K ⊗_k S` and `X_K = Spec T`. Let `x_K ∈ X_K` be a point, with prime
`q_K`, and let `x ∈ X` be the point of the prime `q = q_K ∩ S` it lies over. This file proves
Stacks 00P4: `dim_x X = dim_{x_K} X_K`.

The source's proof, followed here: choose a presentation `S = k[x_1, …, x_n]/I`, base changed to
a presentation `T = K[x_1, …, x_n]/I·K[x_1, …, x_n]`, and let `q'`, `q_K'` be the primes of the
two polynomial rings under `q`, `q_K`. Both vertical arrows of the square
`k[x_1, …, x_n] → S`, `K[x_1, …, x_n] → T` are flat base changes along `k → K`, and they have the
same fibre rings, because the surjection of polynomial rings induces an isomorphism
`K[x_1, …, x_n] ⧸ q'·K[x_1, …, x_n] ≅ T ⧸ q·T`. So the going-down height formula (Lemma 00ON,
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) applied to both gives
`height q_K - height q = height q_K' - height q'`, and Lemma 00P2 turns each side into
`n - dim_x X`, resp. `n - dim_{x_K} X_K`, the local dimension of a polynomial ring over a field
being `n` at every point.

## Main results

* `Stacks.KrullDimension.LocalBaseChange.solution`: the equality of Stacks 00P4.

## Implementation notes

The argument is factored so that the presentation is chosen only once, in `solution`: the
private lemma `localKrullDim_comap_eq_of_presentation` takes an arbitrary pair of flat base
change squares `k → K`, `P → P_K` and `S → T` together with compatible surjections `P ↠ S`,
`P_K ↠ T` whose kernels correspond, and `solution` supplies
`P = k[x_1, …, x_n]`, `P_K = K ⊗_k P`. Of the two polynomial rings that lemma needs only that
they have the *same* Krull dimension, not that it is `n`, and that the two kernels correspond is
right exactness of `K ⊗_k -` (`Algebra.TensorProduct.lTensor_ker`), not flatness.

Three facts used here are not in Mathlib and are proved as private lemmas: for a finite type
domain over a field the local dimension is constant, equal to the Krull dimension
(`localKrullDim_eq_ringKrullDim`, from Lemmas 00OT and 00OS); that the two vertical arrows have
the same fibre ring, in the form that `q·T` pulls back to `q'·P_K`
(`comap_map_eq_map_comap_of_ker_eq_map`); and for a surjection of rings `f : A ↠ B` and ideals
`J`, `Q` of `B`, the height of the image of `Q` in `B ⧸ J` equals the height of the image of
`f⁻¹(Q)` in `A ⧸ f⁻¹(J)` (`height_map_quotient_comap_eq`).

## References

* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
-/


namespace Stacks.KrullDimension.LocalBaseChange

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Cancellation of a finite summand in `WithBot ℕ∞`. Neither `WithTop.add_right_cancel`, which
cancels in `ℕ∞` itself, nor `WithBot.add_right_cancel`, which needs a cancellative summand,
applies to `WithBot ℕ∞` on its own. -/
public lemma add_right_cancel_coe {x y : WithBot ℕ∞} {c : ℕ∞} (hc : c ≠ ⊤)
    (h : x + (c : WithBot ℕ∞) = y + (c : WithBot ℕ∞)) : x = y := by
  cases x <;> cases y <;> simp_all [← WithBot.coe_add, WithBot.coe_inj]

/-- For a domain of finite type over a field, the dimension at a point is the Krull dimension:
`Spec` is irreducible and all its maximal chains of primes have the same length. -/
private lemma localKrullDim_eq_ringKrullDim (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (x : PrimeSpectrum A) :
    TopologicalSpace.localKrullDim (PrimeSpectrum A) x = ringKrullDim A := by
  have key : ∀ m : Ideal A, m.IsMaximal → (m.height : WithBot ℕ∞) = ringKrullDim A :=
    fun m _ ↦ ((Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
      k A).1 m).symm
  rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k x).2]
  obtain ⟨m, hm, hle⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  exact le_antisymm ((iInf₂_le m ⟨hm, hle⟩).trans (key m hm).le)
    (le_iInf₂ fun n hn => (key n hn.1).ge)

/-- A base change of a field extension is flat: if `k → K`, `k → A`, `A → B` is a pushout square
of `k`-algebras with `k` a field, then `B` is a flat `A`-algebra. -/
private lemma flat_of_isPushout (k : Type*) [Field k] (K : Type*) [CommRing K] [Algebra k K]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra K B]
    [Algebra A B] [IsScalarTower k K B] [IsScalarTower k A B] [Algebra.IsPushout k K A B] :
    Module.Flat A B :=
  have h : Algebra.IsPushout k A K B := Algebra.IsPushout.symm ‹_›
  Module.Flat.isBaseChange (h := h.out)

/-- Two vertical arrows of a commuting square of rings have the same fibre ideals. Let
`u : P → P_K`, `v : S → T`, `φ : P ↠ S` and `ψ : P_K ↠ T` commute, with `φ` and `ψ` surjective
and `ker ψ` generated by `ker φ`. Then for every ideal `J` of `S` the extension `J·T` pulls back
along `ψ` to the extension `φ⁻¹(J)·P_K`; together with `height_map_quotient_comap_eq` this says
that `T ⧸ J·T` and `P_K ⧸ φ⁻¹(J)·P_K` are the same fibre ring. -/
private lemma comap_map_eq_map_comap_of_ker_eq_map {P PK S T : Type*} [CommRing P] [CommRing PK]
    [CommRing S] [CommRing T] {u : P →+* PK} {v : S →+* T} {φ : P →+* S} {ψ : PK →+* T}
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) (hsq : ψ.comp u = v.comp φ)
    (hker : RingHom.ker ψ = (RingHom.ker φ).map u) (J : Ideal S) :
    (J.map v).comap ψ = (J.comap φ).map u := by
  have h : ((J.comap φ).map u).map ψ = J.map v := by
    rw [Ideal.map_map, hsq, ← Ideal.map_map, Ideal.map_comap_of_surjective φ hφ]
  rw [← h, Ideal.comap_map_of_surjective ψ hψ, ← RingHom.ker_eq_comap_bot, hker, ← Ideal.map_sup,
    sup_eq_left.mpr (Ideal.comap_mono bot_le)]

/-- Heights of images in a quotient are unchanged by a surjection: for `f : A ↠ B` and ideals
`J`, `Q` of `B`, the image of `f⁻¹(Q)` in `A ⧸ f⁻¹(J)` has the same height as the image of `Q`
in `B ⧸ J`, because `f` induces an isomorphism `A ⧸ f⁻¹(J) ≅ B ⧸ J`. -/
private lemma height_map_quotient_comap_eq {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (J Q : Ideal B) :
    ((Q.comap f).map (Ideal.Quotient.mk (J.comap f))).height
      = (Q.map (Ideal.Quotient.mk J)).height := by
  have hkerg : RingHom.ker ((Ideal.Quotient.mk J).comp f) = J.comap f := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e : (A ⧸ J.comap f) ≃+* (B ⧸ J) := (Ideal.quotEquivOfEq hkerg.symm).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hf))
  have hmap : Ideal.map (e : (A ⧸ J.comap f) →+* (B ⧸ J))
      ((Q.comap f).map (Ideal.Quotient.mk (J.comap f))) = Q.map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_map,
      show (e : (A ⧸ J.comap f) →+* (B ⧸ J)).comp (Ideal.Quotient.mk (J.comap f))
        = (Ideal.Quotient.mk J).comp f from rfl,
      ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  exact (RingEquiv.height_map e _).symm.trans (congrArg Ideal.height hmap)

/-- Stacks 00P4 for a fixed pair of compatible presentations. Here `P → P_K` and `S → T` are two
flat base changes along the field extension `k → K`, `φ : P ↠ S` and `ψ : P_K ↠ T` are
compatible surjections whose kernels correspond, and `P` and `P_K` are domains of finite type
over `k`, resp. `K`, of the same Krull dimension -- the situation of a presentation
`S = k[x_1, …, x_n] ⧸ I` and its base change. -/
private lemma localKrullDim_comap_eq_of_presentation
    (k K S T P PK : Type*) [Field k] [Field K] [CommRing S] [CommRing T]
    [CommRing P] [CommRing PK]
    [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra k P] [Algebra k PK] [Algebra K PK] [Algebra P PK]
    [IsScalarTower k K PK] [IsScalarTower k P PK] [Algebra.IsPushout k K P PK]
    [Algebra.FiniteType k P] [Algebra.FiniteType K PK] [IsDomain P] [IsDomain PK]
    (hdim : ringKrullDim P = ringKrullDim PK)
    {φ : P →ₐ[k] S} (hφ : Function.Surjective φ)
    {ψ : PK →ₐ[K] T} (hψ : Function.Surjective ψ)
    (hsq : ψ.toRingHom.comp (algebraMap P PK) = (algebraMap S T).comp φ.toRingHom)
    (hker : RingHom.ker ψ.toRingHom = (RingHom.ker φ.toRingHom).map (algebraMap P PK))
    (xK : PrimeSpectrum T) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S)
        (PrimeSpectrum.comap (algebraMap S T) xK) =
      TopologicalSpace.localKrullDim (PrimeSpectrum T) xK := by
  have : Algebra.FiniteType k S := Algebra.FiniteType.of_surjective φ hφ
  have : Algebra.FiniteType K T := Algebra.FiniteType.of_surjective ψ hψ
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  have : IsNoetherianRing PK := Algebra.FiniteType.isNoetherianRing K PK
  have : Module.Flat S T := flat_of_isPushout k K S T
  have : Module.Flat P PK := flat_of_isPushout k K P PK
  have : Algebra.HasGoingDown S T := Algebra.HasGoingDown.of_flat
  have : Algebra.HasGoingDown P PK := Algebra.HasGoingDown.of_flat
  -- the prime `q_K'` of `P_K` lies over the prime `q'` of `P`
  have : (Ideal.comap ψ.toRingHom xK.asIdeal).LiesOver
      (Ideal.comap φ.toRingHom (Ideal.comap (algebraMap S T) xK.asIdeal)) := by
    refine ⟨?_⟩
    change Ideal.comap φ.toRingHom (Ideal.comap (algebraMap S T) xK.asIdeal)
      = Ideal.comap (algebraMap P PK) (Ideal.comap ψ.toRingHom xK.asIdeal)
    rw [Ideal.comap_comap, Ideal.comap_comap, hsq]
  have : xK.asIdeal.LiesOver (Ideal.comap (algebraMap S T) xK.asIdeal) := ⟨rfl⟩
  -- the going-down height formula on the two flat base changes
  have hON1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (Ideal.comap (algebraMap S T) xK.asIdeal) xK.asIdeal
  have hON2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (Ideal.comap φ.toRingHom (Ideal.comap (algebraMap S T) xK.asIdeal))
    (Ideal.comap ψ.toRingHom xK.asIdeal)
  -- the two vertical arrows have the same fibre ring, hence the same fibre height
  have hfib := height_map_quotient_comap_eq ψ.toRingHom hψ
    ((Ideal.comap (algebraMap S T) xK.asIdeal).map (algebraMap S T)) xK.asIdeal
  rw [comap_map_eq_map_comap_of_ker_eq_map hφ hψ hsq hker] at hfib
  -- Lemma 00P2 on the two rows, the polynomial rings having local dimension `dim P` everywhere
  have h2a := PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap
    k φ hφ (PrimeSpectrum.comap (algebraMap S T) xK)
  have h2b := PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap
    K ψ hψ xK
  rw [localKrullDim_eq_ringKrullDim k P] at h2a
  rw [localKrullDim_eq_ringKrullDim K PK, ← hdim] at h2b
  simp only [PrimeSpectrum.comap_asIdeal] at h2a h2b
  -- the two height formulas, subtracted: cancel the finite height of `q_K'`
  refine add_right_cancel_coe (c := (Ideal.comap ψ.toRingHom xK.asIdeal).height)
    Ideal.height_ne_top_of_isPrime ?_
  rw [← h2b, hON2, hfib, hON1, WithBot.coe_add, WithBot.coe_add, ← add_assoc, ← add_assoc, ← h2a]

/-- **Stacks 00P4.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `K/k` be a
field extension and let `T = K ⊗_k S` be the base change, presented as a pushout square. Let
`xK ∈ Spec T` be a point and let `x = comap (algebraMap S T) xK ∈ Spec S` be the point it lies
over. Then `Spec S` has the same dimension at `x` as `Spec T` has at `xK`. -/
public theorem solution (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (xK : PrimeSpectrum T) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S)
        (PrimeSpectrum.comap (algebraMap S T) xK) =
      TopologicalSpace.localKrullDim (PrimeSpectrum T) xK := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k S›
  have : Algebra.FiniteType K (K ⊗[k] MvPolynomial (Fin n) k) :=
    Algebra.FiniteType.equiv inferInstance (MvPolynomial.algebraTensorAlgEquiv k K).symm
  have : IsDomain (K ⊗[k] MvPolynomial (Fin n) k) :=
    MulEquiv.isDomain (MvPolynomial (Fin n) K)
      (MvPolynomial.algebraTensorAlgEquiv k K).toMulEquiv
  refine localKrullDim_comap_eq_of_presentation k K S T (MvPolynomial (Fin n) k)
    (K ⊗[k] MvPolynomial (Fin n) k) ?_ hφ
    (ψ := (Algebra.IsPushout.equiv k K S T).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id K K) φ)) ?_ ?_ ?_ xK
  · rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv]
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  · exact (Algebra.IsPushout.equiv k K S T).surjective.comp
      (Algebra.TensorProduct.map_surjective (AlgHom.id K K) φ Function.surjective_id hφ)
  · ext p <;>
      simp [Algebra.TensorProduct.right_algebraMap_apply, Algebra.IsPushout.equiv_tmul]
  · have hk : RingHom.ker
        ((Algebra.IsPushout.equiv k K S T).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K K) φ)).toRingHom
        = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) φ) := by
      exact RingHom.ker_comp_of_injective _ (Algebra.IsPushout.equiv k K S T).injective
    rw [hk, Algebra.TensorProduct.lTensor_ker φ hφ]
    rfl

end Stacks.KrullDimension.LocalBaseChange


/-!
# Local dimension is unchanged by base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `X = Spec S`, let `K/k` be a
field extension, let `S_K = K ⊗_k S` and `X_K = Spec S_K`. Let `q_K ⊆ S_K` be a prime, giving a
point `x_K ∈ X_K`, and let `q = q_K ∩ S` be the prime it lies over, giving `x ∈ X`. Then
$$
  \dim_x X = \dim_{x_K} X_K,
$$
the dimension of `X` at `x` is the dimension of `X_K` at `x_K` (Stacks 00P4). It is the local
counterpart of Lemma 00P3, `dim S = dim S_K`, and holds at every prime of `S_K` over `q`, however
the fibre over `q` is distributed.

The source's proof: present `S = k[x_1, …, x_n]/I`, so that
`S_K = K[x_1, …, x_n]/I·K[x_1, …, x_n]`, and let `q'`, `q_K'` be the primes of the two polynomial
rings under `q`, `q_K`. The square of local rings `k[x_1, …, x_n]_{q'} → S_q`,
`K[x_1, …, x_n]_{q_K'} → (S_K)_{q_K}` has flat vertical arrows — localizations of the flat maps
`S → S_K` and `k[x_1, …, x_n] → K[x_1, …, x_n]` — with the same fibre rings, so Lemma 00ON gives
`height q' - height q = height q_K' - height q_K`; Lemma 00P2 turns each side into `n - dim_x X`,
resp. `n - dim_{x_K} X_K`, since a polynomial ring has local dimension `n` everywhere.

## Main results

* `Algebra.IsPushout.localKrullDim_comap_eq`: the local dimensions of `Spec S` at `x` and of
  `Spec S_K` at `x_K` agree.

## Implementation notes

*`dim_x X` is `TopologicalSpace.localKrullDim`.* That definition is Definition 0055 (4) — the
infimum of `topologicalKrullDim U` over the open neighbourhoods `U` of `x` — with Mathlib's
`topologicalKrullDim` for the dimension of a space, the source's notion. A point and its prime
ideal are one datum, `x : PrimeSpectrum S` with `q = x.asIdeal`, rather than a prime together with
the assertion that `x` corresponds to it. Values lie in `WithBot ℕ∞`, so no finiteness or
nontriviality hypothesis is needed and the degenerate cases are covered.

*The base change is an arbitrary pushout square `Algebra.IsPushout k K S T`*, as in the sibling
00P3, rather than the construction `K ⊗[k] S`. The instance asserts exactly that the canonical
`K`-algebra map `K ⊗_k S → T` built from `algebraMap K T` and `algebraMap S T` is an isomorphism,
so `T` is the source's `S_K` together with its two structure maps, and the source's literal form is
recovered by `inferInstance` once `Algebra.TensorProduct.rightAlgebra` is a local instance. A base
change already presented in another shape — the quotient `K[x_1, …, x_n]/I·K[x_1, …, x_n]` of a
polynomial ring that the source's own proof uses — is then covered with no intermediate
isomorphism.

*"`q_K` lies over `q`" is `x = PrimeSpectrum.comap (algebraMap S T) xK`, taken as a definition
of `x` rather than as a hypothesis.* The bound point is the source's `x_K`, spelled `xK`, and `x`
is a term rather than a variable. The source's `x` is determined by `x_K` — its prime is
`q = q_K ∩ S` — so quantifying over `x_K` alone loses nothing and pins the correspondence; the map
along which the point is pushed is the structure map `S → S_K` of the base change, not `K → S_K`.
The statement is not about *some* prime over `q`: it holds for every one. That there is at least
one is not part of it; it follows from faithful flatness of `S → S_K`.

*No Noetherian hypothesis appears*, although the source's proof passes through Noetherian local
rings: a finite type algebra over a field is Noetherian, so `Algebra.FiniteType k S` already
supplies it for `S`, and `T` is of finite type over `K` because finite type is stable under base
change.

Faithfulness. (1) No hypothesis is idle: `Algebra.FiniteType k S` is essential — for `k = ℚ`,
`K = S = ℚ(t)` and `T = ℚ(t) ⊗_ℚ ℚ(t)`, `Spec S` is a point, so the left side is `0`, while `T` is
a one-dimensional domain (the prime `(t' - t)` has height one) and the right side is `1` at every
point; `Field K` is essential — for `K = T = k[t]` and `S = k`, at the generic point `x_K = ⊥` of
`Spec k[t]` the right side is `1` while `Spec S` is a point and the left side is `0`; `Field k` is
essential, being what makes `K` flat over `k` — for `k = S = ℤ` and `K = T = ℚ` the right side is
`0` while the left side, the local dimension of `Spec ℤ` at `comap _ x_K = ⊥`, is `1`; and `x_K`
occurs on both sides, through `comap` on the left. (2) The scalars and base are the source's: the
pushout square is over `k`, both scalar towers are over `k`, the finite type hypothesis is on `S`
over `k` and not on `T` over `K`, the two local dimensions are those of `Spec S` and `Spec T`
themselves, and the point correspondence is along `algebraMap S T`. (3) The canonical maps are
pinned, not merely asserted to exist: `T` is fixed by the pushout instance together with
`algebraMap K T` and `algebraMap S T` up to the unique `k`-algebra isomorphism compatible with
them, `x` is `comap (algebraMap S T) xK` rather than an unnamed prime under `q_K`, and the
conclusion is an equality of the two local dimensions. (4) The instantiation is not degenerate: for
`k = ℚ`, `K = ℂ`, `S = ℚ[X, Y, Z] ⧸ (X * Y, X * Z)` — the plane `X = 0` met by the line `Y = Z = 0`
— and `x_K` the generic point of the line in `Spec (ℂ[X, Y, Z] ⧸ (X * Y, X * Z))`, both sides are
`1`, strictly less than `dim S = dim T = 2`, so the statement is one about a local quantity and not
a restatement of 00P3; and for `S = ℚ[X]` with `x_K` a closed point of `Spec ℂ[X]` above the closed
point `(X ^ 2 + 1)` both sides are `1`, even though `X ^ 2 + 1` splits after the base change, so
that the fibre over `q` has two points and the equality holds at each.

## References

* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
* [StacksProject 00P3](https://stacks.math.columbia.edu/tag/00P3)
* [StacksProject 00P2](https://stacks.math.columbia.edu/tag/00P2)
-/


namespace Algebra.IsPushout

/-- **Stacks 00P4.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `K/k` be a
field extension and let `T = K ⊗_k S` be the base change, presented as a pushout square. Let
`xK ∈ Spec T` be a point, with prime `q_K`, and let `x = comap (algebraMap S T) xK ∈ Spec S` be
the point of the prime `q = q_K ∩ S` that it lies over. Then `Spec S` has the same dimension at
`x` as `Spec T` has at `xK`. -/
@[stacks 00P4 "`dim_x X` is `TopologicalSpace.localKrullDim`, Definition 0055 (4), as in the
siblings 00P1 and 00P2; the base change `K ⊗_k S` is an arbitrary pushout square of `k`-algebras
`Algebra.IsPushout k K S T`, as in the sibling 00P3; and `q_K` lying over `q` is expressed by
taking `x = PrimeSpectrum.comap (algebraMap S T) xK`. See the module docstring."]
public theorem localKrullDim_comap_eq (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (xK : PrimeSpectrum T) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S)
        (PrimeSpectrum.comap (algebraMap S T) xK) =
      TopologicalSpace.localKrullDim (PrimeSpectrum T) xK :=
  Stacks.KrullDimension.LocalBaseChange.solution k K S T xK

end Algebra.IsPushout


/-!
# Dimension of the fibre of a base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `K/k` be a field extension and
let `T = K ⊗_k S`. For a prime `q ⊆ S` and a prime `Q ⊆ T` lying over `q` this file proves
$$
  \dim (T ⊗_S κ(q))_Q = \dim T_Q - \dim S_q
    = \operatorname{trdeg}_k κ(q) - \operatorname{trdeg}_K κ(Q),
$$
both equalities in the additive form `dim (T ⊗_S κ(q))_Q + a = b`, and that some prime `Q` over
`q` makes the common left-hand quantity zero (Stacks 0CWE). The dimension of the fibre is the
height of the image of `Q` in `T ⧸ q T`.

The argument is the source's. The map `S → T` is faithfully flat, being the base change of the
faithfully flat `k → K`, so it satisfies going-down and the height formula
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` — Lemma 00ON — gives the first equality
at once. For the second, `dim_x Spec S = dim_{x_K} Spec T` (Lemma 00P4) while Lemma 00P1 computes
each local dimension as a height plus a transcendence degree, giving
`ht q + trdeg_k κ(q) = ht Q + trdeg_K κ(Q)`; subtracting the first equality and cancelling the
finite `ht q` leaves the second. For the last part, a prime of `T` over `q` exists because
`Spec T → Spec S` is surjective, and a minimal prime of `q T` below it still lies over `q` while
its image in `T ⧸ q T` is a minimal prime, hence of height zero.

## Main results

* `Stacks.KrullDimension.FibreHeight.solution`: the statement of Stacks 0CWE.

## Implementation notes

Two stability properties of a base change are isolated as lemmas about an arbitrary pushout square,
neither being available in Mathlib next to `Algebra.IsPushout.isIntegral`:
`Stacks.KrullDimension.FibreHeight.faithfullyFlat_of_isPushout`, where the hypothesis that `k` is a
field enters through `Module.FaithfullyFlat k K`, and which supplies both going-down for the first
equality and the surjectivity of `Spec T → Spec S` for the last part; and
`Stacks.KrullDimension.FibreHeight.finiteType_of_isPushout`, which makes `T` Noetherian and is the
hypothesis of Lemma 00P1 over `K`.

The mathematics is in two further lemmas.
`Stacks.KrullDimension.FibreHeight.height_add_trdeg_residueField_eq` is the equality
`ht q + trdeg_k κ(q) = ht Q + trdeg_K κ(Q)`, Lemma 00P4 read through Lemma 00P1 on both sides; it
is the whole content of the second equality, the passage to the stated form being the cancellation
of the finite `ht q`.
`Stacks.KrullDimension.FibreHeight.exists_liesOver_height_map_quotient_eq_zero` is the last part,
proved for an arbitrary algebra and an arbitrary prime over `q`: the fibre over `q` has a generic
point. It rests on
`Stacks.KrullDimension.FibreHeight.height_map_quotient_eq_zero_of_mem_minimalPrimes`, that a prime
minimal over an ideal `I` has height zero in `R ⧸ I`, which is the sharp case of Mathlib's
`Ideal.map_height_le_one_of_mem_minimalPrimes` with the principal ideal removed.

## References

* [StacksProject 0CWE](https://stacks.math.columbia.edu/tag/0CWE)
* [StacksProject 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [StacksProject 00P1](https://stacks.math.columbia.edu/tag/00P1)
* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
-/


namespace Stacks.KrullDimension.FibreHeight

open scoped TensorProduct

section BaseChange

variable (k K S T : Type*) [CommRing k] [CommRing K] [CommRing S] [CommRing T] [Algebra k K]
  [Algebra k S] [Algebra k T] [Algebra K T] [Algebra S T] [IsScalarTower k K T]
  [IsScalarTower k S T] [Algebra.IsPushout k K S T]

/-- In a pushout square of commutative rings
```
k  →  K
↓     ↓
S  →  T
```
(that is, `T = K ⊗[k] S`), if `K` is faithfully flat over `k` then `T` is faithfully flat
over `S`. -/
private theorem faithfullyFlat_of_isPushout [Module.FaithfullyFlat k K] :
    Module.FaithfullyFlat S T :=
  have : Algebra.IsPushout k S K T := Algebra.IsPushout.symm ‹_›
  have : Module.FaithfullyFlat S (S ⊗[k] K) := inferInstance
  Module.FaithfullyFlat.of_linearEquiv S (S ⊗[k] K)
    (Algebra.IsPushout.equiv k S K T).symm.toLinearEquiv

/-- In a pushout square `T = K ⊗[k] S`, if `S` is of finite type over `k` then `T` is of finite
type over `K`: finite type is stable under base change. -/
private theorem finiteType_of_isPushout [Algebra.FiniteType k S] : Algebra.FiniteType K T :=
  Algebra.FiniteType.equiv inferInstance (Algebra.IsPushout.equiv k K S T)

end BaseChange

/-- Lemma 00P4 read through Lemma 00P1 on both sides: in a base change `T = K ⊗_k S` of a finite
type `k`-algebra along a field extension `K/k`, a prime `Q` of `T` lying over a prime `q` of `S`
satisfies `ht q + trdeg_k κ(q) = ht Q + trdeg_K κ(Q)`, both sides being the common local
dimension `dim_x Spec S = dim_{x_K} Spec T`. -/
private theorem height_add_trdeg_residueField_eq (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] (Q : Ideal T) [Q.IsPrime]
    [Q.LiesOver q] :
    q.height + Cardinal.toENat (Algebra.trdeg k q.ResidueField)
      = Q.height + Cardinal.toENat (Algebra.trdeg K Q.ResidueField) := by
  have : Algebra.FiniteType K T := finiteType_of_isPushout k K S T
  have hx : PrimeSpectrum.comap (algebraMap S T) (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum T)
      = (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) :=
    PrimeSpectrum.ext (Ideal.LiesOver.over (A := S) (P := Q) (p := q)).symm
  have h := Algebra.IsPushout.localKrullDim_comap_eq k K S T (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum T)
  rw [hx, PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField k
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S),
    PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField K
      (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum T)] at h
  exact_mod_cast h

/-- A prime `P` minimal over an ideal `I` has height zero in `R ⧸ I`, its image there being a
minimal prime of `R ⧸ I`. -/
public theorem height_map_quotient_eq_zero_of_mem_minimalPrimes {R : Type*} [CommRing R]
    {I P : Ideal R} (hP : P ∈ I.minimalPrimes) : (P.map (Ideal.Quotient.mk I)).height = 0 := by
  rw [Ideal.minimalPrimes_eq_comap] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  have : P'.IsPrime := hP'.1.1
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  exact Ideal.height_eq_zero_iff.mpr hP'

/-- **The fibre of `Spec T → Spec S` over `q` has a generic point.** If some prime `Q` of `T` lies
over an ideal `q` of `S`, then a prime of `T` minimal over `q T` and below `Q` still lies over
`q`, and its image in `T ⧸ q T` has height zero. -/
private theorem exists_liesOver_height_map_quotient_eq_zero {S T : Type*} [CommRing S]
    [CommRing T] [Algebra S T] (q : Ideal S) (Q : Ideal T) [Q.IsPrime] [Q.LiesOver q] :
    ∃ (P : Ideal T) (_ : P.IsPrime) (_ : P.LiesOver q),
      (P.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height = 0 := by
  have hover : q = Q.comap (algebraMap S T) := Ideal.LiesOver.over
  obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.2 hover.le)
  refine ⟨P, hPmin.1.1, ⟨le_antisymm (Ideal.map_le_iff_le_comap.1 hPmin.1.2) ?_⟩,
    height_map_quotient_eq_zero_of_mem_minimalPrimes hPmin⟩
  exact hover ▸ Ideal.comap_mono hPle

/-- **Stacks 0CWE.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `K/k` be a
field extension and let `T = K ⊗_k S` be the base change, presented as a pushout square. Then for
every prime `q` of `S` and every prime `Q` of `T` lying over `q`, the dimension of the fibre ring
`(T ⊗_S κ(q))_Q` — the height of the image of `Q` in `T ⧸ q T` — added to `dim S_q` gives
`dim T_Q`, and added to `trdeg_K κ(Q)` gives `trdeg_k κ(q)`. Moreover, given `q` there is a prime
`Q` over `q` for which this dimension is zero. -/
public theorem solution (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] :
    (∀ (q : Ideal S) [q.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver q],
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height + q.height = Q.height ∧
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height
            + Cardinal.toENat (Algebra.trdeg K Q.ResidueField)
          = Cardinal.toENat (Algebra.trdeg k q.ResidueField)) ∧
      ∀ (q : Ideal S) [q.IsPrime], ∃ (Q : Ideal T) (_ : Q.IsPrime) (_ : Q.LiesOver q),
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height = 0 := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : Algebra.FiniteType K T := finiteType_of_isPushout k K S T
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  have : Module.FaithfullyFlat S T := faithfullyFlat_of_isPushout k K S T
  have : Algebra.HasGoingDown S T := Algebra.HasGoingDown.of_flat
  constructor
  · intro q hq Q hQ hQq
    have hfib := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q
    have hkey := height_add_trdeg_residueField_eq k K S T q Q
    rw [hfib, add_assoc] at hkey
    exact ⟨by rw [hfib, add_comm], (WithTop.add_left_cancel
      (Ideal.height_ne_top_of_isPrime (I := q)) hkey).symm⟩
  · intro q hq
    obtain ⟨x, hx⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := T) ⟨q, hq⟩
    have : x.asIdeal.LiesOver q := ⟨(congrArg PrimeSpectrum.asIdeal hx).symm⟩
    exact exists_liesOver_height_map_quotient_eq_zero q x.asIdeal

end Stacks.KrullDimension.FibreHeight


/-!
# Dimension of the fibre of a base change to a field extension

Let `k` be a field, let `S` be a `k`-algebra of finite type, let `K/k` be a field extension and
let `S_K = K ⊗_k S`. Let `q ⊆ S` be a prime and let `q_K ⊆ S_K` be a prime lying over `q`. Then
$$
  \dim (S_K ⊗_S κ(q))_{q_K} = \dim (S_K)_{q_K} - \dim S_q
    = \operatorname{trdeg}_k κ(q) - \operatorname{trdeg}_K κ(q_K),
$$
and, given `q`, some prime `q_K` over `q` makes this number zero. So the fibre of
`Spec S_K → Spec S` over `q` has, at `q_K`, exactly the dimension by which `q_K` is deeper than
`q`, equivalently the transcendence degree that the residue field loses in the base change; and
the fibre always has a point where nothing is lost, namely a generic point of the fibre.

The source's proof: `S_q → (S_K)_{q_K}` is a flat local homomorphism of Noetherian local rings
with special fibre `(S_K ⊗_S κ(q))_{q_K}`, so Lemma 00ON gives the first equality. For the second,
`dim_x Spec S = dim_{x_K} Spec S_K` (Lemma 00P4) while `dim_x Spec S = dim S_q + trdeg_k κ(q)` and
`dim_{x_K} Spec S_K = dim (S_K)_{q_K} + trdeg_K κ(q_K)` (Lemma 00P1). Choosing `q_K` minimal over
`q S_K` makes the fibre ring's local dimension zero.

## Main results

* `Algebra.IsPushout.height_fiber_add_height_eq_and_add_trdeg_eq`: the two equalities and the
  existence of a prime of the base change over `q` with zero-dimensional fibre local ring.

## Implementation notes

*The two equalities are stated additively, `dim(fibre) + a = b`, not with a truncated
subtraction.* Heights live in `ℕ∞`, where `b - a` is not the source's difference unless `a ≤ b` is
known, and the source's chain of equalities is a statement about the single quantity
`dim (S_K ⊗_S κ(q))_{q_K}`, which is the term the two equations have in common. The additive form
also carries the inequalities `dim S_q ≤ dim (S_K)_{q_K}` and `trdeg_K κ(q_K) ≤ trdeg_k κ(q)`,
which the subtractive form silently assumes.

*`dim (S_K ⊗_S κ(q))_{q_K}` is the height of the image of `q_K` in `S_K ⧸ q S_K`.* This is
Mathlib's spelling of the dimension of the fibre in the going-down height formula
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, which is Lemma 00ON itself. It agrees
with the source's `κ(q) ⊗_S S_K` localized at `q_K` — Mathlib's `Ideal.Fiber` — because a prime
`P` of `S_K` with `q S_K ≤ P ≤ q_K` contracts to a prime of `S` containing `q` and contained in
`q_K ∩ S = q`, hence lies over `q`; so the primes counted below `q_K` in `S_K ⧸ q S_K` are
exactly those of the fibre ring, no localization needed, and the two heights are equal chain by
chain.

*The base change is an arbitrary pushout square `Algebra.IsPushout k K S T`*, as in the siblings
00P3 and 00P4, rather than the construction `K ⊗[k] S`: the instance says exactly that the
canonical `K`-algebra map `K ⊗_k S → T` is an isomorphism, so `T` is the source's `S_K` with its
two structure maps, and a base change already presented in another shape — the quotient
`K[x_1, …, x_n]/I·K[x_1, …, x_n]` of a polynomial ring that the source's own proof uses — is
covered with no intermediate isomorphism.

*"`q_K` lies over `q`" is Mathlib's `Ideal.LiesOver`*, so that the first equality is literally the
shape of the going-down height formula it specializes, and the primes are `Ideal`s with `IsPrime`
instances rather than points of `PrimeSpectrum`; the sibling 00P4, whose subject is the topology of
the two spectra, uses points instead. `Ideal.ResidueField` is `κ(-)`, as in the siblings 00P1,
00P2 and 06RP, and it carries `IsFractionRing (S ⧸ q) q.ResidueField`, so it is the field the
source writes; its `k`-algebra (resp. `K`-algebra) structure is induced by `Algebra k S` (resp.
`Algebra K T`) and is not an extra datum. `Algebra.trdeg` is a `Cardinal` while `Ideal.height` is
an `ℕ∞`, so the sums are formed in `ℕ∞` after `Cardinal.toENat`, exactly as in 00P1; this loses
nothing, since `κ(q)` is essentially of finite type over `k` and `κ(q_K)` over `K`, so both
transcendence degrees are finite (`Algebra.trdeg_lt_aleph0`) and `Cardinal.toENat` is injective on
finite cardinals.

*No Noetherian hypothesis appears*, although the source's proof passes through Noetherian local
rings: `Algebra.FiniteType k S` makes `S` Noetherian, and `T` is of finite type over the field `K`
because finite type is stable under base change, hence Noetherian as well.

Faithfulness. (1) No hypothesis is idle. `Field K` is essential: for `k = ℚ`, `K = T = ℚ[t]` and
`S = ℚ` — a pushout square, since `ℚ[t] ⊗_ℚ ℚ = ℚ[t]` — take `q = ⊥` and `q_K = (t)`; the fibre
ring is `T` itself, in which `(t)` has height `1`, and the second equality would read
`1 + trdeg_{ℚ[t]} ℚ = trdeg_ℚ ℚ = 0`, which is false. `Field k` is essential, being what makes `K`
flat over `k`, so that the fibre dimension is a difference rather than only a bound (Lemma 00OM
gives `≤` in general). `Algebra.FiniteType k S` is used by the second equality: it is the
hypothesis of Lemma 00P1, which computes each local dimension as height plus transcendence
degree, and it is also what makes both residue fields essentially of finite type, so that the two
transcendence degrees are finite and the comparison in `ℕ∞` is faithful; it supplies, together
with `Field K`, the Noetherian hypothesis of the first equality. Both `q` and `q_K` occur in every
conjunct. (2) The scalars and base are the source's: the pushout square is over `k`, both scalar
towers are over `k`, the finite type hypothesis is on `S` over `k` and not on `T` over `K`, the
first transcendence degree is over `k` and the second over `K` — not both over `k` — the heights
are those of `S` and of `T` themselves, and `q_K` lies over `q` along `algebraMap S T`, not along
`algebraMap K T`. (3) The objects the source names are pinned: `T` together with `algebraMap K T`
and `algebraMap S T` is fixed by the pushout instance up to the unique `k`-algebra isomorphism
compatible with them, the fibre ring is the explicit `T ⧸ q T` with the explicit image
`q_K ⧸ q T` of `q_K` in it, the residue fields are `q.ResidueField` and `q_K.ResidueField` with
their canonical structure maps, and the conclusions are equations determining the fibre dimension,
not bounds on it. The last conjunct is the source's "we can always choose `q_K`": an existence
statement, and the only one of the three, the first two holding for *every* prime over `q`.
(4) The instantiation is not degenerate: for `k = ℚ`, `K = ℂ`, `S = ℚ[x]` and `q = ⊥`, the prime
`q_K = ⊥` of `T = ℂ[x]` gives fibre dimension `0` with `trdeg_ℂ ℂ(x) = trdeg_ℚ ℚ(x) = 1` — the
witness for the last conjunct — while `q_K = (x - i)` gives fibre dimension `1`, with
`1 + height ⊥ = height (x - i)` and `1 + trdeg_ℂ ℂ = trdeg_ℚ ℚ(x)`, so both equalities have a
nonzero fibre term and the three parts are not vacuous; and for `S = ℚ[x, y] ⧸ (x * y)`, `q` the
generic point of the line `x = 0` and `q_K` the prime over it, the fibre dimension is again `0`
even though `S` is not a domain.

## References

* [StacksProject 0CWE](https://stacks.math.columbia.edu/tag/0CWE)
* [StacksProject 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [StacksProject 00P1](https://stacks.math.columbia.edu/tag/00P1)
* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
-/


namespace Algebra.IsPushout

/-- **Stacks 0CWE.** Let `k` be a field, let `S` be a finite type `k`-algebra, let `K/k` be a
field extension and let `T = K ⊗_k S` be the base change, presented as a pushout square. Then for
every prime `q` of `S` and every prime `Q` of `T` lying over `q`, the dimension of the fibre ring
`(T ⊗_S κ(q))_Q` — the height of the image of `Q` in `T ⧸ q T` — added to `dim S_q` gives
`dim T_Q`, and added to `trdeg_K κ(Q)` gives `trdeg_k κ(q)`. Moreover, given `q` there is a prime
`Q` over `q` for which this dimension is zero. -/
@[stacks 0CWE "The dimension of the fibre `(S_K ⊗_S κ(𝔮))_{𝔮_K}` is the height of the image of
`𝔮_K` in `S_K ⧸ 𝔮 S_K`, Mathlib's spelling in the going-down height formula (Lemma 00ON); the two
equalities are stated additively rather than with a truncated subtraction in `ℕ∞`; the base change
`K ⊗_k S` is an arbitrary pushout square of `k`-algebras, as in the siblings 00P3 and 00P4; and
transcendence degrees are compared through `Cardinal.toENat`, as in 00P1. See the module
docstring."]
public theorem height_fiber_add_height_eq_and_add_trdeg_eq (k K S T : Type*) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] :
    (∀ (q : Ideal S) [q.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver q],
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height + q.height = Q.height ∧
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height
            + Cardinal.toENat (Algebra.trdeg K Q.ResidueField)
          = Cardinal.toENat (Algebra.trdeg k q.ResidueField)) ∧
      ∀ (q : Ideal S) [q.IsPrime], ∃ (Q : Ideal T) (_ : Q.IsPrime) (_ : Q.LiesOver q),
        (Q.map (Ideal.Quotient.mk (q.map (algebraMap S T)))).height = 0 :=
  Stacks.KrullDimension.FibreHeight.solution k K S T

end Algebra.IsPushout

