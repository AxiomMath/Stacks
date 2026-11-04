module

import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a complete intersection along a field extension

Let `K/k` be a field extension, let `S` be a finite type `k`-algebra, let `S'` be the base change
`K ⊗_k S`, let `q'` be a prime of `S'` and let `q` be the prime of `S` below it. Then the local
ring `S'_{q'}` is a complete intersection over `K` if and only if `S_q` is a complete intersection
over `k`.

## Main results

* `Stacks.CompleteIntersection.BaseChange.spanFinrank_map_of_flat_of_isLocalHom`: for a flat local
  homomorphism of local rings `A → A'` with `A` Noetherian, an ideal `J` of `A` and its extension
  `J·A'` need the same number of generators.
* `Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff`: for a base change
  `S' = K ⊗_k S` along a field extension and a prime `q'` of `S'` over `q` of `S`, `S'_{q'}` is a
  complete intersection over `K` if and only if `S_q` is one over `k`.

## Implementation notes

The base change is an arbitrary pushout square: `Algebra.IsPushout k K S S'` pins `S'` together
with its structure maps up to the unique compatible `k`-algebra isomorphism, so the literal
`K ⊗_k S` satisfies it, and the statement is available for any model.

## References

* [StacksProject 00SI](https://stacks.math.columbia.edu/tag/00SI), Lemma 10.135.10.
* [StacksProject 00SG](https://stacks.math.columbia.edu/tag/00SG), Lemma 10.135.8, here
  `IsCompleteIntersection.localization_atPrime_tfae`.
* [StacksProject 00SC](https://stacks.math.columbia.edu/tag/00SC), Lemma 10.135.4, here
  `Algebra.Generators.tfae_isGlobalCompleteIntersection_away`.
* [StacksProject 00P2](https://stacks.math.columbia.edu/tag/00P2), here
  `PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap`.
* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4), here
  `Algebra.IsPushout.localKrullDim_comap_eq`.
-/

@[expose] public section

namespace Stacks.CompleteIntersection.BaseChange

open TensorProduct IsLocalRing

universe u v w

/-! ### Minimal numbers of generators under a flat local base change -/

/-- Over a local ring the minimal number of generators of a finite module is the dimension of its
reduction modulo the maximal ideal. -/
@[ega "IV 18.10.21" "more general", sga "1 IV 4.4" "more general"]
public theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank
      = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [Module.finrank_eq_spanFinrank_of_free,
    ← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top]
  have e : (ResidueField R ⊗[R] (⊤ : Submodule R M)) ≃ₗ[ResidueField R] (ResidueField R ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) Submodule.topEquiv
  simp [Submodule.spanFinrank, Submodule.spanRank_eq_of_equiv e]

/-- The minimal number of generators of a finite module
over a local ring is unchanged by base change along a local homomorphism of local rings. -/
@[ega "IV 2.5.8.9" "partial"]
public theorem spanFinrank_top_tensorProduct_eq (A B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (⊤ : Submodule B (B ⊗[A] M)).spanFinrank = (⊤ : Submodule A M).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField B (B ⊗[A] M),
    spanFinrank_top_eq_finrank_residueField A M]
  have e1 : (ResidueField B ⊗[B] (B ⊗[A] M)) ≃ₗ[ResidueField B] (ResidueField B ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B) M
  have e2 : (ResidueField B ⊗[ResidueField A] (ResidueField A ⊗[A] M))
      ≃ₗ[ResidueField B] (ResidueField B ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
      (ResidueField B) M
  rw [e1.finrank_eq, ← e2.finrank_eq, Module.finrank_baseChange]

/-- Along a flat ring map `A → A'`, the ideal `J·A'` needs as many generators as the `A'`-module
`A' ⊗_A J`. -/
public theorem spanFinrank_map_eq_spanFinrank_top_tensor {A : Type*} [CommRing A] (A' : Type*)
    [CommRing A'] [Algebra A A'] [Module.Flat A A'] (J : Ideal A) :
    (J.map (algebraMap A A')).spanFinrank = (⊤ : Submodule A' (A' ⊗[A] J)).spanFinrank := by
  set e := Submodule.toBaseChange.toLinearEquiv (R := A) A' (J : Submodule A A) with he
  set ψ : A' ⊗[A] J →ₗ[A'] A' :=
    (TensorProduct.AlgebraTensorModule.rid A A' A').toLinearMap ∘ₗ
      (Submodule.baseChange A' (J : Submodule A A)).subtype ∘ₗ e.toLinearMap with hψ
  have hinj : Function.Injective ψ :=
    ((TensorProduct.AlgebraTensorModule.rid A A' A').injective.comp
      Subtype.val_injective).comp e.injective
  have hrange : LinearMap.range ψ = J.map (algebraMap A A') := by
    rw [hψ]
    simp only [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype, Submodule.baseChange_eq_span, Submodule.map_span, Ideal.map]
    congr 1
    ext y
    simp [Submodule.map_coe, Set.image_image, Algebra.smul_def]
  rw [← Submodule.spanFinrank_map_eq_of_injective ψ hinj (p := ⊤), Submodule.map_top, hrange]

/-- For a flat local homomorphism of local
rings `A → A'` with `A` Noetherian and an ideal `J` of `A`, the ideal `J·A'` needs exactly as many
generators as `J`. -/
public theorem spanFinrank_map_of_flat_of_isLocalHom {A A' : Type*} [CommRing A] [CommRing A']
    [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')]
    [Module.Flat A A'] (J : Ideal A) (hJ : Submodule.FG (J : Submodule A A)) :
    (J.map (algebraMap A A')).spanFinrank = J.spanFinrank := by
  have : Module.Finite A J := Module.Finite.iff_fg.mpr hJ
  rw [spanFinrank_map_eq_spanFinrank_top_tensor, spanFinrank_top_tensorProduct_eq,
    Submodule.spanFinrank_top]

/-! ### The base changed presentation -/

/-- Base changing a presentation `S = k[x_i]/I` along `k → K` gives the presentation
`K ⊗_k S = K[x_i]/I·K[x_i]`. -/
private theorem ker_baseChange {k : Type*} [CommRing k] (K : Type*) [CommRing K] [Algebra k K]
    {S : Type*} [CommRing S] [Algebra k S] {ι : Type*} (P : Algebra.Generators k S ι) :
    (P.baseChange K).ker = P.ker.map (MvPolynomial.map (algebraMap k K)) := by
  let Q : Algebra.Presentation k S ι P.ker :=
    { __ := P
      relation := fun x => x.1
      span_range_relation_eq_ker := by
        rw [show (Set.range fun x : P.ker => (x : P.Ring)) = (P.ker : Set P.Ring) from
          Subtype.range_coe_subtype, Ideal.span_eq] }
  have h := Q.span_range_relation_eq_ker_baseChange K
  rw [show P.ker.map (MvPolynomial.map (algebraMap k K))
    = Ideal.span (MvPolynomial.map (algebraMap k K) '' (P.ker : Set P.Ring)) from rfl,
    Set.image_eq_range]
  exact h.symm

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- A polynomial ring is flat over the polynomial ring on the same variables over a subfield. -/
private theorem flat_mvPolynomial_map {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
    (ι : Type*) :
    RingHom.Flat (MvPolynomial.map (algebraMap k K) : MvPolynomial ι k →+* MvPolynomial ι K) := by
  have e : (MvPolynomial ι k) ⊗[k] K ≃ₗ[MvPolynomial ι k] MvPolynomial ι K :=
    (Algebra.IsPushout.out (R := k) (S := MvPolynomial ι k) (R' := K)
      (S' := MvPolynomial ι K)).equiv
  rw [← MvPolynomial.algebraMap_def, RingHom.flat_algebraMap_iff]
  exact Module.Flat.of_linearEquiv e.symm

/-! ### Local dimensions and heights over a polynomial ring -/

/-- The local Krull dimension at a point is never `-∞`. -/
private theorem localKrullDim_ne_bot {X : Type*} [TopologicalSpace X] (x : X) :
    TopologicalSpace.localKrullDim X x ≠ ⊥ := by
  obtain ⟨⟨U, hxU, _, hd⟩, -⟩ := topologicalKrullDimAt_isLeast X x
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hd, Ne,
    topologicalKrullDim_eq_bot_iff_isEmpty]
  exact fun h => h.false ⟨x, hxU⟩

/-- The spectrum of a polynomial ring in `n` variables over a field has finite local dimension at
every point. -/
private theorem localKrullDim_mvPolynomial_ne_top (k : Type*) [Field k] (n : ℕ)
    (x : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    TopologicalSpace.localKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) x ≠ ⊤ := by
  have hn : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Field.toIsField k)]
    simp
  have hle : TopologicalSpace.localKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) x
      ≤ (n : WithBot ℕ∞) := by
    rw [← hn, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    exact le_iSup _ x
  rintro htop
  rw [htop, top_le_iff, ← ENat.WithBot.coe_eq_natCast] at hle
  exact ENat.natCast_ne_top n (WithBot.coe_injective hle)

/-- For a base change `S → T` of a finite type
`k`-algebra along a field extension `K/k`, a prime `qK` of `T` and its contraction `q` to `S`, the
local dimension of `Spec S` at `q` is that of `Spec T` at `qK`. -/
private theorem localKrullDim_eq_of_eq_comap (k K S T : Type*) [Field k] [Field K] [CommRing S]
    [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] (qK : Ideal T) [qK.IsPrime]
    (h : q = qK.comap (algebraMap S T)) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨q, ‹q.IsPrime›⟩
      = TopologicalSpace.localKrullDim (PrimeSpectrum T) ⟨qK, ‹qK.IsPrime›⟩ := by
  rw [← Algebra.IsPushout.localKrullDim_comap_eq k K S T ⟨qK, ‹qK.IsPrime›⟩]
  congr 1
  exact PrimeSpectrum.ext h

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- The spectra of `k[x_1, …, x_n]` and of `K[x_1, …, x_n]` have the same local dimension at
corresponding points. -/
private theorem localKrullDim_mvPolynomial_eq_of_eq_comap {k : Type*} [Field k] {K : Type*}
    [Field K] [Algebra k K] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime]
    (p' : Ideal (MvPolynomial (Fin n) K)) [p'.IsPrime]
    (h : p = p'.comap (MvPolynomial.map (algebraMap k K))) :
    TopologicalSpace.localKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) ⟨p, ‹p.IsPrime›⟩
      = TopologicalSpace.localKrullDim (PrimeSpectrum (MvPolynomial (Fin n) K))
          ⟨p', ‹p'.IsPrime›⟩ :=
  localKrullDim_eq_of_eq_comap k K _ _ p p' (by rwa [MvPolynomial.algebraMap_def])

/-- Along a surjection the height of a prime does not exceed the height of its contraction. -/
private theorem height_le_height_comap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (q : Ideal S) (hq : q.IsPrime) :
    q.height ≤ (q.comap f).height := by
  have hm : Monotone (PrimeSpectrum.comap f) := fun _ _ h => Ideal.comap_mono h
  have hmono : StrictMono (PrimeSpectrum.comap f) :=
    hm.strictMono_of_injective (PrimeSpectrum.comap_injective_of_surjective f hf)
  have h := Order.height_le_height_apply_of_strictMono _ hmono (⟨q, hq⟩ : PrimeSpectrum S)
  rwa [← PrimeSpectrum.height_eq_orderHeight (⟨q, hq⟩ : PrimeSpectrum S),
    ← PrimeSpectrum.height_eq_orderHeight (PrimeSpectrum.comap f ⟨q, hq⟩)] at h

/-- For a presentation `P` of `S` by `n` generators over a field and a prime `q` of `S` with
contraction `p` to `P.Ring`, the local dimension at `p` plus `ht q` is the local dimension at `q`
plus `ht p`. -/
private theorem localKrullDim_add_height_eq_of_generators {k S : Type*} [Field k] [CommRing S]
    [Algebra k S] {n : ℕ} (P : Algebra.Generators k S (Fin n)) (q : Ideal S) [q.IsPrime]
    (p : Ideal P.Ring) [p.IsPrime] (hp : p = q.comap (algebraMap P.Ring S)) :
    TopologicalSpace.localKrullDim (PrimeSpectrum P.Ring) ⟨p, ‹p.IsPrime›⟩ + (q.height : WithBot ℕ∞)
      = TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨q, ‹q.IsPrime›⟩
        + (p.height : WithBot ℕ∞) := by
  have h := PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap
    k (IsScalarTower.toAlgHom k P.Ring S) P.algebraMap_surjective ⟨q, ‹q.IsPrime›⟩
  rwa [show PrimeSpectrum.comap (IsScalarTower.toAlgHom k P.Ring S).toRingHom ⟨q, ‹q.IsPrime›⟩
    = ⟨p, ‹p.IsPrime›⟩ from PrimeSpectrum.ext hp.symm] at h

/-- Two equations `D + a = E + b` and `D + a' = E + b'` in `WithBot ℕ∞` with `D` finite and `b`,
`b'` finite determine one and the same difference: `b - a = b' - a' = D - E`. -/
private theorem exists_add_of_add_eq_add {D E : WithBot ℕ∞} {a b a' b' : ℕ∞}
    (hD : D ≠ ⊥) (hDt : D ≠ ⊤)
    (h1 : D + (a : WithBot ℕ∞) = E + (b : WithBot ℕ∞))
    (h2 : D + (a' : WithBot ℕ∞) = E + (b' : WithBot ℕ∞))
    (hb : b ≠ ⊤) (hb' : b' ≠ ⊤) (hab : a ≤ b) : ∃ c : ℕ, b = a + c ∧ b' = a' + c := by
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hD
  have hd : d ≠ ⊤ := fun h => hDt (by rw [h]; rfl)
  have ha : a ≠ ⊤ := fun h => hb (top_le_iff.mp (h ▸ hab))
  have hE : E ≠ ⊥ := by
    rintro rfl
    rw [WithBot.bot_add, ← WithBot.coe_add] at h1
    exact (WithBot.coe_ne_bot h1).elim
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hE
  rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_eq_coe] at h1 h2
  have he : e ≠ ⊤ := fun h => by simp [h, hd, ha] at h1
  have ha' : a' ≠ ⊤ := fun h => by
    rw [h, show d + (⊤ : ℕ∞) = ⊤ from WithTop.add_eq_top.mpr (Or.inr rfl)] at h2
    exact (WithTop.add_eq_top.mp h2.symm).elim he hb'
  lift d to ℕ using hd
  lift e to ℕ using he
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift a' to ℕ using ha'
  lift b' to ℕ using hb'
  rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at h1 h2
  rw [Nat.cast_le] at hab
  exact ⟨d - e, by exact_mod_cast show b = a + (d - e) by omega,
    by exact_mod_cast show b' = a' + (d - e) by omega⟩

/-! ### Complete intersections under a field extension of the base -/

universe u₁ u₂ u₃ u₄ u₅ u₆

/-- For a base change `S' = K ⊗_k S` of a finite type `k`-algebra along a field extension `K/k`
and a prime `q'` of `S'` lying over the prime `q` of `S`, the local ring `S'_{q'}` is a complete
intersection over `K` if and only if `S_q` is a complete intersection over `k`. -/
public theorem solution (k : Type u₁) [Field k] (K : Type u₂) [Field K] [Algebra k K]
    (S : Type u₃) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (S' : Type u₄) [CommRing S'] [Algebra k S'] [Algebra K S'] [Algebra S S']
    [IsScalarTower k K S'] [IsScalarTower k S S'] [Algebra.IsPushout k K S S']
    (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime] [q'.LiesOver q]
    (Sq : Type u₅) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra k Sq] [IsScalarTower k S Sq]
    (S'q' : Type u₆) [CommRing S'q'] [Algebra S' S'q'] [IsLocalization.AtPrime S'q' q']
    [Algebra K S'q'] [IsScalarTower K S' S'q'] :
    IsCompleteIntersection K S'q' ↔ IsCompleteIntersection k Sq := by
  classical
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k S›
  have haeval : (MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :
      MvPolynomial (Fin n) k →ₐ[k] S) = f := MvPolynomial.algHom_ext (by simp)
  let P : Algebra.Generators k S (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rw [haeval]; exact hf)
  let P' : Algebra.Generators K S' (Fin n) :=
    (P.baseChange K).ofAlgEquiv (Algebra.IsPushout.equiv k K S S')
  have hS' : Algebra.FiniteType K S' :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval P'.val, fun y => by
        obtain ⟨x, hx⟩ := P'.algebraMap_surjective y
        exact ⟨x, by rw [← Algebra.Generators.algebraMap_apply]; exact hx⟩⟩
  have : IsNoetherianRing (MvPolynomial (Fin n) k) := MvPolynomial.isNoetherianRing_fin
  have : IsNoetherianRing (MvPolynomial (Fin n) K) := MvPolynomial.isNoetherianRing_fin
  set β : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) K := MvPolynomial.map (algebraMap k K)
    with hβ
  set p := q.comap (algebraMap P.Ring S) with hpdef
  set p' := q'.comap (algebraMap P'.Ring S') with hp'def
  have hpprime : p.IsPrime := Ideal.comap_isPrime _ _
  have hp'prime : p'.IsPrime := Ideal.comap_isPrime _ _
  have hcomp : (algebraMap P'.Ring S').comp β
      = (algebraMap S S').comp (algebraMap P.Ring S) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [hβ, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
        Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_C]
      rw [← IsScalarTower.algebraMap_apply k K S', ← IsScalarTower.algebraMap_apply k S S']
    · simp [hβ, P', Algebra.Generators.algebraMap_apply, Algebra.Generators.ofAlgEquiv_val,
        Algebra.IsPushout.equiv_tmul]
  have hq : q = q'.comap (algebraMap S S') := Ideal.LiesOver.over
  have hpp' : p = p'.comap β := by
    rw [hpdef, hp'def, hq, Ideal.comap_comap, Ideal.comap_comap, hcomp]
  have hker : P'.ker = P.ker.map β := by
    rw [Algebra.Generators.ker_ofAlgEquiv, ker_baseChange K P]
  obtain ⟨c, hc, hc'⟩ : ∃ c : ℕ, p.height = q.height + c ∧ p'.height = q'.height + c := by
    have hP2 := localKrullDim_add_height_eq_of_generators P q p hpdef
    have hP2' := localKrullDim_add_height_eq_of_generators P' q' p' hp'def
    rw [← localKrullDim_mvPolynomial_eq_of_eq_comap n p p' hpp',
      ← localKrullDim_eq_of_eq_comap k K S S' q q' hq] at hP2'
    exact exists_add_of_add_eq_add (localKrullDim_ne_bot _)
      (localKrullDim_mvPolynomial_ne_top k n _) hP2 hP2'
      (Ideal.height_ne_top_of_isPrime) (Ideal.height_ne_top_of_isPrime)
      (hpdef ▸ height_le_height_comap (algebraMap P.Ring S) P.algebraMap_surjective q ‹q.IsPrime›)
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime p') :=
    (Localization.localRingHom p p' β hpp').toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p') :=
    (flat_mvPolynomial_map (Fin n)).localRingHom p' p hpp'
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime p')) :=
    Localization.isLocalHom_localRingHom p p' β hpp'
  have hsq : ((algebraMap (Localization.AtPrime p) (Localization.AtPrime p')).comp
      (algebraMap P.Ring (Localization.AtPrime p)))
      = (algebraMap P'.Ring (Localization.AtPrime p')).comp β := RingHom.ext fun x => by
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra]
    exact Localization.localRingHom_to_map p p' β hpp' x
  have hJ : (P'.ker.map (algebraMap P'.Ring (Localization.AtPrime p'))).spanFinrank
      = (P.ker.map (algebraMap P.Ring (Localization.AtPrime p))).spanFinrank := by
    rw [← spanFinrank_map_of_flat_of_isLocalHom (A' := Localization.AtPrime p')
      (P.ker.map (algebraMap P.Ring (Localization.AtPrime p))) (IsNoetherian.noetherian _), hker,
      Ideal.map_map, Ideal.map_map, hsq]
  have h00SG := (IsCompleteIntersection.localization_atPrime_tfae.{u₁, u₃, 0, u₅} k S q Sq).out 1 3
  have h00SG' :=
    (IsCompleteIntersection.localization_atPrime_tfae.{u₂, u₄, 0, u₆} K S' q' S'q').out 1 3
  have h00SC := (Algebra.Generators.tfae_isGlobalCompleteIntersection_away k S P q c hc
    (Localization.AtPrime p)).out 1 2
  have h00SC' := (Algebra.Generators.tfae_isGlobalCompleteIntersection_away K S' P' q' c hc'
    (Localization.AtPrime p')).out 1 2
  rw [h00SG', h00SC', h00SG, h00SC, hJ]

end Stacks.CompleteIntersection.BaseChange

/-- Let `K/k` be a field extension, let `S` be a finite type `k`-algebra and let
`S'` be the base change of `S` along `k → K`, so `S' = K ⊗_k S`. Let `q'` be a prime of `S'` and
let `q` be the prime of `S` it lies over. Then the local ring `S'_{q'}` is a complete intersection
over `K` if and only if the local ring `S_q` is a complete intersection over `k`. -/
@[stacks 00SI "The base change `S' = K ⊗_k S` is an arbitrary pushout square
`Algebra.IsPushout k K S S'`, the shape of the sibling 00SJ; the source's literal form satisfies
it. The source's corresponding prime `q` is the contraction of `q'`, spelled `Ideal.LiesOver`, and
the two local rings are abstract localizations at `q`, resp. `q'`, with the `k`-, resp.
`K`-algebra structure induced from `S`, resp. `S'`, as in item (1) of Lemma 00SG. A complete
intersection over a field (Definition 00SD) is `IsCompleteIntersection`. See the module
docstring.", ega "IV 19.3.4" "affine case"]
public theorem Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra K S'] [Algebra S S']
    [IsScalarTower k K S'] [IsScalarTower k S S'] [Algebra.IsPushout k K S S']
    (q : Ideal S) [q.IsPrime] (q' : Ideal S') [q'.IsPrime] [q'.LiesOver q]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra k Sq] [IsScalarTower k S Sq]
    (S'q' : Type*) [CommRing S'q'] [Algebra S' S'q'] [IsLocalization.AtPrime S'q' q']
    [Algebra K S'q'] [IsScalarTower K S' S'q'] :
    IsCompleteIntersection K S'q' ↔ IsCompleteIntersection k Sq :=
  Stacks.CompleteIntersection.BaseChange.solution k K S S' q q' Sq S'q'

end
