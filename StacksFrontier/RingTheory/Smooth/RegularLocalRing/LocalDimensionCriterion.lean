module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Local
import Mathlib.Tactic.Monotonicity.Lemmas

import StacksFrontier.RingTheory.Kaehler.BaseChange
import StacksFrontier.RingTheory.Smooth.CotangentAtMaximalIdeal
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Basic
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Kaehler.Separable
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing.ClosedPointRegularity

@[expose] public section

/-!
# Smoothness at a point over an arbitrary field

Proof of Stacks 00TT. Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`
and let `x ∈ X` be the point of a prime `𝔮 ⊆ S`. Then `S/k` is smooth at `𝔮` if and only if the
fibre `Ω_{S/k} ⊗_S κ(𝔮)` has dimension at most `dim_x X`, if and only if that dimension equals
`dim_x X`; and in that case `S_𝔮` is a regular local ring.

Everything is deduced from the algebraically closed case, Lemma 00TS, by one base change. Let
`K/k` be an algebraically closed extension carrying a `k`-embedding `ψ : κ(𝔮) → K` — for instance
`K = \overline{κ(𝔮)}` — let `T = K ⊗_k S` and let `𝔪 = ker(T → K)` be the maximal ideal cut out by
`ψ`, so that `𝔪 ∩ S = 𝔮`. Base change does not move the local dimension (Lemma 00P4), and at the
closed point `𝔪` that dimension is the Krull dimension of `T_𝔪` (Lemma 00OT, which contains
Lemma 00OU); base change does not change the dimension of the fibre of the differentials, because
`Ω_{T/K} = T ⊗_S Ω_{S/k}` (`KaehlerDifferential.tensorKaehlerEquiv`, Lemma 00RV) and the residue
field at `𝔪` is `K`; and base change along the flat `k → K` moves the smooth locus to the smooth
locus (Lemma 00TG), so `S/k` is smooth at `𝔮` exactly when `T/K` is smooth at `𝔪`. The three
conditions therefore correspond to items (5), (2) and (3) of Lemma 00TS for `T/K` at `𝔪`. Item (1)
of that lemma gives regularity of `T_𝔪`, and `S_𝔮 → T_𝔪` is a flat local homomorphism, so `S_𝔮`
is regular by Lemma 00OF.

## Main results

* `Stacks.Smooth.LocalDimensionCriterion.solution`: the statement of Stacks 00TT, namely
  `Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing`.

## Implementation notes

The argument is split so that no concrete tensor product occurs in the mathematics: the heart is
`key_of_pushout`, which takes an abstract pushout square `k → K`, `k → S`, `S → T` together with
a maximal ideal `𝔪 ⊆ T` lying over `𝔮` whose residue field is `K`, and `key_of_algClosed`, which
produces such a `T` as `K ⊗[k] S` from an algebraically closed `K` and a `k`-embedding
`ψ : κ(𝔮) → K`. Keeping `K` abstract there is what makes the `S`-algebra structure of `K ⊗[k] S`
unambiguous: for the algebraic closure of `κ(𝔮)` the field `K` is itself an `S`-algebra, and
instance search would otherwise pick that action instead of the one on the right tensor factor.

The residue field at `𝔪` is presented as `T ⧸ 𝔪`, as Lemma 00TS does, rather than as `K`. The two
are related by the datum `e : (T ⧸ 𝔪) ≃ₐ[K] K` of `finrank_tensor_quotient_eq`, whose only role is
to make `T ⧸ 𝔪` a `κ(𝔮)`-algebra over `S` through `ψ`; once that scalar tower is in place the
comparison of fibre dimensions is `finrank_tensorKaehler_eq`, which mentions neither `e` nor `ψ`.

Five steps of the proof are not separate tags of the Stacks Project and are proved here as
private lemmas:
flatness of a base change (`flat_of_isPushout`, also a private lemma of the proof of 00P4);
Lemma 00TG read at a single prime
(`FieldExtensionInvariance.isSmoothAt_iff_isSmoothAt_of_isPushout`, which is Lemma 02UQ
away from a field base); the identity
`dim_x Spec T = dim T_𝔪` at a closed point (`localKrullDim_eq_ringKrullDim_atPrime`, the
closed-point case of 00OU, obtained from 00OT); the invariance of the fibre dimension under the
base change (`finrank_tensorKaehler_eq`); and the descent of regularity from `T_𝔪` to `S_𝔮`
(`isRegularLocalRing_of_flat_of_liesOver`, Lemma 00OF localized at a pair of primes, which is also
a private lemma of the proof of 0C22).

## References

* [StacksProject 00TT](https://stacks.math.columbia.edu/tag/00TT)
-/

@[expose] public section

namespace Stacks.Smooth.LocalDimensionCriterion

open TensorProduct TopologicalSpace

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A base change of a flat algebra is flat: if `k → K`, `k → A`, `A → B` is a pushout square of
`k`-algebras with `K` flat over `k`, then `B` is flat over `A`. -/
private lemma flat_of_isPushout (k : Type*) [CommRing k] (K : Type*) [CommRing K] [Algebra k K]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra K B]
    [Algebra A B] [IsScalarTower k K B] [IsScalarTower k A B] [Algebra.IsPushout k K A B]
    [Module.Flat k K] : Module.Flat A B :=
  have : Algebra.IsPushout k A K B := Algebra.IsPushout.symm ‹_›
  have : Module.Flat A (A ⊗[k] K) := Module.Flat.baseChange k A K
  Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv k A K B).symm.toLinearEquiv

/-- **The closed-point case of Stacks 00OU.** For a finite type algebra `T` over a field `K` and a
point `y` of `Spec T` whose prime is maximal, the dimension of `Spec T` at `y` is the Krull
dimension of `T_y`. This is Lemma 00OT (2): the only maximal ideal containing `y` is `y`. -/
private lemma localKrullDim_eq_ringKrullDim_atPrime (K : Type*) [Field K] {T : Type*} [CommRing T]
    [Algebra K T] [Algebra.FiniteType K T] (y : PrimeSpectrum T) (hy : y.asIdeal.IsMaximal) :
    localKrullDim (PrimeSpectrum T) y = ringKrullDim (Localization.AtPrime y.asIdeal) := by
  have hset : {I : Ideal T | I.IsMaximal ∧ y.asIdeal ≤ I} = {y.asIdeal} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨hy, le_rfl⟩, fun _ h => (hy.eq_of_le h.1.ne_top h.2).symm⟩
  rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height K y).2, hset]
  simp only [Set.mem_singleton_iff, iInf_iInf_eq_left]
  exact (IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal _).symm

/-- **Regularity descends from a flat extension to the local rings below.** Let `S → T` be flat
with `S` Noetherian, let `𝔪` be a prime of `T` lying over the prime `𝔮` of `S`, and let `Sq` be a
model of `S_𝔮`. If `T_𝔪` is a regular local ring then so is `Sq`.

This is Lemma 00OF (`IsRegularLocalRing.of_flat_of_isLocalHom`) applied to the flat local
homomorphism `S_𝔮 → T_𝔪`, which is `Localization.AtPrime.algebraOfLiesOver`. -/
private lemma isRegularLocalRing_of_flat_of_liesOver {S T : Type*} [CommRing S] [CommRing T]
    [IsNoetherianRing S] [Algebra S T] [Module.Flat S T] (𝔮 : Ideal S) [𝔮.IsPrime] (𝔪 : Ideal T)
    [𝔪.IsPrime] [𝔪.LiesOver 𝔮] [IsRegularLocalRing (Localization.AtPrime 𝔪)] (Sq : Type*)
    [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮] : IsRegularLocalRing Sq := by
  let _ := Localization.AtPrime.algebraOfLiesOver 𝔮 𝔪
  have : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl _ ‹_›
  have : IsRegularLocalRing (Localization.AtPrime 𝔮) :=
    .of_flat_of_isLocalHom (Localization.AtPrime 𝔪)
  exact .of_ringEquiv (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮) Sq).toRingEquiv

/-- **The fibre of the differentials is unchanged by a base change realizing it.** Let `k → K`,
`k → S`, `S → T` be a pushout square of `k`-algebras, let `κ` be a field which is an `S`-algebra,
and let `F` be a nontrivial ring which is both a `T`-algebra and a `κ`-algebra, compatibly with
`S`. Then the `F`-fibre of `Ω_{T/K}` and the `κ`-fibre of `Ω_{S/k}` have the same dimension.

`Ω_{T/K} = T ⊗_S Ω_{S/k}` is `KaehlerDifferential.tensorKaehlerEquiv` (Lemma 00RV); the two
`cancelBaseChange`s rewrite `F ⊗_T (T ⊗_S Ω_{S/k})` as `F ⊗_κ (κ ⊗_S Ω_{S/k})`, and taking the
dimension of a base change over a field is `Module.finrank_baseChange`. -/
private lemma finrank_tensorKaehler_eq (k S K T : Type*) [Field k] [CommRing S] [Algebra k S]
    [Field K] [Algebra k K] [CommRing T] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T] (κ F : Type*)
    [Field κ] [CommRing F] [Nontrivial F] [Algebra S κ] [Algebra κ F] [Algebra T F] [Algebra S F]
    [IsScalarTower S T F] [IsScalarTower S κ F] :
    Module.finrank F (F ⊗[T] Ω[T⁄K]) = Module.finrank κ (κ ⊗[S] Ω[S⁄k]) := by
  rw [(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F)
        (KaehlerDifferential.tensorKaehlerEquiv k K S T).symm).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange S T F F Ω[S⁄k]).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange S κ F F Ω[S⁄k]).symm) |>.finrank_eq,
    Module.finrank_baseChange]

/-- The dimension of the fibre of the differentials does not change under a base change to an
extension field which realizes the residue field: if `k → K`, `k → S`, `S → T` is a pushout square
of `k`-algebras, `𝔪 ⊆ T` is an ideal identified with `K` by `e : (T ⧸ 𝔪) ≃ₐ[K] K` and
`ψ : κ(𝔮) → K` is a `k`-algebra map with `e ∘ (S → T ⧸ 𝔪) = ψ ∘ (S → κ(𝔮))`, then the fibre of
`Ω_{T/K}` at `𝔪` and the fibre of `Ω_{S/k}` at `𝔮` have the same dimension. -/
private lemma finrank_tensor_quotient_eq (k S K T : Type*) [Field k] [CommRing S] [Algebra k S]
    [Field K] [Algebra k K] [CommRing T] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T] (q : Ideal S)
    [q.IsPrime] (𝔪 : Ideal T) (e : (T ⧸ 𝔪) ≃ₐ[K] K) (ψ : q.ResidueField →ₐ[k] K)
    (hcomm : ∀ s : S, e (algebraMap S (T ⧸ 𝔪) s) = ψ (algebraMap S q.ResidueField s)) :
    Module.finrank (T ⧸ 𝔪) ((T ⧸ 𝔪) ⊗[T] Ω[T⁄K])
      = Module.finrank q.ResidueField (q.ResidueField ⊗[S] Ω[S⁄k]) := by
  have : Nontrivial (T ⧸ 𝔪) := e.symm.injective.nontrivial
  let _ : Algebra q.ResidueField (T ⧸ 𝔪) := (e.symm.toRingHom.comp ψ.toRingHom).toAlgebra
  have : IsScalarTower S q.ResidueField (T ⧸ 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun s => e.injective <| by
      rw [hcomm s]; exact (e.apply_symm_apply _).symm
  exact finrank_tensorKaehler_eq k S K T q.ResidueField (T ⧸ 𝔪)

/-- The heart of Stacks 00TT: the three conditions and the regularity of `S_𝔮`, given an abstract
base change of `S` to an algebraically closed field `K` and a closed point `𝔪` of it over `𝔮`. -/
private lemma key_of_pushout (k S K T : Type*) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [IsAlgClosed K] [Algebra k K] [CommRing T] [Algebra k T]
    [Algebra K T] [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T]
    [Algebra.IsPushout k K S T] [Algebra.FiniteType K T] (x : PrimeSpectrum S) (𝔪 : Ideal T)
    [h𝔪 : 𝔪.IsMaximal] [𝔪.LiesOver x.asIdeal]
    (hfin : Module.finrank (T ⧸ 𝔪) ((T ⧸ 𝔪) ⊗[T] Ω[T⁄K])
      = Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]))
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq x.asIdeal] :
    List.TFAE
      [Algebra.IsSmoothAt k x.asIdeal,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤
         localKrullDim (PrimeSpectrum S) x,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) =
         localKrullDim (PrimeSpectrum S) x] ∧
      (Algebra.IsSmoothAt k x.asIdeal → IsRegularLocalRing Sq) := by
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.IsPushout k S K T := Algebra.IsPushout.symm ‹_›
  have : Module.Flat S T := flat_of_isPushout k K S T
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  -- the local dimension of `Spec S` at `x` is the Krull dimension of `T_𝔪`
  have hdim : localKrullDim (PrimeSpectrum S) x = ringKrullDim (Localization.AtPrime 𝔪) := by
    rw [show x = PrimeSpectrum.comap (algebraMap S T) ⟨𝔪, h𝔪.isPrime⟩ from
        PrimeSpectrum.ext (𝔪.over_def x.asIdeal), Algebra.IsPushout.localKrullDim_comap_eq k K S T]
    exact localKrullDim_eq_ringKrullDim_atPrime K _ h𝔪
  -- smoothness at `𝔮` over `k` and smoothness at `𝔪` over `K` agree
  have hsm : Algebra.IsSmoothAt k x.asIdeal ↔ Algebra.IsSmoothAt K 𝔪 :=
    FieldExtensionInvariance.isSmoothAt_iff_isSmoothAt_of_isPushout k S K T x.asIdeal 𝔪
  have hts := Algebra.isSmoothAt_tfae_of_isAlgClosed (k := K) (S := T) 𝔪 (Localization.AtPrime 𝔪)
  refine ⟨?_, fun hsmooth => ?_⟩
  · rw [hdim, ← hfin]
    tfae_have 1 ↔ 2 := hsm.trans (hts.out 5 2)
    tfae_have 2 ↔ 3 := hts.out 2 3
    tfae_finish
  · have : IsRegularLocalRing (Localization.AtPrime 𝔪) := (hts.out 5 1).mp (hsm.mp hsmooth)
    exact isRegularLocalRing_of_flat_of_liesOver x.asIdeal 𝔪 Sq

/-- Stacks 00TT, given an algebraically closed field `K/k` and a `k`-embedding of `κ(𝔮)` into it:
the base change is `T = K ⊗[k] S` and the closed point is the kernel of `T → K`. -/
private lemma key_of_algClosed (k S K : Type*) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [IsAlgClosed K] [Algebra k K] (x : PrimeSpectrum S)
    (ψ : x.asIdeal.ResidueField →ₐ[k] K) (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq x.asIdeal] :
    List.TFAE
      [Algebra.IsSmoothAt k x.asIdeal,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤
         localKrullDim (PrimeSpectrum S) x,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) =
         localKrullDim (PrimeSpectrum S) x] ∧
      (Algebra.IsSmoothAt k x.asIdeal → IsRegularLocalRing Sq) := by
  set φ : (K ⊗[k] S) →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K)
      (ψ.comp (IsScalarTower.toAlgHom k S x.asIdeal.ResidueField))
      (fun _ _ => Commute.all _ _) with hφdef
  have hφ : Function.Surjective φ := fun a => ⟨a ⊗ₜ 1, by simp [hφdef]⟩
  have hcomm : ∀ s : S, φ (algebraMap S (K ⊗[k] S) s)
      = ψ (algebraMap S x.asIdeal.ResidueField s) := fun s => by
    simp [hφdef, Algebra.TensorProduct.right_algebraMap_apply]
  have : (RingHom.ker (φ : (K ⊗[k] S) →+* K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (φ : (K ⊗[k] S) →+* K) hφ
  have hcomap : (RingHom.ker (φ : (K ⊗[k] S) →+* K)).comap (algebraMap S (K ⊗[k] S))
      = x.asIdeal := by
    have hinj : Function.Injective ψ := ψ.toRingHom.injective
    ext s
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change φ (algebraMap S (K ⊗[k] S) s) = 0 ↔ s ∈ x.asIdeal
    rw [hcomm s, ← map_zero ψ, hinj.eq_iff, ← RingHom.mem_ker,
      Ideal.ker_algebraMap_residueField]
  have : (RingHom.ker (φ : (K ⊗[k] S) →+* K)).LiesOver x.asIdeal := ⟨hcomap.symm⟩
  exact key_of_pushout k S K (K ⊗[k] S) x (RingHom.ker (φ : (K ⊗[k] S) →+* K))
    (finrank_tensor_quotient_eq k S K (K ⊗[k] S) x.asIdeal _
      (Ideal.quotientKerAlgEquivOfSurjective hφ) ψ fun s => by rw [← hcomm s]; rfl) Sq

/-- **Smoothness at a point is the differential fibre having the local dimension**
(Stacks 00TT). -/
@[sga "1 II 5.3" "affine case"]
public theorem solution
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq x.asIdeal] :
    List.TFAE
      [Algebra.IsSmoothAt k x.asIdeal,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤
         localKrullDim (PrimeSpectrum S) x,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) =
         localKrullDim (PrimeSpectrum S) x] ∧
      (Algebra.IsSmoothAt k x.asIdeal → IsRegularLocalRing Sq) :=
  key_of_algClosed k S (AlgebraicClosure x.asIdeal.ResidueField) x
    (IsScalarTower.toAlgHom k x.asIdeal.ResidueField
      (AlgebraicClosure x.asIdeal.ResidueField)) Sq

end Stacks.Smooth.LocalDimensionCriterion

end

/-!
# Smoothness at a point over an arbitrary field

Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S` and let `x ∈ X` be the
point given by a prime `𝔮 ⊆ S`. The fibre of the module of differentials at `x` is the
`κ(𝔮)`-vector space `Ω_{S/k} ⊗_S κ(𝔮)`; since `Ω_{S/k}` is a finite `S`-module its dimension is
finite. Comparing that dimension with the local dimension `dim_x X` of the space at `x` detects
smoothness: it is never smaller, and `S/k` is smooth at `𝔮` exactly when it is no larger.

This is the arbitrary-field companion of Lemma 00TS, which is the same statement for a maximal
ideal of an algebraically closed field's finite type algebra and where `dim_x X = dim S_𝔪`. Here
neither simplification is available: `𝔮` is any prime, so `dim_x X` — the least dimension of an
open neighbourhood of `x` — is genuinely the local dimension of the space rather than the Krull
dimension of `S_𝔮`, and `κ(𝔮)` need not equal `k`. The source's proof reduces to 00TS by base
change to an algebraically closed `K/k` admitting a `k`-embedding of `κ(𝔮)` and to the maximal
ideal of `S_K = K ⊗_k S` cut out by it, using that base change preserves the local dimension
(Lemma 00P4), the module of differentials (Lemma 00RV) and smoothness in both directions
(Lemma 00TG).

Over a field that is not perfect regularity of `S_𝔮` is strictly weaker than smoothness, so it is
a *consequence* of the three conditions and not a fourth equivalent one: for `k = 𝔽_p(t)` and
`S = k[X]/(X^p - t)` the ring `S` is a field, hence `S_𝔮 = S` is regular and `dim_x X = 0`, while
`Ω_{S/k} = S · dX` has one-dimensional fibre and `S` is not smooth over `k`. The statement below
therefore conjoins the three-way equivalence with the implication from smoothness to regularity,
which is the source's "moreover".

## Main results

* `Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing`: the three conditions of Lemma
  00TT are equivalent, and they imply that the local ring `S_𝔮` is regular.

## Implementation notes

*The point and its prime are one datum.* The source's "a prime `𝔮 ⊆ S` corresponding to `x ∈ X`"
is a single `x : PrimeSpectrum S` with `𝔮 = x.asIdeal`, as in the siblings 00OT and 00P1, rather
than a prime together with the assertion that `x` corresponds to it.

*`dim_x X` is `TopologicalSpace.localKrullDim`.* That definition, already in this library, is
Topology Definition 0055 (4): the infimum over open neighbourhoods `U` of `x` of
`topologicalKrullDim U`, the source's dimension of a space. It is attained, and by Lemma 00OT it
also equals the largest dimension of an irreducible component of `X` through `x` and the least of
the heights of the maximal ideals above `𝔮`; the statement uses none of those reformulations, so
it says the source's `dim_x X` and not a substitute for it. Its values lie in
`WithBot ℕ∞ ≃ {-∞} ∪ ℤ≥0 ∪ {+∞}`, so the finite dimension of the fibre is coerced there.

*The fibre is `κ(𝔮) ⊗[S] Ω[S⁄k]`.* The two tensor factors are transposed relative to the source's
`Ω_{S/k} ⊗_S κ(𝔮)` because Mathlib puts the scalar action of the base-changed ring on the *left*
factor, which is what makes the base change a `κ(𝔮)`-vector space; `TensorProduct.comm` is the
identification and it is `κ(𝔮)`-linear. The residue field is `Ideal.ResidueField x.asIdeal`, the
residue field of the local ring at `𝔮`, which for a maximal ideal is the `S ⧸ 𝔪` used in 00TS but
for a general prime is `Frac(S ⧸ 𝔮)`. Because `Algebra.FiniteType k S` gives
`Module.Finite S Ω[S⁄k]`, the fibre is a finite-dimensional `κ(𝔮)`-vector space and
`Module.finrank` is the source's `dim_{κ(𝔮)}` rather than the junk value `0`.

*`S_𝔮` is an arbitrary model.* `Sq` is any `S`-algebra with `IsLocalization.AtPrime Sq x.asIdeal`,
so the "moreover" is the statement its consumers apply; `Localization.AtPrime x.asIdeal` is a
witness. Regularity is Mathlib's `IsRegularLocalRing`, which is the source's Definition 00OD (as
recorded for the sibling 00OF).

*Smoothness at `𝔮` is Mathlib's `Algebra.IsSmoothAt k x.asIdeal`.* By 00TA this is equivalent to
the source's "there is `g ∉ 𝔮` with `S_g` smooth over `k`"; 00TS states both readings, and here
the named predicate is the one a reader cites and the entry point to `Algebra.smoothLocus`.

Faithfulness to [StacksProject 00TT], point by point.

1. No hypothesis is dead. `Field k` cannot be weakened to a commutative ring: for `k = S = ℤ` at
   the point `x = (p)`, the identity `ℤ → ℤ` is smooth at `(p)` and `Ω_{ℤ/ℤ} = 0` has fibre of
   dimension `0`, while `dim_x Spec ℤ = 1`, so (1) holds and (3) fails. `Algebra.FiniteType k S`
   cannot be dropped: `S = ℚ(t)` over `k = ℚ` is a localization of `ℚ[t]`, hence formally smooth,
   so (1) holds at `𝔮 = 0`, while `dim_x X = 0` and `Ω_{S/k} = S · dt` has one-dimensional fibre,
   so (3) fails again. `x` occurs in every item, and `IsLocalization.AtPrime Sq x.asIdeal` is what
   makes `Sq` the ring `S_𝔮` of the final conjunct.
2. The scalars and the base are the source's: the differentials are those of `S` over `k`
   (`Ω[S⁄k]`), the fibre is taken over `S` at `𝔮` and its dimension over `κ(𝔮)`, `localKrullDim`
   is that of `Spec S` at `x`, and `IsRegularLocalRing Sq` is about the local ring `S_𝔮` — no base
   change to an algebraically closed field appears, that being a device of the proof.
3. Where the source names a canonical object the statement pins it rather than asserting
   existence: the fibre is the base change along `algebraMap S κ(𝔮)`, the dimension is
   `localKrullDim` at the given `x`, and `Sq` is pinned as a localization of `S` at `𝔮` along
   `algebraMap S Sq`.
4. The instantiation is not degenerate. For `k = ℚ`, `S = k[X]`, `x = (X)` and
   `Sq = Localization.AtPrime (X)` all three items hold: the fibre of `Ω_{S/k} = S · dX` is
   one-dimensional and `dim_x X = 1`, and `S_𝔮` is a discrete valuation ring. A non-maximal `𝔮` is
   equally non-vacuous: for `S = k[X, Y]` at the generic point `x = (X)` of a line the fibre is
   two-dimensional over `κ(𝔮) = k(Y)` and `dim_x X = 2`. And no item is automatic: for
   `S = k[X, Y]/(XY)` at the origin `x = (X, Y)` the fibre is two-dimensional while
   `dim_x X = 1`, so (2) and (3) fail, as does (1).

## References

* [StacksProject 00TT](https://stacks.math.columbia.edu/tag/00TT)

## Tags

smooth, smooth at a point, module of differentials, local dimension, regular local ring,
finite type algebra, residue field
-/

@[expose] public section

open TensorProduct TopologicalSpace in
/-- **Smoothness at a point is the differential fibre having the local dimension**
(Stacks 00TT). Let `k` be a field, let `S` be a finite type `k`-algebra, let `X = Spec S`, let
`x ∈ X` be a point with prime ideal `𝔮 = x.asIdeal`, and let `Sq` be a model of `S_𝔮`. The
following are equivalent: (1) `S` is smooth at `𝔮` over `k`; (2)
`dim_{κ(𝔮)} Ω_{S/k} ⊗_S κ(𝔮) ≤ dim_x X`; (3) the same with equality. Moreover, in this case the
local ring `S_𝔮` is regular. -/
@[stacks 00TT "`𝔮` and `x` are one datum `x : PrimeSpectrum S` with `𝔮 = x.asIdeal`; `dim_x X` is
`TopologicalSpace.localKrullDim`, Topology Definition 0055 (4); `κ(𝔮)` is
`Ideal.ResidueField x.asIdeal` and the fibre `Ω_{S/k} ⊗_S κ(𝔮)` is the base change
`κ(𝔮) ⊗[S] Ω[S⁄k]`, whose factors are transposed so that the left one carries the scalar action
making it a `κ(𝔮)`-vector space; `S_𝔮` is an arbitrary model `Sq`. The source's `moreover` is the
final conjunct and not a fourth equivalent item, regularity being strictly weaker than smoothness
over a nonperfect field. See the module docstring.",
  sga "1 II 5.3" "first assertion",
  ega "IV 17.15.5" "affine case", sga "1 II 5.5" "affine (i)<=>(ii bis)"]
public theorem Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq x.asIdeal] :
    List.TFAE
      [Algebra.IsSmoothAt k x.asIdeal,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤
         localKrullDim (PrimeSpectrum S) x,
       (Module.finrank x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) =
         localKrullDim (PrimeSpectrum S) x] ∧
      (Algebra.IsSmoothAt k x.asIdeal → IsRegularLocalRing Sq) :=
    by apply Stacks.Smooth.LocalDimensionCriterion.solution

end
