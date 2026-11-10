module

import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
public import StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.MvPolynomial.FiberAtPrime
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular sequences, flatness and the conormal module of a relative global complete intersection

Let `P` present `S = R[x_1, …, x_n]/(f_1, …, f_c)` as a relative global complete intersection
(Definition 00SP): every nonempty fibre of `Spec(S) → Spec(R)` has dimension `n - c`. Write
`I = (f_1, …, f_c)` for the kernel of `R[x_1, …, x_n] → S`. This file proves the three parts of
Stacks 00SV: for every prime `𝔮` of `S`, with corresponding prime `𝔮'` of `R[x_1, …, x_n]`,

1. `f_1, …, f_c` is a regular sequence in the local ring `R[x_1, …, x_n]_{𝔮'}`;
2. each of the rings `R[x_1, …, x_n]_{𝔮'}/(f_1, …, f_i)` is flat over `R`;
3. the conormal module `I/I²` is free over `S` with basis the classes of `f_1, …, f_c`.

## Main results

* `Algebra.Presentation.isRegular_localization_relation`: part (1).
* `Algebra.Presentation.flat_localization_quotient_relation`: part (2).
* `Algebra.Presentation.exists_basis_cotangent_relation`: part (3).

## Implementation notes

*Over a Noetherian base* the argument is the source's. The fibre `κ(p₀)[x_1, …, x_n]/(f)` of a
relative global complete intersection has dimension `n - c`; a polynomial ring over a field is
Cohen-Macaulay and its spectrum is irreducible, so Lemma 00R9 makes the `f_i` a regular sequence
in its local rings. The fibre ring of `R₀[x]_{𝔮₀'}` over `(R₀)_{p₀}` is such a local ring
(`MvPolynomial.FiberAtPrime.isLocalization`), and the local
criterion for flatness, Lemma 00MG, lifts the regular sequence to `R₀[x]_{𝔮₀'}` together with the
flatness of the partial quotients (`isRegular_and_flat_localization`).

*Over an arbitrary base the source writes `R` as the filtered colimit of its finite type
`ℤ`-subalgebras, descends the presentation to one of them by Lemma 00SU and passes to the colimit
(Lemmas 05UU and 00DB).* Here each of the three conclusions is instead reduced to a finitary
statement, and only the finitely many polynomials that statement involves are descended — to the
finite type `ℤ`-subalgebra `R₀ ⊆ R` their coefficients generate (`exists_descent`). This avoids
Lemma 00SU and the colimit altogether. The fibre over `p₀ = 𝔮' ∩ R₀` has the same dimension as the
one over `p = 𝔮' ∩ R`, being a base change of it along the residue field extension (Lemma 00P3,
`Algebra.IsPushout.ringKrullDim_eq`).

* Part (1) is the implication `f_{i+1} a ∈ (f_1, …, f_i) ⟹ a ∈ (f_1, …, f_i)` in `R[x]_{𝔮'}`.
  Cleared of denominators its hypothesis is one polynomial identity; over `R₀` the descended
  relations are regular, and the conclusion maps back along `R₀[x]_{𝔮₀'} → R[x]_{𝔮'}`.
* Part (2) is the equational criterion for flatness (Lemma 00HK): a relation `∑ r_j x_j = 0` over
  `R` in `R[x]_{𝔮'}/(f_1, …, f_i)` is, cleared of denominators, finitely many polynomial identities;
  over `R₀` the relation is trivial because the descended partial quotient is flat over `R₀`, and
  the trivialization maps back.
* Part (3): surjectivity of `S^c → I/I²`, `e_i ↦ f_i`, is
  `Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker`, and injectivity is the implication
  `∑ ã_i f_i ∈ I² ⟹ ã_i ∈ I`, tested one maximal ideal of `S` at a time. Over `R₀` the relations
  among the weakly regular sequence `f_i` are trivial modulo `I²` (`mem_span_of_sum_mem_sq`, the
  degree one part of Lemma 00LN read through `Ideal.free_and_finrank_cotangent_of_isWeaklyRegular`),
  which replaces the source's appeal to part (1) and Lemma 00HN.

## References

* [Stacks 00SV](https://stacks.math.columbia.edu/tag/00SV), Lemma 10.136.12
* [Stacks 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5, the relative
  global complete intersections
* [Stacks 00R9](https://stacks.math.columbia.edu/tag/00R9),
  `Module.IsMaximalCohenMacaulay.ringKrullDim_quotient_add_length_eq_and_isRegular`, and
  [Stacks 00MG](https://stacks.math.columbia.edu/tag/00MG),
  `Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal`
* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK),
  `Module.Flat.iff_forall_isTrivialRelation`
* [Stacks 00P3](https://stacks.math.columbia.edu/tag/00P3), `Algebra.IsPushout.ringKrullDim_eq`
* [Stacks 00LN](https://stacks.math.columbia.edu/tag/00LN), quasi-regular sequences, whose degree
  one part is `Ideal.free_and_finrank_cotangent_of_isWeaklyRegular`
-/

@[expose] public section

open MvPolynomial TensorProduct

universe u

/-! ### The fibre over a field: the relations are a regular sequence (Stacks 00R9) -/

/-- A field is a Cohen-Macaulay local ring: both its depth and its dimension are `0`. -/
alias isMaximalCohenMacaulay_self_of_isField' := isMaximalCohenMacaulay_self_of_isField

/-- An irreducible space is equidimensional: it has exactly one irreducible component. -/
private lemma equidimensional_of_irreducibleSpace (X : Type*) [TopologicalSpace X]
    [IrreducibleSpace X] : TopologicalSpace.Equidimensional X := by
  intro Z hZ W hW
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ hW
  rw [hZ, hW]

/-- Let `k` be a field and `f₁, …, f_c ∈ k[xᵢ]` (finitely many variables) cut out a closed subset
of dimension at most `n - c`, `n` the number of variables. Then the `fⱼ` form a regular sequence
in the local ring of `k[xᵢ]` at any prime containing them. -/
private lemma isRegular_of_ringKrullDim_le {k : Type*} [Field k] {ι : Type*} [Finite ι] {c : ℕ}
    (f : Fin c → MvPolynomial ι k)
    (hdim :
      ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) + (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞))
    (q : Ideal (MvPolynomial ι k)) [q.IsPrime] (hq : Ideal.span (Set.range f) ≤ q) (Sq : Type*)
    [CommRing Sq] [Algebra (MvPolynomial ι k) Sq] [IsLocalization.AtPrime Sq q] :
    RingTheory.Sequence.IsRegular Sq ((List.ofFn f).map (algebraMap (MvPolynomial ι k) Sq)) := by
  have hk :
    ∀ (p : Ideal k) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun _ _ => isMaximalCohenMacaulay_self_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hS :
    ∀ (p : Ideal (MvPolynomial ι k)) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun p _ =>
    Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial hk p
      (Localization.AtPrime p)
  have hd : ringKrullDim (MvPolynomial ι k) = ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Semifield.toIsField k), zero_add,
      ENat.card_eq_coe_natCard]
    rfl
  have hlen : (List.ofFn f).length = c := List.length_ofFn
  have hne : Ideal.ofList (List.ofFn f) ≠ ⊤ := by
    rw [Ideal.ofList_ofFn]
    exact fun h => Ideal.IsPrime.ne_top ‹q.IsPrime› (top_le_iff.mp (h ▸ hq))
  refine
    (Module.IsMaximalCohenMacaulay.ringKrullDim_quotient_add_length_eq_and_isRegular (k := k) hS
          (equidimensional_of_irreducibleSpace _) (Nat.card ι) hd (List.ofFn f) hne ?_).2
      q (by rwa [Ideal.ofList_ofFn]) Sq
  rw [Ideal.ofList_ofFn, hlen]
  exact hdim

/-! ### Base change of a polynomial quotient -/

/-- `K ⊗_R (R[xᵢ]/(f₁, …, f_c)) ≅ K[xᵢ]/(f̄₁, …, f̄_c)` as `K`-algebras. -/
lemma nonempty_algEquiv_tensor_quotient {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] {ι : Type*} {c : ℕ} (f : Fin c → MvPolynomial ι R) :
    Nonempty
      ((K ⊗[R] (MvPolynomial ι R ⧸ Ideal.span (Set.range f))) ≃ₐ[K]
        (MvPolynomial ι K ⧸
          Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap R K) (f i)))) := by
  refine
    ⟨(Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial ι R) K
            (Ideal.span (Set.range f))).trans
        (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R K) ?_)⟩
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  simp [Function.comp_def]

/-! ### Descent to a finite type `ℤ`-subalgebra -/

/-- Finitely many polynomials over `R` are the images of polynomials over a finite type
ℤ-subalgebra of `R`. -/
private lemma exists_fg_subalgebra_map_eq {R : Type*} [CommRing R] {ι : Type*} {n : Type*}
    [Finite n] (g : n → MvPolynomial ι R) :
    ∃ (R₀ : Subalgebra ℤ R) (g₀ : n → MvPolynomial ι R₀),
      IsNoetherianRing R₀ ∧ ∀ i, MvPolynomial.map (algebraMap R₀ R) (g₀ i) = g i := by
  classical
  let _ := Fintype.ofFinite n
  set T : Finset R :=
    Finset.univ.biUnion fun i : n => (g i).support.image fun d => (g i).coeff d with
    hTdef
  set R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ (T : Set R) with hR₀
  have hmem : ∀ (i : n) (d : ι →₀ ℕ), d ∈ (g i).support → (g i).coeff d ∈ R₀ := by
    intro i d hd
    refine Algebra.subset_adjoin ?_
    simp only [Finset.mem_coe, hTdef, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_image_of_mem _ hd⟩
  have key : ∀ i, ∃ p : MvPolynomial ι R₀, MvPolynomial.map (algebraMap R₀ R) p = g i := by
    intro i
    refine
      ⟨∑ d ∈ (g i).support,
          MvPolynomial.monomial d
            (if h : d ∈ (g i).support then (⟨(g i).coeff d, hmem i d h⟩ : R₀) else 0),
        ?_⟩
    rw [map_sum]
    conv_rhs => rw [(g i).as_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [MvPolynomial.map_monomial]
    simp [hd]
  choose g₀ hg₀ using key
  have : Algebra.FiniteType ℤ R₀ := Algebra.FiniteType.adjoin_of_finite T.finite_toSet
  exact ⟨R₀, g₀, Algebra.FiniteType.isNoetherianRing ℤ R₀, hg₀⟩

/-! ### Relations among a weakly regular sequence -/

/-- **The relations among a weakly regular sequence are trivial modulo `I²`.** If `f₀, …, f_{c-1}`
is a weakly regular sequence generating a proper ideal `I`, then `∑ aᵢ fᵢ ∈ I²` forces `aᵢ ∈ I`
for every `i`. -/
private lemma mem_span_of_sum_mem_sq {A : Type*} [CommRing A] {c : ℕ} (f : Fin c → A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f))
    (hne : Ideal.span (Set.range f) ≠ ⊤) {a : Fin c → A}
    (ha : ∑ i, a i * f i ∈ Ideal.span (Set.range f) ^ 2) (i : Fin c) :
    a i ∈ Ideal.span (Set.range f) := by
  classical
  have key :=
    Ideal.free_and_finrank_cotangent_of_isWeaklyRegular (List.ofFn f) hreg
      (by
        rw [Ideal.ofList_ofFn f]; exact hne)
  rw [Ideal.ofList_ofFn f, List.length_ofFn] at key
  obtain ⟨-, hrank⟩ := key
  set I : Ideal A := Ideal.span (Set.range f) with hI
  have hmem : ∀ j : Fin c, f j ∈ I := fun j ↦ Ideal.subset_span ⟨j, rfl⟩
  set w : Fin c → I.Cotangent := fun j ↦ I.toCotangent ⟨f j, hmem j⟩
  have hsmul : ∀ (r : A) (m : I.Cotangent), Ideal.Quotient.mk I r • m = r • m := fun r m ↦ by
    rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  have hkey :
    ∀ (b : Fin c → A) (hb : ∑ j, b j * f j ∈ I),
      ∑ j, Ideal.Quotient.mk I (b j) • w j = I.toCotangent ⟨∑ j, b j * f j, hb⟩ := by
    intro b hb
    have hc : (⟨∑ j, b j * f j, hb⟩ : I) = ∑ j, b j • (⟨f j, hmem j⟩ : I) :=
      Subtype.ext
        (by
          push_cast; exact Finset.sum_congr rfl fun j _ ↦ rfl)
    rw [hc, map_sum]
    exact
      Finset.sum_congr rfl fun j _ ↦ by
        rw [hsmul]; exact (map_smul _ _ _).symm
  have hspan : ⊤ ≤ Submodule.span (A ⧸ I) (Set.range w) := by
    intro x _
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective x
    have hy : (y : A) ∈ Ideal.span (Set.range f) := by
      rw [← hI]; exact y.2
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
    have hbmem : ∑ j, b j * f j ∈ I := by
      rw [hb]; exact y.2
    refine
      (Submodule.mem_span_range_iff_exists_fun (A ⧸ I)).2 ⟨fun j ↦ Ideal.Quotient.mk I (b j), ?_⟩
    rw [hkey b hbmem]
    exact congrArg I.toCotangent (Subtype.ext hb)
  have hli : LinearIndependent (A ⧸ I) w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, hrank])
  have hzero : ∑ j, Ideal.Quotient.mk I (a j) • w j = 0 := by
    rw [hkey a (Ideal.pow_le_self two_ne_zero ha)]
    exact (I.toCotangent_eq_zero _).2 ha
  have hai := Fintype.linearIndependent_iff.1 hli (fun j ↦ Ideal.Quotient.mk I (a j)) hzero i
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hai

/-- Regularity of the images of a list in `A ⧸ J` depends only on the ideal `J`. -/
lemma isRegular_quotient_congr {A : Type*} [CommRing A] {J₁ J₂ : Ideal A} (h : J₁ = J₂)
    (fs : List A) (H : RingTheory.Sequence.IsRegular (A ⧸ J₂) (fs.map (Ideal.Quotient.mk J₂))) :
    RingTheory.Sequence.IsRegular (A ⧸ J₁) (fs.map (Ideal.Quotient.mk J₁)) := by
  subst h; exact H

/-- The first `i` generators of the image ideal are the image of the first `i` generators. -/
private lemma ofList_take_map_eq_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (l : List A) (i : ℕ) :
    Ideal.ofList ((l.map (algebraMap A B)).take i) =
      (Ideal.ofList (l.take i)).map (algebraMap A B) := by
  rw [Ideal.map_ofList, List.map_take]

/-! ### Over a Noetherian base: the relations are a regular sequence with flat partial quotients -/

section Heart

variable {R₀ : Type*} [CommRing R₀] [IsNoetherianRing R₀] {ι : Type*} [Finite ι] {c : ℕ}

/-- **Parts (1) and (2) of Stacks 00SV over a Noetherian base, at one prime.** Let `R₀` be
Noetherian, let `f₁, …, f_c ∈ R₀[xᵢ]` lie in a prime `Q`, and suppose the fibre
`κ(p₀)[xᵢ]/(f̄)` over `p₀ = Q ∩ R₀` has dimension at most `n - c`. Then the `fⱼ` form a regular
sequence in `R₀[xᵢ]_Q`, and each partial quotient `R₀[xᵢ]_Q/(f₁, …, fᵢ)` is flat over `R₀`. The
fibre ring of `R₀[xᵢ]_Q` is a localization of `κ(p₀)[xᵢ]`, where the `f̄ⱼ` are regular by
Lemma 00R9; the local criterion for flatness, Lemma 00MG, lifts both conclusions. -/
@[sga "7 VI 4.14" "partial"]
private lemma isRegular_and_flat_localization (f : Fin c → MvPolynomial ι R₀)
    (Q : Ideal (MvPolynomial ι R₀)) [Q.IsPrime] (hQ : Ideal.span (Set.range f) ≤ Q)
    (p₀ : Ideal R₀) [p₀.IsPrime] (hp₀ : p₀ = Q.under R₀)
    (hdim :
      ringKrullDim
            (MvPolynomial ι p₀.ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦ MvPolynomial.map (algebraMap R₀ p₀.ResidueField) (f i))) +
          (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
        ((List.ofFn f).map (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))) ∧
      ∀ i, Module.Flat R₀ (Localization.AtPrime Q ⧸ Ideal.ofList
        (((List.ofFn f).map
          (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))).take i)) := by
  subst hp₀
  classical
  let : Algebra (Localization.AtPrime (Q.under R₀)) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver (Q.under R₀) Q
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl (Localization.AtPrime Q) inferInstance
  have : IsNoetherianRing (Localization.AtPrime (Q.under R₀)) :=
    IsLocalization.isNoetherianRing (Q.under R₀).primeCompl
      (Localization.AtPrime (Q.under R₀)) inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime (Q.under R₀)) (Localization.AtPrime Q)) := by
    rw [Localization.AtPrime.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.Flat (Localization.AtPrime (Q.under R₀)) (Localization.AtPrime Q) := by
    have h1 : Module.Flat R₀ (Localization.AtPrime Q) := Module.Flat.trans R₀ (MvPolynomial ι R₀) _
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (Q.under R₀))
      (Q.under R₀).primeCompl (Localization.AtPrime Q)).2 h1
  have hfib : RingTheory.Sequence.IsRegular
      (Localization.AtPrime Q ⧸
        Ideal.map (algebraMap (Localization.AtPrime (Q.under R₀)) (Localization.AtPrime Q))
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under R₀))))
      (((List.ofFn f).map (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (Ideal.map
          (algebraMap (Localization.AtPrime (Q.under R₀)) (Localization.AtPrime Q))
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under R₀)))))) := by
    refine isRegular_quotient_congr
      (J₂ := Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Q.under R₀)) ?_ _ ?_
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    · let := MvPolynomial.FiberAtPrime.algebra Q
      have := MvPolynomial.FiberAtPrime.isLocalization Q
      have :=
        isRegular_of_ringKrullDim_le (fun i ↦ MvPolynomial.FiberAtPrime.residueMap Q (f i)) hdim
          (MvPolynomial.FiberAtPrime.basePrime Q)
          (Ideal.span_le.2 (by
            rintro x ⟨i, rfl⟩
            exact MvPolynomial.FiberAtPrime.residueMap_mem_basePrime Q
              (hQ (Ideal.subset_span ⟨i, rfl⟩))))
          (MvPolynomial.FiberAtPrime Q)
      simpa only [List.map_ofFn, Function.comp_def, RingHom.algebraMap_toAlgebra,
        MvPolynomial.FiberAtPrime.ofResidueField_residueMap, MvPolynomial.FiberAtPrime.mk,
        RingHom.comp_apply] using this
  obtain ⟨hreg, hflat⟩ :=
    Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal hfib
  refine ⟨hreg, fun i ↦ ?_⟩
  have := hflat i
  exact Module.Flat.trans R₀ (Localization.AtPrime (Q.under R₀)) _

end Heart

/-! ### Dimension transfer along a change of base ring -/

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The dimension of `k[x_i]/(f)` is unchanged by extending the field `k ⊆ K` (Lemma 00P3). -/
private lemma ringKrullDim_quotient_map_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} [Finite ι] {c : ℕ} (f : Fin c → MvPolynomial ι k) :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) =
      ringKrullDim
        (MvPolynomial ι K ⧸
          Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap k K) (f i))) := by
  have h1 :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) =
      ringKrullDim (K ⊗[k] (MvPolynomial ι k ⧸ Ideal.span (Set.range f))) :=
    Algebra.IsPushout.ringKrullDim_eq k K _ _
  obtain ⟨e⟩ := nonempty_algEquiv_tensor_quotient (R := k) K f
  rw [h1, ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

/-- The dimension of `k[x_i]/(f)` is unchanged by extending the field `k ⊆ K` (Lemma 00P3). -/
alias ringKrullDim_quotient_map_eq' := ringKrullDim_quotient_map_eq

/-- The fibre dimension over `p₀ = p ∩ R₀` of relations descended to `R₀ ⊆ R` is the fibre dimension
over `p` of the original relations; in particular the bound `dim + c ≤ n` descends. -/
private lemma ringKrullDim_fiber_le_of_algebraMap {R₀ R : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] {ι : Type*} [Finite ι] {c : ℕ} (f₀ : Fin c → MvPolynomial ι R₀) (p : Ideal R)
    [p.IsPrime]
    (hdim :
      ringKrullDim
            (MvPolynomial ι p.ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map ((algebraMap R p.ResidueField).comp (algebraMap R₀ R))
                    (f₀ i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    ringKrullDim
          (MvPolynomial ι (Ideal.under R₀ p).ResidueField ⧸
            Ideal.span
              (Set.range fun i ↦
                MvPolynomial.map (algebraMap R₀ (Ideal.under R₀ p).ResidueField) (f₀ i))) +
        (c : WithBot ℕ∞) ≤
      ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  let : Algebra (Ideal.under R₀ p).ResidueField p.ResidueField :=
    (Ideal.ResidueField.map (Ideal.under R₀ p) p (algebraMap R₀ R) rfl).toAlgebra
  have hcomp :
    (algebraMap (Ideal.under R₀ p).ResidueField p.ResidueField).comp
        (algebraMap R₀ (Ideal.under R₀ p).ResidueField) =
      (algebraMap R p.ResidueField).comp (algebraMap R₀ R) := by
    refine RingHom.ext fun r ↦ ?_
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      RingHom.comp_apply]
  have hmain :=
    ringKrullDim_quotient_map_eq (k := (Ideal.under R₀ p).ResidueField) (K := p.ResidueField)
      (fun i ↦ MvPolynomial.map (algebraMap R₀ _) (f₀ i))
  have hfam :
    (fun i ↦
        MvPolynomial.map (algebraMap (Ideal.under R₀ p).ResidueField p.ResidueField)
          (MvPolynomial.map (algebraMap R₀ (Ideal.under R₀ p).ResidueField) (f₀ i))) =
      fun i ↦ MvPolynomial.map ((algebraMap R p.ResidueField).comp (algebraMap R₀ R)) (f₀ i) := by
    funext i
    rw [MvPolynomial.map_map, hcomp]
  rw [hfam] at hmain
  rw [hmain]
  exact le_of_eq hdim

/-- The fibre dimension over `p₀ = p ∩ R₀` of relations descended to `R₀ ⊆ R` is the fibre dimension
over `p` of the original relations; in particular the bound `dim + c ≤ n` descends. -/
alias ringKrullDim_fiber_le_of_algebraMap' := ringKrullDim_fiber_le_of_algebraMap

end BaseChange

/-! ### Descent to a Noetherian base -/

section Descent

variable {R : Type*} [CommRing R] {ι : Type*} {c : ℕ}

/-- **Finitely many polynomials descend to a Noetherian base on which parts (1) and (2) of
Stacks 00SV hold.** Let `f₁, …, f_c ∈ R[xᵢ]` lie in a prime `Q` over which the fibre
`κ(p)[xᵢ]/(f̄)`, `p = Q ∩ R`, has dimension `n - c`, and let `g` be finitely many further
polynomials. There is a finite type `ℤ`-subalgebra `R₀ ⊆ R` over which all of these are defined,
and over which, at `Q₀ = Q ∩ R₀[xᵢ]`, the descended `fⱼ` form a regular sequence in `R₀[xᵢ]_{Q₀}`
with partial quotients flat over `R₀`.

The fibre over `Q₀ ∩ R₀` has the same dimension as the one over `p`, being a base change of it
along the residue field extension (Lemma 00P3); `R₀` is Noetherian, so
`isRegular_and_flat_localization` applies. -/
private lemma exists_descent {R : Type u} [CommRing R] [Finite ι] (f : Fin c → MvPolynomial ι R)
    (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime] (hQ : Ideal.span (Set.range f) ≤ Q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Q.under R).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Q.under R).ResidueField) (f i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞))
    {m : Type*} [Finite m] (g : m → MvPolynomial ι R) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R₀ R) (f₀ : Fin c → MvPolynomial ι R₀)
      (g₀ : m → MvPolynomial ι R₀), Function.Injective (algebraMap R₀ R) ∧
      (∀ i, MvPolynomial.map (algebraMap R₀ R) (f₀ i) = f i) ∧
      (∀ j, MvPolynomial.map (algebraMap R₀ R) (g₀ j) = g j) ∧
      RingTheory.Sequence.IsRegular
        (Localization.AtPrime (Q.comap (MvPolynomial.map (algebraMap R₀ R))))
        ((List.ofFn f₀).map (algebraMap (MvPolynomial ι R₀)
          (Localization.AtPrime (Q.comap (MvPolynomial.map (algebraMap R₀ R)))))) ∧
      ∀ i, Module.Flat R₀ (Localization.AtPrime (Q.comap (MvPolynomial.map (algebraMap R₀ R))) ⧸
        Ideal.ofList (((List.ofFn f₀).map (algebraMap (MvPolynomial ι R₀)
          (Localization.AtPrime (Q.comap (MvPolynomial.map (algebraMap R₀ R)))))).take i)) := by
  obtain ⟨R₀, g₀, hnoeth, hg₀⟩ := exists_fg_subalgebra_map_eq (Sum.elim f g)
  have := hnoeth
  have hf : ∀ j, MvPolynomial.map (algebraMap R₀ R) (g₀ (Sum.inl j)) = f j :=
    fun j ↦ hg₀ (Sum.inl j)
  set Q₀ := Q.comap (MvPolynomial.map (algebraMap R₀ R)) with hQ₀def
  have hQ₀ : Ideal.span (Set.range fun j ↦ g₀ (Sum.inl j)) ≤ Q₀ := by
    refine Ideal.span_le.2 ?_
    rintro x ⟨j, rfl⟩
    rw [SetLike.mem_coe, hQ₀def, Ideal.mem_comap, hf]
    exact hQ (Ideal.subset_span ⟨j, rfl⟩)
  have hunder : (Q.under R).under R₀ = Q₀.under R₀ := by
    rw [Ideal.under, Ideal.under, Ideal.under, hQ₀def, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun r ↦ ?_
    simp [MvPolynomial.algebraMap_eq]
  have hfam : (fun j ↦ MvPolynomial.map
      ((algebraMap R (Q.under R).ResidueField).comp (algebraMap R₀ R)) (g₀ (Sum.inl j))) =
      fun j ↦ MvPolynomial.map (algebraMap R (Q.under R).ResidueField) (f j) :=
    funext fun j ↦ by rw [← MvPolynomial.map_map, hf]
  have hdim₀ := ringKrullDim_fiber_le_of_algebraMap (R₀ := R₀) (R := R) _ (Q.under R)
    (by rw [hfam]; exact hdim)
  exact ⟨↥R₀, inferInstance, inferInstance, fun j ↦ g₀ (Sum.inl j), fun j ↦ g₀ (Sum.inr j),
    fun _ _ h ↦ Subtype.ext (by simpa using h), hf, fun j ↦ hg₀ (Sum.inr j),
    isRegular_and_flat_localization _ Q₀ hQ₀ _ hunder hdim₀⟩

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]

/-- The map `R₀[xᵢ]_{Q₀} → R[xᵢ]_Q`, `Q₀ = Q ∩ R₀[xᵢ]`, induced by `R₀ ⊆ R`. -/
private noncomputable abbrev descLoc :
    Localization.AtPrime (Q.comap (MvPolynomial.map (σ := ι) (algebraMap R₀ R))) →+*
      Localization.AtPrime Q :=
  Localization.localRingHom _ Q (MvPolynomial.map (algebraMap R₀ R)) rfl

/-- `descLoc` extends `R₀[x_i] → R[x_i]`. -/
private lemma descLoc_algebraMap (x : MvPolynomial ι R₀) :
    descLoc R₀ Q (algebraMap _ _ x) =
      algebraMap _ (Localization.AtPrime Q) (MvPolynomial.map (algebraMap R₀ R) x) :=
  Localization.localRingHom_to_map _ _ _ _ x

/-- The partial ideals `(f₁, …, fᵢ)` of the descended relations generate the partial ideals of
the relations. -/
private lemma map_descLoc_ofList_take {f : Fin c → MvPolynomial ι R}
    {f₀ : Fin c → MvPolynomial ι R₀} (hf : ∀ j, MvPolynomial.map (algebraMap R₀ R) (f₀ j) = f j)
    (i : ℕ) :
    Ideal.map (descLoc R₀ Q) (Ideal.ofList (((List.ofFn f₀).map (algebraMap _ _)).take i)) =
      Ideal.ofList (((List.ofFn f).map (algebraMap _ (Localization.AtPrime Q))).take i) := by
  rw [Ideal.map_ofList]
  simp [List.map_take, List.map_ofFn, Function.comp_def, hf]

end Descent

/-! ### Clearing denominators in a localized polynomial ring -/

/-- **Clearing a denominator.** If the image of `a ∈ A` in `A_Q` lies in the ideal generated by
`J ⊆ A`, then `t a ∈ J` for some `t ∉ Q`. -/
theorem Localization.AtPrime.exists_notMem_mul_mem_of_algebraMap_mem {A : Type*} [CommRing A]
    (Q : Ideal A) [Q.IsPrime] {J : Ideal A} {a : A}
    (h : algebraMap A (Localization.AtPrime Q) a ∈ J.map (algebraMap A _)) :
    ∃ t ∉ Q, t * a ∈ J := by
  obtain ⟨⟨⟨z, hz⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl] at e
  obtain ⟨u, hu⟩ := e
  refine ⟨u * s, Q.primeCompl.mul_mem u.2 s.2, ?_⟩
  have : (u : A) * s * a = u * z := by rw [← hu]; ring
  rw [this]
  exact J.mul_mem_left _ hz

/-! ### Part (1): the relations are a regular sequence -/

/-- **Part (1) of Stacks 00SV, at one prime.** Over an arbitrary base `R`, relations `fⱼ` lying in
a prime `Q` over which the fibre has dimension `n - c` form a regular sequence in `R[xᵢ]_Q`.

Regularity is the finitary implication `f_{i+1} a ∈ (f₁, …, fᵢ) ⟹ a ∈ (f₁, …, fᵢ)`. Clearing
denominators turns its hypothesis into `w f_{i+1} a = ∑ bⱼ fⱼ` in `R[xᵢ]` with `w ∉ Q`; this
descends to a Noetherian `R₀ ⊆ R` (`exists_descent`), where the regularity of the descended
relations gives `a ∈ (f₁, …, fᵢ)` in `R₀[xᵢ]_{Q₀}`, and that membership maps back. -/
private lemma isRegular_localization {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {c : ℕ}
    (f : Fin c → MvPolynomial ι R) (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Q.under R).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Q.under R).ResidueField) (f i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
      ((List.ofFn f).map (algebraMap (MvPolynomial ι R) (Localization.AtPrime Q))) := by
  classical
  have hmax : ∀ r ∈ (List.ofFn f).map (algebraMap (MvPolynomial ι R) (Localization.AtPrime Q)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro r hr
    obtain ⟨_, hmem, rfl⟩ := List.mem_map.1 hr
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' f _).1 hmem
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hQ (Ideal.subset_span ⟨j, rfl⟩))
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmax).2 ?_
  rw [RingTheory.Sequence.isWeaklyRegular_iff_forall_mul_mem]
  intro i hi y hy
  rw [List.length_map, List.length_ofFn] at hi
  set J := Ideal.ofList ((List.ofFn f).take i) with hJ
  rw [ofList_take_map_eq_map] at hy ⊢
  simp only [List.getElem_map, List.getElem_ofFn] at hy
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl y
  have ha : algebraMap _ (Localization.AtPrime Q) (f ⟨i, hi⟩ * a) ∈ J.map (algebraMap _ _) := by
    have := J.map (algebraMap _ (Localization.AtPrime Q)) |>.mul_mem_right
      (algebraMap _ _ (s : MvPolynomial ι R)) hy
    rwa [mul_assoc, IsLocalization.mk'_spec, ← map_mul] at this
  obtain ⟨w, hw, hwa⟩ := Localization.AtPrime.exists_notMem_mul_mem_of_algebraMap_mem Q ha
  rw [hJ, Ideal.ofList_take_ofFn, Submodule.mem_span_image_finset_iff_exists_fun'] at hwa
  obtain ⟨b, hb⟩ := hwa
  obtain ⟨R₀, _, _, f₀, g₀, hinj, hf, hg, hreg₀, -⟩ :=
    exists_descent f Q hQ hdim (Sum.elim ![w, a] b)
  set w₀ := g₀ (Sum.inl 0)
  set a₀ := g₀ (Sum.inl 1)
  have hw₀ : MvPolynomial.map (algebraMap R₀ R) w₀ = w := hg (Sum.inl 0)
  have ha₀ : MvPolynomial.map (algebraMap R₀ R) a₀ = a := hg (Sum.inl 1)
  have hb₀ : ∀ j, MvPolynomial.map (algebraMap R₀ R) (g₀ (Sum.inr j)) = b j :=
    fun j ↦ hg (Sum.inr j)
  set Q₀ := Q.comap (MvPolynomial.map (σ := ι) (algebraMap R₀ R))
  -- the relation descends
  have hrel : w₀ * (f₀ ⟨i, hi⟩ * a₀) ∈ Ideal.ofList ((List.ofFn f₀).take i) := by
    rw [Ideal.ofList_take_ofFn, Submodule.mem_span_image_finset_iff_exists_fun']
    refine ⟨fun j ↦ g₀ (Sum.inr j), MvPolynomial.map_injective _ hinj ?_⟩
    rw [map_mul, map_mul, hw₀, hf, ha₀, ← hb, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_eq_mul, smul_eq_mul, map_mul, hb₀, hf]
  -- regularity downstairs
  have hw₀u : IsUnit (algebraMap _ (Localization.AtPrime Q₀) w₀) :=
    IsLocalization.map_units (M := Q₀.primeCompl) _
      ⟨w₀, show MvPolynomial.map (algebraMap R₀ R) w₀ ∉ Q by rw [hw₀]; exact hw⟩
  have ha₀mem : algebraMap _ (Localization.AtPrime Q₀) a₀ ∈
      Ideal.ofList (((List.ofFn f₀).map (algebraMap _ (Localization.AtPrime Q₀))).take i) := by
    rw [← Ideal.unit_mul_mem_iff_mem _ hw₀u, ← map_mul]
    refine (RingTheory.Sequence.isWeaklyRegular_iff_forall_mul_mem _).1 hreg₀.toIsWeaklyRegular i
      (by rw [List.length_map, List.length_ofFn]; exact hi) _ ?_
    rw [List.getElem_map, List.getElem_ofFn, ← map_mul, ofList_take_map_eq_map,
      show f₀ ⟨i, hi⟩ * (w₀ * a₀) = w₀ * (f₀ ⟨i, hi⟩ * a₀) by ring]
    exact Ideal.mem_map_of_mem _ hrel
  -- map back up
  have hup := Ideal.mem_map_of_mem (descLoc R₀ Q) ha₀mem
  rw [map_descLoc_ofList_take R₀ Q hf, descLoc_algebraMap, ha₀, ofList_take_map_eq_map] at hup
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ hup

/-! ### Part (2): the partial quotients are flat -/

section Flat

variable {R : Type*} [CommRing R] {ι : Type*} {c : ℕ}

/-- A relation `∑ rⱼ xⱼ = 0` over `R` in a quotient `A_Q/J A_Q` of a localized polynomial ring,
cleared of denominators: there are `s ∉ Q` and numerators `aⱼ ∈ A = R[xᵢ]` with `aⱼ = s xⱼ`, and a
`t ∉ Q` with `t ∑ rⱼ aⱼ ∈ J`. -/
private lemma exists_relation_of_sum_smul_eq_zero (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]
    (J : Ideal (MvPolynomial ι R)) {l : ℕ} {r : Fin l → R}
    {x : Fin l → Localization.AtPrime Q ⧸ J.map (algebraMap _ (Localization.AtPrime Q))}
    (hsum : ∑ j, r j • x j = 0) :
    ∃ s ∉ Q, ∃ a : Fin l → MvPolynomial ι R,
      (∀ j, Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) (a j)) =
        Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) s) * x j) ∧
      ∃ t ∉ Q, t * ∑ j, MvPolynomial.C (r j) * a j ∈ J := by
  classical
  choose y hy using fun j ↦ Ideal.Quotient.mk_surjective (x j)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples Q.primeCompl Finset.univ y
  choose a ha using fun j ↦ hs j (Finset.mem_univ j)
  have hC : ∀ z : R, algebraMap R (Localization.AtPrime Q) z =
      algebraMap (MvPolynomial ι R) (Localization.AtPrime Q) (MvPolynomial.C z) := fun z ↦ by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R), MvPolynomial.algebraMap_eq]
  have ha' : ∀ j, algebraMap _ (Localization.AtPrime Q) (a j) =
      algebraMap _ (Localization.AtPrime Q) (s : MvPolynomial ι R) * y j := fun j ↦ by
    rw [ha j, Algebra.smul_def]
  refine ⟨s, s.2, a, fun j ↦ by rw [ha', map_mul, hy], ?_⟩
  have h0 : ∑ j, r j • y j ∈ J.map (algebraMap _ (Localization.AtPrime Q)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, hy]
  refine Localization.AtPrime.exists_notMem_mul_mem_of_algebraMap_mem Q ?_
  have h1 := Ideal.mul_mem_left _ (algebraMap _ (Localization.AtPrime Q) (s : MvPolynomial ι R)) h0
  rw [Finset.mul_sum] at h1
  rw [map_sum]
  refine (congrArg (· ∈ J.map (algebraMap _ (Localization.AtPrime Q)))
    (Finset.sum_congr rfl fun j _ ↦ ?_)).mpr h1
  rw [map_mul, ha', ← hC, Algebra.smul_def]
  ring

/-- The map `R₀[xᵢ]_{Q₀}/J₀ → R[xᵢ]_Q/J` induced by `descLoc` is compatible with the scalars
`R₀ ⊆ R`. -/
private lemma quotientMap_descLoc_algebraMap (R₀ : Type*) [CommRing R₀] [Algebra R₀ R]
    (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]
    {J₀ : Ideal (Localization.AtPrime (Q.comap (MvPolynomial.map (algebraMap R₀ R))))}
    {J : Ideal (Localization.AtPrime Q)} (hle : J₀ ≤ J.comap (descLoc R₀ Q)) (z : R₀) :
    Ideal.quotientMap J (descLoc R₀ Q) hle (algebraMap R₀ _ z) =
      algebraMap R (Localization.AtPrime Q ⧸ J) (algebraMap R₀ R z) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotientMap_mk,
    IsScalarTower.algebraMap_apply R₀ (MvPolynomial ι R₀), MvPolynomial.algebraMap_eq,
    descLoc_algebraMap, MvPolynomial.map_C, ← Ideal.Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply R (MvPolynomial ι R), MvPolynomial.algebraMap_eq]

/-- **Part (2) of Stacks 00SV, at one prime.** Over an arbitrary base `R`, for relations `fⱼ`
lying in a prime `Q` over which the fibre has dimension `n - c`, every partial quotient
`R[xᵢ]_Q/(f₁, …, fᵢ)` is flat over `R`.

By the equational criterion (Lemma 00HK) it suffices that every relation `∑ rⱼ xⱼ = 0` is
trivial. Cleared of denominators, such a relation is finitely many polynomial identities; they
descend to a Noetherian `R₀ ⊆ R` (`exists_descent`), where the relation is trivial because the
descended partial quotient is flat over `R₀`, and the trivialization maps back. -/
private lemma flat_localization_quotient [Finite ι] (f : Fin c → MvPolynomial ι R)
    (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime] (hQ : Ideal.span (Set.range f) ≤ Q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Q.under R).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Q.under R).ResidueField) (f i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) (i : ℕ) :
    Module.Flat R (Localization.AtPrime Q ⧸ Ideal.ofList
      (((List.ofFn f).map (algebraMap (MvPolynomial ι R) (Localization.AtPrime Q))).take i)) := by
  classical
  rw [ofList_take_map_eq_map]
  refine Module.Flat.iff_forall_isTrivialRelation.2 fun {l r x} hsum ↦ ?_
  obtain ⟨s, hs, a, ha, t, ht, hta⟩ := exists_relation_of_sum_smul_eq_zero Q _ hsum
  rw [Ideal.ofList_take_ofFn, Submodule.mem_span_image_finset_iff_exists_fun'] at hta
  obtain ⟨b, hb⟩ := hta
  obtain ⟨R₀, _, _, f₀, g₀, hinj, hf, hg, -, hflat₀⟩ := exists_descent f Q hQ hdim
    (Sum.elim (Sum.elim ![t] fun j ↦ MvPolynomial.C (r j)) (Sum.elim a b))
  set Q₀ := Q.comap (MvPolynomial.map (σ := ι) (algebraMap R₀ R))
  have := hflat₀ i
  rw [ofList_take_map_eq_map] at this
  set t₀ := g₀ (Sum.inl (Sum.inl 0))
  set r₀ : Fin l → R₀ := fun j ↦ (g₀ (Sum.inl (Sum.inr j))).coeff 0
  have ht₀ : MvPolynomial.map (algebraMap R₀ R) t₀ = t := hg _
  have hr₀ : ∀ j, algebraMap R₀ R (r₀ j) = r j := fun j ↦ by
    rw [← MvPolynomial.coeff_map, hg, Sum.elim_inl, Sum.elim_inr, MvPolynomial.coeff_zero_C]
  have ha₀ : ∀ j, MvPolynomial.map (algebraMap R₀ R) (g₀ (Sum.inr (Sum.inl j))) = a j :=
    fun j ↦ hg _
  have hb₀ : ∀ k, MvPolynomial.map (algebraMap R₀ R) (g₀ (Sum.inr (Sum.inr k))) = b k :=
    fun k ↦ hg _
  -- the relation downstairs
  set J₀ := Ideal.ofList ((List.ofFn f₀).take i) with hJ₀def
  have hrel : t₀ * ∑ j, MvPolynomial.C (r₀ j) * g₀ (Sum.inr (Sum.inl j)) ∈ J₀ := by
    rw [hJ₀def, Ideal.ofList_take_ofFn, Submodule.mem_span_image_finset_iff_exists_fun']
    refine ⟨fun k ↦ g₀ (Sum.inr (Sum.inr k)), MvPolynomial.map_injective _ hinj ?_⟩
    simp only [smul_eq_mul, map_sum, map_mul, MvPolynomial.map_C, hb₀, hf, ht₀, ha₀, hr₀]
    exact hb
  set x₀ : Fin l → Localization.AtPrime Q₀ ⧸ J₀.map (algebraMap _ _) :=
    fun j ↦ Ideal.Quotient.mk _ (algebraMap _ _ (g₀ (Sum.inr (Sum.inl j))))
  have hsum₀ : ∑ j, r₀ j • x₀ j = 0 := by
    have ht₀u : IsUnit (algebraMap _ (Localization.AtPrime Q₀) t₀) :=
      IsLocalization.map_units (M := Q₀.primeCompl) _
        ⟨t₀, show MvPolynomial.map (algebraMap R₀ R) t₀ ∉ Q by rw [ht₀]; exact ht⟩
    have hmem := Ideal.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q₀)) hrel
    rw [map_mul, Ideal.unit_mul_mem_iff_mem _ ht₀u, ← Ideal.Quotient.eq_zero_iff_mem] at hmem
    rw [← hmem, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  obtain ⟨k, α, w, hx, hα⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hsum₀
  -- map the trivialization back up
  have hle : J₀.map (algebraMap _ (Localization.AtPrime Q₀)) ≤
      ((Ideal.ofList ((List.ofFn f).take i)).map (algebraMap _ (Localization.AtPrime Q))).comap
        (descLoc R₀ Q) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_ofList, List.map_take,
      map_descLoc_ofList_take R₀ Q hf,
      Ideal.map_ofList, List.map_take]
  set Φ := Ideal.quotientMap _ (descLoc R₀ Q) hle
  have hΦx : ∀ j, Φ (x₀ j) =
      Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) (s : MvPolynomial ι R)) * x j :=
    fun j ↦ by rw [Ideal.quotientMap_mk, descLoc_algebraMap, ha₀, ha]
  set v := Ideal.Quotient.mk ((Ideal.ofList ((List.ofFn f).take i)).map
    (algebraMap _ (Localization.AtPrime Q))) (IsLocalization.mk' _ (1 : MvPolynomial ι R)
      (⟨s, hs⟩ : Q.primeCompl))
  have hv : v * Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) s) = 1 := by
    rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
  refine ⟨k, fun j k' ↦ algebraMap R₀ R (α j k'), fun k' ↦ v * Φ (w k'), fun j ↦ ?_, fun k' ↦ ?_⟩
  · have h := congrArg Φ (hx j)
    rw [hΦx, map_sum] at h
    calc x j = v * (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) s) * x j) := by
          rw [← mul_assoc, hv, one_mul]
      _ = _ := by
          rw [h, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k' _ ↦ ?_
          rw [Algebra.smul_def, map_mul, quotientMap_descLoc_algebraMap, Algebra.smul_def]
          ring
  · rw [← map_zero (algebraMap R₀ R), ← hα k', map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, hr₀]

end Flat

/-! ### Part (3): relations modulo the square of the ideal of relations -/

/-- The square of the ideal generated by a family is generated by the pairwise products. -/
private lemma sq_eq_span_pair {A : Type*} [CommRing A] {c : ℕ} (f : Fin c → A) :
    Ideal.span (Set.range f) ^ 2 =
      Ideal.span (Set.range fun x : Fin c × Fin c ↦ f x.1 * f x.2) := by
  rw [pow_two, Ideal.span_mul_span]
  congr 1
  ext y
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i, j), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, f j, ⟨j, rfl⟩, rfl⟩

/-- **Part (3) of Stacks 00SV, at one prime.** Over an arbitrary base `R`, for relations `f_j`
lying in a prime `Q` over which the fibre has dimension `n - c`, a relation `∑ a_i f_i ∈ (f)²`
forces each `a_i` into `(f)` after multiplication by some `s ∉ Q`. The relation descends to a
Noetherian `R₀ ⊆ R` (`exists_descent`), where the descended relations are regular, so the
relation is trivial modulo `(f)` there (`mem_span_of_sum_mem_sq`). -/
private lemma exists_notMem_mul_mem {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {c : ℕ}
    (f : Fin c → MvPolynomial ι R) (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Q.under R).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Q.under R).ResidueField) (f i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞))
    {a : Fin c → MvPolynomial ι R} (ha : ∑ i, a i * f i ∈ Ideal.span (Set.range f) ^ 2)
    (i : Fin c) : ∃ s ∉ Q, s * a i ∈ Ideal.span (Set.range f) := by
  classical
  rw [sq_eq_span_pair] at ha
  obtain ⟨bb, hbb⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
  obtain ⟨R₀, _, _, f₀, g₀, hinj, hf, hg, hreg, -⟩ := exists_descent f Q hQ hdim (Sum.elim a bb)
  set a₀ : Fin c → MvPolynomial ι R₀ := fun j ↦ g₀ (Sum.inl j) with ha₀def
  set b₀ : Fin c × Fin c → MvPolynomial ι R₀ := fun x ↦ g₀ (Sum.inr x) with hb₀def
  have haa : ∀ j, MvPolynomial.map (algebraMap R₀ R) (a₀ j) = a j := fun j ↦ hg (Sum.inl j)
  have hbm : ∀ x, MvPolynomial.map (algebraMap R₀ R) (b₀ x) = bb x := fun x ↦ hg (Sum.inr x)
  -- the relation descends
  have hid : ∑ j, a₀ j * f₀ j = ∑ x : Fin c × Fin c, b₀ x * (f₀ x.1 * f₀ x.2) := by
    refine MvPolynomial.map_injective _ hinj ?_
    rw [map_sum, map_sum]
    simp only [map_mul, hf, haa, hbm]
    exact hbb.symm
  set Q₀ : Ideal (MvPolynomial ι R₀) := Q.comap (MvPolynomial.map (algebraMap R₀ R)) with hQ₀def
  have hQ₀ : ∀ j, f₀ j ∈ Q₀ := fun j ↦ by
    rw [hQ₀def, Ideal.mem_comap, hf]
    exact hQ (Ideal.subset_span ⟨j, rfl⟩)
  -- pass to the localization
  set A' := Localization.AtPrime Q₀
  set g : Fin c → A' := fun j ↦ algebraMap (MvPolynomial ι R₀) A' (f₀ j) with hgdef
  have hgreg : RingTheory.Sequence.IsWeaklyRegular A' (List.ofFn g) := by
    have h := hreg.toIsWeaklyRegular
    rw [List.map_ofFn] at h
    rw [hgdef]
    exact h
  have hgQ : ∀ j, g j ∈ IsLocalRing.maximalIdeal A' := by
    intro j
    simp only [hgdef]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hQ₀ j)
  have hgne : Ideal.span (Set.range g) ≠ ⊤ := by
    intro h
    refine (IsLocalRing.maximalIdeal.isMaximal A').ne_top (top_le_iff.1 ?_)
    rw [← h]
    exact
      Ideal.span_le.2
        (by
          rintro x ⟨j, rfl⟩; exact hgQ j)
  have hrel :
    ∑ j, algebraMap (MvPolynomial ι R₀) A' (a₀ j) * g j ∈ Ideal.span (Set.range g) ^ 2 := by
    rw [sq_eq_span_pair]
    simp only [hgdef]
    have :
      ∑ j, algebraMap (MvPolynomial ι R₀) A' (a₀ j) * algebraMap (MvPolynomial ι R₀) A' (f₀ j) =
        ∑ x : Fin c × Fin c,
          algebraMap (MvPolynomial ι R₀) A' (b₀ x) *
            (algebraMap (MvPolynomial ι R₀) A' (f₀ x.1) *
              algebraMap (MvPolynomial ι R₀) A' (f₀ x.2)) := by
      simp only [← map_mul, ← map_sum]
      exact congrArg _ hid
    rw [this]
    exact Ideal.sum_mem _ fun x _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
  have hmemloc := mem_span_of_sum_mem_sq g hgreg hgne hrel i
  -- descend the membership along the localization
  have hmap :
    Ideal.span (Set.range g) =
      Ideal.map (algebraMap (MvPolynomial ι R₀) A') (Ideal.span (Set.range f₀)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rw [hgdef]
    rfl
  rw [hmap] at hmemloc
  obtain ⟨t, ht, hmem₀⟩ := Localization.AtPrime.exists_notMem_mul_mem_of_algebraMap_mem Q₀ hmemloc
  refine ⟨MvPolynomial.map (algebraMap R₀ R) t, ht, ?_⟩
  have := Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R₀ R)) hmem₀
  rw [Ideal.map_span, ← Set.range_comp, show (MvPolynomial.map (algebraMap R₀ R)) ∘ f₀ = f from
    funext hf, map_mul, haa] at this
  exact this


/-! ### The fibre of the presentation in polynomial form -/

/-- The fibre `κ(p) ⊗_R S` of a presented algebra has the dimension of `κ(p)[x_i]/(f̄)`. -/
lemma ringKrullDim_fiber_eq_quotient {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} {c : ℕ} (P : Algebra.Presentation R S ι (Fin c)) (p : Ideal R) [p.IsPrime] :
    ringKrullDim (p.Fiber S) =
      ringKrullDim
        (MvPolynomial ι p.ResidueField ⧸
          Ideal.span
            (Set.range fun i ↦
              MvPolynomial.map (algebraMap R p.ResidueField) (P.relation i))) := by
  have e1 : S ≃ₐ[R] MvPolynomial ι R ⧸ Ideal.span (Set.range P.relation) :=
    (P.quotientEquiv.restrictScalars R).symm.trans
      (Ideal.quotientEquivAlgOfEq R P.span_range_relation_eq_ker.symm)
  have e2 :
    p.ResidueField ⊗[R] S ≃ₐ[p.ResidueField]
      p.ResidueField ⊗[R] (MvPolynomial ι R ⧸ Ideal.span (Set.range P.relation)) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e1
  obtain ⟨e3⟩ := nonempty_algEquiv_tensor_quotient (R := R) p.ResidueField P.relation
  exact
    (ringKrullDim_eq_of_ringEquiv e2.toRingEquiv).trans
      (ringKrullDim_eq_of_ringEquiv e3.toRingEquiv)

/-! ### Two computations in the conormal module -/

/-- A combination of the classes of the generators is the class of the corresponding combination
of lifts. -/
private lemma cotangent_linearCombination_eq_mk {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (E : Algebra.Extension R S) {c : ℕ} (g : Fin c → E.Ring) (hg : ∀ j, g j ∈ E.ker)
    (a : Fin c → S) (u : Fin c → E.Ring) (hu : ∀ j, algebraMap E.Ring S (u j) = a j)
    (hmem : ∑ j, u j * g j ∈ E.ker) :
    Fintype.linearCombination S (fun j ↦ Algebra.Extension.Cotangent.mk (P := E) ⟨g j, hg j⟩) a =
      Algebra.Extension.Cotangent.mk ⟨∑ j, u j * g j, hmem⟩ := by
  rw [Fintype.linearCombination_apply]
  have hsum : (⟨∑ j, u j * g j, hmem⟩ : E.ker) = ∑ j, u j • (⟨g j, hg j⟩ : E.ker) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    change ∑ j, u j * g j = ∑ j, ((u j • (⟨g j, hg j⟩ : E.ker) : E.ker) : E.Ring)
    exact Finset.sum_congr rfl fun j _ ↦ rfl
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, ← hu j]
  exact (algebraMap_smul S (u j) (Algebra.Extension.Cotangent.mk (P := E) ⟨g j, hg j⟩)).symm

/-- Generators of the kernel of an extension span its conormal module. -/
private lemma cotangent_linearCombination_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (E : Algebra.Extension R S) {c : ℕ} (g : Fin c → E.Ring) (hg : ∀ j, g j ∈ E.ker)
    (hspan : Ideal.span (Set.range g) = E.ker) :
    Function.Surjective
      (Fintype.linearCombination S fun j ↦
        Algebra.Extension.Cotangent.mk (P := E) ⟨g j, hg j⟩) := by
  intro x
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.1 (by rw [hspan]; exact y.2)
  have hmem : ∑ j, d j * g j ∈ E.ker := by rw [hd]; exact y.2
  refine ⟨fun j ↦ algebraMap E.Ring S (d j), ?_⟩
  rw [cotangent_linearCombination_eq_mk E g hg _ d (fun _ ↦ rfl) hmem]
  exact congrArg _ (Subtype.ext hd)

/-! ### The fibre dimension at a prime of a relative global complete intersection -/

section Presentation

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {ι : Type*}
  {c : ℕ} (P : Algebra.Presentation R S ι (Fin c))

/-- The relations of a presentation lie in the prime of `R[xᵢ]` corresponding to any prime of
`S`. -/
private lemma span_relation_le_comap (q : Ideal S) :
    Ideal.span (Set.range P.relation) ≤ q.comap (algebraMap P.Ring S) := by
  rw [P.span_range_relation_eq_ker]
  intro x hx
  rw [Ideal.mem_comap, show algebraMap P.Ring S x = 0 from hx]
  exact q.zero_mem

/-- For a relative global complete intersection, the fibre `κ(p)[xᵢ]/(f̄)` over the prime `p` of
`R` below any prime of `S` has dimension `n - c`, written additively. -/
private lemma ringKrullDim_quotient_add_eq [Finite ι] [P.IsRelativeGlobalCompleteIntersection]
    (q : Ideal S)
    [q.IsPrime] :
    ringKrullDim
          (MvPolynomial ι ((q.comap (algebraMap P.Ring S)).under R).ResidueField ⧸
            Ideal.span
              (Set.range fun j ↦
                MvPolynomial.map
                  (algebraMap R ((q.comap (algebraMap P.Ring S)).under R).ResidueField)
                  (P.relation j))) +
        (c : WithBot ℕ∞) =
      ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  have hunder : (q.comap (algebraMap P.Ring S)).under R = q.under R := by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [← ringKrullDim_fiber_eq_quotient P]
  have : q.LiesOver ((q.comap (algebraMap P.Ring S)).under R) := ⟨hunder⟩
  have hnt : Nontrivial (((q.comap (algebraMap P.Ring S)).under R).Fiber S) :=
    PrimeSpectrum.nonempty_iff_nontrivial.1
      ⟨PrimeSpectrum.primesOverOrderIsoFiber R S _ ⟨q, ⟨‹_›, ‹_›⟩⟩⟩
  have h := ‹P.IsRelativeGlobalCompleteIntersection›.ringKrullDim_fiber_add_card_eq_card _ hnt
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h

end Presentation

/-! ### Stacks 00SV -/

/-- **Stacks 00SV (1).** Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, be a relative
global complete intersection (Definition 00SP). For every prime `𝔮` of `S`, with corresponding
prime `𝔮'` of `R[x_1, …, x_n]`, the relations `f_1, …, f_c` form a regular sequence in the local
ring `R[x_1, …, x_n]_{𝔮'}`. -/
@[stacks 00SV "(1): `RingTheory.Sequence.IsRegular` is Definition 00LF verbatim, nonvanishing
clause included, for the list of images of `f_1, …, f_c` in `Localization.AtPrime 𝔮'`,
`𝔮' = 𝔮 ∩ R[x_1, …, x_n]`."]
theorem Algebra.Presentation.isRegular_localization_relation {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] {ι : Type*} [Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c)) [P.IsRelativeGlobalCompleteIntersection]
    (q : Ideal S) [q.IsPrime] :
    RingTheory.Sequence.IsRegular (Localization.AtPrime (q.comap (algebraMap P.Ring S)))
      ((List.ofFn P.relation).map
        (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))) :=
  isRegular_localization P.relation _ (span_relation_le_comap P q)
    (ringKrullDim_quotient_add_eq P q)

/-- **Stacks 00SV (2).** Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, be a relative
global complete intersection (Definition 00SP). For every prime `𝔮` of `S`, with corresponding
prime `𝔮'` of `R[x_1, …, x_n]`, each of the rings `R[x_1, …, x_n]_{𝔮'}/(f_1, …, f_i)` is flat
over `R`. -/
@[stacks 00SV "(2): `R[x_1, …, x_n]_{𝔮'}/(f_1, …, f_i)` is the quotient of
`Localization.AtPrime 𝔮'` by the ideal generated by the first `i` images of the relations, for
every `i : ℕ` (`List.take` saturates at `c`)."]
theorem Algebra.Presentation.flat_localization_quotient_relation {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] {ι : Type*} [Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c)) [P.IsRelativeGlobalCompleteIntersection]
    (q : Ideal S) [q.IsPrime] (i : ℕ) :
    Module.Flat R (Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
      Ideal.ofList (((List.ofFn P.relation).map
        (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))).take i)) :=
  flat_localization_quotient P.relation _ (span_relation_le_comap P q)
    (ringKrullDim_quotient_add_eq P q) i

/-! ### The conormal module of a relative global complete intersection -/

/-- **Stacks 00SV (3).** Let `S = R[x_1, …, x_n]/(f_1, …, f_c)`, presented by `P`, be a relative
global complete intersection (Definition 00SP). Then the conormal module `I/I²` of
`I = (f_1, …, f_c)` is free over `S` on the classes of `f_1, …, f_c`. -/
@[stacks 00SV "(3): the conormal module `I/I²` is `P.toExtension.Cotangent`, and the basis is
pinned: its `i`-th vector is the class of the relation `f_i`."]
theorem Algebra.Presentation.exists_basis_cotangent_relation {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] {ι : Type*} [Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c)) [P.IsRelativeGlobalCompleteIntersection] :
    ∃ b : Module.Basis (Fin c) S P.toExtension.Cotangent,
      ∀ i, b i = Algebra.Extension.Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩ := by
  classical
  have hsurj :
    Function.Surjective
      (Fintype.linearCombination S
        (fun i ↦
          Algebra.Extension.Cotangent.mk (P := P.toExtension)
            ⟨P.relation i, P.relation_mem_ker i⟩)) :=
    cotangent_linearCombination_surjective P.toExtension P.relation P.relation_mem_ker
      P.span_range_relation_eq_ker
  have hinj :
    Function.Injective
      (Fintype.linearCombination S
        (fun i ↦
          Algebra.Extension.Cotangent.mk (P := P.toExtension)
            ⟨P.relation i, P.relation_mem_ker i⟩)) := by
    rw [injective_iff_map_eq_zero]
    intro a hψa
    funext i
    change a i = 0
    by_contra hne0
    -- a maximal ideal containing the annihilator of `a i`
    have hAnn : (LinearMap.ker (LinearMap.mulRight S (a i)) : Ideal S) ≠ ⊤ := by
      intro h
      have h1 : (1 : S) ∈ LinearMap.ker (LinearMap.mulRight S (a i)) := by
        rw [h]; trivial
      rw [LinearMap.mem_ker, LinearMap.mulRight_apply, one_mul] at h1
      exact hne0 h1
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hAnn
    have h𝔪p : 𝔪.IsPrime := h𝔪.isPrime
    -- the prime of the polynomial ring under `𝔪`
    set Q : Ideal P.Ring := 𝔪.comap (algebraMap P.Ring S) with hQdef
    have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQ : Ideal.span (Set.range P.relation) ≤ Q := span_relation_le_comap P 𝔪
    -- the relation, read in the conormal module
    have hmem : ∑ j, P.σ (a j) * P.relation j ∈ P.ker :=
      Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (P.relation_mem_ker j)
    have key :=
      cotangent_linearCombination_eq_mk P.toExtension P.relation P.relation_mem_ker a
        (fun j ↦ P.σ (a j)) (fun j ↦ P.toExtension.algebraMap_σ (a j)) hmem
    have harel : ∑ j, P.σ (a j) * P.relation j ∈ Ideal.span (Set.range P.relation) ^ 2 := by
      rw [P.span_range_relation_eq_ker]
      exact (Algebra.Extension.Cotangent.mk_eq_zero_iff _).1 (key ▸ hψa)
    obtain ⟨s, hsQ, hs⟩ :=
      exists_notMem_mul_mem P.relation Q hQ (ringKrullDim_quotient_add_eq P 𝔪) harel i
    refine hsQ ?_
    have h2 : algebraMap P.Ring S (s * P.σ (a i)) = 0 :=
      RingHom.mem_ker.1 (P.span_range_relation_eq_ker.le hs)
    rw [map_mul,
      show algebraMap P.Ring S (P.σ (a i)) = a i from P.toExtension.algebraMap_σ (a i)] at h2
    change algebraMap P.Ring S s ∈ 𝔪
    refine hle ?_
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply]
    exact h2
  refine ⟨(Pi.basisFun S (Fin c)).map (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩), fun i ↦ ?_⟩
  rw [Module.Basis.map_apply]
  change
    Fintype.linearCombination S
        (fun j ↦
          Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation j, P.relation_mem_ker j⟩)
        ((Pi.basisFun S (Fin c)) i) =
      _
  rw [Fintype.linearCombination_apply]
  simp

end
