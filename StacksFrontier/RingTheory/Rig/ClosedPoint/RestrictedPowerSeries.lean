module

public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal

/-!
# Completions at rig-closed points of restricted power series

Let `A` be a Noetherian adic topological ring, complete for an ideal of definition `I`, and let
`A{x_σ}` be the restricted power series ring in finitely many variables — the `I`-adic
completion of `A[x_σ]`.  Let `q ⊆ A{x_σ}` be a prime which is rig-closed, that is, closed in the
complement of the vanishing locus of `I A{x_σ}`, and whose contraction `p = A ∩ q` is rig-closed
in `Spec A`.  Then the canonical map

```
A[x_σ]_{q'} ⟶ A{x_σ}_q,   q' = A[x_σ] ∩ q,
```

induces an isomorphism on the completions at the maximal ideals.

## Main results

* `Rig.adicCompletionMap_localRingHom_bijective`: the canonical map from the completion of
  `A[x_σ]_{q'}` to the completion of `A{x_σ}_q` is bijective.

## Implementation notes

The map on local rings is Mathlib's `Localization.localRingHom` and the map on completions is
`adicCompletionMap`; the conclusion is bijectivity of that canonical map, so no inverse is
chosen.  Completeness of the adic topological ring is `IsAdicComplete I A`, and the topology on
`A{x_σ}` is `RestrictedPowerSeries.adicTopology`, the adic topology for the extension of `I`.

Rig-closedness of a prime is `Rig.Ideal.IsClosedPointAwayFrom`, taken with respect to the ideal
of definition.

## References

* [Stacks Project, Tag 0GGH](https://stacks.math.columbia.edu/tag/0GGH)
* [Stacks Project, Tag 0GGB](https://stacks.math.columbia.edu/tag/0GGB)
* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)
-/

@[expose] public section

namespace Rig

open RestrictedPowerSeries

/-! ### Ideals of definition and the topological nilradical -/

/-- An adically complete adic topological ring is weakly admissible. -/
public theorem isWeaklyAdmissible_of_isAdicComplete
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (I : Ideal A) (hI : IsAdic I)
    (hdef : TopologicalRing.IsIdealOfDefinition I) [IsAdicComplete I A] :
    TopologicalRing.IsWeaklyAdmissible A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  obtain ⟨h₁, h₂⟩ := hI.isAdicComplete_iff.mp inferInstance
  exact ⟨⟨I, hdef.1, fun x hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
    (isIdealOfDefinition_le_topologicalNilradical I hdef hx)⟩, h₁, h₂⟩

/-! ### Restricted power series over a Noetherian ring -/

/-- Restricted power series in finitely many variables over a Noetherian ring form a Noetherian
ring. -/
@[ega "0 7.5.4" "more general"]
public theorem isNoetherianRing_restrictedPowerSeries
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ] :
    IsNoetherianRing (RestrictedPowerSeries I σ) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have := AdicCompletion.isNoetherianRing (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
  exact isNoetherianRing_of_ringEquiv _ (adicCompletionEquiv I σ).symm

/-- The equivalence with the adic completion of the polynomial ring identifies the extension of
`I` to the restricted power series with the extension of `I` to the completion. -/
private theorem map_adicCompletionEquiv_extension
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ] :
    (I.map (coefficientRingHom I σ)).map (adicCompletionEquiv I σ).toRingHom =
      (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)).map
        (algebraMap (MvPolynomial σ A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
            (MvPolynomial σ A))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun a ↦ ?_
  exact adicCompletionEquiv_polynomialRingHom I σ (MvPolynomial.C a)

/-- Restricted power series over a Noetherian ring are adically complete for the extension of
the coefficient ideal. -/
@[ega "0 7.5.4" "(ii)"]
public theorem isAdicComplete_restrictedPowerSeries
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ] :
    IsAdicComplete (I.map (coefficientRingHom I σ)) (RestrictedPowerSeries I σ) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let P := MvPolynomial σ A
  let J : Ideal P := I.map (MvPolynomial.C : A →+* P)
  let C := AdicCompletion J P
  let e : RestrictedPowerSeries I σ ≃+* C := adicCompletionEquiv I σ
  let f : P →+* C := algebraMap P C
  have hmap := map_adicCompletionEquiv_extension I σ
  have hJ : J.FG := (Ideal.fg_of_isNoetherianRing I).map (MvPolynomial.C : A →+* P)
  have hC : IsAdicComplete (J.map f) C := by
    simpa [C, f] using AdicCompletion.isAdicComplete_self J hJ
  exact (IsAdicComplete.congr_ringEquiv (I.map (coefficientRingHom I σ)) e).mp (hmap ▸ hC)

/-- If `B` is Noetherian and `B ⧸ q` is a finite `A`-module, then so is `B ⧸ q ^ (n + 1)`. -/
private theorem finite_quotient_pow_of_finite_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] (q : Ideal B) [Module.Finite A (B ⧸ q)] (n : ℕ) :
    Module.Finite A (B ⧸ q ^ (n + 1)) := by
  classical
  have hpow : q ^ (n + 1) ≤ q := Ideal.pow_le_self n.succ_ne_zero
  let f : (B ⧸ q ^ (n + 1)) →ₐ[A] B ⧸ q := Ideal.Quotient.factorₐ A hpow
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hpow
  have hker : RingHom.ker f.toRingHom =
      Ideal.map (Ideal.Quotient.mk (q ^ (n + 1)) : B →+* B ⧸ q ^ (n + 1)) q := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hb : b ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp
        (show Ideal.Quotient.mk q b = 0 from hx)
      exact Ideal.mem_map_of_mem _ hb
    · intro hx
      obtain ⟨b, hb, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have hkerNil : RingHom.ker f.toRingHom ≤ nilradical (B ⧸ q ^ (n + 1)) := by
    intro x hx
    show x ∈ (⊥ : Ideal (B ⧸ q ^ (n + 1))).radical
    refine Ideal.mem_radical_iff.mpr ⟨n + 1, ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : b ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp
      (show Ideal.Quotient.mk q b = 0 from hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hb (n + 1))
  exact Module.finite_of_surjective_of_ker_le_nilradical f hsurj hkerNil
    (hker ▸ (Ideal.fg_of_isNoetherianRing q).map _)

/-- A homomorphism into a finite module whose image generates modulo an ideal inside the
Jacobson radical is surjective. -/
private theorem surjective_of_dense_finite_module
    {A P N : Type*} [CommRing A] [CommRing P] [CommRing N]
    [Algebra A P] [Algebra A N] [Module.Finite A N]
    (I : Ideal A) (f : P →ₐ[A] N)
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    (happrox : ∀ x : N, ∃ p : P, x - f p ∈ I • (⊤ : Submodule A N)) :
    Function.Surjective f := by
  let F : P →ₗ[A] N := f.toLinearMap
  have hquot : Function.Surjective ((I • (⊤ : Submodule A N)).mkQ ∘ₗ F) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) x
    obtain ⟨p, hp⟩ := happrox y
    refine ⟨p, ?_⟩
    show (I • (⊤ : Submodule A N)).mkQ (F p) = (I • (⊤ : Submodule A N)).mkQ y
    rw [← sub_eq_zero, ← map_sub]
    show Submodule.Quotient.mk (F p - y) = 0
    rw [Submodule.Quotient.mk_eq_zero, ← neg_sub]
    exact Submodule.neg_mem _ hp
  exact LinearMap.surjective_of_surjective_comp_mkQ F I hI hquot

/-- The polynomial ring has dense image in the restricted power series ring for the adic
topology. -/
public theorem denseRange_polynomialRingHom_adic
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ] :
    @DenseRange (RestrictedPowerSeries I σ) (adicTopology I σ) (MvPolynomial σ A)
      (polynomialRingHom I σ) := by
  classical
  let B := RestrictedPowerSeries I σ
  let : TopologicalSpace B := adicTopology I σ
  let IB : Ideal B := I.map (coefficientRingHom I σ)
  let P := MvPolynomial σ A
  let J : Ideal P := I.map (MvPolynomial.C : A →+* P)
  let C := AdicCompletion J P
  let e : B ≃+* C := adicCompletionEquiv I σ
  let f : P →+* C := algebraMap P C
  have hmap : IB.map e.toRingHom = J.map f := map_adicCompletionEquiv_extension I σ
  let : Fintype σ := Fintype.ofFinite σ
  have hJ : J.FG := (Ideal.fg_of_isNoetherianRing I).map (MvPolynomial.C : A →+* P)
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨b, hb⟩
  obtain ⟨n, _, hn⟩ := (Ideal.hasBasis_nhds_adic IB b).mem_iff.mp (hU.mem_nhds hb)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n (e b))
  let y := polynomialRingHom I σ p
  have hzero : AdicCompletion.evalₐ J n (e b - e y) = 0 := by
    rw [map_sub, show e y = AdicCompletion.of J P p from
      adicCompletionEquiv_polynomialRingHom I σ p, AdicCompletion.evalₐ_of, ← hp]
    exact sub_self _
  have hker : e b - e y ∈ (J.map f) ^ n := by
    have hx : e b - e y ∈ RingHom.ker (AdicCompletion.evalₐ J n).toRingHom :=
      RingHom.mem_ker.mpr hzero
    rw [AdicCompletion.ker_evalₐ J hJ n] at hx
    exact hx
  have hmapPow : (IB ^ n).map e.toRingHom = (J.map f) ^ n := by
    rw [Ideal.map_pow, hmap]
  have hpre : b - y ∈ IB ^ n := by
    have hmem : e (b - y) ∈ (IB ^ n).map e.toRingHom := by
      rw [hmapPow]
      simpa only [map_sub] using hker
    obtain ⟨x, hx, hxeq⟩ :=
      (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hmem
    have hxy : x = b - y := e.injective hxeq
    simpa [hxy] using hx
  have hyU : y ∈ U := by
    refine hn ⟨y - b, ?_, by simp⟩
    rw [← neg_sub]
    exact Submodule.neg_mem _ hpre
  exact ⟨y, hyU, ⟨p, rfl⟩⟩

/-- Every restricted power series is congruent to a polynomial modulo the extension of the
coefficient ideal. -/
private theorem exists_polynomial_sub_mem_map_coefficientRingHom
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ]
    (b : RestrictedPowerSeries I σ) :
    ∃ p : MvPolynomial σ A,
      b - polynomialRingHom I σ p ∈ I.map (coefficientRingHom I σ) := by
  let B := RestrictedPowerSeries I σ
  let IB : Ideal B := I.map (coefficientRingHom I σ)
  let f : MvPolynomial σ A →+* B := polynomialRingHom I σ
  let : TopologicalSpace B := adicTopology I σ
  let : IsTopologicalRing B := adicIsTopologicalRing I σ
  let : IsLinearTopology B B := IB.isLinearTopology
  have hIBdef : TopologicalRing.IsIdealOfDefinition IB :=
    (isIdealOfDefinition_iff_isAdic ⟨IB, rfl⟩ IB).2 rfl
  let U : Set B := {z | z - b ∈ IB}
  have hUopen : IsOpen U := hIBdef.1.preimage (continuous_id.sub continuous_const)
  have hUne : U.Nonempty := ⟨b, by simp [U]⟩
  have hd : DenseRange f := denseRange_polynomialRingHom_adic I σ
  obtain ⟨y, hyU, ⟨p, rfl⟩⟩ := (dense_iff_inter_open.mp hd) U hUopen hUne
  refine ⟨p, ?_⟩
  rw [← neg_sub]
  exact Submodule.neg_mem _ (by simpa [U] using hyU)

/-- If `I` lies in the Jacobson radical of `A` and the quotient of the restricted power series
ring by `q ^ (n + 1)` is a finite `A`-module, then the polynomial ring surjects onto that
quotient. -/
private theorem polynomial_quotient_surjective
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hIjac : I ≤ (⊥ : Ideal A).jacobson)
    (σ : Type*) [Finite σ] (q : Ideal (RestrictedPowerSeries I σ)) (n : ℕ)
    (hfinite : Module.Finite A (RestrictedPowerSeries I σ ⧸ q ^ (n + 1))) :
    Function.Surjective fun p : MvPolynomial σ A ↦
      Ideal.Quotient.mk (q ^ (n + 1)) (polynomialRingHom I σ p) := by
  classical
  let B := RestrictedPowerSeries I σ
  let P := MvPolynomial σ A
  let f : P →+* B := polynomialRingHom I σ
  let Q : Ideal B := q ^ (n + 1)
  let N := B ⧸ Q
  have hfiniteN : Module.Finite A N := hfinite
  have happrox : ∀ x : N, ∃ p : P,
      x - (Ideal.Quotient.mk Q).comp f p ∈ I • (⊤ : Submodule A N) := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hmem⟩ := exists_polynomial_sub_mem_map_coefficientRingHom I σ b
    have hmap : (Ideal.Quotient.mk Q).comp (algebraMap A B) = algebraMap A N := rfl
    have hquot : Ideal.Quotient.mk Q (b - f p) ∈ I.map (algebraMap A N) := by
      rw [← hmap, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hmem
    refine ⟨p, ?_⟩
    show Ideal.Quotient.mk Q b - Ideal.Quotient.mk Q (f p) ∈ I • (⊤ : Submodule A N)
    rw [← (Ideal.Quotient.mk Q).map_sub, Ideal.smul_top_eq_map]
    exact hquot
  let ψ : P →ₐ[A] N :=
    { toRingHom := (Ideal.Quotient.mk Q).comp f
      commutes' := fun _ ↦ rfl }
  exact @surjective_of_dense_finite_module A P N _ _ _ _ _ hfiniteN I ψ hIjac happrox

/-- The coefficient map into the restricted power series ring is topologically of finite
type. -/
public theorem isTopologicallyOfFiniteType_coefficientRingHom
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (σ : Type*) [Finite σ] :
    letI : TopologicalSpace (RestrictedPowerSeries I σ) := adicTopology I σ
    TopologicalRing.IsTopologicallyOfFiniteType (coefficientRingHom I σ) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : TopologicalSpace (RestrictedPowerSeries I σ) := adicTopology I σ
  let n := Nat.card σ
  let e : Fin n ≃ σ := (Finite.equivFin σ).symm
  let er : MvPolynomial (Fin n) A ≃+* MvPolynomial σ A := MvPolynomial.renameEquiv A e
  let f : MvPolynomial (Fin n) A →+* RestrictedPowerSeries I σ :=
    (polynomialRingHom I σ).comp er.toRingHom
  refine ⟨n, f, ?_, ?_⟩
  · ext a
    simp [f, coefficientRingHom, polynomialRingHom, er]
  · rw [DenseRange, show Set.range f = Set.range (polynomialRingHom I σ) from
      er.surjective.range_comp (polynomialRingHom I σ)]
    exact denseRange_polynomialRingHom_adic I σ

/-! ### Comparison of the local completions -/

open IsLocalRing

/-- If a ring homomorphism is surjective modulo the square of a prime of the target, then the
maximal ideal of the source localization generates the maximal ideal of the target
localization. -/
private lemma map_maximalIdeal_of_surjective_quotient_sq
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) (q : Ideal S) [q.IsPrime]
    (h : Function.Surjective ((Ideal.Quotient.mk (q ^ 2)).comp f)) :
    (maximalIdeal (Localization.AtPrime (q.comap f))).map
      (Localization.localRingHom (q.comap f) q f rfl) = maximalIdeal (Localization.AtPrime q) := by
  let T := Localization.AtPrime q
  let g := algebraMap S T
  let m := maximalIdeal T
  let l := Localization.localRingHom (q.comap f) q f rfl
  have hq : q ≤ (q.comap f).map f ⊔ q ^ 2 := by
    intro x hx
    obtain ⟨r, hr⟩ := h (Ideal.Quotient.mk (q ^ 2) x)
    have he : f r - x ∈ q ^ 2 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hr
    have heq : f r - x ∈ q := Ideal.pow_le_self (by decide) he
    have hrq : r ∈ q.comap f := by
      show f r ∈ q
      simpa using q.add_mem heq hx
    exact Submodule.mem_sup.mpr ⟨f r, (q.comap f).mem_map_of_mem f hrq, x - f r,
      by simpa only [neg_sub] using (q ^ 2).neg_mem he, by ring⟩
  have hcomp : l.comp (algebraMap R (Localization.AtPrime (q.comap f))) = g.comp f := by
    ext r
    exact Localization.localRingHom_to_map (q.comap f) q f rfl r
  have hmap : (maximalIdeal (Localization.AtPrime (q.comap f))).map l =
      ((q.comap f).map f).map g := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.comap f), Ideal.map_map, hcomp,
      ← Ideal.map_map]
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le l)
  rw [hmap]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Ideal.fg_of_isNoetherianRing m)
    (show m ≤ (⊥ : Ideal T).jacobson by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  have hh := Ideal.map_mono (f := g) hq
  rw [Ideal.map_sup, Ideal.map_pow,
    show q.map g = m from IsLocalization.AtPrime.map_eq_maximalIdeal q T] at hh
  simpa only [pow_two, Ideal.smul_eq_mul] using hh

/-- If a ring homomorphism is surjective modulo a prime of the target, then the induced map of
residue fields of the localizations is surjective. -/
private lemma residueFieldMap_surjective_of_quotient_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : Ideal S) [q.IsPrime]
    (h : Function.Surjective ((Ideal.Quotient.mk q).comp f)) :
    Function.Surjective (ResidueField.map
      (Localization.localRingHom (q.comap f) q f rfl)) := by
  let R' := Localization.AtPrime (q.comap f)
  let S' := Localization.AtPrime q
  let l := Localization.localRingHom (q.comap f) q f rfl
  let g : S →+* ResidueField S' := (residue S').comp (algebraMap S S')
  let g' : R →+* ResidueField R' := (residue R').comp (algebraMap R R')
  let k := ResidueField.map l
  have hbase : ∀ s : S, ∃ r : R, k (g' r) = g s := by
    intro s
    obtain ⟨r, hr⟩ := h (Ideal.Quotient.mk q s)
    refine ⟨r, ?_⟩
    show residue S' (l (algebraMap R R' r)) = g s
    rw [Localization.localRingHom_to_map]
    show g (f r) = g s
    rw [← sub_eq_zero, ← map_sub]
    refine (residue_eq_zero_iff _).mpr ?_
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q]
    exact Ideal.mem_map_of_mem _ ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hr)
  intro y
  obtain ⟨z, rfl⟩ := residue_surjective y
  obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.surj q.primeCompl z
  obtain ⟨a', ha'⟩ := hbase a
  obtain ⟨b', hb'⟩ := hbase b
  refine ⟨g' a' / g' b', ?_⟩
  rw [map_div₀, ha', hb']
  have hb : g b ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr (IsLocalization.map_units S' b)
  refine (div_eq_iff hb).mpr ?_
  have he := congrArg (residue S') hz
  simpa only [g, RingHom.comp_apply, map_mul] using he.symm

/-- A ring homomorphism of adic completions which extends the given one on the source rings is
the canonical one. -/
private lemma adicCompletionMap_eq_of_comp_algebraMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : Ideal R) (I : Ideal S) (hf : J.map f ≤ I)
    (hJ : J.FG) (g : AdicCompletion J R →+* AdicCompletion I S)
    (hg : ∀ r, g (algebraMap R (AdicCompletion J R) r) =
      algebraMap S (AdicCompletion I S) (f r)) :
    adicCompletionMap f J I hf = g := by
  refine RingHom.ext fun x ↦ ?_
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  let h := (AdicCompletion.evalₐ I n).toRingHom.comp g
  have hpow : J ^ n ≤ (I ^ n).comap f := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hf n
  have hker : RingHom.ker (AdicCompletion.evalₐ J n).toRingHom ≤ RingHom.ker h := by
    rw [AdicCompletion.ker_evalₐ J hJ, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro r hr
    show AdicCompletion.evalₐ I n (g (algebraMap R (AdicCompletion J R) r)) = 0
    rw [hg]
    show Ideal.Quotient.mk (I ^ n) (f r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpow hr)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  have hsub : x - algebraMap R (AdicCompletion J R) r ∈
      RingHom.ker (AdicCompletion.evalₐ J n).toRingHom := by
    rw [RingHom.mem_ker, map_sub]
    show AdicCompletion.evalₐ J n x - Ideal.Quotient.mk (J ^ n) r = 0
    rw [hr, sub_self]
  have hh := hker hsub
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hh
  change AdicCompletion.evalₐ I n (g x) =
    AdicCompletion.evalₐ I n (g (algebraMap R (AdicCompletion J R) r)) at hh
  rw [hg] at hh
  rw [adicCompletionMap, AdicCompletion.evalₐ_liftRingHom]
  show Ideal.quotientMap (I ^ n) f hpow (AdicCompletion.evalₐ J n x) = _
  rw [← hr, Ideal.quotientMap_mk, hh]
  rfl

/-- A flat homomorphism of Noetherian rings that is surjective modulo a prime of the target and
modulo its square induces a bijection on the completions of the local rings. -/
private lemma adicCompletionMap_localRingHom_bijective_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : f.Flat) (q : Ideal S) [q.IsPrime]
    (h₁ : Function.Surjective ((Ideal.Quotient.mk q).comp f))
    (h₂ : Function.Surjective ((Ideal.Quotient.mk (q ^ 2)).comp f)) :
    let l := Localization.localRingHom (q.comap f) q f rfl
    Function.Bijective (adicCompletionMap l
      (maximalIdeal (Localization.AtPrime (q.comap f)))
      (maximalIdeal (Localization.AtPrime q)) (map_maximalIdeal_le l)) := by
  let R' := Localization.AtPrime (q.comap f)
  let S' := Localization.AtPrime q
  let l := Localization.localRingHom (q.comap f) q f rfl
  let : Algebra R' S' := l.toAlgebra
  have : IsLocalHom (algebraMap R' S') :=
    Localization.isLocalHom_localRingHom (q.comap f) q f rfl
  have : Module.Flat R' S' := hf.localRingHom q (q.comap f) rfl
  have hmax := map_maximalIdeal_of_surjective_quotient_sq f q h₂
  have hres : Function.Bijective (ResidueField.map l) :=
    ⟨RingHom.injective _, residueFieldMap_surjective_of_quotient_surjective f q h₁⟩
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (A := R') (B := S') (Ideal.fg_of_isNoetherianRing _) hmax hres
  show Function.Bijective (adicCompletionMap l _ _ _)
  rw [adicCompletionMap_eq_of_comp_algebraMap l _ _ _
    (Ideal.fg_of_isNoetherianRing _) e.toRingHom he]
  exact e.bijective

/-- Let `A` be a Noetherian adic topological ring, complete for an ideal of definition `I`, and
let `q` be a prime of the restricted power series ring `A{x_σ}` in finitely many variables.  If
`q` is rig-closed and so is its contraction to `A`, then the canonical map from the local ring of
the polynomial ring at `q ∩ A[x_σ]` to the local ring of `A{x_σ}` at `q` induces a bijection on
the completions at the maximal ideals. -/
@[stacks 0GGH]
public theorem adicCompletionMap_localRingHom_bijective
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : IsAdic I) [IsAdicComplete I A]
    (σ : Type*) [Finite σ]
    (q : Ideal (RestrictedPowerSeries I σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (I.map (coefficientRingHom I σ)) q)
    (hp : Ideal.IsClosedPointAwayFrom I (q.comap (coefficientRingHom I σ))) :
    let f := polynomialRingHom I σ
    let q' := q.comap f
    let l := Localization.localRingHom q' q f rfl
    Function.Bijective
      (adicCompletionMap l
        (IsLocalRing.maximalIdeal (Localization.AtPrime q'))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (IsLocalRing.map_maximalIdeal_le l)) := by
  classical
  let B := RestrictedPowerSeries I σ
  let φ := coefficientRingHom I σ
  let IB : Ideal B := I.map φ
  let P := MvPolynomial σ A
  let f : P →+* B := polynomialRingHom I σ
  have htopA : (inferInstance : TopologicalSpace A) = I.adicTopology := hI
  have oldTopologicalRingA : IsTopologicalRing A := inferInstance
  let : TopologicalSpace A := I.adicTopology
  let : IsTopologicalRing A := Eq.mp
    (congrArg (fun T : TopologicalSpace A ↦
      @IsTopologicalRing A T (inferInstance : NonUnitalNonAssocRing A)) htopA)
    oldTopologicalRingA
  let : TopologicalSpace B := adicTopology I σ
  let : IsTopologicalRing B := adicIsTopologicalRing I σ
  let : IsLinearTopology A A := I.isLinearTopology
  let : IsLinearTopology B B := IB.isLinearTopology
  have hIadic : IsAdic I := rfl
  have hIBad : IsAdic IB := rfl
  have hIBdef : TopologicalRing.IsIdealOfDefinition IB :=
    (isIdealOfDefinition_iff_isAdic ⟨IB, hIBad⟩ IB).2 hIBad
  have hIdef : TopologicalRing.IsIdealOfDefinition I :=
    (isIdealOfDefinition_iff_isAdic ⟨I, hIadic⟩ I).2 hIadic
  let : IsNoetherianRing B := isNoetherianRing_restrictedPowerSeries I σ
  let : IsAdicComplete IB B := isAdicComplete_restrictedPowerSeries I σ
  have hAweak := isWeaklyAdmissible_of_isAdicComplete I hIadic hIdef
  have hBweak := isWeaklyAdmissible_of_isAdicComplete IB hIBad hIBdef
  have hft := isTopologicallyOfFiniteType_coefficientRingHom I σ
  have hcont : Continuous φ :=
    (RingHom.continuous_adic_iff φ I IB).2
      ⟨1, by decide, fun x hx ↦ Ideal.mem_map_of_mem φ (by simpa using hx)⟩
  have hadic : RingHom.IsAdic φ := ⟨I, hIadic, hIBad⟩
  have hradA := radical_eq_topologicalNilradical_of_isIdealOfDefinition I hIdef
  have hradB := radical_eq_topologicalNilradical_of_isIdealOfDefinition IB hIBdef
  have hpTN : Ideal.IsClosedPointAwayFrom (topologicalNilradical A) (q.comap φ) :=
    (isClosedPointAwayFrom_congr_radical I (topologicalNilradical A) (q.comap φ)
      (hradA.trans TopologicalRing.isRadical_topologicalNilradical.radical.symm)).mp hp
  have hqTN : Ideal.IsClosedPointAwayFrom (topologicalNilradical B) q :=
    (isClosedPointAwayFrom_congr_radical IB (topologicalNilradical B) q
      (hradB.trans TopologicalRing.isRadical_topologicalNilradical.radical.symm)).mp hq
  have hrel := rigPoint_relative_tfae hAweak hBweak φ hcont hadic hft q hqTN
  have hfinite : (Ideal.quotientMap (I := q.comap φ) q φ le_rfl).Finite :=
    (hrel.out 2 3 (by rfl) (by rfl) (by decide) (by decide)).mp hpTN
  let π : A ⧸ q.comap φ →+* B ⧸ q := Ideal.quotientMap q φ le_rfl
  let πA : A →+* A ⧸ q.comap φ := Ideal.Quotient.mk _
  have hπeq : π.comp πA = (Ideal.Quotient.mk q).comp φ := by
    ext a
    rfl
  let : Algebra (A ⧸ q.comap φ) (B ⧸ q) :=
    @RingHom.toAlgebra (A ⧸ q.comap φ) (B ⧸ q)
      (Ideal.Quotient.commSemiring (q.comap φ)) (Ideal.Quotient.commSemiring q) π
  let : Algebra A (A ⧸ q.comap φ) :=
    @RingHom.toAlgebra A (A ⧸ q.comap φ) inferInstance
      (Ideal.Quotient.commSemiring (q.comap φ)) πA
  let : Algebra A (B ⧸ q) :=
    @RingHom.toAlgebra A (B ⧸ q) inferInstance (Ideal.Quotient.commSemiring q) (π.comp πA)
  let : IsScalarTower A (A ⧸ q.comap φ) (B ⧸ q) :=
    IsScalarTower.of_algebraMap_eq' (by simp only [RingHom.algebraMap_toAlgebra])
  let : Module.Finite (A ⧸ q.comap φ) (B ⧸ q) := hfinite
  have hAquotfinite : Module.Finite A (A ⧸ q.comap φ) :=
    Module.Finite.of_surjective (Algebra.linearMap A (A ⧸ q.comap φ)) Ideal.Quotient.mk_surjective
  have hABfinite : Module.Finite A (B ⧸ q) := Module.Finite.trans (A ⧸ q.comap φ) (B ⧸ q)
  let : Module.Finite A (B ⧸ q) := hABfinite
  have hsurj (n : ℕ) : Function.Surjective ((Ideal.Quotient.mk (q ^ (n + 1))).comp f) :=
    polynomial_quotient_surjective I (IsAdicComplete.le_jacobson_bot I) σ q n
      (finite_quotient_pow_of_finite_quotient q n)
  have hflat : f.Flat := by
    let J : Ideal P := I.map (MvPolynomial.C : A →+* P)
    let e := adicCompletionEquiv I σ
    have he : f = e.symm.toRingHom.comp (algebraMap P (AdicCompletion J P)) := by
      refine RingHom.ext fun p ↦ ?_
      refine e.injective ?_
      show e (f p) = e (e.symm (algebraMap P (AdicCompletion J P) p))
      rw [e.apply_symm_apply]
      exact adicCompletionEquiv_polynomialRingHom I σ p
    rw [he]
    exact (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian J)).comp
      (RingHom.Flat.of_bijective e.symm.bijective)
  exact adicCompletionMap_localRingHom_bijective_of_flat f hflat q
    (pow_one q ▸ hsurj 0) (hsurj 1)

end Rig

end
