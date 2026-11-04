module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Rigidifying a map to a completed local ring by a pointed finite-type extension

Let `f : T ⟶ S` be a morphism of finite type between Noetherian schemes, let `t` be a point of
`T` over `s ∈ S`, and let a local homomorphism from the local ring of `T` at `t` to the
completion of the local ring of `S` at `s` be given, compatibly with `f`. For every positive
order `N` there is a pointed finite-type scheme over `T` through whose local ring the given map
factors, and such that *every* other local homomorphism which factors through the same extension
agrees with the given one modulo the `N`-th power of the maximal ideal. This is the finiteness
input of the Artin approximation theorem: the approximating extension is constructed by adjoining
finitely many variables for the coefficients that express the images of algebra generators as
elements of the original local ring modulo `𝔪_s^N`.

## Main results

* `AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow` constructs
  the pointed finite-type extension controlling all factorizations modulo the prescribed power of
  the maximal ideal.
* `AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors`
  is the same with the locality of the comparison map dropped: the congruence is proved on an
  affine chart ring, where it holds for every algebra map out of the extension, so a factorizing
  map that is not local is controlled too. The source's statement is the corollary that adds the
  locality back, and the strengthening is what Stacks 0CAY needs.

## Implementation notes

Finite type is represented by `LocallyOfFiniteType` together with `QuasiCompact`. Equalities of
points are used to transport the relevant stalks. A local homomorphism is an `𝒪_{S,s}`-algebra
homomorphism precisely when its composite with the displayed canonical map from `𝒪_{S,s}` is the
completion map. Agreement modulo `𝔪_s^N` means that every difference belongs to the extension to
the completion of the `N`-th power of the maximal ideal of `𝒪_{S,s}`.

The extension itself is `finiteType_extension_ring`: a polynomial ring over the sections of an
affine chart of `T`, in one variable for each pair (algebra generator, ideal generator), modulo
the relations recording the approximation. Its universal property is
`finiteType_extension_bridge`.

## References

* [Stacks Project, Tag 0CAX](https://stacks.math.columbia.edu/tag/0CAX)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-! The only completion input needed below is that every element is congruent, to any fixed
order, to an element of the original local ring. -/

private lemma completion_approximation_mod_pow (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (n : ℕ)
    (x : AdicCompletion (maximalIdeal A) A) :
    ∃ a : A, x - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      (maximalIdeal A ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  let I := maximalIdeal A
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (I ^ n • ⊤) (x.1 n)
  refine ⟨a, ?_⟩
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval
    (M := A) (maximalIdeal A).fg_of_isNoetherianRing]
  show AdicCompletion.eval I A n (x - algebraMap A (AdicCompletion I A) a) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr ha.symm

/-! If two maps from a finite type algebra agree modulo an ideal on algebra generators,
then they agree modulo that ideal everywhere. -/

/-- Two algebra maps which agree modulo an ideal on a generating set of the source agree modulo
that ideal everywhere.

Public because
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/ArtinApproximationMorphism.lean`
proves its congruences with it; it carried a second copy of this statement, under the name
`agreement_of_generators`, until that copy was deleted in favour of this one. -/
theorem agreement_mod_ideal_of_algebra_generators
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] (J : Ideal D) (φ ψ : B →ₐ[R] D)
    (s : Set B) (hs : Algebra.adjoin R s = ⊤)
    (hgen : ∀ b ∈ s, φ b - ψ b ∈ J) :
    ∀ b : B, φ b - ψ b ∈ J := by
  let q : D →ₐ[R] D ⧸ J := Ideal.Quotient.mkₐ R J
  have hmaps : q.comp φ = q.comp ψ := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro b hb
    apply Ideal.Quotient.eq.2
    simpa [q] using hgen b hb
  exact fun b => Ideal.Quotient.eq.1 (AlgHom.congr_fun hmaps b)

/-- Two ring maps out of a localization which agree modulo an ideal on the image of the base
agree modulo that ideal everywhere.

Public for the same reason as `agreement_mod_ideal_of_algebra_generators`: the sibling module
`ArtinApproximationMorphism.lean` held a second copy, named `agreement_of_localization`, which
was deleted in favour of this one. -/
theorem agreement_mod_ideal_of_localization
    {R L D : Type u} [CommRing R] [CommRing L] [CommRing D]
    (M : Submonoid R) [Algebra R L] [IsLocalization M L]
    (K : Ideal D) (φ ψ : L →+* D)
    (hbase : ∀ r : R, φ (algebraMap R L r) - ψ (algebraMap R L r) ∈ K) :
    ∀ x : L, φ x - ψ x ∈ K := by
  let q : D →+* D ⧸ K := Ideal.Quotient.mk K
  have hcomp : (q.comp φ).comp (algebraMap R L) =
      (q.comp ψ).comp (algebraMap R L) := by
    ext r
    exact Ideal.Quotient.eq.2 (hbase r)
  exact fun x => Ideal.Quotient.eq.1 (DFunLike.congr_fun (IsLocalization.ringHom_ext M hcomp) x)

private lemma exists_fin_algebra_generators
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] :
    ∃ n : ℕ, ∃ b : Fin n → B, Algebra.adjoin R (Set.range b) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B).out
  let e := Fintype.equivFin {x // x ∈ s}
  refine ⟨Fintype.card {x // x ∈ s}, fun i => (e.symm i).1, ?_⟩
  have h : Set.range (fun i : Fin (Fintype.card {x // x ∈ s}) => (e.symm i).1) =
      (s : Set B) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  simpa [h] using hs

private lemma exists_coefficients_of_mem_map_span
    {R D : Type u} [CommRing R] [CommRing D] {κ : Type u} [Fintype κ]
    (φ : R →+* D) (v : κ → R) {x : D}
    (hx : x ∈ Ideal.map φ (Ideal.span (Set.range v))) :
    ∃ w : κ → D, x = ∑ k, w k * φ (v k) := by
  have hset : φ '' Set.range v = Set.range (fun k => φ (v k)) := (Set.range_comp φ v).symm
  have hspan : x ∈ Ideal.span (Set.range (fun k => φ (v k))) := by
    rwa [← hset, ← Ideal.map_span]
  obtain ⟨w, hw⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  exact ⟨w, hw.symm⟩

private lemma exists_finite_generators_of_fg
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    ∃ (κ : Type u) (_ : Fintype κ) (v : κ → R),
      Ideal.span (Set.range v) = I ∧ ∀ k, v k ∈ I := by
  classical
  let G := I.generators
  have hG : G.Finite := Submodule.FG.finite_generators hI
  let κ := {x // x ∈ G}
  let : Fintype κ := hG.fintype
  let v : κ → R := fun x => x.1
  refine ⟨κ, inferInstance, v, ?_, ?_⟩
  · have hrange : Set.range v = G := Subtype.range_coe
    rw [hrange]
    exact I.span_generators
  · intro k
    rw [← I.span_generators]
    exact Submodule.subset_span k.2

/-! Local coefficients and ideal generators can be cleared using finitely many elements of the
affine base ring. -/
private theorem clear_local_denominators_for_bridge
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    (M : Submonoid R) [Algebra R A] [IsLocalization M A] [Algebra R B]
    {n : ℕ} {κ : Type u} [Fintype κ]
    (z : κ → A) (K : Ideal D) (β : A →+* D)
    (hKspan : K = Ideal.map β (Ideal.span (Set.range z)))
    (hz : ∀ k, β (z k) ∈ K)
    (b : Fin n → B) (φ : B →+* D)
    (g : R →+* D) (hg : g = β.comp (algebraMap R A))
    (hbase : ∀ r, φ (algebraMap R B r) = g r)
    (happrox : ∀ i, ∃ a : A, φ (b i) - β a ∈ K) :
    ∃ (d a : Fin n → R) (v : κ → R) (w : Fin n → κ → D),
      (∀ i, IsUnit (g (d i))) ∧
      (∀ k, g (v k) ∈ K) ∧
      (∀ i, φ (algebraMap R B (d i) * b i) = g (a i) +
        ∑ k, w i k * g (v k)) := by
  classical
  let a₀ : Fin n → A := fun i => Classical.choose (happrox i)
  have ha₀ (i) : φ (b i) - β (a₀ i) ∈ K := Classical.choose_spec (happrox i)
  let denA : Fin n → M := fun i => (Classical.choose (IsLocalization.surj M (a₀ i))).2
  let numA : Fin n → R := fun i => (Classical.choose (IsLocalization.surj M (a₀ i))).1
  have hA (i) : a₀ i * algebraMap R A (denA i : R) = algebraMap R A (numA i) :=
    (Classical.choose_spec (IsLocalization.surj M (a₀ i)))
  let denZ : κ → M := fun k => (Classical.choose (IsLocalization.surj M (z k))).2
  let numZ : κ → R := fun k => (Classical.choose (IsLocalization.surj M (z k))).1
  have hZ (k) : z k * algebraMap R A (denZ k : R) = algebraMap R A (numZ k) :=
    (Classical.choose_spec (IsLocalization.surj M (z k)))
  let E : M := ∏ k, denZ k
  let q (k : κ) : R := ∏ j ∈ Finset.univ.erase k, (denZ j : R)
  have hprod (k : κ) : q k * (denZ k : R) = (E : R) := by
    simpa [q, E] using
      (Finset.prod_erase_mul Finset.univ (fun j => (denZ j : R)) (Finset.mem_univ k))
  let d : Fin n → R := fun i => (denA i : R) * (E : R)
  let a : Fin n → R := fun i => (E : R) * numA i
  let v : κ → R := numZ
  let c : Fin n → κ → D := fun i => Classical.choose
    (exists_coefficients_of_mem_map_span β z (hKspan ▸ ha₀ i))
  have hgapp (r : R) : g r = β (algebraMap R A r) := RingHom.congr_fun hg r
  have hc (i : Fin n) : φ (b i) - β (a₀ i) = ∑ k, c i k * β (z k) :=
    Classical.choose_spec (exists_coefficients_of_mem_map_span β z (hKspan ▸ ha₀ i))
  let w : Fin n → κ → D := fun i k => c i k * g ((denA i : R) * q k)
  refine ⟨d, a, v, w, ?_, ?_, ?_⟩
  · intro i
    rw [hg]
    simp only [d, RingHom.comp_apply]
    simpa only [map_mul] using
      ((IsLocalization.map_units A (denA i)).mul (IsLocalization.map_units A E)).map β
  · intro k
    rw [hg]
    simp only [v, RingHom.comp_apply]
    rw [← hZ k, map_mul]
    exact K.mul_mem_right _ (hz k)
  · intro i
    simp only [d, a, v]
    have hsum : φ (b i) = β (a₀ i) + ∑ k, c i k * β (z k) := by
      linear_combination hc i
    rw [map_mul, hbase, hsum, hgapp, hgapp, mul_add, Finset.mul_sum]
    congr 1
    · simp only [map_mul, ← hA i]
      ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [w, hgapp, map_mul, ← hZ k, ← hprod k]
      ring

private lemma section_comp_stalk_map
    {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) (_hU : IsAffineOpen U)
    (V : T.Opens) (_hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (s : S) (t : T) (ht : f t = s) (hsU : s ∈ U) (htV : t ∈ V)
    (D : Type u) [CommRing D] [Algebra (S.presheaf.stalk s) D]
    (sigma : T.presheaf.stalk t →+* D)
    (hbase : sigma.comp ((f.stalkMap t).hom.comp
      (eqToHom (congrArg (fun z => S.presheaf.stalk z) ht).symm).hom) =
      algebraMap (S.presheaf.stalk s) D) :
    f.appLE U V hVU ≫ T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma =
      S.presheaf.germ U s hsU ≫ CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) D) := by
  cases ht
  have hbase0 : sigma.comp (f.stalkMap t).hom = algebraMap (S.presheaf.stalk (f t)) D := by
    simpa using hbase
  have hbaseCat : f.stalkMap t ≫ CommRingCat.ofHom sigma =
      CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f t)) D) := by
    ext x
    show sigma ((f.stalkMap t).hom x) = algebraMap (S.presheaf.stalk (f t)) D x
    exact DFunLike.congr_fun hbase0 x
  have hpre : t ∈ f ⁻¹ᵁ U := by
    show f.base t ∈ U
    simpa using hsU
  have hrestrict :
      f.appLE U V hVU ≫ T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma =
      f.app U ≫ T.presheaf.germ (f ⁻¹ᵁ U) t hpre ≫ CommRingCat.ofHom sigma := by
    rw [Scheme.Hom.appLE]
    calc
      f.app U ≫ T.presheaf.map (homOfLE hVU).op ≫
            T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma =
          f.app U ≫ (T.presheaf.map (homOfLE hVU).op ≫ T.presheaf.germ V t htV) ≫
            CommRingCat.ofHom sigma :=
            congrArg (fun k => f.app U ≫ k) (Category.assoc _ _ _).symm
      _ = f.app U ≫ T.presheaf.germ (f ⁻¹ᵁ U) t hpre ≫ CommRingCat.ofHom sigma := by
            rw [T.presheaf.germ_res (homOfLE hVU) t htV]
  calc
    f.appLE U V hVU ≫ T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma =
        f.app U ≫ T.presheaf.germ (f ⁻¹ᵁ U) t hpre ≫ CommRingCat.ofHom sigma := hrestrict
    _ = S.presheaf.germ U (f t) hsU ≫ f.stalkMap t ≫ CommRingCat.ofHom sigma :=
      congrArg (fun k => k ≫ CommRingCat.ofHom sigma) (Scheme.Hom.germ_stalkMap f U t hsU).symm
    _ = S.presheaf.germ U (f t) hsU ≫
        CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f t)) D) :=
      congrArg (fun k => S.presheaf.germ U (f t) hsU ≫ k) hbaseCat

private noncomputable def finiteType_extension_relation
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} {κ : Type u} [Fintype κ]
    (b : Fin n → B) (d a : Fin n → R) (v : κ → R) (i : Fin n) :
    MvPolynomial (Fin n × κ) B :=
  MvPolynomial.C (algebraMap R B (d i) * b i) -
    MvPolynomial.C (algebraMap R B (a i)) -
    ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (algebraMap R B (v k))

private noncomputable abbrev finiteType_extension_ring
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} {κ : Type u} [Fintype κ]
    (b : Fin n → B) (d a : Fin n → R) (v : κ → R) : Type u :=
  MvPolynomial (Fin n × κ) B ⧸
    Ideal.span (Set.range (finiteType_extension_relation b d a v))

private theorem finiteType_extension_bridge
    {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D]
    {n : ℕ} {κ : Type u} [Fintype κ]
    (b : Fin n → B) (hb : Algebra.adjoin R (Set.range b) = ⊤)
    (d a : Fin n → R) (v : κ → R) (w : Fin n → κ → D)
    (K : Ideal D) (hK : ∀ k, algebraMap R D (v k) ∈ K)
    (hd : ∀ i, IsUnit (algebraMap R D (d i)))
    (φ : B →ₐ[R] D)
    (happrox : ∀ i, φ (algebraMap R B (d i) * b i) = algebraMap R D (a i) +
      ∑ k, w i k * algebraMap R D (v k)) :
    let E := finiteType_extension_ring b d a v
    ∃ ρ : E →ₐ[R] D,
      Algebra.FiniteType B E ∧
      ρ.comp ((Algebra.ofId B E).restrictScalars R) = φ ∧
      ∀ ψ : E →ₐ[R] D, ∀ x : B,
        φ x - ψ ((Algebra.ofId B E).restrictScalars R x) ∈ K := by
  classical
  let E := finiteType_extension_ring b d a v
  let P := MvPolynomial (Fin n × κ) B
  let J : Ideal P := Ideal.span (Set.range (finiteType_extension_relation b d a v))
  let : Algebra B D := φ.toRingHom.toAlgebra
  have hTower : IsScalarTower R B D :=
    IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
  let : IsScalarTower R B D := hTower
  let evB : P →ₐ[B] D := MvPolynomial.aeval (fun ik => w ik.1 ik.2)
  have hkill : J ≤ RingHom.ker evB.toRingHom := by
    apply Ideal.span_le.2
    rintro p ⟨i, rfl⟩
    show MvPolynomial.eval₂Hom (algebraMap B D) (fun ik => w ik.1 ik.2)
      (finiteType_extension_relation b d a v i) = 0
    simp only [finiteType_extension_relation, map_sub, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', map_sum, map_mul]
    have h0 : algebraMap B D (algebraMap R B (d i)) * algebraMap B D (b i) =
        algebraMap B D (algebraMap R B (a i)) +
          ∑ k, w i k * algebraMap B D (algebraMap R B (v k)) := by
      simpa [RingHom.algebraMap_toAlgebra, φ.commutes, map_mul] using happrox i
    rw [h0]
    ring
  let ρB : P ⧸ J →ₐ[B] D :=
    Ideal.Quotient.liftₐ J evB (fun p hp => RingHom.mem_ker.mp (hkill hp))
  let ρ : E →ₐ[R] D := ρB.restrictScalars R
  let j : B →ₐ[R] E := (Algebra.ofId B E).restrictScalars R
  refine ⟨ρ, inferInstance, ?_, ?_⟩
  · ext x
    show ρB (algebraMap B E x) = φ x
    rw [← Ideal.Quotient.mk_algebraMap B J x]
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes, ρB, evB]
    show φ.toRingHom x = φ x
    rfl
  · intro ψ x
    apply agreement_mod_ideal_of_algebra_generators
      (R := R) K φ (ψ.comp j) (Set.range b) hb
    rintro _ ⟨i, rfl⟩
    have hmkC (c : B) : Ideal.Quotient.mk J (MvPolynomial.C c) = j c := by
      show Ideal.Quotient.mk J (algebraMap B P c) = algebraMap B E c
      exact Ideal.Quotient.mk_algebraMap B J c
    have hz : ψ (Ideal.Quotient.mk J (finiteType_extension_relation b d a v i)) = 0 := by
      have hz0 : Ideal.Quotient.mk J (finiteType_extension_relation b d a v i) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨i, rfl⟩)
      simpa using congrArg ψ hz0
    have hrel' : ψ (algebraMap R E (d i)) * ψ (j (b i)) - ψ (algebraMap R E (a i)) -
        ∑ k, ψ (Ideal.Quotient.mk J (MvPolynomial.X (i, k))) *
          ψ (algebraMap R E (v k)) = 0 := by
      simpa [finiteType_extension_relation, map_sub, map_sum, map_mul, hmkC] using hz
    have hrel : algebraMap R D (d i) * ψ (j (b i)) - algebraMap R D (a i) -
        ∑ k, ψ (Ideal.Quotient.mk J (MvPolynomial.X (i, k))) * algebraMap R D (v k) = 0 := by
      rw [← ψ.commutes (d i), ← ψ.commutes (a i)]
      simp_rw [← ψ.commutes]
      exact hrel'
    have hψ : algebraMap R D (d i) * ψ (j (b i)) = algebraMap R D (a i) +
        ∑ k, ψ (Ideal.Quotient.mk J (MvPolynomial.X (i, k))) * algebraMap R D (v k) := by
      linear_combination hrel
    have hdiff : algebraMap R D (d i) * (φ (b i) - ψ (j (b i))) =
        ∑ k, (w i k - ψ (Ideal.Quotient.mk J (MvPolynomial.X (i, k)))) *
          algebraMap R D (v k) := by
      have happrox' : algebraMap R D (d i) * φ (b i) =
          algebraMap R D (a i) + ∑ k, w i k * algebraMap R D (v k) := by
        simpa [map_mul, φ.commutes] using happrox i
      rw [mul_sub, happrox', hψ]
      simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      congr 1
      ext k
      ring
    have hdiff_mem : φ (b i) - ψ (j (b i)) ∈ K := by
      apply (Ideal.unit_mul_mem_iff_mem K (hd i)).mp
      rw [hdiff]
      apply Ideal.sum_mem
      intro k hk
      exact K.mul_mem_left _ (hK k)
    simpa only [AlgHom.comp_apply] using hdiff_mem

/-- **A finite type algebra over the sections of an affine open, with a map to a local ring
through which the stalk map factors, is a pointed finite type extension.** The extension is
Noetherian, `E` being of finite type over the Noetherian ring `Γ(T, V)`. For `E` of finite type
over `C = Γ(T, V)` and `ρ : E → D` agreeing with `σ` on `C`, the scheme `Spec E` with the point
`ρ` determines is a finite type `T`-scheme above `t` through which `σ` factors by a local
homomorphism, and `ι : E → 𝒪_{Spec E, t'}` is a factorisation of `ρ` through that stalk.

The last clause is what a consumer needs: for *any* `τ'` out of the stalk of the extension, the
map `τ' ∘ ι` out of `E` and the map `τ' ∘ 𝒪_{T,t} → 𝒪_{Spec E, t'}` out of the stalk agree on
`C`. Applied to the `τ'` of a nearby factorisation, that identifies the composite
`E → D` it determines with the restriction of that factorisation to the chart, which is what makes
a congruence over the extension into a congruence over `E`.

This is the geometric step of
`AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow`, stated for an
arbitrary finite type `E` rather than only for the one Stacks 0CAX manufactures. -/
theorem exists_pointed_extension_of_finiteType_chartAlgebra
    {T : Scheme.{u}} [IsNoetherian T] (t : T) {V : T.Opens} (hV : IsAffineOpen V) (htV : t ∈ V)
    {D : Type u} [CommRing D] [IsLocalRing D]
    (sigma : T.presheaf.stalk t →+* D) (hsigma : IsLocalHom sigma)
    (E : Type u) [CommRing E] [Algebra Γ(T, V) E] [Algebra.FiniteType Γ(T, V) E]
    (rho : E →+* D)
    (hrho : rho.comp (algebraMap Γ(T, V) E) = sigma.comp (T.presheaf.germ V t htV).hom) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g) (_ : IsNoetherian T')
      (tau : T'.presheaf.stalk t' →+* D) (iota : E →+* T'.presheaf.stalk t'),
      IsLocalHom tau ∧
      sigma = tau.comp ((g.stalkMap t').hom.comp
        (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom) ∧
      rho = tau.comp iota ∧
      ∀ tau' : T'.presheaf.stalk t' →+* D,
        (tau'.comp iota).comp (algebraMap Γ(T, V) E) =
          (tau'.comp ((g.stalkMap t').hom.comp
            (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom)).comp
              (T.presheaf.germ V t htV).hom := by
  classical
  let C := Γ(T, V)
  let : IsLocalHom sigma := hsigma
  let γT : C →+* T.presheaf.stalk t := (T.presheaf.germ V t htV).hom
  let T' := Spec (CommRingCat.of E)
  let g : T' ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap C E)) ≫ hV.fromSpec
  let mD : Spec (CommRingCat.of D) ⟶ T' := Spec.map (CommRingCat.ofHom rho)
  let t' : T' := mD (closedPoint (CommRingCat.of D))
  let tau : T'.presheaf.stalk t' →+* D := (Scheme.stalkClosedPointTo mD).hom
  let iota : E →+* T'.presheaf.stalk t' :=
    ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ T'.presheaf.germ ⊤ t' trivial).hom
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap C E))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let : LocallyOfFiniteType g := by
    dsimp only [g]
    infer_instance
  let : QuasiCompact g := by
    dsimp only [g]
    infer_instance
  have hnoethC : IsNoetherianRing C := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hnoethE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing C E
  let : IsNoetherian T' := by
    dsimp only [T']
    infer_instance
  have hchart : hV.fromSpecStalk htV = T.fromSpecStalk t := by
    rw [Scheme.fromSpecStalk]
    exact IsAffineOpen.fromSpecStalk_eq hV
      (isAffineOpen_opensRange (T.affineCover.f (T.affineCover.idx t))) t htV
      (T.affineCover.covers t)
  have hmap : mD ≫ g = Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t := by
    dsimp only [mD, g]
    have hring : CommRingCat.ofHom (algebraMap C E) ≫ CommRingCat.ofHom rho =
        CommRingCat.ofHom (sigma.comp γT) := by
      calc
        CommRingCat.ofHom (algebraMap C E) ≫ CommRingCat.ofHom rho =
            CommRingCat.ofHom (rho.comp (algebraMap C E)) := by
              ext x
              rfl
        _ = CommRingCat.ofHom (sigma.comp γT) := congrArg CommRingCat.ofHom hrho
    calc
      Spec.map (CommRingCat.ofHom rho) ≫
          Spec.map (CommRingCat.ofHom (algebraMap C E)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom (algebraMap C E) ≫ CommRingCat.ofHom rho) ≫
          hV.fromSpec :=
            (Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap C E))
              (CommRingCat.ofHom rho) hV.fromSpec).symm
      _ = Spec.map (CommRingCat.ofHom (sigma.comp γT)) ≫ hV.fromSpec := by rw [hring]
      _ = Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t := by
        have hφcat : T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma =
            CommRingCat.ofHom (sigma.comp γT) := by
          ext x
          rfl
        rw [← hφcat, ← hchart]
        show Spec.map (T.presheaf.germ V t htV ≫ CommRingCat.ofHom sigma) ≫ hV.fromSpec =
          Spec.map (CommRingCat.ofHom sigma) ≫
            (Spec.map (T.presheaf.germ V t htV) ≫ hV.fromSpec)
        exact Spec.map_comp_assoc (T.presheaf.germ V t htV)
          (CommRingCat.ofHom sigma) hV.fromSpec
  let e := SpecToEquivOfLocalRing T (CommRingCat.of D)
  have heK : e (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t) =
      ⟨t, ⟨CommRingCat.ofHom sigma, hsigma⟩⟩ := by
    show e (e.symm ⟨t, ⟨CommRingCat.ofHom sigma, hsigma⟩⟩) = _
    exact e.apply_symm_apply _
  have he : e (mD ≫ g) = ⟨t, ⟨CommRingCat.ofHom sigma, hsigma⟩⟩ :=
    (congrArg e hmap).trans heK
  obtain ⟨hgt, hstalk⟩ := (SpecToEquivOfLocalRing_eq_iff).mp he
  change g t' = t at hgt
  have hcomp : Scheme.stalkClosedPointTo (mD ≫ g) =
      g.stalkMap t' ≫ Scheme.stalkClosedPointTo mD := by
    simpa [t', mD] using Scheme.stalkClosedPointTo_comp mD g
  have hcast : (T.presheaf.stalkCongr (Inseparable.of_eq hgt)).hom =
      eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt) := by
    cases hgt
    simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  have hstalk' : Scheme.stalkClosedPointTo (mD ≫ g) =
      eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt) ≫ CommRingCat.ofHom sigma := by
    calc
      _ = (T.presheaf.stalkCongr (Inseparable.of_eq hgt)).hom ≫
          CommRingCat.ofHom sigma := by
            change Scheme.stalkClosedPointTo (mD ≫ g) =
              (T.presheaf.stalkCongr (Inseparable.of_eq hgt)).hom ≫
                CommRingCat.ofHom sigma at hstalk
            exact hstalk
      _ = _ := congrArg (fun q => q ≫ CommRingCat.ofHom sigma) hcast
  have hcancel :
      eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
        eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt) = 𝟙 _ := by
    cases hgt
    simp
  have hfacCat :
      eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
        g.stalkMap t' ≫ Scheme.stalkClosedPointTo mD = CommRingCat.ofHom sigma := by
    calc
      _ = eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
          (g.stalkMap t' ≫ Scheme.stalkClosedPointTo mD) :=
            CategoryTheory.Category.assoc _ _ _
      _ = eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
          Scheme.stalkClosedPointTo (mD ≫ g) := by rw [← hcomp]
      _ = eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
          (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt) ≫
            CommRingCat.ofHom sigma) := by rw [hstalk']
      _ = (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm ≫
          eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt)) ≫
            CommRingCat.ofHom sigma := (CategoryTheory.Category.assoc _ _ _).symm
      _ = CommRingCat.ofHom sigma := by
        rw [hcancel]
        exact CategoryTheory.Category.id_comp _
  have hfactor : sigma = tau.comp ((g.stalkMap t').hom.comp
      (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm).hom) := by
    simpa [tau, RingHom.comp_assoc] using (congrArg CommRingCat.Hom.hom hfacCat).symm
  -- the sections of the extension over the chart, computed
  have hr : Set.range hV.fromSpec ⊆ (V : Set T) := by rw [hV.range_fromSpec]
  have htop : (⊤ : T'.Opens) ≤ g ⁻¹ᵁ V := by
    intro x hx
    show (Spec.map (CommRingCat.ofHom (algebraMap C E)) ≫ hV.fromSpec) x ∈ (V : Set T)
    rw [Scheme.Hom.comp_apply]
    exact hr ⟨Spec.map (CommRingCat.ofHom (algebraMap C E)) x, rfl⟩
  have hj : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    intro x hx
    show hV.fromSpec x ∈ (V : Set T)
    exact hr ⟨x, rfl⟩
  have hq : (⊤ : (Spec (CommRingCat.of E)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap C E))) ⁻¹ᵁ
        (⊤ : (Spec (CommRingCat.of C)).Opens) := by simp
  have happ : hV.fromSpec.appLE V ⊤ hj ≫
        (Spec.map (CommRingCat.ofHom (algebraMap C E))).appLE ⊤ ⊤ hq =
      g.appLE V ⊤ htop := by
    simpa [g] using Scheme.Hom.appLE_comp_appLE
      (Spec.map (CommRingCat.ofHom (algebraMap C E))) hV.fromSpec V ⊤ ⊤ hj hq
  have hjapp : hV.fromSpec.appLE V ⊤ hj = (Scheme.ΓSpecIso C).inv := by
    have hmapcomp : (Spec C).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
        (Spec C).presheaf.map (homOfLE hj).op = 𝟙 _ := by
      rw [← Functor.map_comp]
      have hinc : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE hj).op = 𝟙 _ :=
        Subsingleton.elim _ _
      rw [hinc]
      simp
    apply (cancel_epi (Scheme.ΓSpecIso C).hom).1
    have hspecIso : (Scheme.ΓSpecIso C).hom ≫ hV.fromSpec.app V =
        (Spec C).presheaf.map (eqToHom hV.fromSpec_preimage_self).op := by
      simpa [C] using hV.ΓSpecIso_hom_fromSpec_app
    calc
      (Scheme.ΓSpecIso C).hom ≫ hV.fromSpec.appLE V ⊤ hj =
          (Scheme.ΓSpecIso C).hom ≫ hV.fromSpec.app V ≫
          (Spec C).presheaf.map (homOfLE hj).op := rfl
      _ = (Spec C).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
            (Spec C).presheaf.map (homOfLE hj).op :=
          congrArg (fun q => q ≫ (Spec C).presheaf.map (homOfLE hj).op) hspecIso
      _ = 𝟙 _ := hmapcomp
      _ = (Scheme.ΓSpecIso C).hom ≫ (Scheme.ΓSpecIso C).inv := by simp
  have hqapp : (Spec.map (CommRingCat.ofHom (algebraMap C E))).appLE ⊤ ⊤ hq =
      (Spec.map (CommRingCat.ofHom (algebraMap C E))).appTop := by
    rw [Scheme.Hom.appLE]
    have hqmap : homOfLE hq = 𝟙 (⊤ : (Spec (CommRingCat.of E)).Opens) :=
      Subsingleton.elim _ _
    rw [hqmap]
    show (Spec.map (CommRingCat.ofHom (algebraMap C E))).app ⊤ ≫ 𝟙 _ = _
    rw [CategoryTheory.Category.comp_id]
  have hCE : g.appLE V ⊤ htop ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom =
      CommRingCat.ofHom (algebraMap C E) := by
    calc
      _ = hV.fromSpec.appLE V ⊤ hj ≫
          (Spec.map (CommRingCat.ofHom (algebraMap C E))).appLE ⊤ ⊤ hq ≫
            (Scheme.ΓSpecIso (CommRingCat.of E)).hom := by
        rw [← happ]
        exact CategoryTheory.Category.assoc _ _ _
      _ = (Scheme.ΓSpecIso C).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap C E))).appTop ≫
            (Scheme.ΓSpecIso (CommRingCat.of E)).hom := by rw [hjapp, hqapp]
      _ = CommRingCat.ofHom (algebraMap C E) := by
        simp only [Scheme.ΓSpecIso_naturality]
        have hIso : Scheme.ΓSpecIso C = Scheme.ΓSpecIso (CommRingCat.of (↑C)) := rfl
        rw [← hIso]
        simp
  refine ⟨T', g, t', hgt, inferInstance, inferInstance, inferInstance, tau, iota,
    Scheme.isLocalHom_stalkClosedPointTo' mD, hfactor, ?_, ?_⟩
  · -- `rho = tau ∘ iota`
    have hgerm := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom rho)
    have hcat : (Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        T'.presheaf.germ ⊤ t' trivial ≫ Scheme.stalkClosedPointTo mD =
        CommRingCat.ofHom rho := by
      rw [show T'.presheaf.germ ⊤ t' trivial ≫ Scheme.stalkClosedPointTo mD =
        (Scheme.ΓSpecIso (CommRingCat.of E)).hom ≫ CommRingCat.ofHom rho from hgerm,
        Iso.inv_hom_id_assoc]
    exact (congrArg CommRingCat.Hom.hom hcat).symm
  · -- the composed clause
    intro tau'
    let : Algebra (T.presheaf.stalk t) D :=
      (tau'.comp ((g.stalkMap t').hom.comp
        (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm).hom)).toAlgebra
    have hbaseTau' : tau'.comp ((g.stalkMap t').hom.comp
        (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm).hom) =
          algebraMap (T.presheaf.stalk t) D := rfl
    have hsectTau' := section_comp_stalk_map g V hV ⊤ (isAffineOpen_top T') htop
      t t' hgt htV (by trivial) D tau' hbaseTau'
    have hcat : CommRingCat.ofHom (algebraMap C E) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          T'.presheaf.germ ⊤ t' trivial ≫ CommRingCat.ofHom tau') =
        T.presheaf.germ V t htV ≫
          CommRingCat.ofHom (algebraMap (T.presheaf.stalk t) D) := by
      calc
        _ = g.appLE V ⊤ htop ≫ T'.presheaf.germ ⊤ t' trivial ≫
              CommRingCat.ofHom tau' := by
          rw [← hCE]
          simp [CategoryTheory.Category.assoc]
        _ = _ := hsectTau'
    exact congrArg CommRingCat.Hom.hom hcat

/-- **A local map from the stalk of a finite-type Noetherian scheme to the completed local ring
of its base can be made rigid modulo any positive power of the base maximal ideal after a
pointed finite-type extension — and the rigidity holds for every factorising map, local or
not.**

This is `AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow`
(Stacks 0CAX) with the locality of `σ'` dropped from the agreement clause. The source states
that clause for local `σ'`, but its proof never uses the locality: the congruence is established
on the affine chart ring `C = Γ(T, V)`, where it holds for *every* `R`-algebra map `E → D`
because the relations defining `E` force it (`finiteType_extension_bridge`), and the passage
from `C` to the stalk `𝒪_{T,t} = C_{𝔭}` is `agreement_mod_ideal_of_localization`, which only
needs the two maps to be defined on the localisation — the denominators are already invertible
there. So no condition on `σ'` beyond being an `𝒪_{S,s}`-algebra map factoring through
`𝒪_{T',t'}` is needed.

This strengthening is what lets Stacks 0CAY be stated with the source's antecedent on the
factorisation of `σ'`: see
`exists_finiteType_pointed_extension_conormalAlgebra_iso_of_isLocalHom` (in the namespace
`Stacks.ConormalApproximation`), where the inner application of 0CAX is made to
`τ' ∘ (𝒪_{T,t} → 𝒪_{T₁,t₁})`, a map whose locality is exactly what the source does not assume. -/
theorem exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors
    {S T : Scheme.{u}} (f : T ⟶ S)
    [IsNoetherian S] [IsNoetherian T]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (s : S) (t : T) (ht : f t = s)
    (sigma : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hsigma : IsLocalHom sigma)
    (hsigma_base :
      sigma.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
        algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g),
      ∃ tau : T'.presheaf.stalk t' →+*
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
        IsLocalHom tau ∧
        sigma = tau.comp ((g.stalkMap t').hom.comp
          (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom) ∧
        tau.comp ((g.stalkMap t').hom.comp
          ((eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom.comp
            ((f.stalkMap t).hom.comp
              (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom))) =
          algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) ∧
        (∀ (sigma' : T.presheaf.stalk t →+*
            AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)),
          sigma'.comp ((f.stalkMap t).hom.comp
              (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
              algebraMap (S.presheaf.stalk s)
                (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                  (S.presheaf.stalk s)) →
          (∃ tau' : T'.presheaf.stalk t' →+*
              AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
            sigma' = tau'.comp ((g.stalkMap t').hom.comp
              (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom)) →
          ∀ a : T.presheaf.stalk t,
            sigma a - sigma' a ∈
              Ideal.map
                (algebraMap (S.presheaf.stalk s)
                  (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                    (S.presheaf.stalk s)))
                (maximalIdeal (S.presheaf.stalk s) ^ N)) := by
  classical
  -- The hypothesis `1 ≤ N` is part of the source statement; the construction below is uniform
  -- in `N` and does not use it.
  have _ : 1 ≤ N := hN
  let A := S.presheaf.stalk s
  let D := AdicCompletion (maximalIdeal A) A
  let beta : A →+* D := algebraMap A D
  let : IsLocalHom sigma := hsigma
  obtain ⟨U, hU, hsU, hsubU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) (by simp)
  obtain ⟨V, hV, htV, hsubV⟩ := exists_isAffineOpen_mem_and_subset
    (U := f ⁻¹ᵁ U) (x := t) (show f t ∈ U from ht ▸ hsU)
  have hVU : V ≤ f ⁻¹ᵁ U := SetLike.coe_subset_coe.mp hsubV
  let R := Γ(S, U)
  let C := Γ(T, V)
  let : Algebra R C := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.FiniteType R C := RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  let : Algebra R A := S.presheaf.algebra_section_stalk ⟨s, hsU⟩
  let p : Ideal R := (hU.primeIdealOf ⟨s, hsU⟩).asIdeal
  let M : Submonoid R := p.primeCompl
  let : IsLocalization.AtPrime A p := hU.isLocalization_stalk ⟨s, hsU⟩
  let : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing M A
      (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
  let : Algebra A D := inferInstance
  let γS : R →+* A := (S.presheaf.germ U s hsU).hom
  let γT : C →+* T.presheaf.stalk t := (T.presheaf.germ V t htV).hom
  let φ : C →+* D := sigma.comp γT
  let g₀ : R →+* D := beta.comp γS
  have hbaseOf : ∀ σ : T.presheaf.stalk t →+* D,
      σ.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z => S.presheaf.stalk z) ht).symm).hom) = algebraMap A D →
      ∀ r : R, σ (γT (algebraMap R C r)) = g₀ r := by
    intro σ hσ r
    have h := congrArg (fun k : CommRingCat.Hom R (CommRingCat.of D) => k.hom r)
      (section_comp_stalk_map f U hU V hV hVU s t ht hsU htV D σ hσ)
    exact h
  have hbase : ∀ r : R, φ (algebraMap R C r) = g₀ r := hbaseOf sigma hsigma_base
  obtain ⟨κ, hκ, z, hzspan, hzin⟩ :=
    exists_finite_generators_of_fg (maximalIdeal A ^ N)
      (maximalIdeal A).fg_of_isNoetherianRing.pow
  let : Fintype κ := hκ
  let K : Ideal D := Ideal.map beta (maximalIdeal A ^ N)
  have hKspan : K = Ideal.map beta (Ideal.span (Set.range z)) := by rw [hzspan]
  have hzK : ∀ k, beta (z k) ∈ K := fun k => Ideal.mem_map_of_mem beta (hzin k)
  obtain ⟨n, b, hb⟩ := exists_fin_algebra_generators (R := R) (B := C)
  have happrox : ∀ i : Fin n, ∃ a : A, φ (b i) - beta a ∈ K :=
    fun i => completion_approximation_mod_pow A N (φ (b i))
  have hg₀ : g₀ = beta.comp (algebraMap R A) := by rfl
  obtain ⟨d, a, v, w, hd, hv, hrel⟩ :=
    clear_local_denominators_for_bridge M z K beta hKspan hzK b φ g₀ hg₀ hbase happrox
  let : Algebra R D := g₀.toAlgebra
  let phiA : C →ₐ[R] D := { toRingHom := φ, commutes' := hbase }
  obtain ⟨rho, hftE, hrho, huniq⟩ :=
    finiteType_extension_bridge b hb d a v w K hv hd phiA hrel
  let E := finiteType_extension_ring b d a v
  let : Algebra.FiniteType C E := hftE
  have hrhoRing : rho.toRingHom.comp (algebraMap C E) = φ := by
    have hh := congrArg AlgHom.toRingHom hrho
    change rho.toRingHom.comp (algebraMap C E) = φ at hh
    exact hh
  obtain ⟨T', g, t', hgt, hftg, hqcg, hnoeth₁, tau, iota, hlocTau, hfactor, hrhoFac, hclause⟩ :=
    exists_pointed_extension_of_finiteType_chartAlgebra t hV htV sigma hsigma E rho.toRingHom
      hrhoRing
  have := hftg
  have := hqcg
  refine ⟨T', g, t', hgt, inferInstance, inferInstance, ?_⟩
  refine ⟨tau, ?_, ?_, ?_, ?_⟩
  · exact hlocTau
  · exact hfactor
  · calc
      _ = (tau.comp ((g.stalkMap t').hom.comp
          (eqToHom (congrArg (fun z => T.presheaf.stalk z) hgt).symm).hom)).comp
            ((f.stalkMap t).hom.comp
              (eqToHom (congrArg (fun z => S.presheaf.stalk z) ht).symm).hom) := by
          simp [RingHom.comp_assoc]
      _ = sigma.comp ((f.stalkMap t).hom.comp
            (eqToHom (congrArg (fun z => S.presheaf.stalk z) ht).symm).hom) := by
          rw [hfactor]
      _ = algebraMap A D := hsigma_base
  · intro sigma' hbase' hfactor' a₀
    obtain ⟨tau', hfactor'⟩ := hfactor'
    let : Algebra R D := g₀.toAlgebra
    let : Algebra (T.presheaf.stalk t) D := sigma'.toAlgebra
    let ψring : E →+* D := tau'.comp iota
    have hψC : ψring.comp (algebraMap C E) = sigma'.comp γT := by
      have h := hclause tau'
      rw [← hfactor'] at h
      exact h
    let ψA : E →ₐ[R] D :=
      { toRingHom := ψring
        commutes' := by
          intro r
          show ψring (algebraMap C E (algebraMap R C r)) = g₀ r
          show (ψring.comp (algebraMap C E)) (algebraMap R C r) = g₀ r
          rw [hψC]
          exact hbaseOf sigma' hbase' r }
    have hsections : ∀ x : C, sigma (γT x) - sigma' (γT x) ∈ K := by
      intro x
      have hx := huniq ψA x
      change φ x - ψring (algebraMap C E x) ∈ K at hx
      change φ x - (ψring.comp (algebraMap C E)) x ∈ K at hx
      rw [hψC] at hx
      show sigma (γT x) - sigma' (γT x) ∈ K
      exact hx
    let pT := (hV.primeIdealOf ⟨t, htV⟩).asIdeal
    let MT := pT.primeCompl
    let : Algebra C (T.presheaf.stalk t) :=
      T.presheaf.algebra_section_stalk ⟨t, htV⟩
    let : IsLocalization.AtPrime (T.presheaf.stalk t) pT :=
      IsAffineOpen.isLocalization_stalk hV ⟨t, htV⟩
    have hstalk := agreement_mod_ideal_of_localization MT K sigma sigma' hsections
    simpa [K, beta] using hstalk a₀

/-- A local map from the stalk of a finite-type Noetherian scheme to the completed local ring
of its base can be made rigid modulo any positive power of the base maximal ideal after a
pointed finite-type extension.

This is the source's statement, in which the comparison maps `σ'` are required to be local. It is
`AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors`,
which proves the agreement clause for every `σ'` factoring through the extension. -/
@[stacks 0CAX]
theorem exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow
    {S T : Scheme.{u}} (f : T ⟶ S)
    [IsNoetherian S] [IsNoetherian T]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (s : S) (t : T) (ht : f t = s)
    (sigma : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hsigma : IsLocalHom sigma)
    (hsigma_base :
      sigma.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
        algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g),
      ∃ tau : T'.presheaf.stalk t' →+*
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
        IsLocalHom tau ∧
        sigma = tau.comp ((g.stalkMap t').hom.comp
          (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom) ∧
        tau.comp ((g.stalkMap t').hom.comp
          ((eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom.comp
            ((f.stalkMap t).hom.comp
              (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom))) =
          algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) ∧
        (∀ (sigma' : T.presheaf.stalk t →+*
            AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)),
          IsLocalHom sigma' →
          sigma'.comp ((f.stalkMap t).hom.comp
              (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
              algebraMap (S.presheaf.stalk s)
                (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                  (S.presheaf.stalk s)) →
          (∃ tau' : T'.presheaf.stalk t' →+*
              AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
            sigma' = tau'.comp ((g.stalkMap t').hom.comp
              (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom)) →
          ∀ a : T.presheaf.stalk t,
            sigma a - sigma' a ∈
              Ideal.map
                (algebraMap (S.presheaf.stalk s)
                  (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                    (S.presheaf.stalk s)))
                (maximalIdeal (S.presheaf.stalk s) ^ N)) := by
  obtain ⟨T', g, t', hgt, hft, hqc, tau, hloc, hfac, hbase, hagree⟩ :=
    exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow_of_factors
      f s t ht sigma hsigma hsigma_base N hN
  exact ⟨T', g, t', hgt, hft, hqc, tau, hloc, hfac, hbase, fun sigma' _ => hagree sigma'⟩

end AlgebraicGeometry
