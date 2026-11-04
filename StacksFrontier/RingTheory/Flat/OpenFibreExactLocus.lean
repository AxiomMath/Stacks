module

public import StacksFrontier.RingTheory.Depth.ExactnessCriterion
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# Openness of the locus where a complex is exact on the fibres

Let `R → S` be a flat ring map of finite type with `R` Noetherian, whose fibres
`S ⊗_R κ(𝔭)` are Cohen–Macaulay and equidimensional of one fixed dimension `d`, and let
`0 → S^{n_{e+1}} → S^{n_e} → ⋯ → S^{n_1} → S^{n_0}` be a complex of finite free `S`-modules.
For a prime `𝔮` of `S` lying over `𝔭` of `R`, the complex `F_𝔮 ⊗_R κ(𝔭)` is the complex of
finite free `S_𝔮/𝔭S_𝔮`-modules obtained by base change. The set of `𝔮` at which this complex is
exact is open in `Spec S`.

The proof follows the source. At a point `𝔮` of the set, the local criterion at each spot of the
complex (Stacks 00MI) shows that `F_𝔮` is already exact, so by the Buchsbaum–Eisenbud criterion
(Stacks 00N1) over `S_𝔮` the rank of `φ_k` over `S_𝔮` is the alternating sum
`r_k = n_{k+1} - n_{k+2} + ⋯`; hence every minor of `φ_k` of size `> r_k` is killed by an
element outside `𝔮`, and dies in every fibre ring near `𝔮`. The criterion over `S_𝔮/𝔭S_𝔮`
gives that the ideal `I_k` of `r_k × r_k` minors of `φ_k` has depth at least `k + 1` in the
fibre ring at `𝔮`. Either `I_k ⊄ 𝔮`, an open condition, or `I_k` contains elements
`f_1, …, f_m` (`m > k`) whose images form a regular sequence in `S_𝔮/𝔭S_𝔮`; by Stacks 00RA
they stay regular at all points of `V(f_1, …, f_m)` near `𝔮`, while off `V(f)` the ideal `I_k`
is the unit ideal. Near `𝔮` all the conditions of 00N1 therefore hold in the fibre rings, and
the complex is exact there.

## Main results

* `Algebra.isOpen_setOf_injective_and_exact_baseChange_fiber`: Stacks 00RB.

## Implementation notes

The complex is given as in Stacks 00N1: maps `φ k : S^{n (k+1)} → S^{n k}` for all `k`, of
which `φ 0, …, φ e` are read, with `φ k ∘ φ (k+1) = 0` for `k < e`. Exactness means injectivity
of the top map and exactness at `S^{n_e}, …, S^{n_1}`.

The fibre complex `F_𝔮 ⊗_R κ(𝔭)` is written as the base change `A ⊗_S F` along
`S → A = S_𝔮/𝔭S_𝔮`, where `𝔭 = 𝔮 ∩ R`: indeed `F_𝔮 ⊗_R κ(𝔭) = F ⊗_S (S_𝔮 ⊗_R κ(𝔭))` and
`S_𝔮 ⊗_R κ(𝔭) ≅ S_𝔮/𝔭S_𝔮`. The quotient is the ring used in Stacks 00RA, and carries its
canonical `S`-algebra structure.

The fibre hypothesis is spelled out as in Stacks 00RA: each nonzero fibre `S ⊗_R κ(𝔭)` has
Cohen–Macaulay local rings, is equidimensional, and has Krull dimension `d`.

The source applies Stacks 00MI to the whole complex; its proof is an application, at each spot
separately, of the local criterion for flatness in the form
`Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top`, and that is the form
used here, over the local homomorphism `R_𝔭 → S_𝔮`.

## References

* [StacksProject 00RB](https://stacks.math.columbia.edu/tag/00RB)

## Tags

exact complex, fibre, flat, Cohen-Macaulay, regular sequence, open locus
-/

open RingTheory.Sequence IsLocalRing Topology
open scoped Pointwise

namespace Stacks.Depth.RegularSequence

/-! ### Depth of an ideal on the ring itself -/

section Depth

variable {B : Type*} [CommRing B]

/-- The depth of the unit ideal on the ring itself is `⊤`. -/
lemma depth_top_self : Module.depth B ⊤ B = ⊤ := by
  simp only [Module.depth, Submodule.top_smul, ↓reduceIte]

/-- If a proper ideal `I` of `B` has depth at least `k + 1` on `B`, then `I` contains a
`B`-regular sequence of length greater than `k`. -/
lemma exists_isRegular_of_le_depth {I : Ideal B} (hI : I ≠ ⊤) {k : ℕ}
    (h : ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth B I B) :
    ∃ rs : List B, (∀ r ∈ rs, r ∈ I) ∧ IsRegular B rs ∧ k < rs.length := by
  have hI' : I • (⊤ : Submodule B B) ≠ ⊤ := by simpa using hI
  simp only [Module.depth, hI', ↓reduceIte] at h
  have hlt : ((k : ℕ) : ℕ∞) < _ := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) h
  obtain ⟨rs, hlt'⟩ := lt_iSup_iff.mp hlt
  obtain ⟨⟨hmem, hreg⟩, hlt''⟩ := lt_iSup_iff.mp hlt'
  exact ⟨rs, hmem, hreg, by exact_mod_cast hlt''⟩

/-- In a nontrivial ring `B`, an ideal of depth at least `1` on `B` is nonzero. -/
lemma ne_bot_of_one_le_depth [Nontrivial B] {I : Ideal B}
    (h : ((0 + 1 : ℕ) : ℕ∞) ≤ Module.depth B I B) : I ≠ ⊥ := by
  rintro rfl
  obtain ⟨rs, hmem, hreg, hlen⟩ := exists_isRegular_of_le_depth bot_ne_top h
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_length_pos hlen
  obtain rfl : r = 0 := by simpa using hmem r List.mem_cons_self
  have h0 := ((isWeaklyRegular_cons_iff B 0 rs).mp hreg.toIsWeaklyRegular).1
  exact one_ne_zero (h0 (show (0 : B) • (1 : B) = (0 : B) • (0 : B) by simp))

end Depth

/-! ### Regular sequences up to units -/

section Units

variable {B : Type*} [CommRing B]

/-- If each term of `rs'` is a unit multiple of the corresponding term of `rs`, then the two
sequences generate the same ideal. -/
lemma ofList_eq_of_forall₂ {rs rs' : List B}
    (h : List.Forall₂ (fun (a b : B) => ∃ u : Bˣ, b = (u : B) * a) rs rs') :
    Ideal.ofList rs' = Ideal.ofList rs := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    obtain ⟨u, rfl⟩ := hab
    rw [Ideal.ofList_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit u.isUnit]

/-- If each term of `rs'` is a unit multiple of the corresponding term of `rs` and `rs` is
weakly `M`-regular, then so is `rs'`. -/
lemma isWeaklyRegular_of_forall₂ {M : Type*} [AddCommGroup M] [Module B M] {rs rs' : List B}
    (h : List.Forall₂ (fun (a b : B) => ∃ u : Bˣ, b = (u : B) * a) rs rs')
    (hrs : IsWeaklyRegular M rs) :
    IsWeaklyRegular M rs' := by
  induction h generalizing M with
  | nil => exact hrs
  | @cons a b l l' hab _ ih =>
    obtain ⟨u, rfl⟩ := hab
    rw [isWeaklyRegular_cons_iff] at hrs ⊢
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hrs.1
      have := congrArg (fun z : M => (↑u⁻¹ : B) • z) hxy
      simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using this
    · have hsub : (a • ⊤ : Submodule B M) = ((↑u * a : B) • ⊤ : Submodule B M) := by
        rw [← Submodule.ideal_span_singleton_smul, ← Submodule.ideal_span_singleton_smul,
          Ideal.span_singleton_mul_left_unit u.isUnit]
      exact (LinearEquiv.isWeaklyRegular_congr (Submodule.quotEquivOfEq _ _ hsub) l').mp
        (ih hrs.2)

/-- If each term of `rs'` is a unit multiple of the corresponding term of `rs` and `rs` is
`M`-regular, then so is `rs'`. -/
lemma isRegular_of_forall₂ {M : Type*} [AddCommGroup M] [Module B M] {rs rs' : List B}
    (h : List.Forall₂ (fun (a b : B) => ∃ u : Bˣ, b = (u : B) * a) rs rs') (hrs : IsRegular M rs) :
    IsRegular M rs' := by
  rw [RingTheory.Sequence.isRegular_iff] at hrs ⊢
  exact ⟨isWeaklyRegular_of_forall₂ h hrs.1, by rw [ofList_eq_of_forall₂ h]; exact hrs.2⟩

end Units

/-! ### Membership in `J • ⊤` for a finite free module -/

/-- A vector `x : ι → B` lies in `J • ⊤` if and only if each of its coordinates lies in `J`. -/
lemma mem_smul_top_pi_iff {B : Type*} [CommRing B] (J : Ideal B) {ι : Type*} [Finite ι]
    (x : ι → B) : x ∈ J • (⊤ : Submodule B (ι → B)) ↔ ∀ i, x i ∈ J := by
  classical
  refine ⟨fun hx i => ?_, fun h => ?_⟩
  · refine Submodule.smul_induction_on (p := fun y => y i ∈ J) hx (fun a ha m _ => ?_)
      (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right (m i) ha
    · simpa using J.add_mem hy hz
  · cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/-! ### Minors under a ring map -/

section Minors

variable {S T : Type*} [CommRing S] [CommRing T] {a b : ℕ}

/-- The ideal generated by the `r × r` minors of `A.map f` is the image under `f` of the ideal
generated by the `r × r` minors of `A`. -/
lemma span_minorSet_map (f : S →+* T) (A : Matrix (Fin a) (Fin b) S) (r : ℕ) :
    Ideal.span (Stacks.DeterminantalRank.minorSet (A.map f) r) =
      (Ideal.span (Stacks.DeterminantalRank.minorSet A r)).map f := by
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨ρ, γ, rfl⟩
    exact ⟨_, ⟨ρ, γ, rfl⟩, by rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]⟩
  · rintro ⟨y, ⟨ρ, γ, rfl⟩, rfl⟩
    exact ⟨ρ, γ, by rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]⟩

/-- A minor of `A.map f` is the image under `f` of the corresponding minor of `A`. -/
lemma det_submatrix_map (f : S →+* T) (A : Matrix (Fin a) (Fin b) S) {r : ℕ}
    (ρ : Fin r → Fin a) (γ : Fin r → Fin b) :
    ((A.map f).submatrix ρ γ).det = f (A.submatrix ρ γ).det := by
  rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]

end Minors

/-! ### The Buchsbaum–Eisenbud criterion for a base changed complex of matrices -/

/-- An integer `z` is the cast of a natural number satisfying `P` if and only if `0 ≤ z` and
`P z.toNat`. -/
lemma exists_natCast_eq_and_iff {z : ℤ} {P : ℕ → Prop} :
    (∃ r : ℕ, (r : ℤ) = z ∧ P r) ↔ 0 ≤ z ∧ P z.toNat := by
  constructor
  · rintro ⟨r, rfl, h⟩
    simpa using h
  · rintro ⟨hz, h⟩
    exact ⟨z.toNat, Int.toNat_of_nonneg hz, h⟩

/-- If `X * Y = 0`, then the linear maps of `X.map f` and `Y.map f` compose to zero. -/
lemma mulVecLin_map_comp_eq_zero {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    {a b c : ℕ} {X : Matrix (Fin a) (Fin b) S} {Y : Matrix (Fin b) (Fin c) S} (h : X * Y = 0) :
    (X.map f).mulVecLin ∘ₗ (Y.map f).mulVecLin = 0 := by
  rw [← Matrix.mulVecLin_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero f),
    Matrix.mulVecLin_zero]

/-- The Buchsbaum–Eisenbud criterion for the complex of matrices `M k` base changed along
`f : S → T` to a Noetherian local ring: the top map is injective and the complex is exact at
each spot if and only if, for every `k ≤ e`, the alternating sum
`r_k = n_{k+1} - n_{k+2} + ⋯` is nonnegative, is the largest `j` with a nonzero `j`-th exterior
power of `M k` over `T`, and the image in `T` of the ideal of `r_k × r_k` minors of `M k` has
depth at least `k + 1`. -/
lemma exact_iff_forall {S T : Type*} [CommRing S] [CommRing T] [IsNoetherianRing T]
    [IsLocalRing T] (f : S →+* T) (e : ℕ) (n : ℕ → ℕ)
    (M : ∀ k, Matrix (Fin (n k)) (Fin (n (k + 1))) S) (hM : ∀ k < e, M k * M (k + 1) = 0) :
    (Function.Injective ((M e).map f).mulVecLin ∧
        ∀ k < e, Function.Exact ((M (k + 1)).map f).mulVecLin ((M k).map f).mulVecLin) ↔
      ∀ k ≤ e, 0 ≤ ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) ∧
        IsGreatest {j : ℕ | exteriorPower.map j ((M k).map f).mulVecLin ≠ 0}
          (∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)).toNat ∧
        ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth T ((Ideal.span (Stacks.DeterminantalRank.minorSet (M k)
          (∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)).toNat)).map f) T := by
  rw [LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors e n
    (fun k => ((M k).map f).mulVecLin) (fun k hk => mulVecLin_map_comp_eq_zero f (hM k hk))]
  refine forall₂_congr fun k _ => ?_
  rw [← exists_natCast_eq_and_iff (P := fun r =>
    IsGreatest {j : ℕ | exteriorPower.map j ((M k).map f).mulVecLin ≠ 0} r ∧
      ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth T ((Ideal.span (Stacks.DeterminantalRank.minorSet (M k)
        r)).map f) T)]
  refine exists_congr fun r => and_congr_right' (and_congr_right' ?_)
  rw [← span_minorSet_map, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  have hset : {x : T | ∃ (ρ : Fin r → Fin (n k)) (γ : Fin r → Fin (n (k + 1))),
      (((M k).map f).submatrix ρ γ).det = x} = Stacks.DeterminantalRank.minorSet ((M k).map f) r :=
    Set.ext fun _ => ⟨fun ⟨ρ, γ, h⟩ => ⟨ρ, γ, h.symm⟩, fun ⟨ρ, γ, h⟩ => ⟨ρ, γ, h.symm⟩⟩
  rw [hset]

/-! ### Base change of a map of finite free modules -/

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]

/-- The standard basis of `T ⊗_S S^a`. -/
noncomputable abbrev tensorBasis (T : Type*) [CommRing T] [Algebra S T] (a : ℕ) :=
  Algebra.TensorProduct.basis T (Pi.basisFun S (Fin a))

/-- Under the standard bases of `T ⊗_S S^a` and `T ⊗_S S^b`, the base change of
`φ : S^a → S^b` is multiplication by the image in `T` of the matrix of `φ`. -/
lemma mulVecLin_comp_equivFun {a b : ℕ} (φ : (Fin a → S) →ₗ[S] (Fin b → S)) :
    ((LinearMap.toMatrix' φ).map (algebraMap S T)).mulVecLin ∘ₗ
        (tensorBasis (S := S) T a).equivFun.toLinearMap =
      (tensorBasis (S := S) T b).equivFun.toLinearMap ∘ₗ φ.baseChange T := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Matrix.mulVecLin_apply, Module.Basis.equivFun_apply]
  have := LinearMap.toMatrix_mulVec_repr (tensorBasis (S := S) T a) (tensorBasis (S := S) T b)
    (φ.baseChange T) x
  have hmat : LinearMap.toMatrix (Pi.basisFun S (Fin a)) (Pi.basisFun S (Fin b)) φ =
      LinearMap.toMatrix' φ := by
    ext i j
    simp [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply]
  rwa [LinearMap.toMatrix_baseChange, hmat] at this

/-- The base change to `T` of the complex `φ` has injective top map and is exact at each spot if
and only if the same holds for the complex of the images in `T` of the matrices of the `φ k`. -/
lemma baseChange_exact_iff (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S)) :
    (Function.Injective ((φ e).baseChange T) ∧
        ∀ k < e, Function.Exact ((φ (k + 1)).baseChange T) ((φ k).baseChange T)) ↔
      (Function.Injective ((LinearMap.toMatrix' (φ e)).map (algebraMap S T)).mulVecLin ∧
        ∀ k < e, Function.Exact
          ((LinearMap.toMatrix' (φ (k + 1))).map (algebraMap S T)).mulVecLin
          ((LinearMap.toMatrix' (φ k)).map (algebraMap S T)).mulVecLin) := by
  refine and_congr ?_ (forall₂_congr fun k _ => ?_)
  · have h := congrArg DFunLike.coe (mulVecLin_comp_equivFun (T := T) (φ e))
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at h
    rw [← EquivLike.injective_comp (tensorBasis (S := S) T (n (e + 1))).equivFun, h,
      EquivLike.comp_injective]
  · exact LinearMap.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _
      (tensorBasis (S := S) T (n (k + 2))).equivFun.toLinearMap
      (tensorBasis (S := S) T (n (k + 1))).equivFun.toLinearMap
      (tensorBasis (S := S) T (n k)).equivFun.toLinearMap
      (mulVecLin_comp_equivFun _) (mulVecLin_comp_equivFun _)
      (LinearEquiv.surjective _) (LinearEquiv.bijective _) (LinearEquiv.injective _)

end BaseChange

/-! ### The fibre rings `S_𝔮/𝔭S_𝔮` -/

section Fibre

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- The fibre ring `S_𝔮/𝔭S_𝔮` at a prime `𝔮` of `S`, where `𝔭 = 𝔮 ∩ R`. -/
abbrev Fib (q : PrimeSpectrum S) : Type _ :=
  Localization.AtPrime q.asIdeal ⧸
    (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal))

/-- The extension `𝔭S_𝔮` of `𝔭 = 𝔮 ∩ R` lies in the maximal ideal of `S_𝔮`. -/
lemma map_le_maximalIdeal (q : PrimeSpectrum S) :
    (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)) ≤
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q.asIdeal _).mpr hx

/-- The fibre ring `S_𝔮/𝔭S_𝔮` is nontrivial. -/
lemma nontrivial_fib (q : PrimeSpectrum S) : Nontrivial (Fib R q) :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
    (map_le_maximalIdeal q))

/-- The fibre ring `S_𝔮/𝔭S_𝔮` is a local ring. -/
lemma isLocalRing_fib (q : PrimeSpectrum S) : IsLocalRing (Fib R q) :=
  have := nontrivial_fib (R := R) q
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- If `R` is Noetherian and `S` is of finite type over `R`, the fibre ring `S_𝔮/𝔭S_𝔮` is
Noetherian. -/
lemma isNoetherianRing_fib [IsNoetherianRing R] [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    IsNoetherianRing (Fib R q) := by
  have := Algebra.FiniteType.isNoetherianRing R S
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  infer_instance

/-- The image of `x : S` in `S_𝔮/𝔭S_𝔮` is the class of its image in `S_𝔮`. -/
lemma algebraMap_fib_apply (q : PrimeSpectrum S) (x : S) :
    algebraMap S (Fib R q) x =
      Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q.asIdeal) x) := rfl

/-- The map `S → S_𝔮/𝔭S_𝔮` is the composite `S → S_𝔮 → S_𝔮/𝔭S_𝔮`. -/
lemma algebraMap_fib_eq (q : PrimeSpectrum S) :
    algebraMap S (Fib R q) =
      (Ideal.Quotient.mk _).comp (algebraMap S (Localization.AtPrime q.asIdeal)) := rfl

/-- The image of `x : S` in `S_𝔮/𝔭S_𝔮` is a unit if and only if `x ∉ 𝔮`. -/
lemma isUnit_algebraMap_fib_iff (q : PrimeSpectrum S) (x : S) :
    IsUnit (algebraMap S (Fib R q) x) ↔ x ∉ q.asIdeal := by
  refine ⟨fun hu hx => ?_, fun hx => ?_⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : Fib R q)
    have h1 : algebraMap S (Localization.AtPrime q.asIdeal) x * b - 1 ∈
        (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hb,
        ← algebraMap_fib_apply]
      simp
    have hxm : algebraMap S (Localization.AtPrime q.asIdeal) x ∈
        maximalIdeal (Localization.AtPrime q.asIdeal) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q.asIdeal x).mpr hx
    have h2 : (1 : Localization.AtPrime q.asIdeal) ∈ maximalIdeal _ := by
      simpa using sub_mem (Ideal.mul_mem_right b _ hxm) (map_le_maximalIdeal q h1)
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  · rw [algebraMap_fib_apply]
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal x).mpr hx).map _

/-- Every element of the extension of an ideal `I` of `S` to `S_𝔮/𝔭S_𝔮` is a unit multiple of
the image of an element of `I`. -/
lemma exists_eq_unit_mul_of_mem_map (q : PrimeSpectrum S) (I : Ideal S) {r : Fib R q}
    (hr : r ∈ I.map (algebraMap S (Fib R q))) :
    ∃ y ∈ I, ∃ u : (Fib R q)ˣ, algebraMap S (Fib R q) y = u * r := by
  rw [algebraMap_fib_eq, ← Ideal.map_map,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  obtain ⟨⟨y, s⟩, hys⟩ :=
    (IsLocalization.mem_map_algebraMap_iff q.asIdeal.primeCompl _).mp hz
  refine ⟨y, y.2, ((isUnit_algebraMap_fib_iff (R := R) q s).mpr s.2).unit, ?_⟩
  rw [IsUnit.unit_spec, algebraMap_fib_apply, algebraMap_fib_apply, ← hys, map_mul, mul_comm]

/-- A finite sequence of elements of the extension of an ideal `I` of `S` to `S_𝔮/𝔭S_𝔮` agrees,
term by term up to units, with the image of a sequence of elements of `I`. -/
lemma exists_forall₂_of_mem_map (q : PrimeSpectrum S) (I : Ideal S) (rs : List (Fib R q))
    (hmem : ∀ r ∈ rs, r ∈ I.map (algebraMap S (Fib R q))) :
    ∃ ys : List S, (∀ y ∈ ys, y ∈ I) ∧
      List.Forall₂ (fun (a b : Fib R q) => ∃ u : (Fib R q)ˣ, b = (u : Fib R q) * a) rs
        (ys.map (algebraMap S (Fib R q))) := by
  induction rs with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons r rs ih =>
    obtain ⟨ys, hys, h₂⟩ := ih fun r' hr' => hmem r' (List.mem_cons_of_mem _ hr')
    obtain ⟨y, hy, u, hu⟩ := exists_eq_unit_mul_of_mem_map q I (hmem r List.mem_cons_self)
    exact ⟨y :: ys, List.forall_mem_cons.mpr ⟨hy, hys⟩, .cons ⟨u, hu⟩ h₂⟩

/-- If `x : S` vanishes in `S_𝔮`, then it vanishes in the fibre rings at all points near `𝔮`. -/
lemma eventually_algebraMap_fib_eq_zero (q : PrimeSpectrum S) {x : S}
    (hx : algebraMap S (Localization.AtPrime q.asIdeal) x = 0) :
    ∀ᶠ q' in 𝓝 q, algebraMap S (Fib R q') x = 0 := by
  obtain ⟨⟨t, ht⟩, hts⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl _ x).mp hx
  filter_upwards [(PrimeSpectrum.basicOpen t).isOpen.mem_nhds ht] with q' hq'
  exact ((isUnit_algebraMap_fib_iff (R := R) q' t).mpr hq').mul_right_eq_zero.mp
    (by rw [← map_mul, hts, map_zero])

/-- Let `S` be of finite type over `R` with nonzero fibres `S ⊗_R κ(𝔭)` Cohen–Macaulay and
equidimensional of dimension `d`. If an ideal `I` of `S` has depth at least `m + 1` in the fibre
ring at `𝔮`, then it does so in the fibre rings at all points near `𝔮`. -/
lemma eventually_le_depth_map [Algebra.FiniteType R S] (d : ℕ)
    (hfib : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
          Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
        TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
        ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (q : PrimeSpectrum S) (I : Ideal S) (m : ℕ)
    (h : ((m + 1 : ℕ) : ℕ∞) ≤ Module.depth (Fib R q) (I.map (algebraMap S (Fib R q))) (Fib R q)) :
    ∀ᶠ q' in 𝓝 q,
      ((m + 1 : ℕ) : ℕ∞) ≤
        Module.depth (Fib R q') (I.map (algebraMap S (Fib R q'))) (Fib R q') := by
  have hunit : ∀ (q' : PrimeSpectrum S) (y : S), y ∈ I → y ∉ q'.asIdeal →
      ((m + 1 : ℕ) : ℕ∞) ≤
        Module.depth (Fib R q') (I.map (algebraMap S (Fib R q'))) (Fib R q') := by
    intro q' y hy hyq
    rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hy)
      ((isUnit_algebraMap_fib_iff q' y).mpr hyq), depth_top_self]
    exact le_top
  by_cases hIq : I ≤ q.asIdeal
  · have := isLocalRing_fib (R := R) q
    have hne : I.map (algebraMap S (Fib R q)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top ?_
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_fib_iff]
      exact not_not.mpr (hIq hx)
    obtain ⟨rs, hmem, hreg, hlen⟩ := exists_isRegular_of_le_depth hne h
    obtain ⟨ys, hys, h₂⟩ := exists_forall₂_of_mem_map q I rs hmem
    have hreg' := isRegular_of_forall₂ h₂ hreg
    have hlen' : rs.length = ys.length := by simpa using h₂.length_eq
    have hopen :=
      Algebra.isOpen_setOf_isRegular_fiber_of_isMaximalCohenMacaulay_of_equidimensional d hfib ys
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hopen
    have hmem : ∀ q' : PrimeSpectrum S, (∀ y ∈ ys, y ∈ q'.asIdeal) →
        (q' ∈ O ↔ IsRegular (Fib R q') (ys.map (algebraMap S (Fib R q')))) := fun q' hq' =>
      Set.ext_iff.mp hOW ⟨q', by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
        exact Ideal.span_le.mpr fun y hy => hq' y hy⟩
    filter_upwards [hO.mem_nhds ((hmem q fun y hy => hIq (hys y hy)).mpr hreg')] with q' hq'
    by_cases hall : ∀ y ∈ ys, y ∈ q'.asIdeal
    · have hreg'' := (hmem q' hall).mp hq'
      refine le_trans ?_ (Module.le_depth_of_isRegular _ (fun r hr => ?_) hreg'')
      · simp only [List.length_map]
        exact_mod_cast (by omega : m + 1 ≤ ys.length)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
        exact Ideal.mem_map_of_mem _ (hys y hy)
    · push Not at hall
      obtain ⟨y, hy, hyq⟩ := hall
      exact hunit q' y (hys y hy) hyq
  · obtain ⟨x, hxI, hxq⟩ := SetLike.not_le_iff_exists.mp hIq
    filter_upwards [(PrimeSpectrum.basicOpen x).isOpen.mem_nhds hxq] with q' hq'
    exact hunit q' x hxI hq'

end Fibre

/-! ### Lifting exactness from the fibre ring to `S_𝔮` -/

section Lift

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `X x ∈ J • ⊤`, then the reduction modulo `J` of `X` kills the reduction of `x`. -/
private lemma mulVecLin_map_mk_eq_zero {B : Type*} [CommRing B] (J : Ideal B) {a b : ℕ}
    (X : Matrix (Fin a) (Fin b) B) (x : Fin b → B)
    (hx : X.mulVecLin x ∈ J • (⊤ : Submodule B (Fin a → B))) :
    (X.map (Ideal.Quotient.mk J)).mulVecLin (Ideal.Quotient.mk J ∘ x) = 0 := by
  rw [mem_smul_top_pi_iff] at hx
  ext i
  rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, Pi.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hx i

/-- If the reductions modulo `J` of `Y` and `X` form an exact pair and `X x ∈ J • ⊤`, then `x`
lies in `J • ⊤ ⊔ range Y`. -/
lemma mem_sup_of_exact_map_mk {B : Type*} [CommRing B] (J : Ideal B) {a b c : ℕ}
    (X : Matrix (Fin a) (Fin b) B) (Y : Matrix (Fin b) (Fin c) B)
    (h : Function.Exact (Y.map (Ideal.Quotient.mk J)).mulVecLin
      (X.map (Ideal.Quotient.mk J)).mulVecLin)
    (x : Fin b → B) (hx : X.mulVecLin x ∈ J • (⊤ : Submodule B (Fin a → B))) :
    x ∈ J • (⊤ : Submodule B (Fin b → B)) ⊔ LinearMap.range Y.mulVecLin := by
  have h0 := mulVecLin_map_mk_eq_zero J X x hx
  rw [mem_smul_top_pi_iff] at hx
  obtain ⟨y', hy'⟩ := (h (Ideal.Quotient.mk J ∘ x)).mp h0
  choose y hy using fun i => Ideal.Quotient.mk_surjective (I := J) (y' i)
  refine Submodule.mem_sup.mpr ⟨x - Y.mulVecLin y, ?_, Y.mulVecLin y,
    LinearMap.mem_range_self _ _, sub_add_cancel _ _⟩
  rw [mem_smul_top_pi_iff]
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_mem, Pi.sub_apply, map_sub, sub_eq_zero,
    Matrix.mulVecLin_apply, RingHom.map_mulVec]
  have hy'' : (Ideal.Quotient.mk J ∘ y) = y' := funext hy
  rw [hy'', ← Matrix.mulVecLin_apply, hy']
  rfl

/-- If the reduction modulo `J` of `X` is injective and `X x ∈ J • ⊤`, then `x ∈ J • ⊤`. -/
lemma mem_smul_top_of_injective_map_mk {B : Type*} [CommRing B] (J : Ideal B) {a b : ℕ}
    (X : Matrix (Fin a) (Fin b) B) (h : Function.Injective (X.map (Ideal.Quotient.mk J)).mulVecLin)
    (x : Fin b → B) (hx : X.mulVecLin x ∈ J • (⊤ : Submodule B (Fin a → B))) :
    x ∈ J • (⊤ : Submodule B (Fin b → B)) := by
  have := h ((mulVecLin_map_mk_eq_zero J X x hx).trans (map_zero _).symm)
  rw [mem_smul_top_pi_iff]
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact congrFun this i

/-- The local criterion at one spot of a complex of finite free `S_𝔮`-modules, for the local
homomorphism `R_𝔭 → S_𝔮` with `𝔭 = 𝔮 ∩ R`. -/
lemma ker_eq_range_localization [Module.Flat R S] [IsNoetherianRing R] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) {a b : ℕ} {P : Type*} [AddCommGroup P]
    [Module (Localization.AtPrime q.asIdeal) P]
    (g : P →ₗ[Localization.AtPrime q.asIdeal] (Fin b → Localization.AtPrime q.asIdeal))
    (X : Matrix (Fin a) (Fin b) (Localization.AtPrime q.asIdeal)) (hg : X.mulVecLin ∘ₗ g = 0)
    (hex : ∀ x, X.mulVecLin x ∈ (q.asIdeal.under R).map
        (algebraMap R (Localization.AtPrime q.asIdeal)) •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (Fin a → Localization.AtPrime q.asIdeal)) →
      x ∈ (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)) •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal) (Fin b → Localization.AtPrime q.asIdeal)) ⊔
          LinearMap.range g) :
    LinearMap.ker X.mulVecLin = LinearMap.range g := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal)) := Localization.isLocalHom_localRingHom _ _ _ _
  have := Algebra.FiniteType.isNoetherianRing R S
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have : Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (Fin a → Localization.AtPrime q.asIdeal) :=
    Module.Flat.trans _ (Localization.AtPrime q.asIdeal) _
  have hJ : Ideal.map (algebraMap (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal)) (maximalIdeal (Localization.AtPrime (q.asIdeal.under R)))
        = (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  exact (Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top
    (R := Localization.AtPrime (q.asIdeal.under R)) g X.mulVecLin hg
    (by rwa [hJ])).1

/-- Let `R → S` be flat of finite type with `R` Noetherian, and `X * Y = 0`. If the images of
`Y` and `X` in `S_𝔮/𝔭S_𝔮` form an exact pair, then so do their images in `S_𝔮`. -/
lemma exact_localization_of_exact_fib [Module.Flat R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) {a b c : ℕ}
    (X : Matrix (Fin a) (Fin b) S) (Y : Matrix (Fin b) (Fin c) S) (hXY : X * Y = 0)
    (h : Function.Exact (Y.map (algebraMap S (Fib R q))).mulVecLin
      (X.map (algebraMap S (Fib R q))).mulVecLin) :
    Function.Exact (Y.map (algebraMap S (Localization.AtPrime q.asIdeal))).mulVecLin
      (X.map (algebraMap S (Localization.AtPrime q.asIdeal))).mulVecLin := by
  rw [LinearMap.exact_iff]
  refine ker_eq_range_localization (R := R) q _ _ (mulVecLin_map_comp_eq_zero _ hXY) fun x hx => ?_
  exact mem_sup_of_exact_map_mk _ _ _ (by rwa [Matrix.map_map, Matrix.map_map]) x hx

/-- Let `R → S` be flat of finite type with `R` Noetherian. If the image of `X` in
`S_𝔮/𝔭S_𝔮` is injective, then so is its image in `S_𝔮`. -/
lemma injective_localization_of_injective_fib [Module.Flat R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) {a b : ℕ} (X : Matrix (Fin a) (Fin b) S)
    (h : Function.Injective (X.map (algebraMap S (Fib R q))).mulVecLin) :
    Function.Injective (X.map (algebraMap S (Localization.AtPrime q.asIdeal))).mulVecLin := by
  rw [← LinearMap.ker_eq_bot]
  have := ker_eq_range_localization (R := R) (P := Fin 0 → Localization.AtPrime q.asIdeal) q 0
    (X.map (algebraMap S (Localization.AtPrime q.asIdeal))) (LinearMap.comp_zero _)
    fun x hx => Submodule.mem_sup_left (mem_smul_top_of_injective_map_mk _ _
      (by rwa [Matrix.map_map]) x hx)
  rw [this, LinearMap.range_zero]

end Lift

end Stacks.Depth.RegularSequence

open Stacks.Depth.RegularSequence

/-- Let `R → S` be a flat ring map of finite type with `R` Noetherian, whose nonzero fibres
`S ⊗_R κ(𝔭)` are Cohen–Macaulay and equidimensional of dimension `d`, and let
`0 → S^{n_{e+1}} →[φ e] S^{n_e} → ⋯ → S^{n_1} →[φ 0] S^{n_0}` be a complex of finite free
`S`-modules. Then the set of primes `𝔮` of `S` at which the complex
`F_𝔮 ⊗_R κ(𝔭) = F ⊗_S S_𝔮/𝔭S_𝔮`, `𝔭 = 𝔮 ∩ R`, is exact is open in `Spec S`. -/
@[stacks 00RB "The complex is indexed as in 00N1: `φ k : S^{n (k+1)} → S^{n k}`, read for
`k ≤ e`, and exactness is injectivity of `φ e` and exactness at `S^{n_e}, …, S^{n_1}`.
`F_𝔮 ⊗_R κ(𝔭)` is the base change of `F` along `S → S_𝔮/𝔭S_𝔮`, the ring of 00RA, which is
`S_𝔮 ⊗_R κ(𝔭)`. The fibre hypothesis is spelled out as in 00RA. See the module docstring."]
public theorem Algebra.isOpen_setOf_injective_and_exact_baseChange_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Flat R S] (d : ℕ)
    (hfib : ∀ (p : Ideal R) [p.IsPrime], Nontrivial (p.Fiber S) →
      (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
          Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
        TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
        ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (n : ℕ → ℕ) (φ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen {q : PrimeSpectrum S |
      Function.Injective ((φ e).baseChange (Localization.AtPrime q.asIdeal ⧸
          (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))) ∧
      ∀ k < e, Function.Exact
        ((φ (k + 1)).baseChange (Localization.AtPrime q.asIdeal ⧸
          (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal))))
        ((φ k).baseChange (Localization.AtPrime q.asIdeal ⧸
          (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal))))} := by
  classical
  have := Algebra.FiniteType.isNoetherianRing R S
  set M : ∀ k, Matrix (Fin (n k)) (Fin (n (k + 1))) S := fun k => LinearMap.toMatrix' (φ k)
    with hMdef
  have hM : ∀ k < e, M k * M (k + 1) = 0 := fun k hk => by
    simp only [hMdef, ← LinearMap.toMatrix'_comp, hφ k hk, map_zero]
  set s : ℕ → ℤ := fun k => ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)
  have hset : ∀ q : PrimeSpectrum S,
      (Function.Injective ((φ e).baseChange (Fib R q)) ∧
        ∀ k < e, Function.Exact ((φ (k + 1)).baseChange (Fib R q)) ((φ k).baseChange (Fib R q)))
      ↔ ∀ k ≤ e, 0 ≤ s k ∧
        IsGreatest {j : ℕ | exteriorPower.map j ((M k).map (algebraMap S (Fib R q))).mulVecLin ≠ 0}
          (s k).toNat ∧
        ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth (Fib R q)
          ((Ideal.span (Stacks.DeterminantalRank.minorSet (M k) (s k).toNat)).map
            (algebraMap S (Fib R q))) (Fib R q) := fun q => by
    have := isLocalRing_fib (R := R) q
    have := isNoetherianRing_fib (R := R) q
    rw [baseChange_exact_iff, exact_iff_forall _ e n M hM]
  show IsOpen {q : PrimeSpectrum S | Function.Injective ((φ e).baseChange (Fib R q)) ∧
    ∀ k < e, Function.Exact ((φ (k + 1)).baseChange (Fib R q)) ((φ k).baseChange (Fib R q))}
  simp_rw [hset]
  refine isOpen_iff_mem_nhds.mpr fun q hq => ?_
  have hqF := (baseChange_exact_iff (T := Fib R q) e n φ).mp ((hset q).mpr hq)
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have hqS := (exact_iff_forall (algebraMap S (Localization.AtPrime q.asIdeal)) e n M hM).mp
    ⟨injective_localization_of_injective_fib q (M e) hqF.1,
      fun k hk => exact_localization_of_exact_fib q (M k) (M (k + 1)) (hM k hk) (hqF.2 k hk)⟩
  have hE1 : ∀ᶠ q' in 𝓝 q, ∀ k : Fin (e + 1), ∀ j : Fin (n k + 1),
      ∀ ρ : Fin j → Fin (n k), ∀ γ : Fin j → Fin (n (k + 1)),
        (s k).toNat < j → algebraMap S (Fib R q') ((M k).submatrix ρ γ).det = 0 := by
    simp only [Filter.eventually_all]
    intro k j ρ γ hj
    have hzero : algebraMap S (Localization.AtPrime q.asIdeal) ((M k).submatrix ρ γ).det = 0 := by
      have hle := (hqS k (Nat.lt_succ_iff.mp k.2)).2.1.2
      have hmap : exteriorPower.map j
          ((M k).map (algebraMap S (Localization.AtPrime q.asIdeal))).mulVecLin = 0 := by
        by_contra hne
        exact absurd (hle hne) (not_le.mpr hj)
      rw [← det_submatrix_map]
      by_contra hne
      exact (Stacks.DeterminantalRank.exteriorPower_map_ne_zero_iff_exists_minor _ _).mpr
        ⟨_, ⟨ρ, γ, rfl⟩, hne⟩ hmap
    exact eventually_algebraMap_fib_eq_zero (R := R) q hzero
  have hE2 : ∀ᶠ q' in 𝓝 q, ∀ k : Fin (e + 1),
      ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth (Fib R q')
        ((Ideal.span (Stacks.DeterminantalRank.minorSet (M k) (s k).toNat)).map
          (algebraMap S (Fib R q'))) (Fib R q') :=
    Filter.eventually_all.mpr fun k =>
      eventually_le_depth_map d hfib q _ k (hq k (Nat.lt_succ_iff.mp k.2)).2.2
  filter_upwards [hE1, hE2] with q' h1 h2
  have := nontrivial_fib (R := R) q'
  intro k hk
  refine ⟨(hq k hk).1, ⟨?_, fun j hj => ?_⟩, h2 ⟨k, Nat.lt_succ_iff.mpr hk⟩⟩
  · show exteriorPower.map _ _ ≠ 0
    rw [Stacks.DeterminantalRank.exteriorPower_map_ne_zero_iff_exists_minor]
    by_contra hall
    push Not at hall
    refine ne_bot_of_one_le_depth (le_trans ?_ (h2 ⟨k, Nat.lt_succ_iff.mpr hk⟩)) ?_
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    · rw [← span_minorSet_map, Ideal.span_eq_bot]
      exact hall
  · obtain ⟨x, ⟨ρ, γ, rfl⟩, hne⟩ :=
      (Stacks.DeterminantalRank.exteriorPower_map_ne_zero_iff_exists_minor _ _).mp hj
    have hjn : j ≤ n k := StacksComplex.rankSet_le_n _ ⟨ρ, γ, hne⟩
    by_contra hlt
    rw [not_le] at hlt
    rw [det_submatrix_map] at hne
    exact hne (h1 ⟨k, Nat.lt_succ_iff.mpr hk⟩ ⟨j, Nat.lt_succ_iff.mpr hjn⟩ ρ γ hlt)
