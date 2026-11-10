module

public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Algebra.Homology.SpectralSequence.LengthDegeneration
public import StacksFrontier.Homology.Perfect.MinimalRepresentative

/-!
# Lengths of the cohomology of finite free complexes, and when the differentials vanish

Let `A` be a ring of finite length (an Artinian ring) and let `P` be a complex of finite free
`A`-modules, `P^i ≅ A^{n_i}`. Then `ℓ(H^i(P)) ≤ n_i · ℓ(A)`, and equality in every degree holds
exactly when every differential of `P` vanishes, in which case `H^i(P) ≅ P^i` is free of rank
`n_i`. For the rank-minimal representative of a pseudo-coherent object over an Artinian local
ring ([Stacks, Tag 0BCC]), `n_i = dim_κ H^i(K ⊗ᴸ κ)`, so this is the numerical criterion for the
cohomology of `K` to be free and to commute with base change.

Over a reduced ring the same conclusion follows from the fibres: if at every prime `𝔭` the complex
`P ⊗ κ(𝔭)` has cohomology of dimension `n_i` in every degree `i`, all differentials of `P`
vanish, since their matrix entries lie in every prime.

Over a Noetherian local ring `A` with maximal ideal `𝔪` a linear map into a finite module whose
image lies in `𝔪^k N` for every `k` is zero (Krull's intersection theorem); in particular a map of
finite modules whose reductions modulo every `𝔪^k` vanish is zero. This passes the vanishing of
the differentials of a minimal complex from the Artinian quotients `A/𝔪^k` to `A`.

These are the two algebraic reductions in Deligne's proof that the de Rham cohomology sheaves of
a proper smooth morphism over `ℚ` are finite locally free, the assertion of [Stacks, Tag 0FMN]
that the source defers to a future reference.

## Main results

* `HomologicalComplex.moduleCat_d_eq_zero_of_forall_length_homology_eq`: a complex of finite
  length modules whose homology is everywhere as long as its terms has zero differentials.
* `CochainComplex.moduleCat_length_homology_le_of_free`: `ℓ(H^i(P)) ≤ n_i · ℓ(A)`.
* `CochainComplex.moduleCat_d_eq_zero_of_length_homology_eq_of_free`: equality in every degree
  forces all differentials to vanish.
* `CochainComplex.moduleCatHomologyIsoXOfDEqZero`: then `H^i(P) ≅ P^i`.
* `ModuleCat.Hom.eq_zero_of_forall_extendScalars_residueField_map_eq_zero`: over a reduced ring,
  a map into a free module which vanishes at every residue field is zero.
* `CochainComplex.moduleCat_d_eq_zero_of_forall_finrank_homology_residueField`: over a reduced
  ring, a complex with `P^i ≅ R^{n_i}` whose fibre at every point has cohomology of dimension
  `n_i` in degree `i` has zero differentials, so its cohomology modules are free of rank `n_i`.
  This is the algebra behind "a perfect complex with locally constant fibre Betti numbers on a
  reduced scheme has finite locally free cohomology" (which fails on a non-reduced base).
* `LinearMap.eq_zero_of_forall_range_le_pow_smul_top`: Krull's intersection theorem for the
  image of a linear map.
* `LinearMap.eq_zero_of_forall_extendScalars_map_eq_zero`: a map of modules over a Noetherian
  local ring, with finite target, whose reductions modulo every power of `𝔪` vanish, is zero.

## References

* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- **A complex of finite length modules whose homology is everywhere as long as its terms has
zero differentials.** -/
lemma moduleCat_d_eq_zero_of_forall_length_homology_eq
    (h : ∀ i, Module.length R (K.homology i) = Module.length R (K.X i))
    (htop : ∀ i, Module.length R (K.X i) ≠ ⊤) (i j : ι) : K.d i j = 0 :=
  (K.moduleCat_d_eq_zero_of_length_homology_eq i (h i) (htop i) j).1

end HomologicalComplex

/-- The length of `A^n` is `n · ℓ(A)`. -/
lemma Module.length_ulift_fin_pi (R : Type u) [CommRing R] (n : ℕ) :
    Module.length R (ULift.{w} (Fin n → R)) = n * Module.length R R := by
  rw [(ULift.moduleEquiv (R := R) (M := Fin n → R)).length_eq, Module.length_pi_of_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

namespace CochainComplex

variable {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{max w u} A) ℤ)
  (n : ℤ → ℕ) (hP : ∀ i, Nonempty (P.X i ≅ ModuleCat.of A (ULift.{w} (Fin (n i) → A))))
include hP

/-- For a complex with `P^i ≅ A^{n_i}`, the length of `P^i` is `n_i · ℓ(A)`. -/
lemma moduleCat_length_X_of_free (i : ℤ) :
    Module.length A (P.X i) = n i * Module.length A A := by
  rw [CategoryTheory.Iso.moduleCat_length_eq (hP i).some]
  exact Module.length_ulift_fin_pi A (n i)

/-- **`ℓ(H^i(P)) ≤ n_i · ℓ(A)`** for a complex with `P^i ≅ A^{n_i}`. -/
lemma moduleCat_length_homology_le_of_free (i : ℤ) :
    Module.length A (P.homology i) ≤ n i * Module.length A A := by
  rw [← P.moduleCat_length_X_of_free n hP i]
  exact P.moduleCat_length_homology_le i

/-- **The numerical criterion for a finite free complex over a ring of finite length.** If
`P^i ≅ A^{n_i}`, `ℓ(A)` is finite and `ℓ(H^i(P)) = n_i · ℓ(A)` for every `i`, then every
differential of `P` vanishes. -/
lemma moduleCat_d_eq_zero_of_length_homology_eq_of_free (hA : Module.length A A ≠ ⊤)
    (h : ∀ i, Module.length A (P.homology i) = n i * Module.length A A) (i j : ℤ) :
    P.d i j = 0 := by
  refine P.moduleCat_d_eq_zero_of_forall_length_homology_eq (fun i => ?_) (fun i => ?_) i j
  · rw [h i, P.moduleCat_length_X_of_free n hP i]
  · rw [P.moduleCat_length_X_of_free n hP i]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hA
    rw [← hm, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _

omit hP in
/-- When all differentials of a cochain complex vanish, its cohomology in degree `i` is its term
in degree `i`. -/
noncomputable def moduleCatHomologyIsoXOfDEqZero (h : ∀ i j, P.d i j = 0) (i : ℤ) :
    P.homology i ≅ P.X i :=
  (P.isoHomologyπ (i - 1) i (by simp) (h _ _)).symm ≪≫ P.iCyclesIso i (i + 1) (by simp) (h _ _)

end CochainComplex

/-- If the base change of `f` along `φ` vanishes, then `1 ⊗ f x = 0` in `S ⊗_R N`. -/
private theorem tmul_one_apply_eq_zero_of_extendScalars_map_eq_zero {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (h : (ModuleCat.extendScalars φ).map f = 0) (x : M) :
    (TensorProduct.tmul R (show (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) from (1 : S))
      (f.hom x) : TensorProduct R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) N) =
      0 := by
  have hx : ((ModuleCat.extendScalars φ).map f).hom
      ((1 : S) ⊗ₜ[R] x) = 0 := by
    rw [h]
    rfl
  exact hx

namespace LinearMap

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- **Krull's intersection theorem for the image of a linear map.** Over a Noetherian local ring,
a linear map into a finite module whose image lies in `𝔪^k N` for every `k` is zero. -/
lemma eq_zero_of_forall_range_le_pow_smul_top (f : M →ₗ[A] N)
    (h : ∀ k : ℕ, LinearMap.range f ≤ (IsLocalRing.maximalIdeal A) ^ k • ⊤) : f = 0 := by
  have hbot : LinearMap.range f ≤ ⊥ := by
    rw [← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top]
    exact le_iInf h
  exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hbot)

omit [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A N] in
/-- The reduction of a linear map modulo an ideal `I` vanishes exactly when its image lies in
`I N`. -/
lemma range_le_smul_top_of_extendScalars_map_eq_zero {M' N' : ModuleCat.{v} A} (f : M' ⟶ N')
    (I : Ideal A) (h : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f = 0) :
    LinearMap.range f.hom ≤ I • (⊤ : Submodule A N') := by
  rintro _ ⟨x, rfl⟩
  have hx : (TensorProduct.tmul A (1 : A ⧸ I) (f.hom x) : TensorProduct A (A ⧸ I) N') = 0 :=
    tmul_one_apply_eq_zero_of_extendScalars_map_eq_zero _ f h x
  have := congrArg (TensorProduct.quotTensorEquivQuotSMul (N' : Type v) I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
    Submodule.Quotient.mk_eq_zero] at this
  exact this

/-- **A map of modules over a Noetherian local ring, with finite target, whose reductions
modulo every power of the maximal ideal vanish, is zero.** -/
lemma eq_zero_of_forall_extendScalars_map_eq_zero {M' N' : ModuleCat.{v} A} [Module.Finite A N']
    (f : M' ⟶ N')
    (h : ∀ k : ℕ, (ModuleCat.extendScalars
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ k))).map f = 0) : f = 0 := by
  ext1
  exact eq_zero_of_forall_range_le_pow_smul_top f.hom fun k =>
    range_le_smul_top_of_extendScalars_map_eq_zero f _ (h k)

end LinearMap

namespace ModuleCat.Hom

variable {R : Type u} [CommRing R]

/-- **Over a reduced ring, a map into a free module which vanishes at every residue field is
zero**: its matrix entries lie in every prime ideal, hence in the nilradical. -/
lemma eq_zero_of_forall_extendScalars_residueField_map_eq_zero [IsReduced R]
    {M N : ModuleCat.{v} R} [Module.Free R N] (f : M ⟶ N)
    (h : ∀ (p : Ideal R) [p.IsPrime],
      (ModuleCat.extendScalars (algebraMap R p.ResidueField)).map f = 0) : f = 0 := by
  ext x
  let b := Module.Free.chooseBasis R N
  refine b.ext_elem fun j => ?_
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  refine IsReduced.eq_zero _ ((mem_nilradical).1 ?_)
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p (hp : p.IsPrime)
  let K' := (ModuleCat.restrictScalars (algebraMap R p.ResidueField)).obj
    (ModuleCat.of p.ResidueField p.ResidueField)
  have hx : (TensorProduct.tmul R (show K' from (1 : p.ResidueField)) (f.hom x) :
      TensorProduct R K' N) = 0 :=
    tmul_one_apply_eq_zero_of_extendScalars_map_eq_zero _ f (h p) x
  have := congrArg ((TensorProduct.rid R K').toLinearMap ∘ₗ LinearMap.lTensor K' (b.coord j)) hx
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_zero] at this
  replace this : algebraMap R p.ResidueField (b.repr (f.hom x) j) * 1 = 0 := this
  rw [mul_one] at this
  rw [← Ideal.ker_algebraMap_residueField (I := p)]
  exact this

end ModuleCat.Hom

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsReduced R] (P : CochainComplex (ModuleCat.{max w u} R) ℤ)
  (n : ℤ → ℕ) (hP : ∀ i, Nonempty (P.X i ≅ ModuleCat.of R (ULift.{w} (Fin (n i) → R))))
include hP

/-- **Over a reduced ring, a finite free complex whose fibres have cohomology of the ranks of its
terms has zero differentials.** Let `P^i ≅ R^{n_i}` and suppose that for every prime `𝔭` the
complex `P ⊗_R κ(𝔭)` has `dim_{κ(𝔭)} H^i(P ⊗_R κ(𝔭)) = n_i` for all `i`. Then every differential
of `P` vanishes, so `H^i(P) ≅ P^i` is free of rank `n_i` (`moduleCatHomologyIsoXOfDEqZero`). -/
theorem moduleCat_d_eq_zero_of_forall_finrank_homology_residueField
    (h : ∀ (p : Ideal R) [p.IsPrime] (i : ℤ), Module.finrank p.ResidueField
      ((((ModuleCat.extendScalars.{u, u, max w u}
          (algebraMap R p.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) = n i) (i j : ℤ) : P.d i j = 0 := by
  have : ∀ k, Module.Free R (P.X k) := fun k =>
    Module.Free.of_equiv ((hP k).some.toLinearEquiv.symm)
  refine ModuleCat.Hom.eq_zero_of_forall_extendScalars_residueField_map_eq_zero _ fun p _ => ?_
  let Q := ((ModuleCat.extendScalars.{u, u, max w u}
    (algebraMap R p.ResidueField)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hQ : ∀ k, Nonempty (Q.X k ≅ ModuleCat.of p.ResidueField
      (ULift.{w} (Fin (n k) → p.ResidueField))) := fun k =>
    ⟨(ModuleCat.extendScalars.{u, u, max w u} (algebraMap R p.ResidueField)).mapIso (hP k).some ≪≫
      (StacksDraft.Perfect.extendScalars_standard_free_iso.{u, w}
        (algebraMap R p.ResidueField) (n k)).some⟩
  have hlen1 : Module.length p.ResidueField p.ResidueField = 1 := by
    rw [Module.length_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hfin : ∀ k, Module.Finite p.ResidueField (Q.homology k) := fun k => by
    have hle := CochainComplex.moduleCat_length_homology_le_of_free.{w} Q n hQ k
    rw [hlen1, mul_one] at hle
    have : IsFiniteLength p.ResidueField (Q.homology k) :=
      Module.length_ne_top_iff.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle)
    have : IsNoetherian p.ResidueField (Q.homology k) :=
      ((isFiniteLength_iff_isNoetherian_isArtinian).1 this).1
    infer_instance
  exact CochainComplex.moduleCat_d_eq_zero_of_length_homology_eq_of_free.{w} Q n hQ
    (by rw [hlen1]; exact ENat.one_ne_top) (fun k => by
      rw [Module.length_eq_finrank, h p k, hlen1, mul_one]) i j

end CochainComplex
