module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Invariant.Profinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Primes and residue fields of an invariant ring

Let a group `G` act on a commutative ring `B` with invariant subring `A`.  The primes of `B`
over a fixed prime of `A` form a single `G`-orbit, the induced residue field extensions are
algebraic and normal, and the decomposition group at a prime surjects onto the relative
automorphism group of its residue field extension.

For a normal domain `A` with fraction field `K`, a possibly infinite Galois extension `L / K`
and the integral closure `B` of `A` in `L`, the same three statements hold for
`Gal(L/K)` acting on `B`.  In a tower `M / L / K` of Galois extensions with integral closures
`C` and `B`, restriction `Gal(M/K) → Gal(L/K)` carries the decomposition group and the inertia
group at a prime of `C` onto the corresponding groups at its contraction to `B`.

## Main results

* `Algebra.IsInvariant.exists_smul_of_under_eq`: primes lying over the same prime of an invariant
  subring form one orbit.
* `Ideal.IsFractionRing.normal` and `IsFractionRing.stabilizerHom_surjective`: the residue field
  extension at such a prime is normal, hence algebraic, and the decomposition group surjects onto
  its relative automorphism group.
* `IsIntegralClosure.exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective`: the
  same, for the integral closure in a possibly infinite Galois extension.
* `IsIntegralClosure.image_stabilizer_and_inertia_restrictNormalHom`: restriction maps
  decomposition and inertia groups onto decomposition and inertia groups in a tower.

## Implementation notes

The Mathlib results above are stated for an arbitrary invariant subring and arbitrary fraction
fields of the quotient domains, which is more general than taking the full fixed ring and its
residue fields.

Residue fields are likewise represented by arbitrary fraction fields of the quotient domains,
`Normal k l` carries algebraicity of `l / k`, and the decomposition and inertia groups are
`MulAction.stabilizer` and `Ideal.inertia`.  Surjectivity of a restriction map onto a subgroup,
together with the fact that it lands there, is expressed as equality of the image with that
subgroup.

## References

* [Stacks Project, Tag 0BRI](https://stacks.math.columbia.edu/tag/0BRI)
* [Stacks Project, Tag 0BRJ](https://stacks.math.columbia.edu/tag/0BRJ)
* [Stacks Project, Tag 0BRK](https://stacks.math.columbia.edu/tag/0BRK)
* [Stacks Project, Tag 0BSX](https://stacks.math.columbia.edu/tag/0BSX)
-/

@[expose] public section

open scoped Pointwise

add_to_stacks 0BRI Algebra.IsInvariant.exists_smul_of_under_eq

add_to_stacks 0BRJ "normality, hence algebraicity, of the residue field extension"
  Ideal.IsFractionRing.normal

add_to_stacks 0BRJ "surjectivity of the decomposition group onto the relative automorphisms"
  IsFractionRing.stabilizerHom_surjective
add_to_sga "1 V 1.1" "more general" IsFractionRing.stabilizerHom_surjective
add_to_sga "1 V 1.3" "special case" IsFractionRing.stabilizerHom_surjective

section Profinite

open Polynomial

universe uC

/-- For a profinite group `G` acting on `B` with invariant subring `A`, every `b : B` is a root
of a monic polynomial over `A` which splits in `B` and all of whose roots in any domain `C` are
images of the `G`-orbit of `b`. -/
private lemma exists_monic_splits_aeval_eq_zero_of_profinite
    {A B G : Type*} {C : Type uC} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing C] [IsDomain C]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    [Algebra.IsInvariant A B G] (b : B) :
    ∃ p : A[X], p.Monic ∧ (p.map (algebraMap A B)).eval b = 0 ∧
      (p.map (algebraMap A B)).Splits ∧
      ∀ (f : B →+* C) (z : C),
        ((p.map (algebraMap A B)).map f).eval z = 0 → ∃ g : G, z = f (g • b) := by
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let _ : Finite (G ⧸ N.1.1) := finite_of_compact_of_discrete
  let _ : Fintype (G ⧸ N.1.1) := Fintype.ofFinite _
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g ↦ hN g.2⟩
  obtain ⟨p, hp, -, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B' (G ⧸ N.1.1) b')
    (MulSemiringAction.monic_charpoly (G ⧸ N.1.1) b')
  have hcomp : (FixedPoints.subalgebra A B N.1.1).val.toRingHom.comp
      (algebraMap A B') = algebraMap A B := by ext; rfl
  have hpB := congrArg (Polynomial.map (FixedPoints.subalgebra A B N.1.1).val.toRingHom) hp
  rw [Polynomial.map_map, hcomp] at hpB
  refine ⟨p, hmonic, ?_, ?_, ?_⟩
  · have heval := congrArg ((FixedPoints.subalgebra A B N.1.1).val : B' →+* B)
      (MulSemiringAction.eval_charpoly (G ⧸ N.1.1) b')
    rw [hpB]
    calc
      _ = (FixedPoints.subalgebra A B N.1.1).val
          ((MulSemiringAction.charpoly (G ⧸ N.1.1) b').eval b') :=
        Polynomial.eval_map_apply (f :=
          (FixedPoints.subalgebra A B N.1.1).val.toRingHom) b'
      _ = 0 := by simpa using heval
  · rw [hpB]
    exact (MulSemiringAction.splits_charpoly (G ⧸ N.1.1) b').map
      (FixedPoints.subalgebra A B N.1.1).val.toRingHom
  · intro f z hz
    rw [hpB] at hz
    simp only [MulSemiringAction.charpoly, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, sub_eq_zero] at hz
    obtain ⟨g, -, hg⟩ := hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    change z = f (g • b) at hg
    exact ⟨g, hg⟩

/-- For a profinite group `G` acting on `B` with invariant subring `A`, the residue field
extension at a prime `Q` of `B` over `P` is normal. -/
private lemma normal_of_profinite
    {A B G K L : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B)
    [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    [Field K] [Field L] [Algebra K L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
    [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
    [IsScalarTower (A ⧸ P) K L] : Normal K L := by
  have := Algebra.IsInvariant.isIntegral_of_profinite (A := A) (B := B) (G := G)
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  change algebraMap A (A ⧸ P) a ≠ 0 at ha
  change algebraMap A (A ⧸ P) a • x = y * algebraMap B (B ⧸ Q) b at h
  obtain ⟨p, h_monic, h_eval, h_splits, -⟩ :=
    exists_monic_splits_aeval_eq_zero_of_profinite (C := L)
      (A := A) (B := B) (G := G) b
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have h_eval_aeval : Polynomial.aeval b p = 0 := by
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have h_eval' : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C,
      aeval_X, ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d,
      mul_div, ← map_mul]
    rw [← Algebra.smul_def, h, map_mul, mul_div_cancel_left₀ _ (by simpa using hy),
      aeval_map_algebraMap, aeval_algebraMap_apply, aeval_map_algebraMap,
      aeval_algebraMap_apply, h_eval_aeval, map_zero, map_zero]
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval'))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map, Polynomial.map_map, comm₁, RingHom.comp_assoc, comm₂,
      ← RingHom.comp_assoc, ← Polynomial.map_map]
    exact h_splits.map ((algebraMap (B ⧸ Q) L).comp (algebraMap B (B ⧸ Q)))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

/-- Every `A ⧸ P`-automorphism of a domain `k` containing `B ⧸ Q` restricts to an
`A ⧸ P`-automorphism of `B ⧸ Q`, for a profinite group `G` acting on `B` with invariant
subring `A`. -/
private lemma exists_residueAlgEquiv_of_profinite
    {A B G k : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
    [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k]
    [IsScalarTower (A ⧸ P) (B ⧸ Q) k] [IsDomain k] [FaithfulSMul (B ⧸ Q) k]
    (sigma : k ≃ₐ[A ⧸ P] k) :
    ∃ tau : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q, ∀ x : B ⧸ Q,
      algebraMap _ _ (tau x) = sigma (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) →ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have range_le (rho : k →ₐ[A ⧸ P] k) : (rho.comp f).range ≤ f.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    algebraize [(algebraMap (A ⧸ P) k).comp (algebraMap A (A ⧸ P)),
      (algebraMap (B ⧸ Q) k).comp (algebraMap B (B ⧸ Q))]
    have : IsScalarTower A (B ⧸ Q) k := .of_algebraMap_eq fun x ↦
      (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (Ideal.Quotient.mk P x))
    have : IsScalarTower A B k := .of_algebraMap_eq fun x ↦
      (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (Ideal.Quotient.mk P x))
    obtain ⟨p, -, hp, -, hroots⟩ :=
      exists_monic_splits_aeval_eq_zero_of_profinite (C := k)
        (A := A) (B := B) (G := G) x
    have hp' : Polynomial.aeval x p = 0 := by
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hx : Polynomial.aeval (rho (algebraMap (B ⧸ Q) k (Ideal.Quotient.mk Q x))) p = 0 := by
      have hquot : Polynomial.aeval (Ideal.Quotient.mk Q x) p =
          algebraMap B (B ⧸ Q) (Polynomial.aeval x p) := by
        simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        rw [IsScalarTower.algebraMap_eq A B (B ⧸ Q), ← Polynomial.map_map]
        exact Polynomial.eval_map_apply (f := algebraMap B (B ⧸ Q)) x
      exact (DFunLike.congr_fun (Polynomial.aeval_algHom ((rho.restrictScalars A).comp
        (IsScalarTower.toAlgHom A (B ⧸ Q) k)) _) p).trans (by
          simp only [AlgHom.comp_apply, hquot, hp', map_zero])
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hx
    have hx' : ((p.map (algebraMap A B)).map (algebraMap B k)).eval
        (rho (algebraMap (B ⧸ Q) k (Ideal.Quotient.mk Q x))) = 0 := by
      simpa only [Polynomial.map_map, IsScalarTower.algebraMap_eq A B k] using hx
    obtain ⟨g, hg⟩ := hroots (algebraMap B k) _ hx'
    exact ⟨Ideal.Quotient.mk Q (g • x), hg.symm⟩
  let e := AlgEquiv.ofInjective f hf
  let tau₁ : (B ⧸ Q) →ₐ[A ⧸ P] B ⧸ Q :=
    (e.symm.toAlgHom.comp (Subalgebra.inclusion (range_le sigma.toAlgHom))).comp
      (sigma.toAlgHom.comp f).rangeRestrict
  let tau₂ : (B ⧸ Q) →ₐ[A ⧸ P] B ⧸ Q :=
    (e.symm.toAlgHom.comp (Subalgebra.inclusion (range_le sigma.symm.toAlgHom))).comp
      (sigma.symm.toAlgHom.comp f).rangeRestrict
  have h₁ (x : B ⧸ Q) : algebraMap _ _ (tau₁ x) = sigma (algebraMap _ _ x) :=
    congr_arg Subtype.val (e.apply_symm_apply ⟨_, range_le sigma.toAlgHom ⟨x, rfl⟩⟩)
  have h₂ (x : B ⧸ Q) : algebraMap _ _ (tau₂ x) = sigma.symm (algebraMap _ _ x) :=
    congr_arg Subtype.val (e.apply_symm_apply ⟨_, range_le sigma.symm.toAlgHom ⟨x, rfl⟩⟩)
  refine ⟨{ __ := tau₁, invFun := tau₂, left_inv := ?_, right_inv := ?_ }, h₁⟩
  · intro x
    apply hf
    calc
      algebraMap (B ⧸ Q) k (tau₂ (tau₁ x)) =
          sigma.symm (algebraMap (B ⧸ Q) k (tau₁ x)) := h₂ _
      _ = sigma.symm (sigma (algebraMap (B ⧸ Q) k x)) := congrArg sigma.symm (h₁ _)
      _ = _ := sigma.symm_apply_apply _
  · intro x
    apply hf
    calc
      algebraMap (B ⧸ Q) k (tau₁ (tau₂ x)) =
          sigma (algebraMap (B ⧸ Q) k (tau₂ x)) := h₁ _
      _ = sigma (sigma.symm (algebraMap (B ⧸ Q) k x)) := congrArg sigma (h₂ _)
      _ = _ := sigma.apply_symm_apply _

end Profinite

namespace IsIntegralClosure

section Galois

open Polynomial

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

universe uA uK uL uB uC

/-- For the integral closure `B` of a normal domain `A` in a Galois extension `L / K` of its
fraction field, `A` is the invariant subring of the `Gal(L/K)`-action on `B`. -/
private lemma isInvariant
    (A : Type uA) (K : Type uK) (L : Type uL) (B : Type uB)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosed A] [IsIntegralClosure B A L]
    [IsGalois K L] :
    let _ := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  have hb' : algebraMap B L b ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans
      (congrArg (algebraMap B L) (hb g))
  rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hb'
  obtain ⟨k, hk⟩ := hb'
  have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (B := L), ← hk, isIntegral_algebraMap_iff] at hbint
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbint
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

/-- The `Gal(L/K)`-action on the integral closure `B` commutes with the scalar action of `A`. -/
private lemma smulCommClass_galRestrict
    (A : Type uA) (K : Type uK) (L : Type uL) (B : Type uB)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosed A] [IsIntegralClosure B A L]
    [IsGalois K L] :
    let _ := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass Gal(L/K) A B := by
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  exact ⟨fun σ a b ↦ by
    simp only [Algebra.smul_def, smul_mul']
    congr 1
    exact (galRestrict A K L B σ).commutes a⟩

/-- The `Gal(L/K)`-action on the integral closure `B` is continuous for the discrete topology
on `B`. -/
private lemma continuousSMul
    (A : Type uA) (K : Type uK) (L : Type uL) (B : Type uB)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosed A] [IsIntegralClosure B A L]
    [IsGalois K L] :
    let _ := IsIntegralClosure.MulSemiringAction A K L B
    let _ : TopologicalSpace B := ⊥
    ContinuousSMul Gal(L/K) B := by
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  have h : (MulAction.stabilizer Gal(L/K) b : Set Gal(L/K)) =
      MulAction.stabilizer Gal(L/K) (algebraMap B L b) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [← (FaithfulSMul.algebraMap_injective B L).eq_iff]
    change algebraMap B L ((galRestrict A K L B g) b) = algebraMap B L b ↔
      g (algebraMap B L b) = algebraMap B L b
    rw [algebraMap_galRestrict_apply]
  rw [h]
  exact stabilizer_isOpen_of_isIntegral (algebraMap B L b)

/-- In a possibly infinite Galois extension, the primes of an integral closure above a fixed
prime form one Galois orbit.  The induced residue-field extension is normal, and its
decomposition group surjects onto the relative automorphism group. -/
@[stacks 0BRK, sga "1 V 1.1" "special case", sga "1 V 1.3" "special case"]
theorem exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective
    (A : Type uA) (K : Type uK) (L : Type uL) (B : Type uB)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegrallyClosed A] [IsIntegralClosure B A L]
    [IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun σ a b ↦ by
        simp only [Algebra.smul_def, smul_mul']
        congr 1
        exact (galRestrict A K L B σ).commutes a⟩
    (∀ (Q Q' : Ideal B) [Q.IsPrime] [Q'.IsPrime],
      Q.under A = Q'.under A → ∃ σ : Gal(L/K), Q' = σ • Q) ∧
    ∀ (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P],
      ∀ (k l : Type*) [Field k] [Field l] [Algebra k l]
        [Algebra (A ⧸ P) k] [IsFractionRing (A ⧸ P) k]
        [Algebra (B ⧸ Q) l] [IsFractionRing (B ⧸ Q) l]
        [Algebra (A ⧸ P) l] [IsScalarTower (A ⧸ P) (B ⧸ Q) l]
        [IsScalarTower (A ⧸ P) k l],
        Normal k l ∧
          Function.Surjective (IsFractionRing.stabilizerHom Gal(L/K) P Q k l) := by
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass Gal(L/K) A B :=
    smulCommClass_galRestrict A K L B
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul Gal(L/K) B := continuousSMul A K L B
  have : Algebra.IsInvariant A B Gal(L/K) := isInvariant A K L B
  constructor
  · exact fun Q Q' _ _ h ↦ Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite Q Q' h
  · intro P Q _ _ k l _ _ _ _ _ _ _ _ _ _
    have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
    constructor
    · exact normal_of_profinite (G := Gal(L/K)) P Q
    · intro sigma
      obtain ⟨tau, htau⟩ := exists_residueAlgEquiv_of_profinite
        (G := Gal(L/K)) P Q (sigma.restrictScalars (A ⧸ P))
      obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
        (G := Gal(L/K)) P Q tau
      refine ⟨g, AlgEquiv.ext_iff.mpr ?_⟩
      have heq : (IsFractionRing.stabilizerHom Gal(L/K) P Q k l g).toRingEquiv.toRingHom =
          sigma.toRingEquiv.toRingHom := by
        apply IsFractionRing.ringHom_ext (A := B ⧸ Q)
        intro x
        simp only [IsFractionRing.stabilizerHom, MonoidHom.coe_comp,
          Function.comp_apply, IsFractionRing.fieldEquivOfAlgEquivHom_apply, hg]
        change IsFractionRing.fieldEquivOfAlgEquiv k l l tau
            (algebraMap (B ⧸ Q) l x) = sigma (algebraMap (B ⧸ Q) l x)
        rw [IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
        exact htau x
      exact fun x ↦ DFunLike.congr_fun heq x

end Galois

section Tower

attribute [local instance] FractionRing.liftAlgebra

universe uA uK uL uM uB uC

/-- In a tower of possibly infinite Galois extensions, restriction maps the decomposition group
and the inertia group at a prime of the larger integral closure onto the corresponding groups at
its contraction to the smaller integral closure. -/
@[stacks 0BSX]
theorem image_stabilizer_and_inertia_restrictNormalHom
    (A : Type uA) (K : Type uK) (L : Type uL) (M : Type uM)
    (B : Type uB) (C : Type uC)
    [CommRing A] [Field K] [Field L] [Field M] [CommRing B] [CommRing C]
    [Algebra A K] [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [IsScalarTower A K L] [IsScalarTower K L M]
    [IsScalarTower A K M] [IsScalarTower A L M]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [Algebra A C] [Algebra C M] [IsScalarTower A C M]
    [Algebra B C] [Algebra B M] [IsScalarTower A B C]
    [IsScalarTower B L M] [IsScalarTower B C M]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsIntegralClosure C A M]
    [IsGalois K L] [IsGalois K M]
    (r : Ideal C) [r.IsPrime] :
    letI := IsIntegralClosure.MulSemiringAction A K M C
    letI : SMulCommClass Gal(M/K) A C :=
      ⟨fun σ a c ↦ by
        simp only [Algebra.smul_def, smul_mul']
        congr 1
        exact (galRestrict A K M C σ).commutes a⟩
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun σ a b ↦ by
        simp only [Algebra.smul_def, smul_mul']
        congr 1
        exact (galRestrict A K L B σ).commutes a⟩
    let q := r.under B
    let res : Gal(M/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
    res '' (MulAction.stabilizer Gal(M/K) r : Set Gal(M/K)) =
        (MulAction.stabilizer Gal(L/K) q : Set Gal(L/K)) ∧
      res '' (r.inertia Gal(M/K) : Set Gal(M/K)) =
        (q.inertia Gal(L/K) : Set Gal(L/K)) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M C
  have : SMulCommClass Gal(M/K) A C :=
    smulCommClass_galRestrict A K M C
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass Gal(L/K) A B :=
    smulCommClass_galRestrict A K L B
  let q := r.under B
  let res : Gal(M/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  have hres : Function.Surjective res :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) M
  have hcompat (g : Gal(M/K)) (x : B) :
      algebraMap B C (res g • x) = g • algebraMap B C x := by
    apply FaithfulSMul.algebraMap_injective C M
    calc
      algebraMap C M (algebraMap B C (res g • x)) =
          algebraMap L M (algebraMap B L (res g • x)) := by
            rw [← IsScalarTower.algebraMap_apply B C M,
              ← IsScalarTower.algebraMap_apply B L M]
      _ = algebraMap L M (res g (algebraMap B L x)) := by
            congr 1
            exact algebraMap_galRestrict_apply A (res g) x
      _ = g (algebraMap L M (algebraMap B L x)) :=
            AlgEquiv.restrictNormal_commutes g L _
      _ = algebraMap C M (g • algebraMap B C x) := by
            change _ = algebraMap C M (galRestrict A K M C g (algebraMap B C x))
            rw [algebraMap_galRestrict_apply A]
            congr 1
            rw [← IsScalarTower.algebraMap_apply B C M,
              ← IsScalarTower.algebraMap_apply B L M]
  have hres_one (κ : Gal(M/L)) : res (κ.restrictScalars K) = 1 := by
    ext x
    apply (algebraMap L M).injective
    calc
      algebraMap L M (res (κ.restrictScalars K) x) = κ.restrictScalars K (algebraMap L M x) :=
        AlgEquiv.restrictNormal_commutes _ L x
      _ = κ (algebraMap L M x) := rfl
      _ = algebraMap L M x := κ.commutes x
      _ = algebraMap L M ((1 : Gal(L/K)) x) := rfl
  have : Algebra.IsIntegral A B := ⟨IsIntegralClosure.isIntegral A L⟩
  have : IsScalarTower A B M := .of_algebraMap_eq fun x ↦ by
    calc
      algebraMap A M x = algebraMap L M (algebraMap A L x) :=
        IsScalarTower.algebraMap_apply A L M x
      _ = algebraMap L M (algebraMap B L (algebraMap A B x)) := by
        rw [IsScalarTower.algebraMap_apply A B L]
      _ = algebraMap B M (algebraMap A B x) := (IsScalarTower.algebraMap_apply B L M _).symm
  have : IsIntegralClosure C B M := IsIntegralClosure.tower_top (R := A)
  have : IsIntegrallyClosedIn B L := IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let _ := IsIntegralClosure.MulSemiringAction B L M C
  have : SMulCommClass Gal(M/L) B C := smulCommClass_galRestrict B L M C
  have : r.LiesOver q := ⟨rfl⟩
  let k := FractionRing (B ⧸ q)
  let l := FractionRing (C ⧸ r)
  have hBRK :=
    exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective B L M C
  have hrelative := (hBRK.2 q r k l).2
  have hunder_smul (g : Gal(M/K)) : (g • r).under B = res g • q := by
    ext x
    simp only [Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rw [← hcompat g⁻¹]
    simp only [map_inv]
    rfl
  have hκinv (κ : Gal(M/L)) (x : C) : (κ.restrictScalars K)⁻¹ • x = κ⁻¹ • x :=
    FaithfulSMul.algebraMap_injective C M rfl
  have hdecomp :
      res '' (MulAction.stabilizer Gal(M/K) r : Set Gal(M/K)) =
        (MulAction.stabilizer Gal(L/K) q : Set Gal(L/K)) := by
    apply Set.Subset.antisymm
    · rintro σ ⟨τ, hτ, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hτ ⊢
      rw [← hunder_smul, hτ]
    · intro σ hσ
      obtain ⟨τ, rfl⟩ := hres σ
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ
      obtain ⟨κ, hκ⟩ := hBRK.1 (τ • r) r (by rw [hunder_smul, hσ])
      let κ' : Gal(M/K) := κ.restrictScalars K
      refine ⟨κ' * τ, ?_, ?_⟩
      · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul]
        rw [show κ' • (τ • r) = κ • (τ • r) by
          ext x; simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, κ', hκinv]]
        exact hκ.symm
      · rw [map_mul, show res κ' = 1 from hres_one κ, one_mul]
  refine ⟨hdecomp, ?_⟩
  apply Set.Subset.antisymm
  · rintro σ ⟨τ, hτ, rfl⟩ x
    change algebraMap B C ((res τ • x) - x) ∈ r
    rw [map_sub, hcompat]
    exact hτ (algebraMap B C x)
  · intro σ hσ
    have hσstab : σ ∈ MulAction.stabilizer Gal(L/K) q :=
      q.inertia_le_stabilizer hσ
    obtain ⟨τ, hτstab, hτres⟩ := Set.ext_iff.mp hdecomp σ |>.mpr hσstab
    let τr : MulAction.stabilizer Gal(M/K) r := ⟨τ, hτstab⟩
    let θ₀ : (C ⧸ r) ≃+* (C ⧸ r) :=
      (Ideal.Quotient.stabilizerHom r (r.under ℤ) Gal(M/K) τr).toRingEquiv
    let θ : (C ⧸ r) ≃ₐ[B ⧸ q] (C ⧸ r) :=
      { θ₀ with
        commutes' := by
          intro z
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
          apply Ideal.Quotient.eq.mpr
          have hb := hσ b
          rw [← hτres] at hb
          change algebraMap B C (res τ • b - b) ∈ r at hb
          rw [map_sub, hcompat] at hb
          exact hb }
    let φ : Gal(l/k) := IsFractionRing.fieldEquivOfAlgEquiv k l l θ
    obtain ⟨κ, hκ⟩ := hrelative φ
    let κ' : Gal(M/K) := κ.1.restrictScalars K
    have hresidue (x : C) : κ.1 • x - τ • x ∈ r := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      apply IsFractionRing.injective (C ⧸ r) l
      have hx := DFunLike.congr_fun hκ (algebraMap (C ⧸ r) l (Ideal.Quotient.mk r x))
      rw [IsFractionRing.stabilizerHom_apply_apply_mk] at hx
      change _ = (IsFractionRing.fieldEquivOfAlgEquiv k l l θ)
        (algebraMap (C ⧸ r) l (Ideal.Quotient.mk r x)) at hx
      rw [IsFractionRing.fieldEquivOfAlgEquiv_algebraMap] at hx
      change _ = algebraMap (C ⧸ r) l
        (Ideal.Quotient.mk r (τ • x)) at hx
      exact hx
    refine ⟨κ'⁻¹ * τ, ?_, ?_⟩
    · intro x
      rw [mul_smul]
      have hx : κ.1⁻¹ • (κ.1 • x - τ • x) ∈ κ.1⁻¹ • r :=
        (Ideal.smul_mem_pointwise_smul_iff).2 (hresidue x)
      have hκstab : κ.1 • r = r := κ.2
      have hκinvstab : κ.1⁻¹ • r = r := inv_smul_eq_iff.2 hκstab.symm
      rw [hκinvstab, smul_sub, inv_smul_smul] at hx
      rw [hκinv]
      exact r.neg_mem_iff.mp (by simpa using hx)
    · rw [map_mul, map_inv, show res κ' = 1 from hres_one κ.1, inv_one, one_mul, hτres]

end Tower

end IsIntegralClosure
