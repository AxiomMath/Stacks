module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Determinants of endomorphisms of finite-length modules

Let `R` be a commutative local ring with residue field `k`, and let `φ` be an endomorphism of a
finite-length `R`-module `M`. Choosing a composition series of `M` by `φ`-invariant submodules
and multiplying the ordinary invariants of the induced endomorphisms of the simple factors gives
the determinant, the trace and the characteristic polynomial of `φ` over `k`. Jordan–Hölder makes
these independent of the series, and concatenating series shows that the determinant and the
characteristic polynomial are multiplicative — and the trace additive — along an equivariant
short exact sequence.

Two computations pin the construction down. Multiplication by a unit `u` of `R` on a
finite-length module `M` has determinant the norm of the residue of `u` raised to the length of
`M`; and for a flat local extension `R → R'` with finite-length fibre, the residue map carries
the determinant of `φ` to the determinant of the base change of `φ`, again raised to the length
of the fibre.

## Main definitions

* `FiniteLengthEndomorphism.StableCompositionSeries`: a composition series in the lattice of
  submodules invariant under an endomorphism.
* `FiniteLengthEndomorphism.det`, `FiniteLengthEndomorphism.trace`,
  `FiniteLengthEndomorphism.charpoly`: the three residue-field invariants.

## Main results

* `FiniteLengthEndomorphism.stableCompositionSeries_jordanHolder`: the invariants do not depend
  on the chosen stable composition series.
* `FiniteLengthEndomorphism.det_exact`, `FiniteLengthEndomorphism.trace_exact`,
  `FiniteLengthEndomorphism.charpoly_exact`: multiplicativity of the determinant and the
  characteristic polynomial and additivity of the trace in an equivariant short exact sequence.
* `FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length`: the determinant of
  multiplication by a scalar.
* `FiniteLengthEndomorphism.map_det_pow_eq_det_baseChange`: compatibility with a flat local base
  change.

## Implementation notes

The invariants are products over a chosen stable composition series, the trace being taken in a
multiplicative type synonym so that all three are handled by one construction. The
exact-sequence laws are proved once, for the triple of invariants
(`FiniteLengthEndomorphism.values_exact`), and then read off componentwise.

## References

* [Stacks Project, Section 0GSX](https://stacks.math.columbia.edu/tag/0GSX)
* [Stacks Project, Tag 0GSY](https://stacks.math.columbia.edu/tag/0GSY)
* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
* [Stacks Project, Tag 0GT0](https://stacks.math.columbia.edu/tag/0GT0)
-/

namespace FiniteLengthEndomorphism

/-! ### The residue-field invariants of a stable composition series -/

section

universe u v v₁ v₂ v₃

@[expose] public section

open Polynomial

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The residue field of the local ring used by the finite-length invariants. -/
public abbrev ResidueField := IsLocalRing.ResidueField R

/-- A composition series of the pair `(M, φ)`: every member is an `R`-submodule stable under
`φ`, and the series runs from zero to the whole module. -/
public structure StableCompositionSeries {M : Type v} [AddCommGroup M] [Module R M]
    (φ : Module.End R M) where
  /-- The underlying composition series of `R[X]`-submodules of `M`, with `X` acting by `φ`. -/
  series : CompositionSeries (Submodule R[X] (Module.AEval' φ))
  head_eq_bot : series.head = ⊥
  last_eq_top : series.last = ⊤

omit [IsLocalRing R] in
/-- Two stable composition series of the same pair have the same simple factors, up to a
permutation and isomorphism.  This is the Jordan--Hölder independence used in the definition of
the finite-length invariants. -/
public theorem stableCompositionSeries_jordanHolder {M : Type v} [AddCommGroup M] [Module R M]
    {φ : Module.End R M} (s t : StableCompositionSeries R φ) :
    CompositionSeries.Equivalent s.series t.series :=
  CompositionSeries.jordan_holder s.series t.series
    (s.head_eq_bot.trans t.head_eq_bot.symm) (s.last_eq_top.trans t.last_eq_top.symm)

/-- The determinant, trace, and characteristic polynomial attached to one finite-length
endomorphism. -/
public structure Values where
  /-- The determinant. -/
  determinant : ResidueField R
  /-- The trace. -/
  trace : ResidueField R
  /-- The characteristic polynomial. -/
  characteristicPolynomial : (ResidueField R)[X]

omit [IsLocalRing R] in
/-- Finite length is preserved when the polynomial action is obtained by evaluating at an
endomorphism.  This is the order-theoretic bridge needed to construct invariant composition
series. -/
private theorem finiteLength_aeval {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (phi : Module.End R M) :
    IsFiniteLength R[X] (Module.AEval' phi) := by
  have hR : IsFiniteLength R (Module.AEval' phi) :=
    (LinearEquiv.refl R M).isFiniteLength hM
  have hNA := (isFiniteLength_iff_isNoetherian_isArtinian.mp hR).1
  have hAR := (isFiniteLength_iff_isNoetherian_isArtinian.mp hR).2
  let : IsNoetherian R[X] (Module.AEval' phi) := isNoetherian_of_tower R hNA
  let : IsArtinian R[X] (Module.AEval' phi) := isArtinian_of_tower R hAR
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

omit [IsLocalRing R] in
/-- Every finite-length endomorphism admits a composition series by invariant submodules. -/
public theorem stableCompositionSeries_nonempty {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (phi : Module.End R M) :
    Nonempty (StableCompositionSeries R phi) := by
  have h := finiteLength_aeval R hM phi
  rw [isFiniteLength_iff_exists_compositionSeries] at h
  obtain ⟨s, hs0, hs1⟩ := h
  exact ⟨⟨s, hs0, hs1⟩⟩

/-- A simple module over an algebra of a local ring is annihilated by the maximal ideal
when it is finite over the local ring. -/
private theorem IsSimpleModule.isTorsionBySet_maximalIdeal_of_finite
    (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite R M] [IsSimpleModule S M] :
    Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) := by
  intro x ⟨r, hr⟩
  let f : Module.End S M := (Module.toModuleEnd S M) r
  rcases LinearMap.surjective_or_eq_zero f with hs | hz
  · have hf : (⊤ : Submodule R M) ≤ Ring.jacobson R • ⊤ := by
      intro y hy
      obtain ⟨z, hz⟩ := hs y
      rw [← hz]
      change r • z ∈ _
      exact Submodule.smul_mem_smul (show r ∈ Ring.jacobson R by
        simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using hr) (Submodule.mem_top)
    have hb := (Module.Finite.fg_top (R := R) (M := M)).eq_bot_of_le_jacobson_smul hf
    rw [Submodule.eq_bot_iff] at hb
    exact hb _ Submodule.mem_top
  · have hz' := congrArg (fun q : Module.End S M => q x) hz
    simpa [f, Module.toModuleEnd_apply] using hz'

/-- A simple module over a local ring is isomorphic to the residue field. -/
private theorem nonempty_linearEquiv_residueField_of_isSimpleModule
    (S : Type*) [CommRing S] [IsLocalRing S] (M : Type*) [AddCommGroup M] [Module S M]
    [IsSimpleModule S M] : Nonempty (M ≃ₗ[S] IsLocalRing.ResidueField S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule S M›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- The three invariants as a commutative monoid, using addition for the trace. -/
public abbrev Invariants := ResidueField R × Multiplicative (ResidueField R) ×
  (ResidueField R)[X]

/-- Ordinary finite-dimensional residue-field invariants, packaged multiplicatively. -/
public noncomputable def linearInvariants {V : Type*} [AddCommGroup V]
    [Module (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (f : Module.End (ResidueField R) V) : Invariants R :=
  (LinearMap.det f, Multiplicative.ofAdd (LinearMap.trace (ResidueField R) V f),
    LinearMap.charpoly f)

private theorem linearInvariants_conj {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ResidueField R) V] [Module (ResidueField R) W]
    [FiniteDimensional (ResidueField R) V] [FiniteDimensional (ResidueField R) W]
    (e : V ≃ₗ[ResidueField R] W) (f : Module.End (ResidueField R) V) :
    linearInvariants R (e.conj f) = linearInvariants R f := by
  have hd : LinearMap.det (e.conj f) = LinearMap.det f := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using LinearMap.det_conj f e
  simp only [linearInvariants, hd, LinearMap.trace_conj', LinearEquiv.charpoly_conj]

private theorem linearInvariants_submodule {V : Type*} [AddCommGroup V]
    [Module (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (W : Submodule (ResidueField R) V) (f : Module.End (ResidueField R) V)
    (hf : W ≤ W.comap f) :
    linearInvariants R f = linearInvariants R (f.restrict hf) *
      linearInvariants R (W.mapQ W f hf) := by
  classical
  let bW := Module.Free.chooseBasis (ResidueField R) W
  let bQ := Module.Free.chooseBasis (ResidueField R) (V ⧸ W)
  let b := bW.sumQuot bQ
  let A := LinearMap.toMatrix bW bW (f.restrict hf)
  let B := Matrix.of fun i l => b.repr (f (b (Sum.inr l))) (Sum.inl i)
  let D := LinearMap.toMatrix bQ bQ (W.mapQ W f hf)
  have hm : LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply Module.Basis.sumQuot_repr_inl_of_mem
      | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        suffices W.mkQ (f (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hf (Submodule.coe_mem (bW k))
      | inr l =>
        simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  apply Prod.ext
  · exact LinearMap.det_eq_det_mul_det W f hf
  · apply Prod.ext
    · change LinearMap.trace _ _ f = LinearMap.trace _ _ (f.restrict hf) +
        LinearMap.trace _ _ (W.mapQ W f hf)
      rw [LinearMap.trace_eq_matrix_trace _ b, hm,
        LinearMap.trace_eq_matrix_trace _ bW, LinearMap.trace_eq_matrix_trace _ bQ]
      simp [Matrix.trace, Fintype.sum_sum_type, A, D]
    · change f.charpoly = (f.restrict hf).charpoly * (W.mapQ W f hf).charpoly
      rw [← LinearMap.charpoly_toMatrix f b, hm,
        ← LinearMap.charpoly_toMatrix (f.restrict hf) bW,
        ← LinearMap.charpoly_toMatrix (W.mapQ W f hf) bQ]
      exact Matrix.charpoly_fromBlocks_zero₂₁ A B D

private theorem residueModule_eq {V : Type*} [AddCommGroup V] [Module R V]
    [m : Module (ResidueField R) V] [IsScalarTower R (ResidueField R) V]
    (h : Module.IsTorsionBySet R V (IsLocalRing.maximalIdeal R)) : h.module = m := by
  apply Module.ext'
  intro a x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
  exact (IsScalarTower.algebraMap_smul (ResidueField R) r x).symm

/-- Linear invariants of a finite module annihilated by the maximal ideal. The value on
other modules is immaterial: composition factors satisfy this annihilation condition. -/
public noncomputable def residueInvariants {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] (f : Module.End R V) : Invariants R := by
  classical
  exact if h : Module.IsTorsionBySet R V (IsLocalRing.maximalIdeal R) then
    letI : Module (ResidueField R) V := h.module
    let : IsScalarTower R (ResidueField R) V := h.isScalarTower
    let : FiniteDimensional (ResidueField R) V :=
      Module.Finite.of_restrictScalars_finite R (ResidueField R) V
    linearInvariants R (f.extendScalarsOfSurjective
      (IsLocalRing.residue_surjective (R := R)))
  else 1

/-- A module over the residue field is annihilated by the maximal ideal of the base ring. -/
private theorem isTorsionBySet_maximalIdeal_of_residueField_module {V : Type*} [AddCommGroup V]
    [Module R V] [Module (ResidueField R) V] [IsScalarTower R (ResidueField R) V] :
    Module.IsTorsionBySet R V (IsLocalRing.maximalIdeal R) := by
  intro x ⟨r, hr⟩
  rw [← IsScalarTower.algebraMap_smul (ResidueField R) r x]
  have hz : algebraMap R (ResidueField R) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hz, zero_smul]

private theorem residueInvariants_eq {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module (ResidueField R) V]
    [IsScalarTower R (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (f : Module.End (ResidueField R) V) :
    residueInvariants R (f.restrictScalars R) = linearInvariants R f := by
  have h := isTorsionBySet_maximalIdeal_of_residueField_module (R := R) (V := V)
  classical
  unfold residueInvariants
  rw [dite_eq_left h]
  have hm := residueModule_eq R h
  cases hm
  rfl

private theorem residueInvariants_equiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] [Module.Finite R V] [Module.Finite R W]
    (e : V ≃ₗ[R] W) (f : Module.End R V) (g : Module.End R W)
    (he : ∀ x, e (f x) = g (e x)) : residueInvariants R f = residueInvariants R g := by
  classical
  have ht : Module.IsTorsionBySet R V (IsLocalRing.maximalIdeal R) ↔
      Module.IsTorsionBySet R W (IsLocalRing.maximalIdeal R) := by
    constructor
    · intro h x a
      obtain ⟨x, rfl⟩ := e.surjective x
      rw [← e.map_smul, h, e.map_zero]
    · intro h x a
      apply e.injective
      rw [e.map_smul, h, e.map_zero]
  by_cases h : Module.IsTorsionBySet R V (IsLocalRing.maximalIdeal R)
  · have h' := ht.mp h
    let : Module (ResidueField R) V := h.module
    let : IsScalarTower R (ResidueField R) V := h.isScalarTower
    let : Module (ResidueField R) W := h'.module
    let : IsScalarTower R (ResidueField R) W := h'.isScalarTower
    let : FiniteDimensional (ResidueField R) V :=
      Module.Finite.of_restrictScalars_finite R (ResidueField R) V
    let : FiniteDimensional (ResidueField R) W :=
      Module.Finite.of_restrictScalars_finite R (ResidueField R) W
    let e' := e.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R))
    let f' := f.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R))
    let g' := g.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R))
    have hg : g' = e'.conj f' := by
      ext x
      change g x = e (f (e.symm x))
      simpa using (he (e.symm x)).symm
    change residueInvariants R (f'.restrictScalars R) =
      residueInvariants R (g'.restrictScalars R)
    rw [residueInvariants_eq, residueInvariants_eq, hg, linearInvariants_conj]
  · simp only [residueInvariants, dite_eq_right h, dite_eq_right (mt ht.mpr h)]

private noncomputable def quotientIntervalEquiv {S : Type*} [Ring S]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module S V] [Module S W]
    (f : V →ₗ[S] W) (A B : Submodule S V) (C D : Submodule S W)
    (hA : C.comap f = A) (hB : B.map f = D) :
    (B ⧸ A.comap B.subtype) ≃ₗ[S] (D ⧸ C.comap D.subtype) := by
  let fB : B →ₗ[S] D := (f.comp B.subtype).codRestrict D (fun x => by
    rw [← hB]
    exact Submodule.mem_map.mpr ⟨x, x.property, rfl⟩)
  have hfB : Function.Surjective fB := by
    intro y
    have hy : y.val ∈ B.map f := hB.symm ▸ y.property
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let q := (C.comap D.subtype).mkQ.comp fB
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hfB
  have hk : q.ker = A.comap B.subtype := by
    ext x
    change (C.comap D.subtype).mkQ (fB x) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change f x ∈ C ↔ x.val ∈ A
    rw [← hA]
    rfl
  exact ((A.comap B.subtype).quotEquivOfEq q.ker hk.symm).trans
    (q.quotKerEquivOfSurjective hq)

private theorem comap_covBy_of_surjective {S : Type*} [Ring S]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module S V] [Module S W]
    (f : V →ₗ[S] W) (hf : Function.Surjective f) {A B : Submodule S W}
    (h : A ⋖ B) : A.comap f ⋖ B.comap f := by
  have := (covBy_iff_quot_is_simple h.le).mp h
  apply (covBy_iff_quot_is_simple (Submodule.comap_mono h.le)).mpr
  exact IsSimpleModule.congr (quotientIntervalEquiv f _ _ A B rfl
    (Submodule.map_comap_eq_of_surjective hf B))

private def mapSeries {S : Type*} [Ring S]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module S V] [Module S W]
    (f : V →ₗ[S] W) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule S V)) : CompositionSeries (Submodule S W) where
  length := s.length
  toFun i := (s i).map f
  step i := Submodule.map_covBy_of_injective hf (s.step i)

private def comapSeries {S : Type*} [Ring S]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module S V] [Module S W]
    (f : V →ₗ[S] W) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule S W)) : CompositionSeries (Submodule S V) where
  length := s.length
  toFun i := (s i).comap f
  step i := comap_covBy_of_surjective f hf (s.step i)

section Factors

variable {M : Type*} [AddCommGroup M] [Module R M] [Module R[X] M]
    [IsScalarTower R R[X] M] [IsNoetherian R M]

omit [IsLocalRing R] in
/-- Every subquotient of a Noetherian module is finite over the base ring. -/
public theorem finite_factor (A B : Submodule R[X] M) :
    Module.Finite R (B ⧸ A.comap B.subtype) := by
  have : IsNoetherian R B := isNoetherian_of_injective
    (B.subtype.restrictScalars R) B.subtype_injective
  exact Module.Finite.of_surjective
    ((A.comap B.subtype).mkQ.restrictScalars R) (Submodule.mkQ_surjective (A.comap B.subtype))

/-- A simple polynomial-module factor is annihilated by the maximal ideal of the base ring. -/
public theorem factor_isTorsionBySet {A B : Submodule R[X] M} (hAB : A ⋖ B) :
    Module.IsTorsionBySet R (B ⧸ A.comap B.subtype) (IsLocalRing.maximalIdeal R) := by
  let := finite_factor R A B
  let := (covBy_iff_quot_is_simple hAB.le).mp hAB
  exact IsSimpleModule.isTorsionBySet_maximalIdeal_of_finite R R[X] _

/-- The residue-field invariants of the indeterminate acting on a subquotient. -/
public noncomputable def factorInvariants (A B : Submodule R[X] M) : Invariants R :=
  let := finite_factor R A B
  residueInvariants R ((Module.toModuleEnd R (B ⧸ A.comap B.subtype)) (X : R[X]))

private theorem factorInvariants_iso {A B C D : Submodule R[X] M}
    (h : JordanHolderLattice.Iso (A, B) (C, D)) :
    factorInvariants R A B = factorInvariants R C D := by
  let := finite_factor R A B
  let := finite_factor R C D
  unfold factorInvariants
  apply residueInvariants_equiv R (h.linearEquiv.restrictScalars R)
  intro x
  exact h.linearEquiv.map_smul X x

/-- The product of factor invariants in a composition series. -/
public noncomputable def seriesInvariants
    (s : CompositionSeries (Submodule R[X] M)) : Invariants R :=
  ∏ i : Fin s.length, factorInvariants R (s i.castSucc) (s i.succ)

/-- Jordan--Hölder equivalent series give the same product of factor invariants. -/
public theorem seriesInvariants_equivalent
    {s t : CompositionSeries (Submodule R[X] M)} (h : s.Equivalent t) :
    seriesInvariants R s = seriesInvariants R t := by
  obtain ⟨e, he⟩ := h
  exact Fintype.prod_equiv e _ _ (fun i => factorInvariants_iso R (he i))

private theorem seriesInvariants_eq
    (s t : CompositionSeries (Submodule R[X] M))
    (hh : s.head = t.head) (hl : s.last = t.last) :
    seriesInvariants R s = seriesInvariants R t :=
  seriesInvariants_equivalent R (CompositionSeries.jordan_holder s t hh hl)

private theorem seriesInvariants_smash
    (s t : CompositionSeries (Submodule R[X] M)) (h : s.last = t.head) :
    seriesInvariants R (s.smash t h) = seriesInvariants R s * seriesInvariants R t := by
  unfold seriesInvariants
  change (∏ i : Fin (s.length + t.length), factorInvariants R
    ((s.smash t h) i.castSucc) ((s.smash t h) i.succ)) = _
  rw [Fin.prod_univ_add]
  simp only [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd,
    RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]

variable {N : Type*} [AddCommGroup N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] [IsNoetherian R N]

private theorem factorInvariants_hom (f : M →ₗ[R[X]] N)
    (A B : Submodule R[X] M) (C D : Submodule R[X] N)
    (hA : C.comap f = A) (hB : B.map f = D) :
    factorInvariants R A B = factorInvariants R C D := by
  let := finite_factor R A B
  let := finite_factor R C D
  unfold factorInvariants
  let e := quotientIntervalEquiv f A B C D hA hB
  apply residueInvariants_equiv R (e.restrictScalars R)
  intro x
  exact e.map_smul X x

private theorem seriesInvariants_map (f : M →ₗ[R[X]] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R[X] M)) :
    seriesInvariants R (mapSeries f hf s) = seriesInvariants R s := by
  apply Finset.prod_congr rfl
  intro i _
  exact (factorInvariants_hom R f _ _ _ _
    (Submodule.comap_map_eq_of_injective hf _) rfl).symm

private theorem seriesInvariants_comap (f : M →ₗ[R[X]] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R[X] N)) :
    seriesInvariants R (comapSeries f hf s) = seriesInvariants R s := by
  apply Finset.prod_congr rfl
  intro i _
  exact factorInvariants_hom R f _ _ _ _ rfl
    (Submodule.map_comap_eq_of_surjective hf _)

end Factors

private theorem residueInvariants_submodule {M : Type*} [AddCommGroup M]
    [Module R M] [Module R[X] M] [IsScalarTower R R[X] M] [IsNoetherian R M]
    (N : Submodule R[X] M)
    [Module.Finite R N] [Module.Finite R (M ⧸ N)]
    (h : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    residueInvariants R ((Module.toModuleEnd R M) (X : R[X])) =
      residueInvariants R ((Module.toModuleEnd R N) (X : R[X])) *
      residueInvariants R ((Module.toModuleEnd R (M ⧸ N)) (X : R[X])) := by
  let : Module (ResidueField R) M := h.module
  let : IsScalarTower R (ResidueField R) M := h.isScalarTower
  let : FiniteDimensional (ResidueField R) M :=
    Module.Finite.of_restrictScalars_finite R (ResidueField R) M
  let Nk : Submodule (ResidueField R) M :=
    { carrier := N
      zero_mem' := N.zero_mem
      add_mem' := N.add_mem
      smul_mem' := by
        intro a x hx
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
        change r • x ∈ N
        exact (N.restrictScalars R).smul_mem r hx }
  let f := ((Module.toModuleEnd R M) (X : R[X])).extendScalarsOfSurjective
    (IsLocalRing.residue_surjective (R := R))
  have hf : Nk ≤ Nk.comap f := fun x hx => N.smul_mem X hx
  have hh := linearInvariants_submodule R Nk f hf
  rw [← residueInvariants_eq R f, ← residueInvariants_eq R (f.restrict hf),
    ← residueInvariants_eq R (Nk.mapQ Nk f hf)] at hh
  exact hh

private theorem residueInvariants_subsingleton {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Subsingleton M] (f : Module.End R M) :
    residueInvariants R f = 1 := by
  have h : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) :=
    fun _ _ => Subsingleton.elim _ _
  let : Module (ResidueField R) M := h.module
  let : IsScalarTower R (ResidueField R) M := h.isScalarTower
  let : FiniteDimensional (ResidueField R) M :=
    Module.Finite.of_restrictScalars_finite R (ResidueField R) M
  let f' := f.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R))
  change residueInvariants R (f'.restrictScalars R) = 1
  rw [residueInvariants_eq]
  have hf : f' = 0 := Subsingleton.elim _ _
  simp [linearInvariants, hf, LinearMap.det_zero, LinearMap.charpoly_zero,
    Module.finrank_zero_of_subsingleton]

section ModuleInvariants

variable {M : Type*} [AddCommGroup M] [Module R M] [Module R[X] M]
    [IsScalarTower R R[X] M] [IsNoetherian R M] [IsArtinian R M]

omit [IsLocalRing R] in
/-- A module of finite length over the base ring has a polynomial-module composition series. -/
public theorem moduleSeries_exists :
    ∃ s : CompositionSeries (Submodule R[X] M), s.head = ⊥ ∧ s.last = ⊤ := by
  have : IsNoetherian R[X] M := isNoetherian_of_tower R inferInstance
  have : IsArtinian R[X] M := isArtinian_of_tower R inferInstance
  exact exists_compositionSeries_of_isNoetherian_isArtinian R[X] M

/-- Invariants of a polynomial module of finite length over the base ring, obtained by
choosing a composition series and taking the product of its factor invariants. -/
public noncomputable def moduleInvariants : Invariants R :=
  seriesInvariants R (moduleSeries_exists (R := R) (M := M)).choose

/-- The invariants can be computed using any composition series from bottom to top. -/
public theorem moduleInvariants_eq_series (s : CompositionSeries (Submodule R[X] M))
    (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
    moduleInvariants R (M := M) = seriesInvariants R s :=
  seriesInvariants_eq R _ s
    ((moduleSeries_exists (R := R) (M := M)).choose_spec.1.trans h₀.symm)
    ((moduleSeries_exists (R := R) (M := M)).choose_spec.2.trans h₁.symm)

private theorem moduleInvariants_simple [IsSimpleModule R[X] M] :
    moduleInvariants R (M := M) = residueInvariants R ((Module.toModuleEnd R M) (X : R[X])) := by
  let s : CompositionSeries (Submodule R[X] M) :=
    (RelSeries.singleton _ ⊥).snoc ⊤ isCoatom_bot.covBy_top
  rw [moduleInvariants_eq_series R s rfl rfl]
  change (∏ i : Fin 1, factorInvariants R (s i.castSucc) (s i.succ)) = _
  rw [Fin.prod_univ_one]
  change factorInvariants R ⊥ ⊤ = _
  let := finite_factor R (⊥ : Submodule R[X] M) ⊤
  unfold factorInvariants
  let e : ((⊤ : Submodule R[X] M) ⧸ (⊥ : Submodule R[X] M).comap
      (⊤ : Submodule R[X] M).subtype) ≃ₗ[R[X]] M :=
    (Submodule.quotEquivOfEqBot _ (by simp)).trans Submodule.topEquiv
  apply residueInvariants_equiv R (e.restrictScalars R)
  intro x
  exact e.map_smul X x

private theorem moduleInvariants_subsingleton [Subsingleton M] :
    moduleInvariants R (M := M) = 1 := by
  rw [moduleInvariants_eq_series R (RelSeries.singleton _ ⊥) rfl (Subsingleton.elim _ _)]
  change (∏ i : Fin 0, _) = 1
  exact Finset.prod_empty

variable {N P : Type*} [AddCommGroup N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] [IsNoetherian R N] [IsArtinian R N]
    [AddCommGroup P] [Module R P] [Module R[X] P]
    [IsScalarTower R R[X] P] [IsNoetherian R P] [IsArtinian R P]

private theorem moduleInvariants_exact (f : M →ₗ[R[X]] N) (g : N →ₗ[R[X]] P)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    moduleInvariants R (M := N) = moduleInvariants R (M := M) * moduleInvariants R (M := P) := by
  obtain ⟨s, hs₀, hs₁⟩ := moduleSeries_exists (R := R) (M := M)
  obtain ⟨t, ht₀, ht₁⟩ := moduleSeries_exists (R := R) (M := P)
  let sf := mapSeries f hf s
  let tg := comapSeries g hg t
  have hconn : sf.last = tg.head := by
    change s.last.map f = t.head.comap g
    rw [hs₁, ht₀, Submodule.map_top, Submodule.comap_bot]
    exact hex.linearMap_ker_eq.symm
  have hs : sf.head = ⊥ := by
    change s.head.map f = ⊥
    simp only [hs₀, Submodule.map_bot]
  have ht : tg.last = ⊤ := by
    change t.last.comap g = ⊤
    simp only [ht₁, Submodule.comap_top]
  rw [moduleInvariants_eq_series R (sf.smash tg hconn)
    (by simpa using hs) (by simpa using ht), seriesInvariants_smash,
    seriesInvariants_map, seriesInvariants_comap,
    moduleInvariants_eq_series R s hs₀ hs₁, moduleInvariants_eq_series R t ht₀ ht₁]

end ModuleInvariants

private theorem moduleInvariants_eq_residue_aux (M : Type*) [AddCommGroup M]
    [Module R[X] M] (hM : IsFiniteLength R[X] M) :
    ∀ [Module R M] [IsScalarTower R R[X] M] [IsNoetherian R M] [IsArtinian R M],
    Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) →
    moduleInvariants R (M := M) = residueInvariants R ((Module.toModuleEnd R M) (X : R[X])) := by
  induction hM with
  | of_subsingleton =>
    intro _ _ _ _ _
    rw [moduleInvariants_subsingleton, residueInvariants_subsingleton]
  | @of_simple_quotient M _ _ N _ _ ih =>
    intro _ _ _ _ h
    have : IsNoetherian R N := isNoetherian_of_injective
      (N.subtype.restrictScalars R) N.subtype_injective
    have : IsArtinian R N := isArtinian_of_injective
      (N.subtype.restrictScalars R) N.subtype_injective
    have : IsNoetherian R (M ⧸ N) := isNoetherian_of_surjective
      (N.mkQ.restrictScalars R) (LinearMap.range_eq_top.mpr N.mkQ_surjective)
    have : IsArtinian R (M ⧸ N) := isArtinian_of_surjective M
      (N.mkQ.restrictScalars R) N.mkQ_surjective
    have hn : Module.IsTorsionBySet R N (IsLocalRing.maximalIdeal R) := by
      intro x a
      apply Subtype.ext
      exact h (x := (x : M)) (a := a)
    rw [moduleInvariants_exact R N.subtype N.mkQ N.subtype_injective
      (LinearMap.exact_iff.mpr (by simp)) N.mkQ_surjective,
      ih hn, moduleInvariants_simple, residueInvariants_submodule R N h]

private theorem moduleInvariants_eq_residue {M : Type*} [AddCommGroup M]
    [Module R M] [Module R[X] M] [IsScalarTower R R[X] M]
    [IsNoetherian R M] [IsArtinian R M]
    (h : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    moduleInvariants R (M := M) = residueInvariants R ((Module.toModuleEnd R M) (X : R[X])) := by
  have : IsNoetherian R[X] M := isNoetherian_of_tower R inferInstance
  have : IsArtinian R[X] M := isArtinian_of_tower R inferInstance
  exact moduleInvariants_eq_residue_aux R M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) h

/-- Invariants of a finite-length endomorphism, with the polynomial indeterminate acting
by that endomorphism. The construction works directly in the module's universe. -/
public noncomputable def smallValues {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) : Values R := by
  let : IsNoetherian R (Module.AEval' φ) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let : IsArtinian R (Module.AEval' φ) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let a := moduleInvariants R (M := Module.AEval' φ)
  exact ⟨a.1, a.2.1.toAdd, a.2.2⟩

/-- The determinant over the residue field of an endomorphism of a finite-length module. -/
public noncomputable def det {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) : ResidueField R :=
  (smallValues R hM φ).determinant

/-- The trace over the residue field of an endomorphism of a finite-length module. -/
public noncomputable def trace {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) : ResidueField R :=
  (smallValues R hM φ).trace

/-- The characteristic polynomial over the residue field of an endomorphism of a finite-length
module. -/
public noncomputable def charpoly {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) : (ResidueField R)[X] :=
  (smallValues R hM φ).characteristicPolynomial

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The invariants on any zero module have their empty-product and empty-sum values. -/
public theorem smallValues_subsingleton {M : Type v} [AddCommGroup M] [Module R M]
    [Subsingleton M] (hM : IsFiniteLength R M) (φ : Module.End R M) :
    smallValues R hM φ = ⟨1, 0, 1⟩ := by
  let : Subsingleton (Module.AEval' φ) :=
    ⟨fun a b => (Module.AEval'.of φ).symm.injective (Subsingleton.elim _ _)⟩
  unfold smallValues
  dsimp only
  rw [moduleInvariants_subsingleton]
  rfl

/-- The zero endomorphism of the zero module has determinant `1`. -/
@[simp] public theorem det_zero : det R (M := PUnit) IsFiniteLength.of_subsingleton 0 = 1 := by
  exact congrArg Values.determinant (smallValues_subsingleton R _ _)

/-- The zero endomorphism of the zero module has trace `0`. -/
@[simp] public theorem trace_zero :
    trace R (M := PUnit) IsFiniteLength.of_subsingleton 0 = 0 := by
  exact congrArg Values.trace (smallValues_subsingleton R _ _)

/-- The zero endomorphism of the zero module has characteristic polynomial `1`. -/
@[simp] public theorem charpoly_zero :
    charpoly R (M := PUnit) IsFiniteLength.of_subsingleton 0 = 1 := by
  exact congrArg Values.characteristicPolynomial (smallValues_subsingleton R _ _)

/-- The three invariant laws obtained by concatenating composition series in an
equivariant short exact sequence. The modules may lie in independent universes. -/
public theorem values_exact (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (h₁ : IsFiniteLength R M₁) (h₂ : IsFiniteLength R M₂) (h₃ : IsFiniteLength R M₃)
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) (φ₃ : Module.End R M₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hexact : Function.Exact f g) (hg : Function.Surjective g)
    (hfφ : f.comp φ₁ = φ₂.comp f) (hgφ : g.comp φ₂ = φ₃.comp g) :
    (smallValues R h₂ φ₂).determinant =
        (smallValues R h₁ φ₁).determinant * (smallValues R h₃ φ₃).determinant ∧
      (smallValues R h₂ φ₂).trace =
        (smallValues R h₁ φ₁).trace + (smallValues R h₃ φ₃).trace ∧
      (smallValues R h₂ φ₂).characteristicPolynomial =
        (smallValues R h₁ φ₁).characteristicPolynomial *
          (smallValues R h₃ φ₃).characteristicPolynomial := by
  let : IsNoetherian R (Module.AEval' φ₁) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₁).1
  let : IsArtinian R (Module.AEval' φ₁) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₁).2
  let : IsNoetherian R (Module.AEval' φ₂) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₂).1
  let : IsArtinian R (Module.AEval' φ₂) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₂).2
  let : IsNoetherian R (Module.AEval' φ₃) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₃).1
  let : IsArtinian R (Module.AEval' φ₃) := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₃).2
  let f' : Module.AEval' φ₁ →ₗ[R[X]] Module.AEval' φ₂ :=
    LinearMap.ofAEval φ₁ ((Module.AEval'.of φ₂).toLinearMap.comp f)
      (fun x => by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          Module.AEval'.X_smul_of, Module.End.smul_def]
          using congrArg (Module.AEval'.of φ₂) (LinearMap.congr_fun hfφ x))
  let g' : Module.AEval' φ₂ →ₗ[R[X]] Module.AEval' φ₃ :=
    LinearMap.ofAEval φ₂ ((Module.AEval'.of φ₃).toLinearMap.comp g)
      (fun x => by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          Module.AEval'.X_smul_of, Module.End.smul_def]
          using congrArg (Module.AEval'.of φ₃) (LinearMap.congr_fun hgφ x))
  have h := moduleInvariants_exact R f' g' hf hexact hg
  unfold smallValues
  dsimp only
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- Determinant is multiplicative in an equivariant short exact sequence. -/
@[stacks 0GSY "multiplicativity of the residue-field determinant"]
public theorem det_exact (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (h₁ : IsFiniteLength R M₁) (h₂ : IsFiniteLength R M₂) (h₃ : IsFiniteLength R M₃)
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) (φ₃ : Module.End R M₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hexact : Function.Exact f g) (hg : Function.Surjective g)
    (hfφ : f.comp φ₁ = φ₂.comp f) (hgφ : g.comp φ₂ = φ₃.comp g) :
    det R h₂ φ₂ = det R h₁ φ₁ * det R h₃ φ₃ :=
  (values_exact R M₁ M₂ M₃ h₁ h₂ h₃ φ₁ φ₂ φ₃ f g hf hexact hg hfφ hgφ).1

/-- Trace is additive in an equivariant short exact sequence. -/
@[stacks 0GSY "additivity of the residue-field trace"]
public theorem trace_exact (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (h₁ : IsFiniteLength R M₁) (h₂ : IsFiniteLength R M₂) (h₃ : IsFiniteLength R M₃)
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) (φ₃ : Module.End R M₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hexact : Function.Exact f g) (hg : Function.Surjective g)
    (hfφ : f.comp φ₁ = φ₂.comp f) (hgφ : g.comp φ₂ = φ₃.comp g) :
    trace R h₂ φ₂ = trace R h₁ φ₁ + trace R h₃ φ₃ :=
  (values_exact R M₁ M₂ M₃ h₁ h₂ h₃ φ₁ φ₂ φ₃ f g hf hexact hg hfφ hgφ).2.1

/-- Characteristic polynomial is multiplicative in an equivariant short exact sequence. -/
@[stacks 0GSY "multiplicativity of the residue-field characteristic polynomial"]
public theorem charpoly_exact (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (h₁ : IsFiniteLength R M₁) (h₂ : IsFiniteLength R M₂) (h₃ : IsFiniteLength R M₃)
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) (φ₃ : Module.End R M₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hexact : Function.Exact f g) (hg : Function.Surjective g)
    (hfφ : f.comp φ₁ = φ₂.comp f) (hgφ : g.comp φ₂ = φ₃.comp g) :
    charpoly R h₂ φ₂ = charpoly R h₁ φ₁ * charpoly R h₃ φ₃ :=
  (values_exact R M₁ M₂ M₃ h₁ h₂ h₃ φ₁ φ₂ φ₃ f g hf hexact hg hfφ hgφ).2.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a residue-field vector space, the composition-series construction agrees with
ordinary linear algebra. -/
public theorem smallValues_residue (V : Type v) [AddCommGroup V] [Module (ResidueField R) V]
    [Module R V] [IsScalarTower R (ResidueField R) V]
    [FiniteDimensional (ResidueField R) V]
    (h : IsFiniteLength R V) (φ : Module.End (ResidueField R) V) :
    smallValues R h (φ.restrictScalars R) =
      ⟨LinearMap.det φ, LinearMap.trace (ResidueField R) V φ, LinearMap.charpoly φ⟩ := by
  let : IsNoetherian R (Module.AEval' (φ.restrictScalars R)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  let : IsArtinian R (Module.AEval' (φ.restrictScalars R)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  let : IsNoetherian R V := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have ht : Module.IsTorsionBySet R (Module.AEval' (φ.restrictScalars R))
      (IsLocalRing.maximalIdeal R) :=
    isTorsionBySet_maximalIdeal_of_residueField_module (R := R) (V := V)
  have he := moduleInvariants_eq_residue R ht
  unfold smallValues
  dsimp only
  rw [he]
  have hh : residueInvariants R ((Module.toModuleEnd R
      (Module.AEval' (φ.restrictScalars R))) (X : R[X])) = linearInvariants R φ := by
    calc
      _ = residueInvariants R (φ.restrictScalars R) := by
        apply residueInvariants_equiv R (Module.AEval'.of (φ.restrictScalars R)).symm
        intro x
        exact Module.AEval'.of_symm_X_smul _ x
      _ = _ := residueInvariants_eq R φ
  rw [hh]
  rfl

/-- On a finite-dimensional residue-field vector space, the finite-length determinant is the
ordinary determinant. -/
public theorem det_residue (V : Type v) [AddCommGroup V] [Module (ResidueField R) V]
    [Module R V] [IsScalarTower R (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (h : IsFiniteLength R V) (φ : Module.End (ResidueField R) V) :
    det R h (φ.restrictScalars R) = LinearMap.det φ := by
  simpa [det] using congrArg Values.determinant (smallValues_residue R V h φ)

/-- On a finite-dimensional residue-field vector space, the finite-length trace is the ordinary
trace. -/
public theorem trace_residue (V : Type v) [AddCommGroup V] [Module (ResidueField R) V]
    [Module R V] [IsScalarTower R (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (h : IsFiniteLength R V) (φ : Module.End (ResidueField R) V) :
    trace R h (φ.restrictScalars R) = LinearMap.trace (ResidueField R) V φ := by
  simpa [trace] using congrArg Values.trace (smallValues_residue R V h φ)

/-- On a finite-dimensional residue-field vector space, the finite-length characteristic
polynomial is the ordinary characteristic polynomial. -/
public theorem charpoly_residue (V : Type v) [AddCommGroup V] [Module (ResidueField R) V]
    [Module R V] [IsScalarTower R (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (h : IsFiniteLength R V) (φ : Module.End (ResidueField R) V) :
    charpoly R h (φ.restrictScalars R) = LinearMap.charpoly φ := by
  simpa [charpoly] using congrArg Values.characteristicPolynomial
    (smallValues_residue R V h φ)

end

end

/-! ### The determinant of multiplication by a scalar -/

section

universe u v w

private theorem finiteLength_restrictScalars
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M : Type w) [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (hM : IsFiniteLength R' M) : IsFiniteLength R M :=
  Module.length_ne_top_iff.mp <| by
    rw [IsLocalRing.length_restrictScalars R R' M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) (by
      rw [Module.length_eq_finrank]
      exact ENat.natCast_ne_top _)

private theorem multiplication_det_eq_norm_pow_length_restrict
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M : Type w) [AddCommGroup M] [Module R' M]
    (hM : IsFiniteLength R' M) (u : R') :
    (letI : Module R M := Module.compHom M (algebraMap R R')
    letI : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    FiniteLengthEndomorphism.det R (finiteLength_restrictScalars R R' M hM)
        ((LinearMap.lsmul R' M u).restrictScalars R) =
      Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue R' u) ^
        (Module.length R' M).toNat) := by
  let : Module R M := Module.compHom M (algebraMap R R')
  let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      let : Module R M := Module.compHom M (algebraMap R R')
      let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      have hd := FiniteLengthEndomorphism.smallValues_subsingleton R
        (finiteLength_restrictScalars R R' M .of_subsingleton)
        ((LinearMap.lsmul R' M u).restrictScalars R)
      have hdet := congrArg FiniteLengthEndomorphism.Values.determinant hd
      simpa [FiniteLengthEndomorphism.det, Module.length_eq_zero] using hdet
  | @of_simple_quotient M _ _ N _ hN ih =>
      let : Module R M := Module.compHom M (algebraMap R R')
      let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let : Module R N := Module.compHom N (algebraMap R R')
      let : IsScalarTower R R' N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let Q := M ⧸ N
      let : Module R Q := Module.compHom Q (algebraMap R R')
      let : IsScalarTower R R' Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let φN : Module.End R N := ((LinearMap.lsmul R' N u).restrictScalars R)
      let φM : Module.End R M := ((LinearMap.lsmul R' M u).restrictScalars R)
      let φQ : Module.End R Q := ((LinearMap.lsmul R' Q u).restrictScalars R)
      have hQ' : IsFiniteLength R' Q :=
        isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
      have hdet := FiniteLengthEndomorphism.det_exact R N M Q
        (finiteLength_restrictScalars R R' N hN)
        (finiteLength_restrictScalars R R' M (.of_simple_quotient hN))
        (finiteLength_restrictScalars R R' Q hQ') φN φM φQ
        (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
        N.subtype_injective (LinearMap.exact_iff.mpr (by
          rw [LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
          congr 1
          rw [N.ker_mkQ]
          exact (Submodule.range_subtype N).symm)) N.mkQ_surjective
        (by ext x; rfl) (by ext x; rfl)
      rw [hdet, ih]
      let K := IsLocalRing.ResidueField R'
      obtain ⟨e⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule R' Q
      let : IsSimpleModule R' K := IsSimpleModule.congr e.symm
      let φK : Module.End (IsLocalRing.ResidueField R) K :=
        LinearMap.lsmul K K (IsLocalRing.residue R' u)
      have hK' : IsFiniteLength R' K := Module.length_ne_top_iff.mp <| by
        rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' K)]
        simp
      have hK : IsFiniteLength R K := finiteLength_restrictScalars R R' K hK'
      have hzero : IsFiniteLength R PUnit.{1} := .of_subsingleton
      have hcompare := FiniteLengthEndomorphism.det_exact R Q K PUnit.{1}
        (finiteLength_restrictScalars R R' Q hQ') hK hzero φQ
        (φK.restrictScalars R) 0 (e.restrictScalars R) 0 e.injective
        (LinearMap.exact_iff.mpr (by
          rw [LinearMap.ker_zero]
          exact (LinearMap.range_eq_top.mpr
            (show Function.Surjective (e.restrictScalars R) from e.surjective)).symm))
        (fun x => ⟨0, Subsingleton.elim _ x⟩)
        (by ext x; exact e.map_smul u x) (by rfl)
      have hdetQ : FiniteLengthEndomorphism.det R
          (finiteLength_restrictScalars R R' Q hQ') φQ =
          Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue R' u) := by
        rw [FiniteLengthEndomorphism.det_zero, mul_one] at hcompare
        rw [← hcompare, FiniteLengthEndomorphism.det_residue]
        exact Algebra.norm_apply _ _
      rw [hdetQ]
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
        N.mkQ_surjective (LinearMap.exact_iff.mpr (by rw [N.ker_mkQ, Submodule.range_subtype]))]
      rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' Q), ENat.toNat_add]
      all_goals simp [Module.length_ne_top_iff.mpr hN, pow_succ]

/-- For a local homomorphism of local rings with finite residue-field extension, the determinant
over the source residue field of multiplication by `u` on a finite-length target module is the
appropriate power of the residue-field norm of `u`. -/
@[stacks 0GSZ]
public theorem multiplication_det_eq_norm_pow_length
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M' : Type w) [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (hM' : IsFiniteLength R' M') (u : R') :
    let hM : IsFiniteLength R M' := Module.length_ne_top_iff.mp <| by
      rw [IsLocalRing.length_restrictScalars R R' M']
      exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM') (by
        rw [Module.length_eq_finrank]
        exact ENat.natCast_ne_top _)
    FiniteLengthEndomorphism.det R hM
        ((LinearMap.lsmul R' M' u).restrictScalars R) =
      Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue R' u) ^
        (Module.length R' M').toNat
    := by
  have hmodule : (inferInstance : Module R M') = Module.compHom M' (algebraMap R R') := by
    apply Module.ext'
    intro r x
    exact (IsScalarTower.algebraMap_smul R' r x).symm
  cases hmodule
  exact multiplication_det_eq_norm_pow_length_restrict R R' M' hM' u

end

/-! ### Flat local base change -/

section

universe u v w

set_option maxRecDepth 4096

open scoped TensorProduct

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
private theorem finiteLength_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (m : ℕ)
    (hm : Module.length S
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) = m)
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) : IsFiniteLength S (TensorProduct R S M) := by
  rw [← Module.length_ne_top_iff]
  rw [IsLocalRing.length_baseChange R S M, hm]
  exact ne_of_lt (WithTop.mul_lt_top
    (lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr hM)) (ENat.natCast_lt_top m))

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
private theorem det_congr
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} {N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (φ : Module.End R M) (ψ : Module.End R N)
    (e : M ≃ₗ[R] N)
    (hφ : e.toLinearMap.comp φ = ψ.comp e.toLinearMap) :
    FiniteLengthEndomorphism.det R hM φ =
      FiniteLengthEndomorphism.det R hN ψ := by
  let g : N →ₗ[R] PUnit.{1} := 0
  have hg : Function.Surjective g := by
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  have hexact : Function.Exact e.toLinearMap g := by
    rw [LinearMap.exact_iff]
    simp [g]
  have hcomm : g.comp ψ = (0 : Module.End R PUnit.{1}).comp g := by
    ext x
  have h := FiniteLengthEndomorphism.det_exact R M N PUnit.{1} hM hN
    IsFiniteLength.of_subsingleton φ ψ 0 e.toLinearMap g
    e.injective hexact hg hφ hcomm
  simpa using h.symm

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
private theorem det_exact_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (m : ℕ)
    (hm : Module.length S
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) = m)
    {M₁ M₂ M₃ : Type w}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (h₁ : IsFiniteLength R M₁) (h₂ : IsFiniteLength R M₂)
    (h₃ : IsFiniteLength R M₃)
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) (φ₃ : Module.End R M₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (hg : Function.Surjective g)
    (hfφ : f.comp φ₁ = φ₂.comp f) (hgφ : g.comp φ₂ = φ₃.comp g) :
    FiniteLengthEndomorphism.det S (finiteLength_baseChange m hm h₂)
      (LinearMap.baseChange S φ₂) =
      FiniteLengthEndomorphism.det S (finiteLength_baseChange m hm h₁)
        (LinearMap.baseChange S φ₁) *
      FiniteLengthEndomorphism.det S (finiteLength_baseChange m hm h₃)
        (LinearMap.baseChange S φ₃) := by
  have hfi : Function.Injective (LinearMap.baseChange S f) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hge : Function.Surjective (LinearMap.baseChange S g) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective S hg
  have he : Function.Exact (LinearMap.baseChange S f) (LinearMap.baseChange S g) := by
    simp only [LinearMap.baseChange_eq_lTensor]
    exact lTensor_exact S hexact hg
  have hfc : (LinearMap.baseChange S f).comp (LinearMap.baseChange S φ₁) =
      (LinearMap.baseChange S φ₂).comp (LinearMap.baseChange S f) := by
    simpa only [← LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange S) hfφ
  have hgc : (LinearMap.baseChange S g).comp (LinearMap.baseChange S φ₂) =
      (LinearMap.baseChange S φ₃).comp (LinearMap.baseChange S g) := by
    simpa only [← LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange S) hgφ
  exact FiniteLengthEndomorphism.det_exact S
    (TensorProduct R S M₁) (TensorProduct R S M₂) (TensorProduct R S M₃)
    (finiteLength_baseChange m hm h₁) (finiteLength_baseChange m hm h₂)
    (finiteLength_baseChange m hm h₃)
    (LinearMap.baseChange S φ₁) (LinearMap.baseChange S φ₂)
    (LinearMap.baseChange S φ₃)
    (LinearMap.baseChange S f) (LinearMap.baseChange S g)
    hfi he hge hfc hgc

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule
open IsLocalRing

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
private theorem finiteLength_of_exact
    {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module A L] [Module A M] [Module A N]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (hL : IsFiniteLength A L) (hN : IsFiniteLength A N) : IsFiniteLength A M := by
  rw [← Module.length_ne_top_iff, Module.length_eq_add_of_exact f g hf hg he]
  exact ne_of_lt (WithTop.add_lt_top.mpr ⟨(Module.length_ne_top_iff.mpr hL).lt_top,
    (Module.length_ne_top_iff.mpr hN).lt_top⟩)

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
/-- `rTensor` along a `B`-linear map commutes with `lTensor` of an endomorphism of `V`. -/
private theorem rTensor_comp_lTensor_restrictScalars
    {K S B V : Type*} [Field K] [CommRing S] [CommRing B] [Algebra S B] [Algebra K B]
    [AddCommGroup V] [Module K V]
    {P Q : Type*} [AddCommGroup P] [Module B P] [Module S P] [IsScalarTower S B P] [Module K P]
    [IsScalarTower K B P] [SMulCommClass K S P]
    [AddCommGroup Q] [Module B Q] [Module S Q] [IsScalarTower S B Q] [Module K Q]
    [IsScalarTower K B Q] [SMulCommClass K S Q] (φ : Module.End K V) (u : P →ₗ[B] Q) :
    ((rTensor K V u).restrictScalars S).comp ((lTensor B P φ).restrictScalars S) =
      ((lTensor B Q φ).restrictScalars S).comp ((rTensor K V u).restrictScalars S) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

section Fibre
variable {K S B : Type*} [Field K] [CommRing S] [IsLocalRing S] [CommRing B]
  [Algebra S B] [Algebra K B]
  [Algebra B (ResidueField S)] [IsScalarTower S B (ResidueField S)]
  [Algebra K (ResidueField S)] [IsScalarTower K B (ResidueField S)]

variable {N V : Type*} [AddCommGroup N] [Module B N] [Module S N]
  [IsScalarTower S B N] [Module K N] [IsScalarTower K B N]
  [SMulCommClass K S N]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
private theorem det_tensor_simple
    (hSB : Function.Surjective (algebraMap S B)) [IsSimpleModule B N]
    (φ : Module.End K V) :
    ∃ h : IsFiniteLength S (N ⊗[K] V),
      FiniteLengthEndomorphism.det S h ((lTensor B N φ).restrictScalars S) =
        algebraMap K (ResidueField S) (LinearMap.det φ) := by
  have : IsSimpleModule S N :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hSB).mpr inferInstance
  obtain ⟨e⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule S N
  let eB : N ≃ₗ[B] ResidueField S := e.extendScalarsOfSurjective hSB
  let t := (TensorProduct.AlgebraTensorModule.congr eB (LinearEquiv.refl K V)).restrictScalars S
  have hres : IsFiniteLength S ((ResidueField S) ⊗[K] V) := by
    rw [← Module.length_ne_top_iff, Module.length_eq_of_surjective
      (IsLocalRing.residue_surjective (R := S))]
    exact Module.length_ne_top
  have ht := t.symm.isFiniteLength hres
  refine ⟨ht, ?_⟩
  rw [det_congr ht hres _ ((LinearMap.baseChange (ResidueField S) φ).restrictScalars S) t]
  · rw [FiniteLengthEndomorphism.det_residue, LinearMap.det_baseChange]
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
set_option backward.isDefEq.respectTransparency false in
private theorem det_tensor_finiteLength
    (hSB : Function.Surjective (algebraMap S B))
    (φ : Module.End K V) (N : Type*) [AddCommGroup N] [Module B N]
    (hN : IsFiniteLength B N) :
    ∀ [Module S N] [IsScalarTower S B N] [Module K N] [IsScalarTower K B N]
      [SMulCommClass K S N],
    ∃ h : IsFiniteLength S (N ⊗[K] V),
      FiniteLengthEndomorphism.det S h ((lTensor B N φ).restrictScalars S) =
        algebraMap K (ResidueField S) (LinearMap.det φ) ^ (Module.length S N).toNat := by
  induction hN with
  | of_subsingleton =>
    intro _ _ _ _ _
    refine ⟨IsFiniteLength.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero, ENat.toNat_zero, pow_zero]
    exact congrArg FiniteLengthEndomorphism.Values.determinant
      (FiniteLengthEndomorphism.smallValues_subsingleton S _ _)
  | @of_simple_quotient N _ _ P hP hN ih =>
    intro _ _ _ _ _
    let : SMulCommClass K S P := ⟨fun k s n => by
      simp only [← IsScalarTower.algebraMap_smul (R := K) B,
        ← IsScalarTower.algebraMap_smul (R := S) B]
      exact smul_comm _ _ _⟩
    let : SMulCommClass K S (N ⧸ P) := ⟨fun k s n => by
      simp only [← IsScalarTower.algebraMap_smul (R := K) B,
        ← IsScalarTower.algebraMap_smul (R := S) B]
      exact smul_comm _ _ _⟩
    obtain ⟨hPV, hdetP⟩ := ih
    obtain ⟨hQV, hdetQ⟩ := det_tensor_simple (B := B) (N := N ⧸ P) hSB φ
    let f := (rTensor K V P.subtype).restrictScalars S
    let g := (rTensor K V P.mkQ).restrictScalars S
    have hf : Function.Injective f :=
      Module.Flat.rTensor_preserves_injective_linearMap
        (P.subtype.restrictScalars K) P.subtype_injective
    have hg : Function.Surjective g :=
      LinearMap.rTensor_surjective V (g := P.mkQ.restrictScalars K) P.mkQ_surjective
    have he : Function.Exact f g := rTensor_exact V
      (f := P.subtype.restrictScalars K) (g := P.mkQ.restrictScalars K)
      (LinearMap.exact_subtype_mkQ P)
      P.mkQ_surjective
    have hNV := finiteLength_of_exact f g hf hg he hPV hQV
    refine ⟨hNV, ?_⟩
    have hd := FiniteLengthEndomorphism.det_exact S _ _ _ hPV hNV hQV
      ((lTensor B P φ).restrictScalars S) ((lTensor B N φ).restrictScalars S)
      ((lTensor B (N ⧸ P) φ).restrictScalars S) f g hf he hg
      (rTensor_comp_lTensor_restrictScalars φ _)
      (rTensor_comp_lTensor_restrictScalars φ _)
    rw [hd, hdetP, hdetQ]
    have : IsSimpleModule S (N ⧸ P) :=
      (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hSB).mpr hP
    have hlen := Module.length_eq_add_of_exact (P.subtype.restrictScalars S)
      (P.mkQ.restrictScalars S) P.subtype_injective P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
    rw [hlen, Module.length_eq_one S (N ⧸ P), ENat.toNat_add, ENat.toNat_one, pow_succ]
    · rw [Module.length_eq_of_surjective hSB]
      exact Module.length_ne_top_iff.mpr hN
    · exact ENat.one_ne_top
end Fibre

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
set_option backward.isDefEq.respectTransparency false in
private theorem det_baseChange_residue
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    {V : Type*} [AddCommGroup V] [Module R V] [Module (ResidueField R) V]
    [IsScalarTower R (ResidueField R) V] [FiniteDimensional (ResidueField R) V]
    (m : ℕ) (hm : Module.length S (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) = m)
    (φ : Module.End (ResidueField R) V) :
    ∃ h : IsFiniteLength S (S ⊗[R] V),
      FiniteLengthEndomorphism.det S h (LinearMap.baseChange S (φ.restrictScalars R)) =
        algebraMap (ResidueField R) (ResidueField S) (LinearMap.det φ) ^ m := by
  let K := ResidueField R
  let B := S ⊗[R] K
  let : Algebra K B := Algebra.TensorProduct.rightAlgebra
  let q : B →ₐ[S] ResidueField S := Algebra.TensorProduct.lift
    (Algebra.ofId S (ResidueField S)) (IsScalarTower.toAlgHom R K (ResidueField S))
    (fun _ _ => Commute.all _ _)
  let : Algebra B (ResidueField S) := q.toRingHom.toAlgebra
  let : IsScalarTower S B (ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun s => (q.commutes s).symm)
  let : IsScalarTower K B (ResidueField S) := IsScalarTower.of_algebraMap_eq (fun k => by
    change algebraMap K (ResidueField S) k = q (1 ⊗ₜ[R] k)
    change algebraMap K (ResidueField S) k =
      algebraMap S (ResidueField S) 1 * algebraMap K (ResidueField S) k
    rw [map_one, one_mul])
  have hSB : Function.Surjective (algebraMap S B) :=
    Algebra.TensorProduct.includeLeft_surjective S S (residue_surjective (R := R))
  have hlen : Module.length S B = m := by
    change Module.length S (S ⊗[R] (R ⧸ maximalIdeal R)) = m
    rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (maximalIdeal R)).toLinearEquiv.length_eq]
    exact hm
  have hB : IsFiniteLength B B := by
    rw [← Module.length_ne_top_iff, ← Module.length_eq_of_surjective hSB, hlen]
    exact ENat.natCast_ne_top m
  obtain ⟨hBV, hd⟩ := det_tensor_finiteLength (S := S) hSB φ B hB
  let : TensorProduct.CompatibleSMul R K B V :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective B V (residue_surjective (R := R))
  let : TensorProduct.CompatibleSMul R K K V :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective K V (residue_surjective (R := R))
  let eV : K ⊗[R] V ≃ₗ[K] V := TensorProduct.lidOfCompatibleSMul R K V
  let e : B ⊗[K] V ≃ₗ[S] S ⊗[R] V :=
    (TensorProduct.equivOfCompatibleSMul R K S B V).trans
      ((TensorProduct.AlgebraTensorModule.assoc R R S S K V).trans
        (LinearEquiv.baseChange R S _ _ (eV.restrictScalars R)))
  have hSV := e.isFiniteLength hBV
  refine ⟨hSV, ?_⟩
  rw [← det_congr hBV hSV _ _ e]
  · simpa only [hlen, ENat.toNat_natCast] using hd
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b v =>
      induction b using TensorProduct.inductionOn with
      | add b c hb hc => simp only [TensorProduct.add_tmul, map_add, hb, hc]
      | tmul s k =>
        change s ⊗ₜ[R] (k • φ v) = s ⊗ₜ[R] φ (k • v)
        rw [map_smul]

open Polynomial

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
set_option backward.isDefEq.respectTransparency false in
private theorem det_baseChange_simple
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    {M : Type*} [AddCommGroup M] [Module R M] [Module R[X] M]
    [IsScalarTower R R[X] M] [IsSimpleModule R[X] M]
    (m : ℕ) (hm : Module.length S (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) = m)
    (hM : IsFiniteLength R M) :
    FiniteLengthEndomorphism.det S (finiteLength_baseChange m hm hM)
        (LinearMap.baseChange S ((Module.toModuleEnd R M) (X : R[X]))) =
      algebraMap (ResidueField R) (ResidueField S)
        (FiniteLengthEndomorphism.det R hM ((Module.toModuleEnd R M) (X : R[X]))) ^ m := by
  let : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  have ht := IsSimpleModule.isTorsionBySet_maximalIdeal_of_finite R R[X] M
  let : Module (ResidueField R) M := ht.module
  let : IsScalarTower R (ResidueField R) M := ht.isScalarTower
  let : FiniteDimensional (ResidueField R) M :=
    Module.Finite.of_restrictScalars_finite R (ResidueField R) M
  let φ := ((Module.toModuleEnd R M) (X : R[X])).extendScalarsOfSurjective
    (residue_surjective (R := R))
  obtain ⟨h, hd⟩ := det_baseChange_residue (R := R) (S := S) m hm φ
  change FiniteLengthEndomorphism.det S _ (LinearMap.baseChange S (φ.restrictScalars R)) =
    algebraMap (ResidueField R) (ResidueField S)
      (FiniteLengthEndomorphism.det R hM (φ.restrictScalars R)) ^ m
  rw [FiniteLengthEndomorphism.det_residue]
  exact hd

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
set_option backward.isDefEq.respectTransparency false in
private theorem det_baseChange_polynomial
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (m : ℕ) (hm : Module.length S (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) = m)
    (M : Type*) [AddCommGroup M] [Module R[X] M] (hM : IsFiniteLength R[X] M) :
    ∀ [Module R M] [IsScalarTower R R[X] M] (h : IsFiniteLength R M),
    FiniteLengthEndomorphism.det S (finiteLength_baseChange m hm h)
        (LinearMap.baseChange S ((Module.toModuleEnd R M) (X : R[X]))) =
      algebraMap (ResidueField R) (ResidueField S)
        (FiniteLengthEndomorphism.det R h ((Module.toModuleEnd R M) (X : R[X]))) ^ m := by
  induction hM with
  | of_subsingleton =>
    intro _ _ h
    have hR := FiniteLengthEndomorphism.smallValues_subsingleton R h
      ((Module.toModuleEnd R _) (X : R[X]))
    have hS := FiniteLengthEndomorphism.smallValues_subsingleton S
      (finiteLength_baseChange m hm h)
      (LinearMap.baseChange S ((Module.toModuleEnd R _) (X : R[X])))
    change (FiniteLengthEndomorphism.smallValues S _ _).determinant =
      algebraMap (ResidueField R) (ResidueField S)
        (FiniteLengthEndomorphism.smallValues R _ _).determinant ^ m
    rw [hR, hS]
    simp
  | @of_simple_quotient M _ _ N hN hfin ih =>
    intro _ _ h
    have hsub : IsFiniteLength R N := h.of_injective (f := N.subtype.restrictScalars R)
      N.subtype_injective
    have hquot : IsFiniteLength R (M ⧸ N) := h.of_surjective (f := N.mkQ.restrictScalars R)
      N.mkQ_surjective
    let φ₁ := (Module.toModuleEnd R N) (X : R[X])
    let φ₂ := (Module.toModuleEnd R M) (X : R[X])
    let φ₃ := (Module.toModuleEnd R (M ⧸ N)) (X : R[X])
    have hfφ : (N.subtype.restrictScalars R).comp φ₁ = φ₂.comp (N.subtype.restrictScalars R) := by
      ext x
      rfl
    have hgφ : (N.mkQ.restrictScalars R).comp φ₂ = φ₃.comp (N.mkQ.restrictScalars R) := by
      ext x
      rfl
    have hex : Function.Exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R) :=
      LinearMap.exact_subtype_mkQ N
    rw [det_exact_baseChange m hm hsub h hquot φ₁ φ₂ φ₃
      (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.subtype_injective hex N.mkQ_surjective hfφ hgφ,
      ih hsub, det_baseChange_simple m hm hquot,
      FiniteLengthEndomorphism.det_exact R N M (M ⧸ N) hsub h hquot φ₁ φ₂ φ₃
        (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
        N.subtype_injective hex N.mkQ_surjective hfφ hgφ,
      map_mul, mul_pow]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the module structures on the base-changed tensor products is slow
/-- **Stacks 0GT0.** Under a flat local homomorphism `R → S` whose closed fibre has finite
length `m`, the determinant of a finite-length module endomorphism after scalar extension is the
image in the residue field of `S` of the original determinant raised to the power `m`. -/
@[stacks 0GT0]
public theorem map_det_pow_eq_det_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (m : ℕ)
    (hm : Module.length S
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) = m)
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (phi : Module.End R M) :
    ∃ hMS : IsFiniteLength S (S ⊗[R] M),
      IsLocalRing.ResidueField.map (algebraMap R S)
          (FiniteLengthEndomorphism.det R hM phi ^ m) =
        FiniteLengthEndomorphism.det S hMS (LinearMap.baseChange S phi)
    := by
  let e := Module.AEval'.of phi
  have hM' := e.isFiniteLength hM
  obtain ⟨s⟩ := FiniteLengthEndomorphism.stableCompositionSeries_nonempty R hM phi
  have hp : IsFiniteLength R[X] (Module.AEval' phi) :=
    isFiniteLength_iff_exists_compositionSeries.mpr ⟨s.series, s.head_eq_bot, s.last_eq_top⟩
  let ψ := (Module.toModuleEnd R (Module.AEval' phi)) (X : R[X])
  have he : e.toLinearMap.comp phi = ψ.comp e.toLinearMap := by
    ext x
    exact (Module.AEval'.X_smul_of phi x).symm
  have hd := det_congr hM hM' phi ψ e he
  have hMS := finiteLength_baseChange m hm hM
  have hMS' := finiteLength_baseChange m hm hM'
  have hde := det_congr hMS hMS' (LinearMap.baseChange S phi) (LinearMap.baseChange S ψ)
    (LinearEquiv.baseChange R S _ _ e) (by
      change (LinearMap.baseChange S e.toLinearMap).comp (LinearMap.baseChange S phi) =
        (LinearMap.baseChange S ψ).comp (LinearMap.baseChange S e.toLinearMap)
      simpa only [← LinearMap.baseChange_comp] using
        congrArg (LinearMap.baseChange S) he)
  refine ⟨hMS, ?_⟩
  rw [hde, det_baseChange_polynomial m hm (Module.AEval' phi) hp hM', ← hd]
  exact map_pow _ _ _

set_option maxRecDepth 4096

open scoped TensorProduct

end

end FiniteLengthEndomorphism
