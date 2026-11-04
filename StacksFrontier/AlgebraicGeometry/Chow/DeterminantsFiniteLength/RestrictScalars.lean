module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.Dimension.Finite
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaIsomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor

/-!
# Determinants and local maps with unchanged residue field

For a local homomorphism of local rings inducing an isomorphism of residue fields,
restriction of scalars preserves the length and the determinant of a finite-length module.
The comparison carries admissible symbols to the same symbols, is natural for module
isomorphisms, and respects the determinant isomorphism of a short exact sequence.

## Main definitions

* `Module.FiniteLength.determinantRestrictScalarsEquiv` is the canonical semilinear
  determinant isomorphism.

## Main results

* `Module.FiniteLength.isFiniteLength_restrictScalars` and
  `Module.FiniteLength.moduleLength_restrictScalars` give preservation of finite length and
  of length.
* `Module.FiniteLength.determinantRestrictScalarsEquiv_symbol` specifies the isomorphism on
  symbols.
* `Module.FiniteLength.determinantRestrictScalarsEquiv_natural` and
  `Module.FiniteLength.determinantRestrictScalarsEquiv_exact` give naturality and
  exact-sequence compatibility.

## References

* [Stacks Project, Tag 02PC](https://stacks.math.columbia.edu/tag/02PC)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] RingHomInvPair.of_ringEquiv_symm

namespace Module.FiniteLength
universe u v w x

/-- For a local homomorphism of local rings, the induced map of residue fields is the algebra
map. -/
private theorem residueFieldMap_eq_algebraMap
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)] :
    algebraMap (IsLocalRing.ResidueField R₀) (IsLocalRing.ResidueField R) =
      IsLocalRing.ResidueField.map (algebraMap R₀ R) := by
  ext c
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  simp

/-- A local homomorphism of local rings inducing an isomorphism of residue fields does not
change the length of a module. -/
private theorem length_restrictScalars_eq
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] :
    Module.length R₀ M = Module.length R M := by
  have hκlen : Module.length (IsLocalRing.ResidueField R₀)
      (IsLocalRing.ResidueField R) = 1 := by
    refine Module.length_eq_one_iff.mpr (isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨inferInstance, fun x hx y => ?_⟩)
    obtain ⟨a, ha⟩ := hκ.2 (y / x)
    exact ⟨a, by rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def,
      residueFieldMap_eq_algebraMap, ha, div_mul_cancel₀ y hx]⟩
  rw [IsLocalRing.length_restrictScalars R₀ R M, hκlen, mul_one]

/-- When the residue fields agree, every element of `R` is congruent modulo the maximal ideal to
the image of an element of `R₀`, whose residue class corresponds to its own. -/
private theorem exists_residue_eq_and_sub_mem_maximalIdeal
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R))) (a : R) :
    ∃ a₀ : R₀, IsLocalRing.residue R₀ a₀ = (RingEquiv.ofBijective
        (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ).symm (IsLocalRing.residue R a) ∧
      a - algebraMap R₀ R a₀ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ((RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ).symm (IsLocalRing.residue R a))
  refine ⟨a₀, ha₀, (IsLocalRing.residue_eq_zero_iff _).mp ?_⟩
  rw [map_sub, ← IsLocalRing.ResidueField.map_residue (algebraMap R₀ R) a₀, ha₀, sub_eq_zero]
  exact ((RingEquiv.ofBijective _ hκ).apply_symm_apply _).symm

/-- An element of the `R`-span of a set lies in an `R₀`-submodule containing every `R`-multiple
of every member of the set. -/
private theorem mem_of_mem_span_of_forall_smul_mem
    {R₀ : Type u} {R : Type v} [CommRing R₀] [CommRing R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    {N : Submodule R₀ M} {s : Set M} (hs : ∀ y ∈ s, ∀ a : R, a • y ∈ N) {x : M}
    (hx : x ∈ Submodule.span R s) : x ∈ N := by
  suffices ∀ a : R, a • x ∈ N by simpa using this 1
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => simp
  | add y z _ _ hy hz => exact fun a => by rw [smul_add]; exact N.add_mem (hy a) (hz a)
  | smul c y _ hy => exact fun a => by rw [smul_smul]; exact hy (a * c)

/-- An element of an `R₀`-submodule stays in it after scaling by any element of `R`, provided
this holds for scaling by elements of the maximal ideal of `R`. -/
private theorem smul_mem_of_forall_maximalIdeal_smul_mem
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] {N : Submodule R₀ M} {y : M} (hy : y ∈ N)
    (h : ∀ d ∈ IsLocalRing.maximalIdeal R, d • y ∈ N) (a : R) : a • y ∈ N := by
  obtain ⟨a₀, -, hd⟩ := exists_residue_eq_and_sub_mem_maximalIdeal hκ a
  rw [show a = algebraMap R₀ R a₀ + (a - algebraMap R₀ R a₀) by ring, add_smul, algebraMap_smul]
  exact add_mem (N.smul_mem a₀ hy) (h _ hd)

/-- For an admissible sequence over `R`, the span over `R` of the entries preceding an index
is contained in their span over `R₀`. -/
public theorem spanBefore_le_restrictScalars
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] {n : ℕ} (e : Fin n → M)
    (he : IsAdmissibleSequence (R := R) e) :
    ∀ i : Fin n,
      ∀ x, x ∈ spanBefore (R := R) e i → x ∈ spanBefore (R := R₀) e i := by
  intro i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero =>
        intro x hx
        simpa [spanBefore] using hx
    | succ i ih =>
      intro x hx
      refine mem_of_mem_span_of_forall_smul_mem (R := R) ?_ hx
      rintro _ ⟨j, hj, rfl⟩
      refine smul_mem_of_forall_maximalIdeal_smul_mem hκ (Submodule.subset_span ⟨j, hj, rfl⟩)
        fun d hd => ?_
      exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio Fin.castSucc_lt_succ.le))
        (ih _ (Submodule.span_mono
          (Set.image_mono (Set.Iio_subset_Iio (Fin.le_castSucc_iff.mpr hj))) (he j _ hd)))

/-- An admissible sequence over `R` is admissible over `R₀`. -/
private theorem admissibleSequence_restrictScalars_aux
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] {n : ℕ} {e : Fin n → M}
    (he : IsAdmissibleSequence (R := R) e) :
    IsAdmissibleSequence (R := R₀) e := by
  intro i r hr
  simpa [Algebra.smul_def] using spanBefore_le_restrictScalars hκ e he i _
    (he i (algebraMap R₀ R r) (map_nonunit (algebraMap R₀ R) r hr))

/-- For an admissible sequence over `R`, the span over `R` of its entries is contained in
their span over `R₀`; in particular the two spans agree. -/
public theorem spanRange_le_restrictScalars
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] {n : ℕ} (e : Fin n → M)
    (he : IsAdmissibleSequence (R := R) e) :
    ∀ x, x ∈ Submodule.span R (Set.range e) →
      x ∈ Submodule.span R₀ (Set.range e) := by
  intro x hx
  refine mem_of_mem_span_of_forall_smul_mem (R := R) ?_ hx
  rintro _ ⟨i, rfl⟩
  exact smul_mem_of_forall_maximalIdeal_smul_mem hκ (Submodule.subset_span ⟨i, rfl⟩) fun d hd =>
    Submodule.span_mono (Set.image_subset_range _ _)
      (spanBefore_le_restrictScalars hκ e he i _ (he i _ hd))

/-- A module of finite length over `R` has finite length over `R₀`. -/
@[stacks 02PC "finite length"]
public theorem isFiniteLength_restrictScalars
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M) :
    IsFiniteLength R₀ M :=
  Module.length_ne_top_iff.mp
    ((length_restrictScalars_eq (M := M) hκ).symm ▸ Module.length_ne_top_iff.mpr hM)

/-- The length is unchanged by restriction along a local homomorphism inducing an
isomorphism of residue fields. -/
@[stacks 02PC "length"]
public theorem moduleLength_restrictScalars
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (_hM : IsFiniteLength R M) :
    moduleLength R M = moduleLength R₀ M :=
  congrArg ENat.toNat (length_restrictScalars_eq (M := M) hκ).symm

/-- An admissible sequence remains admissible after restriction of scalars. -/
public theorem admissibleSequence_restrictScalars
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M) :
    IsAdmissibleSequence (R := R₀)
      (fun i : Fin (moduleLength R₀ M) ↦
        e.1 (Fin.cast (moduleLength_restrictScalars hκ hM).symm i)) := by
  let hlen := moduleLength_restrictScalars hκ hM
  let e' : Fin (moduleLength R₀ M) → M := fun i => e.1 (Fin.cast hlen.symm i)
  have he' : IsAdmissibleSequence (R := R) e' := by
    intro i r hr
    have hi := e.2 (Fin.cast hlen.symm i) r hr
    rw [spanBefore_eq_cast (R := R) hlen e.1 (Fin.cast hlen.symm i)] at hi
    simpa [e'] using hi
  simpa [e'] using admissibleSequence_restrictScalars_aux hκ he'

/-- The symbol of a spanning admissible sequence is nonzero. -/
private theorem symbol_ne_zero_of_span_eq_top
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) : symbol e ≠ 0 := fun hz => by
  have : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_determinant_eq_one hM]; exact Nat.one_pos)
  simpa [hz] using span_symbol_eq_top hM e he

/-- Every element of the determinant of a spanning admissible sequence's span is a scalar
multiple of its symbol. -/
private theorem exists_smul_symbol_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) (z : determinant R M) :
    ∃ c : IsLocalRing.ResidueField R, c • symbol e = z :=
  Submodule.mem_span_singleton.mp (span_symbol_eq_top hM e he ▸ Submodule.mem_top :
    z ∈ (IsLocalRing.ResidueField R) ∙ symbol e)

/-- Restricting scalars preserves a spanning admissible sequence, reindexed by the length
equality. -/
private theorem span_restrictScalars_eq_top
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M) (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) :
    Submodule.span R₀ (Set.range fun i : Fin (moduleLength R₀ M) =>
      e.1 (Fin.cast (moduleLength_restrictScalars hκ hM).symm i)) = ⊤ := by
  rw [show Set.range (fun i : Fin (moduleLength R₀ M) =>
      e.1 (Fin.cast (moduleLength_restrictScalars hκ hM).symm i)) = Set.range e.1 from
    (finCongr (moduleLength_restrictScalars hκ hM).symm).surjective.range_comp e.1, eq_top_iff]
  exact fun x _ => spanRange_le_restrictScalars hκ e.1 e.2 x (he ▸ Submodule.mem_top)

/-- Construction data for the canonical determinant comparison, including its action on
admissible symbols. -/
public noncomputable def determinantRestrictScalarsComparisonData
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M) :
    { f : determinant R M ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.ofBijective
        (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ).symm]
        determinant R₀ M //
      ∀ e : AdmissibleSequence R M,
        f (symbol e) = symbol ⟨fun i : Fin (moduleLength R₀ M) ↦
          e.1 (Fin.cast (moduleLength_restrictScalars hκ hM).symm i),
          admissibleSequence_restrictScalars hκ hM e⟩ } := by
  classical
  let hlen := moduleLength_restrictScalars hκ hM
  let ρ := RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ
  let seq : AdmissibleSequence R M → AdmissibleSequence R₀ M := fun e =>
    ⟨fun i => e.1 (Fin.cast hlen.symm i), admissibleSequence_restrictScalars hκ hM e⟩
  let freeMap : DeterminantFree R M →ₛₗ[RingHomClass.toRingHom ρ.symm]
      DeterminantFree R₀ M :=
    (Finsupp.mapRange.linearMap (RingHom.toSemilinearMap ρ.symm)).comp
      (Finsupp.lmapDomain (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R) seq)
  let qmap := (Submodule.mkQ (determinantRelations R₀ M)).comp freeMap
  have hsingle (e : AdmissibleSequence R M) (c : IsLocalRing.ResidueField R) :
      freeMap (Finsupp.single e c) = Finsupp.single (seq e) (ρ.symm c) := by
    ext e'
    simp [freeMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hkernel : ∀ z : DeterminantFree R M,
      freeMap z ∈ determinantRelations R₀ M → z ∈ qmap.ker := fun z hz =>
    LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr hz)
  have hupdateCast (f : Fin (moduleLength R M) → M) (i : Fin (moduleLength R M)) (v : M) :
      (fun j : Fin (moduleLength R₀ M) => Function.update f i v (Fin.cast hlen.symm j)) =
        Function.update (fun j => f (Fin.cast hlen.symm j)) (Fin.cast hlen i) v := by
    funext j
    simp only [Function.update_apply, Fin.ext_iff, Fin.val_cast]
  have hrel : determinantRelations R M ≤ qmap.ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change DeterminantRelation z at hz
    cases hz with
    | dependent e a ha =>
        have ha' : e.1 a ∈ spanBefore (R := R₀) e.1 a :=
          spanBefore_le_restrictScalars hκ e.1 e.2 a (e.1 a) ha
        have hseq : (seq e).1 (Fin.cast hlen a) = e.1 a := by simp [seq]
        have hspan := spanBefore_eq_cast (R := R₀) hlen e.1 a
        have hdep : DeterminantRelation (Finsupp.single (seq e) 1) :=
          DeterminantRelation.dependent (seq e) (Fin.cast hlen a) (by
            rw [← hspan]
            simpa [hseq] using ha')
        have hrel' : Finsupp.single (seq e) 1 ∈ determinantRelations R₀ M :=
          Submodule.subset_span hdep
        apply hkernel
        rw [hsingle]
        simpa [ρ] using hrel'
    | unitChange e a unit replacement x ha hx hreplacement =>
        let c₀ := ρ.symm (IsLocalRing.residue R (unit : R))
        obtain ⟨u₀, hu₀⟩ := IsLocalRing.residue_surjective c₀
        have hc₀ : c₀ ≠ 0 := by
          intro hzero
          have hsource : IsLocalRing.residue R (unit : R) = 0 := by
            apply ρ.symm.injective
            simp [c₀] at hzero
          exact ((IsLocalRing.residue_ne_zero_iff_isUnit (unit : R)).mpr unit.isUnit) hsource
        have hu₀unit : IsUnit u₀ :=
          (IsLocalRing.residue_ne_zero_iff_isUnit u₀).mp (hu₀ ▸ hc₀)
        let unit₀ : R₀ˣ := hu₀unit.unit
        have hunit₀res : IsLocalRing.residue R₀ (unit₀ : R₀) = c₀ := by
          rw [IsUnit.unit_spec hu₀unit]
          exact hu₀
        have hdeltares : IsLocalRing.residue R
            ((unit : R) - algebraMap R₀ R (unit₀ : R₀)) = 0 := by
          rw [map_sub, ← IsLocalRing.ResidueField.map_residue (algebraMap R₀ R), hunit₀res,
            sub_eq_zero]
          exact (ρ.apply_symm_apply _).symm
        have hdelta : (unit : R) - algebraMap R₀ R (unit₀ : R₀) ∈
            IsLocalRing.maximalIdeal R :=
          (IsLocalRing.residue_eq_zero_iff _).mp hdeltares
        let x₀ : M := x +
          ((unit : R) - algebraMap R₀ R (unit₀ : R₀)) • replacement
        have hbefore : spanBefore (R := R) (Function.update e.1 a replacement) a =
            spanBefore (R := R) e.1 a :=
          congrArg (Submodule.span R)
            (Set.image_congr fun j hj => Function.update_of_ne (Set.mem_Iio.1 hj).ne _ _)
        have hdeltaR :
            ((unit : R) - algebraMap R₀ R (unit₀ : R₀)) • replacement ∈
              spanBefore (R := R) e.1 a := by
          rw [← hbefore]
          simpa using hreplacement a _ hdelta
        have hxR₀ : x ∈ spanBefore (R := R₀) e.1 a :=
          spanBefore_le_restrictScalars hκ e.1 e.2 a x hx
        have hdeltaR₀ :
            ((unit : R) - algebraMap R₀ R (unit₀ : R₀)) • replacement ∈
              spanBefore (R := R₀) e.1 a :=
          spanBefore_le_restrictScalars hκ e.1 e.2 a _ hdeltaR
        have hx₀ : x₀ ∈ spanBefore (R := R₀) e.1 a :=
          (spanBefore (R := R₀) e.1 a).add_mem hxR₀ hdeltaR₀
        have hspan := spanBefore_eq_cast (R := R₀) hlen e.1 a
        let a₀ := Fin.cast hlen a
        have hx₀' : x₀ ∈ spanBefore (R := R₀) (seq e).1 a₀ := by
          rw [← hspan]
          exact hx₀
        have hreplaceCast :
            (fun j : Fin (moduleLength R₀ M) =>
              Function.update e.1 a replacement (Fin.cast hlen.symm j)) =
            Function.update (seq e).1 a₀ replacement :=
          hupdateCast e.1 a replacement
        have hrepl₀ : IsAdmissibleSequence (R := R₀)
            (Function.update (seq e).1 a₀ replacement) := by
          simpa [hreplaceCast] using admissibleSequence_restrictScalars hκ hM
            ⟨Function.update e.1 a replacement, hreplacement⟩
        have hvalue : e.1 a = (unit₀ : R₀) • replacement + x₀ := by
          rw [ha]
          simp only [x₀, sub_smul, algebraMap_smul]
          abel
        have hunitRel : DeterminantRelation
            (Finsupp.single (seq e) 1 -
              IsLocalRing.residue R₀ unit₀ •
                Finsupp.single
                  ⟨Function.update (seq e).1 a₀ replacement, hrepl₀⟩ 1) :=
          DeterminantRelation.unitChange (seq e) a₀ unit₀ replacement x₀
            (by simpa [seq, a₀] using hvalue) hx₀' hrepl₀
        have htarget :
            Finsupp.single (seq e) 1 - ρ.symm (IsLocalRing.residue R unit) •
              Finsupp.single
                ⟨Function.update (seq e).1 a₀ replacement, hrepl₀⟩ 1 ∈
              determinantRelations R₀ M := by
          have hunitScalar : ρ.symm (IsLocalRing.residue R unit) =
              IsLocalRing.residue R₀ unit₀ := by
            simpa [c₀] using hunit₀res.symm
          rw [hunitScalar]
          exact Submodule.subset_span hunitRel
        let heRep : AdmissibleSequence R M :=
          ⟨Function.update e.1 a replacement, hreplacement⟩
        have hseqRep : seq heRep =
            ⟨Function.update (seq e).1 a₀ replacement, hrepl₀⟩ :=
          Subtype.ext hreplaceCast
        have hfree : freeMap
            (Finsupp.single e 1 - IsLocalRing.residue R unit • Finsupp.single heRep 1) ∈
            determinantRelations R₀ M := by
          rw [map_sub, freeMap.map_smulₛₗ, hsingle, hsingle, hseqRep]
          simpa using htarget
        apply hkernel
        simpa [heRep] using hfree
    | swap e a b hba ha hswap =>
        let a₀ := Fin.cast hlen a
        let b₀ := Fin.cast hlen b
        let eSwap : AdmissibleSequence R M :=
          ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩
        have hcastInner :
            (fun j : Fin (moduleLength R₀ M) =>
              Function.update e.1 b (e.1 a) (Fin.cast hlen.symm j)) =
              Function.update (seq e).1 b₀ ((seq e).1 a₀) := by
          calc
            _ = Function.update (fun j => e.1 (Fin.cast hlen.symm j)) b₀ (e.1 a) :=
              hupdateCast e.1 b (e.1 a)
            _ = Function.update (seq e).1 b₀ ((seq e).1 a₀) := by
              simp [seq, a₀]
        have hcastSwap :
            (fun j : Fin (moduleLength R₀ M) =>
              Function.update (Function.update e.1 b (e.1 a)) a (e.1 b)
                (Fin.cast hlen.symm j)) =
              Function.update (Function.update (seq e).1 b₀ ((seq e).1 a₀))
                a₀ ((seq e).1 b₀) := by
          calc
            _ = Function.update
                (fun j => Function.update e.1 b (e.1 a) (Fin.cast hlen.symm j))
                a₀ (e.1 b) := hupdateCast _ a (e.1 b)
            _ = Function.update (Function.update (seq e).1 b₀ ((seq e).1 a₀))
                a₀ ((seq e).1 b₀) := by rw [hcastInner]; simp [seq, b₀]
        have hswap₀ : IsAdmissibleSequence (R := R₀)
            (Function.update (Function.update (seq e).1 b₀ ((seq e).1 a₀))
              a₀ ((seq e).1 b₀)) := by
          rw [← hcastSwap]
          exact admissibleSequence_restrictScalars hκ hM eSwap
        let eSwap₀ : AdmissibleSequence R₀ M :=
          ⟨Function.update (Function.update (seq e).1 b₀ ((seq e).1 a₀))
              a₀ ((seq e).1 b₀), hswap₀⟩
        have hseqSwap : seq eSwap = eSwap₀ := Subtype.ext hcastSwap
        have hba₀ : b₀.val + 1 = a₀.val := by
          simpa [a₀, b₀] using hba
        have hcondition₀ : ∀ r₀, r₀ ∈ IsLocalRing.maximalIdeal R₀ →
            r₀ • (seq e).1 a₀ ∈ spanBefore (R := R₀) (seq e).1 b₀ := by
          intro r₀ hr₀
          have hr : algebraMap R₀ R r₀ ∈ IsLocalRing.maximalIdeal R :=
            map_nonunit (algebraMap R₀ R) r₀ hr₀
          have hm := ha (algebraMap R₀ R r₀) hr
          have hm' : (algebraMap R₀ R r₀) • e.1 a ∈
              spanBefore (R := R₀) e.1 b :=
            spanBefore_le_restrictScalars hκ e.1 e.2 b
              ((algebraMap R₀ R r₀) • e.1 a) hm
          have hspan := spanBefore_eq_cast (R := R₀) hlen e.1 b
          rw [hspan] at hm'
          simpa [seq, a₀, b₀] using hm'
        have hswapRel : DeterminantRelation
            (Finsupp.single (seq e) 1 + Finsupp.single eSwap₀ 1) :=
          DeterminantRelation.swap (seq e) a₀ b₀ hba₀ hcondition₀ hswap₀
        have htarget : Finsupp.single (seq e) 1 + Finsupp.single eSwap₀ 1 ∈
            determinantRelations R₀ M := Submodule.subset_span hswapRel
        have hfree : freeMap (Finsupp.single e 1 + Finsupp.single eSwap 1) ∈
            determinantRelations R₀ M := by
          rw [map_add, hsingle, hsingle, hseqSwap]
          simpa [ρ] using htarget
        apply hkernel
        simpa [eSwap] using hfree
  let detMap := (determinantRelations R M).liftQ qmap hrel
  have hdetSymbol (e : AdmissibleSequence R M) :
      detMap (symbol e) = symbol (seq e) := by
    change (Submodule.Quotient.mk (freeMap (Finsupp.single e 1)) : determinant R₀ M) = _
    rw [hsingle]
    simp [symbol]
  have hdimR := finrank_determinant_eq_one hM
  have hdimR₀ := finrank_determinant_eq_one
    (isFiniteLength_restrictScalars hκ hM)
  letI : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_pos (show
      0 < Module.finrank (IsLocalRing.ResidueField R) (determinant R M) by
        rw [hdimR]
        exact Nat.zero_lt_one)
  letI : Nontrivial (determinant R₀ M) :=
    Module.nontrivial_of_finrank_pos (show
      0 < Module.finrank (IsLocalRing.ResidueField R₀) (determinant R₀ M) by
        rw [hdimR₀]
        exact Nat.zero_lt_one)
  letI : IsSimpleOrder
      (Submodule (IsLocalRing.ResidueField R) (determinant R M)) :=
    is_simple_module_of_finrank_eq_one hdimR
  letI : IsSimpleModule (IsLocalRing.ResidueField R) (determinant R M) := {}
  letI : IsSimpleOrder
      (Submodule (IsLocalRing.ResidueField R₀) (determinant R₀ M)) :=
    is_simple_module_of_finrank_eq_one hdimR₀
  letI : IsSimpleModule (IsLocalRing.ResidueField R₀) (determinant R₀ M) := {}
  let eG := Classical.choose (exists_admissible_generator hM)
  have heG : Submodule.span R (Set.range eG.1) = ⊤ :=
    Classical.choose_spec (exists_admissible_generator hM)
  have hrange : Set.range (seq eG).1 = Set.range eG.1 :=
    (finCongr hlen.symm).surjective.range_comp eG.1
  have htargetGen : Submodule.span R₀ (Set.range (seq eG).1) = ⊤ := by
    rw [hrange, eq_top_iff]
    exact fun x _ => spanRange_le_restrictScalars hκ eG.1 eG.2 x (heG ▸ Submodule.mem_top)
  have hdetMapNonzero : detMap (symbol eG) ≠ 0 := by
    rw [hdetSymbol]
    exact fun hz => bot_ne_top (α := Submodule (IsLocalRing.ResidueField R₀) (determinant R₀ M))
      (by simpa [hz] using
        span_symbol_eq_top (isFiniteLength_restrictScalars hκ hM) (seq eG) htargetGen)
  have hker : detMap.ker = ⊥ :=
    (IsSimpleModule.toIsSimpleOrder.eq_bot_or_eq_top detMap.ker).resolve_right fun htop =>
      hdetMapNonzero (LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top))
  have hinj : Function.Injective detMap := LinearMap.ker_eq_bot.mp hker
  let z := detMap (symbol eG)
  have hcyc : (IsLocalRing.ResidueField R₀) ∙ z = ⊤ :=
    (IsSimpleModule.toIsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot =>
      hdetMapNonzero (Submodule.span_singleton_eq_bot.mp hbot)
  have hsurj : Function.Surjective detMap := by
    intro y
    obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp
      (show y ∈ (IsLocalRing.ResidueField R₀) ∙ z by rw [hcyc]; exact Submodule.mem_top)
    obtain ⟨c, hc⟩ := ρ.symm.surjective c₀
    refine ⟨c • symbol eG, ?_⟩
    rw [detMap.map_smulₛₗ]
    change (ρ.symm c) • detMap (symbol eG) = y
    rw [hc]
    simpa [z] using hc₀
  exact ⟨LinearEquiv.ofBijective detMap ⟨hinj, hsurj⟩, hdetSymbol⟩

/-- The canonical comparison of determinant spaces for a local ring map with unchanged
residue field. -/
@[stacks 02PC "canonical isomorphism"]
public noncomputable def determinantRestrictScalarsEquiv
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M) :
    determinant R M ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.ofBijective
      (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ).symm]
      determinant R₀ M :=
  (determinantRestrictScalarsComparisonData hκ hM).1

/-- The canonical comparison takes a determinant symbol to the symbol of the same
sequence over the smaller local ring. -/
@[stacks 02PC "symbols"]
public theorem determinantRestrictScalarsEquiv_symbol
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M]
    [IsScalarTower R₀ R M] (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M) :
    determinantRestrictScalarsEquiv hκ hM (symbol e) =
    symbol ⟨fun i : Fin (moduleLength R₀ M) ↦
      e.1 (Fin.cast (moduleLength_restrictScalars hκ hM).symm i),
      admissibleSequence_restrictScalars hκ hM e⟩ :=
  (determinantRestrictScalarsComparisonData hκ hM).2 e

/-- The canonical comparison commutes with symbol-preserving determinant maps induced
by an isomorphism of modules. -/
@[stacks 02PC "functoriality"]
public theorem determinantRestrictScalarsEquiv_natural
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {M : Type w} {N : Type x}
    [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
    [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (g : M ≃ₗ[R] N)
    (gR : determinant R M ≃ₗ[IsLocalRing.ResidueField R] determinant R N)
    (gR₀ : determinant R₀ M ≃ₗ[IsLocalRing.ResidueField R₀] determinant R₀ N)
    (hgR : ∀ e : AdmissibleSequence R M, ∃ e' : AdmissibleSequence R N,
      (∃ h : moduleLength R M = moduleLength R N,
        ∀ i, e'.1 (Fin.cast h i) = g (e.1 i)) ∧
      gR (symbol e) = symbol e')
    (hgR₀ : ∀ e : AdmissibleSequence R₀ M, ∃ e' : AdmissibleSequence R₀ N,
      (∃ h : moduleLength R₀ M = moduleLength R₀ N,
        ∀ i, e'.1 (Fin.cast h i) = g (e.1 i)) ∧
      gR₀ (symbol e) = symbol e')
    (z : determinant R M) :
    determinantRestrictScalarsEquiv hκ hN (gR z) =
      gR₀ (determinantRestrictScalarsEquiv hκ hM z) := by
  classical
  let hMlen := moduleLength_restrictScalars hκ hM
  let hNlen := moduleLength_restrictScalars hκ hN
  obtain ⟨eG, heG⟩ := exists_admissible_generator hM
  obtain ⟨c, hc⟩ := exists_smul_symbol_eq hM eG heG z
  obtain ⟨eR, ⟨hR, hRseq⟩, hgRseq⟩ := hgR eG
  let e₀ : AdmissibleSequence R₀ M :=
    ⟨fun i => eG.1 (Fin.cast hMlen.symm i),
      admissibleSequence_restrictScalars hκ hM eG⟩
  obtain ⟨eR₀, ⟨hR₀, hR₀seq⟩, hgR₀seq⟩ := hgR₀ e₀
  let eRrestrict : AdmissibleSequence R₀ N :=
    ⟨fun i => eR.1 (Fin.cast hNlen.symm i),
      admissibleSequence_restrictScalars hκ hN eR⟩
  have hidx (i : Fin (moduleLength R₀ N)) :
      Fin.cast hR (Fin.cast hMlen.symm (Fin.cast hR₀.symm i)) =
        Fin.cast hNlen.symm i := by
    apply Fin.ext
    simp
  have hseq : eRrestrict = eR₀ := by
    apply Subtype.ext
    funext i
    have hleft := hRseq (Fin.cast hMlen.symm (Fin.cast hR₀.symm i))
    rw [hidx] at hleft
    have hright := hR₀seq (Fin.cast hR₀.symm i)
    simpa [e₀] using hleft.trans hright.symm
  rw [← hc, gR.map_smul, hgRseq]
  simp only [map_smulₛₗ]
  rw [determinantRestrictScalarsEquiv_symbol hκ hN eR,
    determinantRestrictScalarsEquiv_symbol hκ hM eG, hgR₀seq, ← hseq]
  simp [eRrestrict, RingHom.id_apply]

/-- The determinant comparison respects the canonical determinant isomorphism of a
short exact sequence. -/
@[stacks 02PC "exact sequences"]
public theorem determinantRestrictScalarsEquiv_exact
    {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R]
    [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    {K : Type w} {L : Type x} {M : Type*}
    [AddCommGroup K] [Module R₀ K] [Module R K] [IsScalarTower R₀ R K]
    [AddCommGroup L] [Module R₀ L] [Module R L] [IsScalarTower R₀ R L]
    [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M)
    (a : determinant R K) (b : determinant R M) :
    determinantRestrictScalarsEquiv hκ hL
        (determinantExactSequenceMap i p hi hp hip hK hL hM (a ⊗ₜ[IsLocalRing.ResidueField R] b)) =
      determinantExactSequenceMap (i.restrictScalars R₀) (p.restrictScalars R₀)
        hi hp hip (isFiniteLength_restrictScalars hκ hK)
        (isFiniteLength_restrictScalars hκ hL)
        (isFiniteLength_restrictScalars hκ hM)
        ((determinantRestrictScalarsEquiv hκ hK a) ⊗ₜ[IsLocalRing.ResidueField R₀]
          (determinantRestrictScalarsEquiv hκ hM b)) := by
  classical
  let hKlen := moduleLength_restrictScalars hκ hK
  let hLlen := moduleLength_restrictScalars hκ hL
  let hMlen := moduleLength_restrictScalars hκ hM
  let ρ := RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ
  obtain ⟨eK, heK⟩ := exists_admissible_generator hK
  obtain ⟨eM, heM⟩ := exists_admissible_generator hM
  have hK₀ := isFiniteLength_restrictScalars hκ hK
  have hL₀ := isFiniteLength_restrictScalars hκ hL
  have hM₀ := isFiniteLength_restrictScalars hκ hM
  let eK₀ : AdmissibleSequence R₀ K :=
    ⟨fun j => eK.1 (Fin.cast hKlen.symm j),
      admissibleSequence_restrictScalars hκ hK eK⟩
  let eM₀ : AdmissibleSequence R₀ M :=
    ⟨fun j => eM.1 (Fin.cast hMlen.symm j),
      admissibleSequence_restrictScalars hκ hM eM⟩
  have heK₀ : Submodule.span R₀ (Set.range eK₀.1) = ⊤ := span_restrictScalars_eq_top hκ hK eK heK
  have heM₀ : Submodule.span R₀ (Set.range eM₀.1) = ⊤ := span_restrictScalars_eq_top hκ hM eM heM
  have hsymK := symbol_ne_zero_of_span_eq_top hK eK heK
  have hsymM := symbol_ne_zero_of_span_eq_top hM eM heM
  obtain ⟨c, hc⟩ := exists_smul_symbol_eq hK eK heK a
  obtain ⟨d, hd⟩ := exists_smul_symbol_eq hM eM heM b
  let f : Fin (moduleLength R M) → L := fun j => Classical.choose (hp (eM.1 j))
  have hf : ∀ j, p (f j) = eM.1 j := fun j => Classical.choose_spec (hp (eM.1 j))
  obtain ⟨hlenR, hadmR, hvalueR⟩ :=
    determinantExactSequenceMap_spec i p hi hp hip hK hL hM
      eK eM hsymK hsymM f hf
  let eL : AdmissibleSequence R L :=
    ⟨fun j => Fin.append (fun k => i (eK.1 k)) f (Fin.cast hlenR j), hadmR⟩
  have hvalueR' :
      determinantExactSequenceMap i p hi hp hip hK hL hM
        (symbol eK ⊗ₜ[IsLocalRing.ResidueField R] symbol eM) = symbol eL := hvalueR
  let f₀ : Fin (moduleLength R₀ M) → L :=
    fun j => f (Fin.cast hMlen.symm j)
  have hf₀ : ∀ j, (p.restrictScalars R₀) (f₀ j) = eM₀.1 j := fun j => hf _
  obtain ⟨hlenR₀, hadmR₀, hvalueR₀⟩ :=
    determinantExactSequenceMap_spec (i.restrictScalars R₀) (p.restrictScalars R₀)
      hi hp hip hK₀ hL₀ hM₀ eK₀ eM₀ (symbol_ne_zero_of_span_eq_top hK₀ eK₀ heK₀)
      (symbol_ne_zero_of_span_eq_top hM₀ eM₀ heM₀) f₀ hf₀
  let eL₀ : AdmissibleSequence R₀ L :=
    ⟨fun j => Fin.append (fun k => i (eK₀.1 k)) f₀ (Fin.cast hlenR₀ j), hadmR₀⟩
  have hvalueR₀' :
      determinantExactSequenceMap (i.restrictScalars R₀) (p.restrictScalars R₀)
        hi hp hip hK₀ hL₀ hM₀
        (symbol eK₀ ⊗ₜ[IsLocalRing.ResidueField R₀] symbol eM₀) = symbol eL₀ := hvalueR₀
  let eLrestrict : AdmissibleSequence R₀ L :=
    ⟨fun j => eL.1 (Fin.cast hLlen.symm j),
      admissibleSequence_restrictScalars hκ hL eL⟩
  let hsum : moduleLength R K + moduleLength R M =
      moduleLength R₀ K + moduleLength R₀ M := congrArg₂ Nat.add hKlen hMlen
  have htotal (j : Fin (moduleLength R₀ L)) :
      Fin.cast hlenR (Fin.cast hLlen.symm j) =
        Fin.cast hsum.symm (Fin.cast hlenR₀ j) := by
    apply Fin.ext
    simp only [Fin.val_cast]
  have happend : ∀ q : Fin (moduleLength R₀ K + moduleLength R₀ M),
      Fin.append (fun k => i (eK.1 k)) f (Fin.cast hsum.symm q) =
        Fin.append (fun k => i (eK₀.1 k)) f₀ q := by
    intro q
    induction q using Fin.addCases with
    | left j =>
        have hidx : Fin.cast hsum.symm
            (Fin.castAdd (moduleLength R₀ M) j) =
            Fin.castAdd (moduleLength R M) (Fin.cast hKlen.symm j) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_castAdd]
        rw [hidx]
        simp [eK₀, Fin.append_left]
    | right j =>
        have hidx : Fin.cast hsum.symm
            (Fin.natAdd (moduleLength R₀ K) j) =
            Fin.natAdd (moduleLength R K) (Fin.cast hMlen.symm j) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_natAdd]
          rw [← hKlen]
        rw [hidx]
        simp [f₀, Fin.append_right]
  have hconcat : eLrestrict = eL₀ := Subtype.ext <| funext fun j => by
    show Fin.append (fun k => i (eK.1 k)) f
        (Fin.cast hlenR (Fin.cast hLlen.symm j)) =
      Fin.append (fun k => i (eK₀.1 k)) f₀ (Fin.cast hlenR₀ j)
    rw [htotal j, happend]
  have htensorR :
      (c • symbol eK) ⊗ₜ[IsLocalRing.ResidueField R] (d • symbol eM) =
        (c * d) • (symbol eK ⊗ₜ[IsLocalRing.ResidueField R] symbol eM) := by
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  rw [← hc, ← hd, htensorR, map_smul, hvalueR', map_smulₛₗ,
    determinantRestrictScalarsEquiv_symbol hκ hL eL]
  simp only [map_smulₛₗ]
  rw [determinantRestrictScalarsEquiv_symbol hκ hK eK,
    determinantRestrictScalarsEquiv_symbol hκ hM eM]
  simp only [RingHom.coe_coe, map_mul, TensorProduct.tmul_smul, map_smul]
  have hinner :
      determinantExactSequenceMap (i.restrictScalars R₀) (p.restrictScalars R₀)
        hi hp hip hK₀ hL₀ hM₀
        ((ρ.symm c • symbol eK₀) ⊗ₜ[IsLocalRing.ResidueField R₀] symbol eM₀) =
        ρ.symm c • symbol eL₀ := by
    rw [← TensorProduct.smul_tmul', map_smul, hvalueR₀']
  show (ρ.symm c * ρ.symm d) • symbol eLrestrict =
    ρ.symm d •
      determinantExactSequenceMap (i.restrictScalars R₀) (p.restrictScalars R₀)
        hi hp hip hK₀ hL₀ hM₀
        ((ρ.symm c • symbol eK₀) ⊗ₜ[IsLocalRing.ResidueField R₀] symbol eM₀)
  rw [hconcat, hinner, smul_smul, mul_comm]

end Module.FiniteLength
end
