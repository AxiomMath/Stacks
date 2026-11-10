module

public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DeterminantLine
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DualNumberIdeals

/-!
# The periodic determinant of multiplication on dual numbers

For a field `k`, let `k[ε]` be the dual-number ring. Multiplication by two nonzero scalar
multiples `u ε` and `v ε` gives an exact two-periodic complex. Its periodic determinant is
`-u / v` under the canonical map from `k` to the residue field of `k[ε]`.

## Main results

* `DualNumber.periodicDeterminant_unitMulT` computes the periodic determinant of the two
  multiplications.

## Implementation notes

The exactness and finite-length witnesses are included in the conclusion, rather than assumed,
since they hold for every field and both units. The equality is expressed in the residue field
of `k[ε]` by mapping `-u / v` from `k`; this is the canonical identification of that residue
field with `k` in the source.

## References

* [Stacks Project, Tag 02PP](https://stacks.math.columbia.edu/tag/02PP)
-/

@[expose] public section

open scoped TensorProduct

open Module.FiniteLength AlgebraicGeometry

namespace DualNumber

universe u v

/-- The dual numbers have finite length over themselves. -/
private lemma dualNumber_isFiniteLength (k : Type u) [Field k] :
    IsFiniteLength (DualNumber k) (DualNumber k) := by
  have : IsArtinianRing (DualNumber k) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨2, by
      rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow]
      simp [pow_two]⟩
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The image of multiplication by a unit multiple of `ε` is a simple module. -/
private lemma dualRange_isSimple (k : Type u) [Field k] (a : kˣ) :
    IsSimpleModule (DualNumber k) (LinearMap.range (unitMulT k a)) := by
  let R := DualNumber k
  let f : R →ₗ[R] R := unitMulT k (1 : kˣ)
  have hker : LinearMap.ker f = IsLocalRing.maximalIdeal R := by
    rw [ker_unitMulT, DualNumber.maximalIdeal_eq_span_singleton_eps]
  have hsimpleQuot : IsSimpleModule R (R ⧸ LinearMap.ker f) := by
    rw [hker]
    change IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R)
    rw [isSimpleModule_iff_quot_maximal]
    exact ⟨IsLocalRing.maximalIdeal R,
      IsLocalRing.maximalIdeal.isMaximal R,
      ⟨LinearEquiv.refl _ _⟩⟩
  exact (LinearEquiv.ofEq _ _ (by rw [range_unitMulT, range_unitMulT])).isSimpleModule_iff.mp
    ((LinearMap.quotKerEquivRange f).isSimpleModule_iff.mp hsimpleQuot)

/-- That image has length one. -/
private lemma dualRange_moduleLength (k : Type u) [Field k] (a : kˣ) :
    moduleLength (DualNumber k) (LinearMap.range (unitMulT k a)) = 1 := by
  change (Module.length (DualNumber k) (LinearMap.range (unitMulT k a))).toNat = 1
  rw [Module.length_eq_one_iff.mpr (dualRange_isSimple k a)]
  rfl

/-- That image has finite length. -/
private lemma dualRange_isFiniteLength (k : Type u) [Field k] (a : kˣ) :
    IsFiniteLength (DualNumber k) (LinearMap.range (unitMulT k a)) :=
  (dualNumber_isFiniteLength k).of_surjective
    (LinearMap.surjective_rangeRestrict (unitMulT k a))

/-- Two multiplications by unit multiples of `ε` form an exact sequence. -/
private lemma dual_unitMulT_exact (k : Type u) [Field k] (a b : kˣ) :
    Function.Exact (unitMulT k a) (unitMulT k b) := by
  rw [LinearMap.exact_iff, ker_unitMulT, range_unitMulT]

/-- The inclusion of the image of `f` and the corestriction of `g` are exact when `f, g` are. -/
private lemma exact_subtype_rangeRestrict {R M N P : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g) :
    Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact h.linearMap_ker_eq

/-- The span of the entries before the first index is zero. -/
private lemma spanBefore_zero_eq_bot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (h : 0 < n) : spanBefore (R := R) e ⟨0, h⟩ = ⊥ := by
  have hIio : Set.Iio (⟨0, h⟩ : Fin n) = ∅ := by
    ext j
    simp [Fin.lt_def]
  change Submodule.span R (e '' Set.Iio ⟨0, h⟩) = ⊥
  rw [hIio]
  simp

/-- The dual numbers have length two over themselves. -/
private lemma dualNumber_moduleLength (k : Type u) [Field k] :
    moduleLength (DualNumber k) (DualNumber k) = 2 := by
  let R := DualNumber k
  let f : R →ₗ[R] R := unitMulT k (1 : kˣ)
  have hex := exact_subtype_rangeRestrict (dual_unitMulT_exact k 1 1)
  have hlen : Module.length R R =
      Module.length R (LinearMap.range f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype _) f.surjective_rangeRestrict
      hex
  change (Module.length R R).toNat = 2
  rw [hlen, Module.length_eq_one_iff.mpr (dualRange_isSimple k 1)]
  norm_num

/-- A non-unit of the dual numbers annihilates `ε`. -/
private lemma dual_mul_eps_eq_zero (k : Type u) [Field k] {r : DualNumber k}
    (hr : r ∈ IsLocalRing.maximalIdeal (DualNumber k)) :
    r * DualNumber.eps = 0 := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps] at hr
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
  rw [hc, mul_right_comm, DualNumber.eps_mul_eps, zero_mul]

/-- The one-term admissible sequence `ε` in the image of multiplication by `a ε`. -/
private def dualRangeSequence (k : Type u) [Field k] (a : kˣ) :
    AdmissibleSequence (DualNumber k) (LinearMap.range (unitMulT k a)) := by
  refine ⟨fun _ ↦ ⟨DualNumber.eps, ?_⟩, ?_⟩
  · rw [range_unitMulT]
    exact Ideal.mem_span_singleton_self _
  · intro i r hr
    rcases i with ⟨i, hi⟩
    rw [dualRange_moduleLength] at hi
    interval_cases i
    rw [spanBefore_zero_eq_bot _ (by simp [dualRange_moduleLength]), Submodule.mem_bot]
    exact Subtype.ext (by simpa [smul_eq_mul] using dual_mul_eps_eq_zero k hr)

/-- That sequence spans the image. -/
private lemma dualRangeSequence_span_top (k : Type u) [Field k] (a : kˣ) :
    Submodule.span (DualNumber k)
      (Set.range (dualRangeSequence k a).1) = ⊤ := by
  apply top_unique
  intro x _
  have hxspan : (x : DualNumber k) ∈ Ideal.span {DualNumber.eps} := by
    simpa [range_unitMulT] using x.property
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hxspan
  let e : LinearMap.range (unitMulT k a) := dualRangeSequence k a |>.1 ⟨0, by
    simp [dualRange_moduleLength]⟩
  have hxeq : x = c • e := by
    apply Subtype.ext
    change (x : DualNumber k) = c * DualNumber.eps
    simpa [e, smul_eq_mul, mul_comm] using hc
  rw [hxeq]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨_, rfl⟩)

/-- The admissible sequence `(ε, 1)` of the dual numbers over themselves. -/
private noncomputable def dualNumberSequence (k : Type u) [Field k] :
    AdmissibleSequence (DualNumber k) (DualNumber k) := by
  let f : Fin (moduleLength (DualNumber k) (DualNumber k)) → DualNumber k :=
    fun i ↦ if i.val = 0 then DualNumber.eps else 1
  refine ⟨f, ?_⟩
  intro i r hr
  rcases i with ⟨i, hi⟩
  have hn := dualNumber_moduleLength k
  rw [hn] at hi
  interval_cases i
  · rw [spanBefore_zero_eq_bot _ (by simp [hn]), Submodule.mem_bot]
    simpa [f, smul_eq_mul] using dual_mul_eps_eq_zero k hr
  · have himage : f '' Set.Iio (⟨1, by simp [hn]⟩ :
        Fin (moduleLength (DualNumber k) (DualNumber k))) = {DualNumber.eps} := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        change j < ⟨1, by simp [hn]⟩ at hj
        have hj' : j.val < 1 := Fin.lt_def.mp hj
        have hj0 : j.val = 0 := by omega
        simp [f, hj0]
      · rintro rfl
        refine ⟨⟨0, by simp [hn]⟩, ?_, ?_⟩
        · change (⟨0, by simp [hn]⟩ :
            Fin (moduleLength (DualNumber k) (DualNumber k))) < _
          exact Fin.lt_def.mpr (by norm_num)
        · simp [f]
    have hspan : spanBefore (R := DualNumber k) f ⟨1, by simp [hn]⟩ =
        Ideal.span {DualNumber.eps} := by
      change Submodule.span (DualNumber k) (f '' Set.Iio ⟨1, by simp [hn]⟩) = _
      rw [himage]
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps] at hr
    rw [hspan]
    simpa [f, smul_eq_mul] using hr

/-- Two linear maps agree when they agree on a generator. -/
private lemma linearMap_eq_of_span_singleton {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (z : V) (hz : Submodule.span K {z} = ⊤) (f g : V →ₗ[K] W)
    (hfg : f z = g z) : f = g := by
  ext x
  have hx : x ∈ Submodule.span K {z} := by simp [hz]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, map_smul, hfg]

/-- The tensor of two generators generates the tensor product. -/
private lemma tensor_symbols_span {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (v : V) (w : W) (hv : Submodule.span K {v} = ⊤)
    (hw : Submodule.span K {w} = ⊤) :
    Submodule.span K {v ⊗ₜ[K] w} = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← TensorProduct.span_tmul_eq_top K V W, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (by simp [hv] : a ∈ Submodule.span K {v})
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp (by simp [hw] : b ∈ Submodule.span K {w})
  exact Submodule.mem_span_singleton.mpr ⟨c * d, (TensorProduct.smul_tmul_smul c d v w).symm⟩

/-- Multiplication by `a ε` sends the image of `a⁻¹` to `ε`. -/
private lemma unitMulT_preimage (k : Type u) [Field k] (a : kˣ) :
    unitMulT k a (algebraMap k (DualNumber k) ((a⁻¹ : kˣ) : k)) = DualNumber.eps := by
  rw [unitMulT, LinearMap.mulLeft_apply, mul_right_comm, ← map_mul]
  simp

/-- The determinant map of the dual-number complex, evaluated on the tensor of the two canonical
symbols. -/
private lemma periodicGamma_dual_value (k : Type u) [Field k] (a b : kˣ)
    (hba : Function.Exact (unitMulT k b) (unitMulT k a))
    (hM : IsFiniteLength (DualNumber k) (DualNumber k)) :
    periodicGamma (unitMulT k a) (unitMulT k b) hba hM
      (symbol (dualRangeSequence k b) ⊗ₜ[IsLocalRing.ResidueField (DualNumber k)]
        symbol (dualRangeSequence k a)) =
      IsLocalRing.residue (DualNumber k)
        ((Units.map (algebraMap k (DualNumber k)).toMonoidHom a⁻¹ : (DualNumber k)ˣ) :
          DualNumber k) •
          symbol (dualNumberSequence k) := by
  classical
  let R := DualNumber k
  let eA := dualRangeSequence k a
  let eB := dualRangeSequence k b
  have hA := dualRange_isFiniteLength k a
  have hB := dualRange_isFiniteLength k b
  let i := (LinearMap.range (unitMulT k b)).subtype
  let p := (unitMulT k a).rangeRestrict
  have hip : Function.Exact i p := exact_subtype_rangeRestrict hba
  let f : Fin (moduleLength R (LinearMap.range (unitMulT k a))) → R :=
    fun _ ↦ algebraMap k R ((a⁻¹ : kˣ) : k)
  obtain ⟨hlen, hadm, hval⟩ := determinantExactSequenceMap_spec i p
    (Submodule.injective_subtype _) (unitMulT k a).surjective_rangeRestrict
    hip hB hM hA eB eA
    (symbol_ne_zero_of_span_top hB eB (dualRangeSequence_span_top k b))
    (symbol_ne_zero_of_span_top hA eA (dualRangeSequence_span_top k a)) f
    fun _ ↦ Subtype.ext (unitMulT_preimage k a)
  let out : Fin (moduleLength R R) → R :=
    fun j ↦ Fin.append (fun q ↦ (i (eB.1 q) : R)) f (Fin.cast hlen j)
  let eOut : AdmissibleSequence R R := ⟨out, hadm⟩
  let j0 : Fin (moduleLength R R) := ⟨0, by rw [dualNumber_moduleLength]; omega⟩
  let j1 : Fin (moduleLength R R) := ⟨1, by rw [dualNumber_moduleLength]; omega⟩
  let qB0 : Fin (moduleLength R (LinearMap.range (unitMulT k b))) :=
    ⟨0, by rw [dualRange_moduleLength]; omega⟩
  let qA0 : Fin (moduleLength R (LinearMap.range (unitMulT k a))) :=
    ⟨0, by rw [dualRange_moduleLength]; omega⟩
  have hcast0 : Fin.cast hlen j0 =
      Fin.castAdd (moduleLength R (LinearMap.range (unitMulT k a))) qB0 :=
    Fin.ext (by simp [j0, qB0])
  have hcast1 : Fin.cast hlen j1 =
      Fin.natAdd (moduleLength R (LinearMap.range (unitMulT k b))) qA0 := by
    have hcastb : moduleLength R (LinearMap.range (unitMulT k b)) = 1 :=
      dualRange_moduleLength k b
    exact Fin.ext (by simp [j1, qA0, hcastb])
  have hentry : out j1 = algebraMap k R ((a⁻¹ : kˣ) : k) := by
    change Fin.append (fun q ↦ (i (eB.1 q) : R)) f (Fin.cast hlen j1) = _
    rw [hcast1, Fin.append_right]
  have hupdate : Function.update out j1 1 = (dualNumberSequence k).1 := by
    funext j
    rcases j with ⟨j, hj⟩
    rw [dualNumber_moduleLength] at hj
    interval_cases j
    · change Function.update out j1 1 j0 = (dualNumberSequence k).1 j0
      rw [Function.update_of_ne (fun h ↦ by simpa [j0, j1] using congrArg Fin.val h)]
      change Fin.append (fun q ↦ (i (eB.1 q) : R)) f (Fin.cast hlen j0) = _
      rw [hcast0, Fin.append_left]
      change DualNumber.eps = (dualNumberSequence k).1 j0
      simp [dualNumberSequence, j0]
    · change Function.update out j1 1 j1 = (dualNumberSequence k).1 j1
      rw [Function.update_self]
      change (1 : DualNumber k) = (dualNumberSequence k).1 j1
      simp [dualNumberSequence, j1]
  have hupdAdm : IsAdmissibleSequence (R := R) (Function.update out j1 1) :=
    hupdate ▸ (dualNumberSequence k).property
  have hchange := symbol_unitChange eOut j1
    (Units.map (algebraMap k R).toMonoidHom a⁻¹) (1 : R) (0 : R)
    (by simpa [smul_eq_mul, Units.coe_map] using hentry) (by simp)
    hupdAdm
  change periodicGamma (unitMulT k a) (unitMulT k b) hba hM
      (symbol eB ⊗ₜ[IsLocalRing.ResidueField R] symbol eA) = _
  rw [periodicGamma, hval]
  change symbol eOut = _
  rw [hchange, show (⟨Function.update eOut.1 j1 1, hupdAdm⟩ : AdmissibleSequence R R) =
    dualNumberSequence k from Subtype.ext hupdate]

/-- **Stacks Project, Tag 02PP.** The periodic determinant of multiplication by `u ε` and
`v ε` on the dual numbers is `-u / v`. -/
@[stacks 02PP "dual_periodic_determinant"]
theorem periodicDeterminant_unitMulT (k : Type u) [Field k] (u v : kˣ) :
    ∃ (hφψ : Function.Exact (unitMulT k u) (unitMulT k v))
      (hψφ : Function.Exact (unitMulT k v) (unitMulT k u))
      (hM : IsFiniteLength (DualNumber k) (DualNumber k)),
      periodicDeterminant (unitMulT k u) (unitMulT k v) hφψ hψφ hM =
        Units.map (algebraMap k (IsLocalRing.ResidueField (DualNumber k))) (-u / v) := by
  refine ⟨dual_unitMulT_exact k u v, dual_unitMulT_exact k v u,
    dualNumber_isFiniteLength k, ?_⟩
  let R := DualNumber k
  let κ := IsLocalRing.ResidueField R
  let hu := dualRange_isFiniteLength k u
  let hv := dualRange_isFiniteLength k v
  let hM := dualNumber_isFiniteLength k
  let eu := dualRangeSequence k u
  let ev := dualRangeSequence k v
  let d : κˣ := Units.map (algebraMap k κ).toMonoidHom (-u / v)
  have hd : IsPeriodicDeterminant (unitMulT k u) (unitMulT k v)
      (dual_unitMulT_exact k u v) (dual_unitMulT_exact k v u) hM d := by
    change periodicGamma (unitMulT k v) (unitMulT k u)
        (dual_unitMulT_exact k u v) hM ∘ₗ
        (TensorProduct.comm κ (determinant R (LinearMap.range (unitMulT k v)))
          (determinant R (LinearMap.range (unitMulT k u)))).toLinearMap =
      (((-1 : κ) ^ (moduleLength R (LinearMap.range (unitMulT k u)) *
        moduleLength R (LinearMap.range (unitMulT k v))) * (d : κ)) •
        periodicGamma (unitMulT k u) (unitMulT k v)
          (dual_unitMulT_exact k v u) hM)
    let z := symbol ev ⊗ₜ[κ] symbol eu
    have hspanV := span_symbol_eq_top hv ev (dualRangeSequence_span_top k v)
    have hspanU := span_symbol_eq_top hu eu (dualRangeSequence_span_top k u)
    have hzspan := tensor_symbols_span (symbol ev) (symbol eu) hspanV hspanU
    apply linearMap_eq_of_span_singleton z hzspan
    change periodicGamma (unitMulT k v) (unitMulT k u)
        (dual_unitMulT_exact k u v) hM
        (TensorProduct.comm κ (determinant R (LinearMap.range (unitMulT k v)))
          (determinant R (LinearMap.range (unitMulT k u))) z) =
      (((-1 : κ) ^ (moduleLength R (LinearMap.range (unitMulT k u)) *
        moduleLength R (LinearMap.range (unitMulT k v))) * (d : κ)) •
        periodicGamma (unitMulT k u) (unitMulT k v)
          (dual_unitMulT_exact k v u) hM z)
    rw [TensorProduct.comm_tmul, periodicGamma_dual_value k v u (dual_unitMulT_exact k u v) hM,
      periodicGamma_dual_value k u v (dual_unitMulT_exact k v u) hM]
    simp only [smul_smul]
    have hres (x : k) : IsLocalRing.residue R (algebraMap k R x) = algebraMap k κ x := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply k R κ x).symm
    have hcoeff :
        (((-1 : κ) ^ (moduleLength R (LinearMap.range (unitMulT k u)) *
            moduleLength R (LinearMap.range (unitMulT k v)))) * (d : κ)) *
          IsLocalRing.residue R
            (Units.map (algebraMap k R).toMonoidHom u⁻¹ : R) =
        IsLocalRing.residue R
          (Units.map (algebraMap k R).toMonoidHom v⁻¹ : R) := by
      rw [dualRange_moduleLength, dualRange_moduleLength]
      simp only [Units.coe_map]
      change (((-1 : κ) ^ (1 * 1) * (d : κ)) *
          IsLocalRing.residue R (algebraMap k R ((u⁻¹ : kˣ) : k))) =
        IsLocalRing.residue R (algebraMap k R ((v⁻¹ : kˣ) : k))
      rw [hres ((u⁻¹ : kˣ) : k), hres ((v⁻¹ : kˣ) : k)]
      simp [d, Units.coe_map]
      have hu0 : algebraMap k κ (u : k) ≠ 0 := by simp
      have hv0 : algebraMap k κ (v : k) ≠ 0 := by simp
      field_simp [hu0, hv0]
    rw [hcoeff]
  exact (eq_periodicDeterminant (unitMulT k u) (unitMulT k v) (dual_unitMulT_exact k u v)
    (dual_unitMulT_exact k v u) hM hd).symm

end DualNumber
