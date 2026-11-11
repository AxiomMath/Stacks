module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DeterminantLine
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DualNumberGenerator
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DualNumberIdeals

/-!
# Determinant exact-sequence maps for dual numbers

For two nonzero scalar multiples `u ε` and `v ε` acting on the dual numbers over a field, the
determinant maps associated to their image exact sequences send the tensor of the two classes
of `ε` to respectively `u⁻¹ [ε, 1]` and `v⁻¹ [ε, 1]`.

## Main definitions

* `DualNumber.dualRangeEps` is the class of `ε` in the image of multiplication by `a ε`.
* `DualNumber.dualRangeGenerator` is the canonical admissible sequence in that image.

## Main results

* `DualNumber.periodicGamma_unitMulT_first` computes the map associated to multiplication
  by `u ε`.
* `DualNumber.periodicGamma_unitMulT_second` computes the map associated to multiplication
  by `v ε`.

## Implementation notes

The endomorphisms are restricted from the dual-number ring to its coefficient field before
taking determinants, so these are `k`-linear variants of the maps in Stacks Tag 02PP. The
source's statements, over the dual-number ring, are
`DualNumber.periodicGamma_unitMulT_dualRangeSequence_first` and `_second`. The canonical
admissible sequence in each range has every entry equal to `ε`. Exactness and finite length
are passed as witnesses to `AlgebraicGeometry.periodicGamma`. The two declarations treat the two
equations separately.

## References

* [Stacks Project, Tag 02PP](https://stacks.math.columbia.edu/tag/02PP)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

open Module.FiniteLength

namespace DualNumber

universe u

/-- The class of `ε` in the image of multiplication by `a ε`. -/
def dualRangeEps (k : Type u) [Field k] (a : kˣ) :
    LinearMap.range ((unitMulT k a).restrictScalars k) :=
  ⟨DualNumber.eps, by
    change DualNumber.eps ∈ LinearMap.range (unitMulT k a)
    rw [range_unitMulT]
    exact Ideal.mem_span_singleton_self _⟩

/-- The canonical admissible sequence `ε` in the image of multiplication by `a ε`. -/
def dualRangeGenerator (k : Type u) [Field k] (a : kˣ) :
    AdmissibleSequence k (LinearMap.range ((unitMulT k a).restrictScalars k)) :=
  ⟨fun _ ↦ dualRangeEps k a, by
    intro i r hr
    rw [IsLocalRing.maximalIdeal_eq_bot, Submodule.mem_bot] at hr
    subst r
    simp⟩

/-- The class of `ε` spans the image of multiplication by `a ε`. -/
private lemma dualRangeEps_span (k : Type u) [Field k] (a : kˣ) :
    Submodule.span k ({dualRangeEps k a} : Set
      (LinearMap.range ((unitMulT k a).restrictScalars k))) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  have hxIdeal : (x : DualNumber k) ∈ Ideal.span ({DualNumber.eps} : Set (DualNumber k)) := by
    rw [← range_unitMulT]
    exact x.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxIdeal
  have hmul : c * DualNumber.eps = (c.fst : k) • DualNumber.eps := by
    rw [← c.inl_fst_add_inr_snd_eq]
    ext <;> simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]
  have hx : x = (c.fst : k) • dualRangeEps k a := Subtype.ext (hc.symm.trans hmul)
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- That image has length one over the coefficient field. -/
private lemma moduleLength_dualRange (k : Type u) [Field k] (a : kˣ) :
    moduleLength k (LinearMap.range ((unitMulT k a).restrictScalars k)) = 1 := by
  let V := LinearMap.range ((unitMulT k a).restrictScalars k)
  let e : k →ₗ[k] V := LinearMap.toSpanSingleton k V (dualRangeEps k a)
  have hsurj : Function.Surjective e := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact dualRangeEps_span k a
  have hinj : Function.Injective e := fun x y hxy ↦ by
    simpa [e, LinearMap.toSpanSingleton_apply, dualRangeEps] using
      congrArg (fun z : V ↦ (z : DualNumber k).snd) hxy
  change (Module.length k V).toNat = 1
  rw [← (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).length_eq]
  simp

/-- The canonical admissible sequence spans that image. -/
private lemma dualRangeGenerator_span (k : Type u) [Field k] (a : kˣ) :
    Submodule.span k (Set.range (dualRangeGenerator k a).1) = ⊤ := by
  have hlen := moduleLength_dualRange k a
  let j : Fin (moduleLength k (LinearMap.range ((unitMulT k a).restrictScalars k))) :=
    Fin.cast hlen.symm ⟨0, by decide⟩
  exact eq_top_iff.2 <| (dualRangeEps_span k a).ge.trans
    (Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨j, rfl⟩))

/-- The determinant map for multiplication by `a ε` sends the tensor of the two classes of `ε`
to `a⁻¹ [ε, 1]`. -/
private lemma periodicGamma_unitMulT_formula
    (k : Type u) [Field k] (a b : kˣ)
    (hba : Function.Exact ((unitMulT k b).restrictScalars k)
      ((unitMulT k a).restrictScalars k))
    (hM : IsFiniteLength k (DualNumber k)) :
    AlgebraicGeometry.periodicGamma ((unitMulT k a).restrictScalars k)
        ((unitMulT k b).restrictScalars k) hba hM
        (symbol (dualRangeGenerator k b) ⊗ₜ[IsLocalRing.ResidueField k]
          symbol (dualRangeGenerator k a)) =
      IsLocalRing.residue k a⁻¹ • symbol (dualGenerator k) := by
  let ψ := (unitMulT k b).restrictScalars k
  let φ := (unitMulT k a).restrictScalars k
  let K := LinearMap.range ψ
  let N := LinearMap.range φ
  have hlenK := moduleLength_dualRange k b
  have hlenN := moduleLength_dualRange k a
  have hK : IsFiniteLength k K := hM.of_injective K.subtype_injective
  have hN : IsFiniteLength k N := hM.of_injective N.subtype_injective
  have hlenK' : moduleLength k K = 1 := by simpa [K, ψ] using hlenK
  have hKsym : symbol (dualRangeGenerator k b) ≠ 0 :=
    AlgebraicGeometry.symbol_ne_zero_of_span_top hK _ (dualRangeGenerator_span k b)
  have hNsym : symbol (dualRangeGenerator k a) ≠ 0 :=
    AlgebraicGeometry.symbol_ne_zero_of_span_top hN _ (dualRangeGenerator_span k a)
  let i : K →ₗ[k] DualNumber k := K.subtype
  let p : DualNumber k →ₗ[k] N := φ.rangeRestrict
  have hi : Function.Injective i := Submodule.injective_subtype K
  have hp : Function.Surjective p :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ)
  have hip : Function.Exact i p := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact hba.linearMap_ker_eq
  have hspec := determinantExactSequenceMap_spec i p hi hp hip hK hM
    (hM.of_surjective hp)
  let lift : Fin (moduleLength k N) → DualNumber k := fun _ ↦
    algebraMap k (DualNumber k) (a⁻¹ : k)
  have hlift : ∀ j, p (lift j) = (dualRangeGenerator k a).1 j := by
    intro j
    apply Subtype.ext
    change unitMulT k a (algebraMap k (DualNumber k) (a⁻¹ : k)) = DualNumber.eps
    simp [unitMulT, mul_comm, ← map_mul]
  obtain ⟨hlen, hadm, heq⟩ := hspec (dualRangeGenerator k b)
    (dualRangeGenerator k a) hKsym hNsym lift hlift
  change AlgebraicGeometry.periodicGamma φ ψ hba hM
      (symbol (dualRangeGenerator k b) ⊗ₜ[IsLocalRing.ResidueField k]
        symbol (dualRangeGenerator k a)) =
      symbol ⟨fun j ↦ Fin.append (fun q ↦ i ((dualRangeGenerator k b).1 q))
        lift (Fin.cast hlen j), hadm⟩ at heq
  let iOne : Fin (moduleLength k (DualNumber k)) :=
    Fin.cast (dualNumberModuleLength k).symm ⟨1, by decide⟩
  have hentry : (dualGenerator k).1 iOne = 1 := by
    simp [iOne, dualGenerator, dualGeneratorEntries]
    rfl
  let hKzero : Fin (moduleLength k K) := Fin.cast hlenK.symm ⟨0, by decide⟩
  let hNzero : Fin (moduleLength k N) := Fin.cast hlenN.symm ⟨0, by decide⟩
  have hfun : (fun j : Fin (moduleLength k (DualNumber k)) ↦
      Fin.append (fun q ↦ i ((dualRangeGenerator k b).1 q)) lift (Fin.cast hlen j)) =
      Function.update (dualGenerator k).1 iOne
        (algebraMap k (DualNumber k) (a⁻¹ : k)) := by
    funext j
    let j2 : Fin 2 := Fin.cast (dualNumberModuleLength k) j
    have hj : j = Fin.cast (dualNumberModuleLength k).symm j2 := Fin.ext (by simp [j2])
    rw [hj]
    have hjval : j2.val = 0 ∨ j2.val = 1 := by omega
    rcases hjval with hjval | hjval
    · have hj2 : j2 = ⟨0, by decide⟩ := Fin.ext hjval
      rw [hj2]
      have hcast : Fin.cast hlen (Fin.cast (dualNumberModuleLength k).symm ⟨0, by decide⟩) =
          Fin.castAdd (moduleLength k N) hKzero := Fin.ext (by simp [hKzero])
      rw [hcast, Fin.append_left]
      have hne : (Fin.cast (dualNumberModuleLength k).symm ⟨0, by decide⟩ :
          Fin (moduleLength k (DualNumber k))) ≠ iOne := by
        intro h
        have hv := congrArg Fin.val h
        simp [iOne] at hv
      change DualNumber.eps = Function.update (dualGenerator k).1 iOne
        (algebraMap k (DualNumber k) (a⁻¹ : k))
          (Fin.cast (dualNumberModuleLength k).symm ⟨0, by decide⟩)
      rw [Function.update_of_ne hne]
      simp [dualGenerator, dualGeneratorEntries]
    · have hj2 : j2 = ⟨1, by decide⟩ := Fin.ext hjval
      rw [hj2]
      have hcast : Fin.cast hlen (Fin.cast (dualNumberModuleLength k).symm ⟨1, by decide⟩) =
          Fin.natAdd (moduleLength k K) hNzero := Fin.ext (by simp [hNzero, hlenK'])
      rw [hcast, Fin.append_right]
      have heqOne : (Fin.cast (dualNumberModuleLength k).symm ⟨1, by decide⟩ :
          Fin (moduleLength k (DualNumber k))) = iOne := Fin.ext (by simp [iOne])
      rw [heqOne, Function.update_self]
  have hadm' : IsAdmissibleSequence (R := k)
      (Function.update (dualGenerator k).1 iOne
        (algebraMap k (DualNumber k) (a⁻¹ : k))) := hfun ▸ hadm
  let updated : AdmissibleSequence k (DualNumber k) :=
    ⟨Function.update (dualGenerator k).1 iOne
      (algebraMap k (DualNumber k) (a⁻¹ : k)), hadm'⟩
  have hsymbolChange := symbol_unitChange (dualGenerator k) iOne a
    (algebraMap k (DualNumber k) (a⁻¹ : k)) 0 (by
      rw [hentry]
      simp only [add_zero]
      rw [Algebra.smul_def (R := k) (A := DualNumber k)]
      rw [← map_mul]
      simp) (by simp)
    hadm'
  have hconcat : (⟨fun j : Fin (moduleLength k (DualNumber k)) ↦
      Fin.append (fun q ↦ i ((dualRangeGenerator k b).1 q)) lift (Fin.cast hlen j),
      hadm⟩ : AdmissibleSequence k (DualNumber k)) = updated := Subtype.ext hfun
  have hscalar : IsLocalRing.residue k a⁻¹ * IsLocalRing.residue k a = 1 := by simp
  have hchange : symbol updated = IsLocalRing.residue k a⁻¹ • symbol (dualGenerator k) := by
    have hc := congrArg (fun z ↦ IsLocalRing.residue k a⁻¹ • z) hsymbolChange
    rw [smul_smul, hscalar, one_smul] at hc
    exact hc.symm
  calc
    AlgebraicGeometry.periodicGamma φ ψ hba hM
        (symbol (dualRangeGenerator k b) ⊗ₜ[IsLocalRing.ResidueField k]
          symbol (dualRangeGenerator k a)) =
        symbol updated :=
      heq.trans (congrArg symbol hconcat)
    _ = IsLocalRing.residue k a⁻¹ • symbol (dualGenerator k) := hchange

/-- The `k`-linear determinant map for multiplication by `u ε`, with the endomorphisms restricted
to the coefficient field, sends the tensor of the two classes of `ε` to `u⁻¹ [ε, 1]`. This is the
`k`-linear variant of the computation in Stacks Tag 02PP; the statement over the dual numbers is
`DualNumber.periodicGamma_unitMulT_dualRangeSequence_first`. -/
theorem periodicGamma_unitMulT_first
    (k : Type u) [Field k] (u v : kˣ)
    (hvu : Function.Exact ((unitMulT k v).restrictScalars k)
      ((unitMulT k u).restrictScalars k))
    (hM : IsFiniteLength k (DualNumber k)) :
      AlgebraicGeometry.periodicGamma ((unitMulT k u).restrictScalars k)
          ((unitMulT k v).restrictScalars k) hvu hM
          (symbol (dualRangeGenerator k v) ⊗ₜ[IsLocalRing.ResidueField k]
            symbol (dualRangeGenerator k u)) =
      IsLocalRing.residue k u⁻¹ • symbol (dualGenerator k) :=
  periodicGamma_unitMulT_formula k u v hvu hM

/-- The `k`-linear determinant map for multiplication by `v ε`, with the endomorphisms restricted
to the coefficient field, sends the tensor of the two classes of `ε` to `v⁻¹ [ε, 1]`. This is the
`k`-linear variant of the computation in Stacks Tag 02PP; the statement over the dual numbers is
`DualNumber.periodicGamma_unitMulT_dualRangeSequence_second`. -/
theorem periodicGamma_unitMulT_second
    (k : Type u) [Field k] (u v : kˣ)
    (huv : Function.Exact ((unitMulT k u).restrictScalars k)
      ((unitMulT k v).restrictScalars k))
    (hM : IsFiniteLength k (DualNumber k)) :
      AlgebraicGeometry.periodicGamma ((unitMulT k v).restrictScalars k)
          ((unitMulT k u).restrictScalars k) huv hM
          (symbol (dualRangeGenerator k u) ⊗ₜ[IsLocalRing.ResidueField k]
            symbol (dualRangeGenerator k v)) =
      IsLocalRing.residue k v⁻¹ • symbol (dualGenerator k) :=
  periodicGamma_unitMulT_formula k v u huv hM

end DualNumber
