module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.ZMod
public import StacksFrontier.NumberTheory.TraceFormula.ConstantCharpoly.ClosedConditions
public import StacksFrontier.NumberTheory.TraceFormula.ConstantCharpoly.UnipotentBlocks
public import StacksFrontier.NumberTheory.TraceFormula.GeometricMonodromyFiniteness

/-!
# Finite image from constant characteristic polynomials and finite `H¹`

Let `G` be a compact topological group and `ρ : G → GL_n(F_ℓ[[t]])` a continuous
representation, `F_ℓ[[t]]` with its coefficientwise topology. Suppose that the characteristic
polynomial of every `ρ(g)` has coefficients in `F_ℓ`, and that every open subgroup of `G` has
only finitely many continuous characters with values in `F_ℓ`. Then the image of `ρ` is finite.

## Proof

Let `F` be the fraction field of `F_ℓ[[t]]`.
1. The subgroup `Γ` of elements reducing to `1` modulo `t` is open, and its elements are
   unipotent: their characteristic polynomial is that of their reduction, `(X - 1)ⁿ`.
2. Over a finite extension `E` of `F` there are an invertible `P` and a grading `d` for which
   every `P⁻¹ ρ(g) P`, `g ∈ Γ`, is graded upper triangular with diagonal blocks irreducible over
   an algebraic closure (`exists_finiteDimensional_isGradedUpper_absolutelyIrreducible`). As
   the family is unipotent, Burnside's theorem and the trace form make the diagonal blocks the
   identity blocks.
3. By induction on `s ≥ 1` there is an open subgroup `N_s ⊆ Γ` on which the entries `(i, j)` of
   `P⁻¹ ρ(g) P` with `d j - d i < s` are those of the identity. On `N_s` the entries with
   `d j - d i = s` add up under products, so their coordinates in an `F`-basis of `E`, with
   denominators cleared, are continuous homomorphisms to `F_ℓ[[t]]`, and their coefficients
   are continuous `F_ℓ`-characters. There are finitely many of those, so these entries take
   finitely many values on `N_s`, and the subgroup where they vanish has finite index; it is
   closed, hence open, and is `N_{s+1}`.
4. For `s` beyond the spread of `d`, `ρ` is trivial on `N_s`, which is open; a homomorphism from
   a compact group trivial on an open subgroup has finite image.

## Main definitions

* `Stacks.TraceFormula.conjMatrix`: the conjugate `P⁻¹ A P` over `E` of a matrix `A` over `R`.
* `Stacks.TraceFormula.conjEntry`: an entry of `P⁻¹ B P`, as an `F`-linear functional of `B`.

## Main results

* `Stacks.TraceFormula.mul_apply_eq_add_of_forall_lt`: entries at the first nontrivial level of
  products of level-`s` unipotent matrices add up.
* `Stacks.TraceFormula.exists_isOpen_forall_conjMatrix_apply_eq_one_apply`: the inductive step.
* `Stacks.TraceFormula.finite_range_of_charpoly_coeff_mem_range_C`: the theorem.
-/

@[expose] public noncomputable section

open Matrix Stacks.EtaleCohomology
open scoped PowerSeries.WithPiTopology

namespace Stacks.TraceFormula

section Conj

variable {R : Type*} (F : Type*) {E ι : Type*} [CommRing R] [Field F] [Algebra R F] [Field E]
  [Algebra F E] [Fintype ι] [DecidableEq ι]

/-- The conjugate `P⁻¹ A P` over `E` of a matrix `A` over `R`, for `R → F → E`. -/
def conjMatrix (P : (Matrix ι ι E)ˣ) (A : Matrix ι ι R) : Matrix ι ι E :=
  (↑P⁻¹ : Matrix ι ι E) * (A.map (algebraMap R F)).map (algebraMap F E) * (↑P : Matrix ι ι E)

variable {F}

/-- Conjugation is multiplicative. -/
theorem conjMatrix_mul (P : (Matrix ι ι E)ˣ) (A B : Matrix ι ι R) :
    conjMatrix F P (A * B) = conjMatrix F P A * conjMatrix F P B := by
  simp only [conjMatrix, Matrix.map_mul, mul_assoc, Units.mul_inv_cancel_left]

/-- Conjugation fixes the identity. -/
theorem conjMatrix_one (P : (Matrix ι ι E)ˣ) : conjMatrix F P (1 : Matrix ι ι R) = 1 := by
  simp [conjMatrix]

/-- The conjugate of a unipotent matrix is unipotent. -/
theorem isNilpotent_conjMatrix_sub_one (P : (Matrix ι ι E)ˣ) {A : Matrix ι ι R}
    (h : IsNilpotent (A - 1)) : IsNilpotent (conjMatrix F P A - 1) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  set φ : Matrix ι ι R →+* Matrix ι ι E :=
    (algebraMap F E).mapMatrix.comp (algebraMap R F).mapMatrix with hφ
  have : conjMatrix F P A - 1 = (↑P⁻¹ : Matrix ι ι E) * φ (A - 1) * (↑P : Matrix ι ι E) := by
    rw [map_sub, map_one, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rfl
  rw [this, Units.conj_pow', ← map_pow, hm, map_zero, mul_zero, zero_mul]

/-- A matrix over `R ⊆ F` whose conjugate is the identity is the identity. -/
theorem eq_one_of_conjMatrix_eq_one (hinj : Function.Injective (algebraMap R F))
    (P : (Matrix ι ι E)ˣ) {A : Matrix ι ι R} (h : conjMatrix F P A = 1) : A = 1 := by
  have h1 : (A.map (algebraMap R F)).map (algebraMap F E) = 1 := by
    have : (A.map (algebraMap R F)).map (algebraMap F E) =
        (↑P : Matrix ι ι E) * conjMatrix F P A * (↑P⁻¹ : Matrix ι ι E) := by
      simp [conjMatrix, mul_assoc]
    rw [this, h, mul_one, Units.mul_inv]
  rw [Matrix.map_map] at h1
  exact Matrix.map_injective ((algebraMap F E).injective.comp hinj)
    (h1.trans (Matrix.map_one _ (by simp) (by simp)).symm)

/-- The entry `(i, j)` of `P⁻¹ B P`, as an `F`-linear functional of the matrix `B` over `F`. -/
def conjEntry (P : (Matrix ι ι E)ˣ) (i j : ι) : Matrix ι ι F →ₗ[F] E where
  toFun B := ((↑P⁻¹ : Matrix ι ι E) * B.map (algebraMap F E) * (↑P : Matrix ι ι E)) i j
  map_add' B C := by simp [Matrix.map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    have : (c • B).map (algebraMap F E) = c • B.map (algebraMap F E) := by
      ext k l
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        map_mul, Algebra.smul_def]
    simp only [RingHom.id_apply, this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]

/-- The functional `conjEntry` evaluated on a matrix over `R` is an entry of `conjMatrix`. -/
theorem conjEntry_map_algebraMap (P : (Matrix ι ι E)ˣ) (i j : ι) (A : Matrix ι ι R) :
    conjEntry P i j (A.map (algebraMap R F)) = conjMatrix F P A i j :=
  rfl

end Conj

/-- **The first nontrivial level of a product adds up.** Let `s ≥ 1`, and let `S` and `U` agree
with the identity matrix at all entries `(i, j)` with `d j - d i < s`. Then at an entry with
`d j - d i = s` the product `S * U` is the sum `S i j + U i j`: every other term of the
product vanishes. -/
theorem mul_apply_eq_add_of_forall_lt {ι S' : Type*} [Fintype ι] [DecidableEq ι] [Ring S']
    {S U : Matrix ι ι S'} {d : ι → ℤ} {s : ℤ} (hs : 1 ≤ s)
    (hS : ∀ i j, d j - d i < s → S i j = (1 : Matrix ι ι S') i j)
    (hU : ∀ i j, d j - d i < s → U i j = (1 : Matrix ι ι S') i j) {i j : ι}
    (hij : d j - d i = s) : (S * U) i j = S i j + U i j := by
  have hne : i ≠ j := by
    rintro rfl
    omega
  have h0 : ∀ k, k ≠ i ∧ k ≠ j → S i k * U k j = 0 := by
    intro k hk
    by_cases h : d k - d i < s
    · rw [hS i k h, Matrix.one_apply_ne (Ne.symm hk.1), zero_mul]
    · rw [hU k j (by omega), Matrix.one_apply_ne hk.2, mul_zero]
  rw [Matrix.mul_apply, Fintype.sum_eq_add i j hne h0, hS i i (by omega), hU j j (by omega),
    Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul, mul_one, add_comm]

section Step

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ℓ n : ℕ}
  [Fact ℓ.Prime] {F E : Type*} [Field F] [Algebra (PowerSeries (ZMod ℓ)) F]
  [IsFractionRing (PowerSeries (ZMod ℓ)) F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- **The inductive step.** Let `H` be an open subgroup of `G` with finitely many continuous
`F_ℓ`-characters, on which the entries `(i, j)` of `P⁻¹ ρ(g) P` with `d j - d i < s` are those
of the identity, `s ≥ 1`. Then there is an open subgroup `H' ≤ H` on which this holds for
`d j - d i < s + 1`. The entries with `d j - d i = s` define a homomorphism from `H` to an
additive group, which is determined by the continuous `F_ℓ`-characters of `H` it induces through
coordinates and coefficients, so has finite image; its kernel is closed of finite index. -/
theorem exists_isOpen_forall_conjMatrix_apply_eq_one_apply
    (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (P : (Matrix (Fin n) (Fin n) E)ˣ) (d : Fin n → ℤ) (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hH1 : Finite {χ : H →* Multiplicative (ZMod ℓ) // Continuous χ}) {s : ℤ} (hs : 1 ≤ s)
    (hlev : ∀ g ∈ H, ∀ i j, d j - d i < s →
      conjMatrix F P (ρ g).val i j = (1 : Matrix (Fin n) (Fin n) E) i j) :
    ∃ H' : Subgroup G, IsOpen (H' : Set G) ∧ H' ≤ H ∧ ∀ g ∈ H', ∀ i j, d j - d i < s + 1 →
      conjMatrix F P (ρ g).val i j = (1 : Matrix (Fin n) (Fin n) E) i j := by
  classical
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hcont : Continuous fun g : H => (ρ g).val :=
    Units.continuous_val.comp (ρ.continuous.comp continuous_subtype_val)
  have hne : ∀ i j, d j - d i = s → i ≠ j := by
    rintro i j h rfl
    omega
  have hadd : ∀ g ∈ H, ∀ h ∈ H, ∀ i j, d j - d i = s → conjMatrix F P (ρ (g * h)).val i j =
      conjMatrix F P (ρ g).val i j + conjMatrix F P (ρ h).val i j := by
    intro g hg h hh i j hij
    rw [map_mul, Units.val_mul, conjMatrix_mul]
    exact mul_apply_eq_add_of_forall_lt hs (hlev g hg) (hlev h hh) hij
  let θ : H →* Multiplicative (Fin n → Fin n → E) :=
    { toFun := fun g => Multiplicative.ofAdd fun i j =>
        if d j - d i = s then conjMatrix F P (ρ g).val i j else 0
      map_one' := by
        rw [ofAdd_eq_one]
        funext i j
        simp only [OneMemClass.coe_one, map_one, Units.val_one, conjMatrix_one, Pi.zero_apply]
        split_ifs with h
        · exact Matrix.one_apply_ne (hne i j h)
        · rfl
      map_mul' := fun g h => by
        rw [← ofAdd_add]
        congr 1
        funext i j
        simp only [Subgroup.coe_mul, Pi.add_apply]
        split_ifs with hij
        · exact hadd g g.2 h h.2 i j hij
        · rw [add_zero] }
  have hθ : ∀ g : H, θ g = Multiplicative.ofAdd fun i j =>
      if d j - d i = s then conjMatrix F P (ρ g).val i j else 0 := fun g => rfl
  set b := Module.finBasis F E
  choose r hr f hf hfL using fun (i j : Fin n) (k : Fin (Module.finrank F E)) =>
    exists_continuous_algebraMap_eq_mul (R := PowerSeries (ZMod ℓ))
      ((b.coord k).comp (conjEntry P i j))
  have hfL' : ∀ i j k A, algebraMap _ F (f i j k A) =
      algebraMap _ F (r i j k) * b.repr (conjMatrix F P A i j) k := fun i j k A => by
    rw [hfL]
    rfl
  have hfadd : ∀ g ∈ H, ∀ h ∈ H, ∀ i j, d j - d i = s → ∀ k,
      f i j k (ρ (g * h)).val = f i j k (ρ g).val + f i j k (ρ h).val := by
    intro g hg h hh i j hij k
    apply IsFractionRing.injective (PowerSeries (ZMod ℓ)) F
    rw [map_add, hfL', hfL', hfL', hadd g hg h hh i j hij, map_add, Finsupp.add_apply, mul_add]
  have hχ : ∀ i j, d j - d i = s → ∀ k (m : ℕ),
      ∃ χ : {χ : H →* Multiplicative (ZMod ℓ) // Continuous χ}, ∀ g : H,
        Multiplicative.toAdd (χ.1 g) = PowerSeries.coeff m (f i j k (ρ g).val) := by
    intro i j hij k m
    have h0 : f i j k (ρ 1).val = 0 := by
      have := hfadd 1 H.one_mem 1 H.one_mem i j hij k
      rw [mul_one] at this
      exact left_eq_add.mp this
    let χ : H →* Multiplicative (ZMod ℓ) :=
      { toFun := fun g => Multiplicative.ofAdd (PowerSeries.coeff m (f i j k (ρ g).val))
        map_one' := by rw [OneMemClass.coe_one, h0, map_zero, ofAdd_zero]
        map_mul' := fun g h => by
          simp only [Subgroup.coe_mul, hfadd g g.2 h h.2 i j hij k, map_add, ofAdd_add] }
    exact ⟨⟨χ, continuous_ofAdd.comp ((PowerSeries.WithPiTopology.continuous_coeff _ m).comp
      ((hf i j k).comp hcont))⟩, fun g => rfl⟩
  have hfib : ∀ g h : H, (∀ χ : {χ : H →* Multiplicative (ZMod ℓ) // Continuous χ},
      χ.1 g = χ.1 h) → θ g = θ h := by
    intro g h hgh
    rw [hθ, hθ]
    congr 1
    funext i j
    split_ifs with hij
    · refine b.ext_elem_iff.mpr fun k => ?_
      have hf_eq : f i j k (ρ g).val = f i j k (ρ h).val := by
        ext m
        obtain ⟨χ, hχv⟩ := hχ i j hij k m
        rw [← hχv, ← hχv, hgh χ]
      have h2 := congrArg (algebraMap _ F) hf_eq
      rw [hfL', hfL'] at h2
      exact mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hr i j k)) h2
    · rfl
  let ev : H → ({χ : H →* Multiplicative (ZMod ℓ) // Continuous χ} → Multiplicative (ZMod ℓ)) :=
    fun g χ => χ.1 g
  have hfin : (Set.range θ).Finite := by
    refine (Set.finite_range fun v : Set.range ev => θ v.2.choose).subset ?_
    rintro _ ⟨g, rfl⟩
    have hspec := (⟨ev g, g, rfl⟩ : Set.range ev).2.choose_spec
    exact ⟨⟨ev g, g, rfl⟩, hfib _ _ fun χ => congrFun hspec χ⟩
  have : Finite θ.range := hfin.to_subtype
  have := Subgroup.finiteIndex_ker θ
  have hker : ∀ g : H, g ∈ θ.ker ↔ ∀ i j, d j - d i = s → conjMatrix F P (ρ g).val i j = 0 := by
    intro g
    rw [MonoidHom.mem_ker, hθ, ofAdd_eq_one, funext_iff]
    simp only [funext_iff, Pi.zero_apply, ite_eq_right_iff]
  have hclosed : IsClosed (θ.ker : Set H) := by
    have : (θ.ker : Set H) = ⋂ i, ⋂ j, ⋂ (_ : d j - d i = s), (fun g : H => (ρ g).val) ⁻¹'
        {A | conjEntry P i j (A.map (algebraMap (PowerSeries (ZMod ℓ)) F)) = 0} := by
      ext g
      simp only [SetLike.mem_coe, hker, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        conjEntry_map_algebraMap]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      (isClosed_setOf_map_eq_of_finiteDimensional _ _).preimage hcont
  have hopen : IsOpen (θ.ker : Set H) := θ.ker.isOpen_of_isClosed_of_finiteIndex hclosed
  refine ⟨θ.ker.map H.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isOpenMap_subtype_val _ hopen
  · rintro _ ⟨g, hg, rfl⟩ i j hij
    rcases lt_or_eq_of_le (show d j - d i ≤ s by omega) with h | h
    · exact hlev g g.2 i j h
    · rw [Matrix.one_apply_ne (hne i j h)]
      exact (hker g).mp hg i j h

end Step

/-- **A compact group representation over `F_ℓ[[t]]` with constant characteristic polynomials
and finite `H¹` on open subgroups has finite image.** Let `G` be a compact topological group and
`ρ : G → GL_n(F_ℓ[[t]])` continuous, `F_ℓ[[t]]` with its coefficientwise topology. If the
characteristic polynomial of every `ρ(g)` has its coefficients in `F_ℓ`, and every open subgroup
of `G` has finitely many continuous characters with values in `F_ℓ`, then the image of `ρ` is
finite. -/
theorem finite_range_of_charpoly_coeff_mem_range_C
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {ℓ n : ℕ} [Fact ℓ.Prime]
    (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hchar : ∀ g i, ((ρ g : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i) ∈
      Set.range (PowerSeries.C (R := ZMod ℓ)))
    (hH1 : ∀ V : Subgroup G, IsOpen (V : Set G) →
      Finite {χ : V →* Multiplicative (ZMod ℓ) // Continuous χ}) :
    (Set.range ρ).Finite := by
  classical
  let F := FractionRing (PowerSeries (ZMod ℓ))
  let red : Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)) →*
      Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ) :=
    Units.map (PowerSeries.constantCoeff (R := ZMod ℓ)).mapMatrix.toMonoidHom
  let Γ : Subgroup G := (red.comp ρ.toMonoidHom).ker
  have hmemΓ : ∀ g, g ∈ Γ ↔ (ρ g).val.map PowerSeries.constantCoeff = 1 := by
    intro g
    simp [Γ, red, Units.ext_iff]
  have hΓopen : IsOpen (Γ : Set G) := by
    have : (Γ : Set G) = ⋂ i, ⋂ j, (fun g => PowerSeries.constantCoeff ((ρ g).val i j)) ⁻¹'
        {(1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) i j} := by
      ext g
      simp only [SetLike.mem_coe, hmemΓ, Set.mem_iInter, Set.mem_preimage,
        Set.mem_singleton_iff, ← Matrix.ext_iff, Matrix.map_apply]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_discrete _).preimage ((PowerSeries.WithPiTopology.continuous_constantCoeff _).comp
        ((Units.continuous_val.comp ρ.continuous).matrix_elem i j))
  have hnilR : ∀ g ∈ Γ, ((ρ g).val - 1) ^ n = 0 := fun g hg => by
    simpa using pow_sub_one_eq_zero_of_charpoly_coeff_mem_range_C (hchar g) ((hmemΓ g).mp hg)
  obtain ⟨E, _, P, d, hup, hirr⟩ :=
    exists_finiteDimensional_isGradedUpper_absolutelyIrreducible (K := AlgebraicClosure F)
      (fun g : Γ => (ρ g).val.map (algebraMap (PowerSeries (ZMod ℓ)) F))
  have hlev1 : ∀ g ∈ Γ, ∀ i j, d j - d i < 1 →
      conjMatrix F P (ρ g).val i j = (1 : Matrix (Fin n) (Fin n) E) i j := by
    intro g hg i j hij
    rcases lt_or_eq_of_le (show d j - d i ≤ 0 by omega) with h | h
    · rw [Matrix.one_apply_ne (by rintro rfl; simp at h)]
      exact hup ⟨g, hg⟩ i j (by omega)
    · exact apply_eq_one_apply_of_isNilpotent_sub_one (K := AlgebraicClosure F)
        (fun a : Γ => conjMatrix F P (ρ a).val) d (fun a => hup a)
        (fun a b => ⟨a * b, by rw [Subgroup.coe_mul, map_mul, Units.val_mul, conjMatrix_mul]⟩)
        ⟨1, by rw [OneMemClass.coe_one, map_one, Units.val_one, conjMatrix_one]⟩
        (fun a => isNilpotent_conjMatrix_sub_one P ⟨n, hnilR a a.2⟩) hirr ⟨g, hg⟩ (by omega)
  have key : ∀ k : ℕ, ∃ H : Subgroup G, IsOpen (H : Set G) ∧ ∀ g ∈ H, ∀ i j,
      d j - d i < (k : ℤ) + 1 →
        conjMatrix F P (ρ g).val i j = (1 : Matrix (Fin n) (Fin n) E) i j := by
    intro k
    induction k with
    | zero => exact ⟨Γ, hΓopen, fun g hg i j hij => hlev1 g hg i j (by simpa using hij)⟩
    | succ k ih =>
      obtain ⟨H, hH, hlev⟩ := ih
      obtain ⟨H', hH', -, hlev'⟩ := exists_isOpen_forall_conjMatrix_apply_eq_one_apply ρ P d H hH
        (hH1 H hH) (s := (k : ℤ) + 1) (by omega) hlev
      exact ⟨H', hH', fun g hg i j hij => hlev' g hg i j (by push_cast at hij; omega)⟩
  obtain ⟨H, hH, hlev⟩ := key (Finset.univ.sup fun p : Fin n × Fin n => (d p.2 - d p.1).toNat)
  refine (finite_range_of_isOpen_le_ker ρ.toMonoidHom hH fun g hg => ?_).subset ?_
  · rw [MonoidHom.mem_ker]
    have hT : conjMatrix F P (ρ g).val = 1 := by
      refine Matrix.ext fun i j => hlev g hg i j ?_
      have : (d j - d i).toNat ≤ Finset.univ.sup fun p : Fin n × Fin n => (d p.2 - d p.1).toNat :=
        Finset.le_sup (f := fun p : Fin n × Fin n => (d p.2 - d p.1).toNat)
          (Finset.mem_univ (i, j))
      omega
    exact Units.ext (eq_one_of_conjMatrix_eq_one (IsFractionRing.injective _ F) P hT)
  · rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩

end Stacks.TraceFormula

end
