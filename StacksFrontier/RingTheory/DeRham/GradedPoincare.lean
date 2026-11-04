module

public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.DifferentialDegree
public import StacksFrontier.RingTheory.DeRham.PolynomialAlgEquivQuasiIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded Poincaré lemma

Let `R` be a commutative ring and `T = ⊕_{n ≥ 0} T_n` an `ℕ`-graded `R`-algebra containing `ℚ`,
and let `S → T → S` be maps of `R`-algebras composing to the identity, with `S` mapping onto
`T_0` and `T → S` killing `T_n` for `n > 0`. Then the restriction of forms
`Ω^•_{S/R} → Ω^•_{T/R}` is a homotopy equivalence of complexes of `R`-modules, with homotopy
inverse the restriction along `T → S` (`GradedDeRham.Retraction.homotopyEquiv`).

The Euler derivation `E` (`a ↦ n a` on `T_n`) lifts to a `T`-linear form on `Ω_{T/R}`, and
contraction with it is an operator `ι_E : Ω^{p+1}_{T/R} → Ω^p_{T/R}`. Cartan's formula says that
`L_E = ι_E ∘ d + d ∘ ι_E` acts on the weight-`w` forms of [Stacks, Tag 0FU9] as multiplication by
`w` (`GradedDeRham.cartan_of_mem`). So `w⁻¹ ι_E` contracts the weight-`w` part for `w > 0`, while
the weight-zero part is the image of `Ω^•_{S/R}`.

## Main definitions

* `GradedDeRham.eulerDerivation`: the Euler derivation of an `ℕ`-graded algebra.
* `GradedDeRham.eulerContraction`: contraction with the Euler vector field.
* `GradedDeRham.cartan`: the operator `ι_E ∘ d + d ∘ ι_E`.
* `GradedDeRham.homotopyMap`: `w⁻¹ ι_E` on the weight-`w` forms.
* `GradedDeRham.Retraction`: the hypotheses on `S → T → S`.

## Main results

* `GradedDeRham.cartan_of_mem`: Cartan's formula on the weight-`w` forms.
* `GradedDeRham.Retraction.homotopyEquiv`: **the graded Poincaré lemma**.
* `GradedDeRham.Retraction.quasiIso`: the same, as a quasi-isomorphism.

## References

* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace GradedDeRham

section Euler

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
  (gr : ℕ → Submodule R T) [GradedAlgebra gr]

/-- The Euler operator `∑ aₙ ↦ ∑ n aₙ` of an `ℕ`-graded algebra, as an `R`-linear map. -/
def eulerLinearMap : T →ₗ[R] T :=
  DirectSum.toModule R ℕ T (fun n => n • (gr n).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv gr).toLinearMap

/-- The Euler operator acts on `T_n` as multiplication by `n`. -/
theorem eulerLinearMap_of_mem {n : ℕ} {a : T} (h : a ∈ gr n) : eulerLinearMap gr a = n • a := by
  rw [eulerLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem gr h,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

/-- **The Euler derivation** of an `ℕ`-graded algebra: `a ↦ n a` on `T_n`. -/
def eulerDerivation : Derivation R T T :=
  Derivation.mk' (eulerLinearMap gr) fun a b => by
    induction a using DirectSum.Decomposition.inductionOn gr with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_smul, smul_add]; abel
    | @homogeneous m a =>
      induction b using DirectSum.Decomposition.inductionOn gr with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb', add_smul, smul_add]; abel
      | @homogeneous n b =>
        have hab : (a : T) * b ∈ gr (m + n) := SetLike.GradedMul.mul_mem a.2 b.2
        rw [eulerLinearMap_of_mem gr hab, eulerLinearMap_of_mem gr a.2,
          eulerLinearMap_of_mem gr b.2, smul_eq_mul, smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
          nsmul_eq_mul, Nat.cast_add]
        ring

/-- The Euler derivation acts on `T_n` as multiplication by `n`. -/
theorem eulerDerivation_of_mem {n : ℕ} {a : T} (h : a ∈ gr n) :
    eulerDerivation gr a = n • a :=
  eulerLinearMap_of_mem gr h

end Euler

section Cartan

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
  (gr : ℕ → Submodule R T) [GradedAlgebra gr]

/-- The `T`-linear form `Ω_{T/R} → T` lifting the Euler derivation, `d b ↦ E b`. -/
def eulerForm : Ω[T⁄R] →ₗ[T] T :=
  (eulerDerivation gr).liftKaehlerDifferential

/-- The Euler form sends `d b` to `E b`. -/
@[simp]
theorem eulerForm_D (b : T) : eulerForm gr (D R T b) = eulerDerivation gr b :=
  Derivation.liftKaehlerDifferential_comp_D _ b

/-- **Contraction with the Euler vector field**, `ι_E : Ω^{p+1}_{T/R} → Ω^p_{T/R}`. -/
@[sga "7 XI 1.1" "special case"]
def eulerContraction (p : ℕ) : ⋀[T]^(p + 1) (Ω[T⁄R]) →ₗ[T] ⋀[T]^p (Ω[T⁄R]) :=
  exteriorPower.contraction (eulerForm gr) p

/-- **The Lie derivative along the Euler vector field**, by Cartan's formula:
`L_E = ι_E ∘ d + d ∘ ι_E` on `Ω^p_{T/R}` (only the first term in degree `0`). -/
def cartan : (p : ℕ) → ⋀[T]^p (Ω[T⁄R]) →ₗ[R] ⋀[T]^p (Ω[T⁄R])
  | 0 => (eulerContraction gr 0).restrictScalars R ∘ₗ deRhamDifferential (A := R) 0
  | p + 1 => (eulerContraction gr (p + 1)).restrictScalars R ∘ₗ
        deRhamDifferential (A := R) (p + 1) +
      deRhamDifferential (A := R) p ∘ₗ (eulerContraction gr p).restrictScalars R

/-- In degree `0`, `L_E ω = ι_E (d ω)`. -/
theorem cartan_zero_apply (ω : ⋀[T]^0 (Ω[T⁄R])) :
    cartan gr 0 ω = eulerContraction gr 0 (deRhamDifferential (A := R) 0 ω) := rfl

/-- In degree `p + 1`, `L_E ω = ι_E (d ω) + d (ι_E ω)`. -/
theorem cartan_succ_apply (p : ℕ) (ω : ⋀[T]^(p + 1) (Ω[T⁄R])) :
    cartan gr (p + 1) ω = eulerContraction gr (p + 1) (deRhamDifferential (A := R) (p + 1) ω) +
      deRhamDifferential (A := R) p (eulerContraction gr p ω) := rfl

/-- For a `0`-form `ω`, `ι_E (e ∧ ω) = E(e) ω`, where `E(e)` is `eulerForm gr e`. -/
theorem eulerContraction_wedgeLeft_zero (e : Ω[T⁄R]) (ω : ⋀[T]^0 (Ω[T⁄R])) :
    eulerContraction gr 0 (exteriorPower.wedgeLeft e 0 ω) = eulerForm gr e • ω :=
  LinearMap.congr_fun (exteriorPower.contraction_comp_wedgeLeft_zero (eulerForm gr) e) ω

/-- The Koszul identity `ι_E (e ∧ ω) = E(e) ω - e ∧ ι_E ω`, where `E(e)` is `eulerForm gr e`. -/
theorem eulerContraction_wedgeLeft_succ (p : ℕ) (e : Ω[T⁄R]) (ω : ⋀[T]^(p + 1) (Ω[T⁄R])) :
    eulerContraction gr (p + 1) (exteriorPower.wedgeLeft e (p + 1) ω) =
      eulerForm gr e • ω - exteriorPower.wedgeLeft e p (eulerContraction gr p ω) := by
  have h := LinearMap.congr_fun
    (exteriorPower.contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction (eulerForm gr) e p) ω
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq] at h
  exact eq_sub_of_add_eq h

/-- `L_E (b ω) = E(b) ω + b L_E ω`. -/
theorem cartan_smul (p : ℕ) (b : T) (ω : ⋀[T]^p (Ω[T⁄R])) :
    cartan gr p (b • ω) = eulerDerivation gr b • ω + b • cartan gr p ω := by
  cases p with
  | zero =>
    rw [cartan_zero_apply, cartan_zero_apply, deRhamDifferential_smul, map_add,
      eulerContraction_wedgeLeft_zero, eulerForm_D, map_smul]
  | succ p =>
    rw [cartan_succ_apply, cartan_succ_apply, deRhamDifferential_smul, map_add,
      eulerContraction_wedgeLeft_succ, eulerForm_D, map_smul, map_smul (eulerContraction gr p),
      deRhamDifferential_smul, smul_add]
    abel

/-- `L_E (d b ∧ ω) = d(E b) ∧ ω + d b ∧ L_E ω`. -/
theorem cartan_wedgeLeft (p : ℕ) (b : T) (ω : ⋀[T]^p (Ω[T⁄R])) :
    cartan gr (p + 1) (exteriorPower.wedgeLeft (D R T b) p ω) =
      exteriorPower.wedgeLeft (D R T (eulerDerivation gr b)) p ω +
        exteriorPower.wedgeLeft (D R T b) p (cartan gr p ω) := by
  rw [cartan_succ_apply, deRhamDifferential_wedgeLeft_D, map_neg,
    eulerContraction_wedgeLeft_succ, eulerForm_D]
  cases p with
  | zero =>
    rw [eulerContraction_wedgeLeft_zero, eulerForm_D, deRhamDifferential_smul,
      cartan_zero_apply]
    abel
  | succ q =>
    rw [eulerContraction_wedgeLeft_succ, eulerForm_D, map_sub, deRhamDifferential_smul,
      deRhamDifferential_wedgeLeft_D, cartan_succ_apply, map_add]
    abel

/-- On a wedge `d a₁ ∧ ⋯ ∧ d a_p` of homogeneous elements, `L_E` is multiplication by the
sum of their degrees. -/
theorem cartan_ιMulti (p : ℕ) (degree : Fin p → ℕ) (a : ∀ i, gr (degree i)) :
    cartan gr p (exteriorPower.ιMulti T p fun i ↦ D R T (a i : T)) =
      (∑ i, degree i) • exteriorPower.ιMulti T p fun i ↦ D R T (a i : T) := by
  induction p with
  | zero =>
    have h := deRhamDifferential_smul_ιMulti_D (A := R) (B := T) 0 (fun _ ↦ (1 : T))
    simp only [one_smul, Derivation.map_one_eq_zero] at h
    have h0 : (exteriorPower.ιMulti T (0 + 1) fun _ : Fin (0 + 1) ↦ (0 : Ω[T⁄R])) = 0 :=
      (exteriorPower.ιMulti T (0 + 1)).map_coord_zero 0 rfl
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_smul, cartan_zero_apply,
      Subsingleton.elim (fun i : Fin 0 ↦ D R T (a i : T)) (fun _ ↦ 0), h, h0, map_zero]
  | succ p ih =>
    have hsplit : (exteriorPower.ιMulti T (p + 1) fun i ↦ D R T (a i : T)) =
        exteriorPower.wedgeLeft (D R T (a 0 : T)) p
          (exteriorPower.ιMulti T p fun i ↦ D R T (a i.succ : T)) := by
      rw [exteriorPower.wedgeLeft_ιMulti]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    rw [hsplit, cartan_wedgeLeft, ih (fun i ↦ degree i.succ) (fun i ↦ a i.succ),
      eulerDerivation_of_mem gr (a 0).2, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul T (degree 0), exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
      Fin.sum_univ_succ, add_smul, Nat.cast_smul_eq_nsmul]

/-- On a generator `a₀ · d a₁ ∧ ⋯ ∧ d a_p` of homogeneous elements, `L_E` is multiplication by
the sum of their degrees. -/
theorem cartan_smul_ιMulti (p : ℕ) (degree : Fin (p + 1) → ℕ) (a : ∀ i, gr (degree i)) :
    cartan gr p ((a 0 : T) • exteriorPower.ιMulti T p fun i ↦ D R T (a i.succ : T)) =
      (∑ i, degree i) • ((a 0 : T) • exteriorPower.ιMulti T p fun i ↦ D R T (a i.succ : T)) := by
  rw [cartan_smul, cartan_ιMulti gr p (fun i ↦ degree i.succ) (fun i ↦ a i.succ),
    eulerDerivation_of_mem gr (a 0).2, Fin.sum_univ_succ, add_smul, smul_assoc,
    smul_comm (a 0 : T)]

/-- **Cartan's formula for the Euler vector field**: on the weight-`w` forms,
`ι_E ∘ d + d ∘ ι_E = w`. -/
theorem cartan_of_mem (p w : ℕ) {x : ⋀[T]^p (Ω[T⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p w) : cartan gr p x = w • x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨degree, a, rfl, rfl⟩ := hx
    exact cartan_smul_ιMulti gr p degree a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

end Cartan

section Homotopy

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
  (gr : ℕ → Submodule R T) [GradedAlgebra gr]

/-- `Ω^p_{T/R}` is the internal direct sum of its weight components. -/
theorem isInternal_forms (p : ℕ) :
    DirectSum.IsInternal (gradedDifferentialFormComponent gr p) :=
  isInternal_gradedDifferentialFormComponent gr (DirectSum.Decomposition.isInternal gr) p

/-- The decomposition of `Ω^p_{T/R}` into its weight components, as a linear equivalence. -/
def formsDecomposition (p : ℕ) :
    (DirectSum ℕ fun w ↦ gradedDifferentialFormComponent gr p w) ≃ₗ[R] ⋀[T]^p (Ω[T⁄R]) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (isInternal_forms gr p)

/-- The decomposition of a form of weight `w` is concentrated in the component `w`. -/
theorem formsDecomposition_symm_of_mem (p w : ℕ) {x : ⋀[T]^p (Ω[T⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p w) :
    (formsDecomposition gr p).symm x = DirectSum.of _ w ⟨x, hx⟩ :=
  (formsDecomposition gr p).symm_apply_eq.2 (DirectSum.coeLinearMap_of _ w ⟨x, hx⟩).symm

/-- The de Rham differential preserves the weight of a form. -/
theorem deRhamDifferential_mem (p w : ℕ) {x : ⋀[T]^p (Ω[T⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p w) :
    deRhamDifferential (A := R) p x ∈ gradedDifferentialFormComponent gr (p + 1) w :=
  deRhamDifferential_maps_gradedDifferentialFormComponent gr SetLike.GradedOne.one_mem p w
    (deRhamDifferential (A := R) p) (deRhamDifferential_smul_ιMulti_D p)
    (Submodule.mem_map_of_mem hx)

variable [Algebra ℚ T]

/-- **The homotopy operator of the graded Poincaré lemma**: `w⁻¹ ι_E` on the weight-`w` part
of `Ω^{p+1}_{T/R}` (and `0` on the weight-zero part). -/
def homotopyMap (p : ℕ) : ⋀[T]^(p + 1) (Ω[T⁄R]) →ₗ[R] ⋀[T]^p (Ω[T⁄R]) :=
  DirectSum.toModule R ℕ _ (fun w ↦
      DistribSMul.toLinearMap R _ (algebraMap ℚ T (w : ℚ)⁻¹) ∘ₗ
        (eulerContraction gr p).restrictScalars R ∘ₗ
          (gradedDifferentialFormComponent gr (p + 1) w).subtype) ∘ₗ
    (formsDecomposition gr (p + 1)).symm.toLinearMap

/-- On a form of weight `w`, `homotopyMap gr p` is `w⁻¹ ι_E`. -/
theorem homotopyMap_of_mem (p w : ℕ) {x : ⋀[T]^(p + 1) (Ω[T⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr (p + 1) w) :
    homotopyMap gr p x = algebraMap ℚ T (w : ℚ)⁻¹ • eulerContraction gr p x := by
  rw [homotopyMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    formsDecomposition_symm_of_mem gr (p + 1) w hx, ← DirectSum.lof_eq_of R,
    DirectSum.toModule_lof]
  rfl

/-- The de Rham differential commutes with multiplication by a rational number. -/
theorem deRhamDifferential_algebraMap_rat_smul (p : ℕ) (q : ℚ) (x : ⋀[T]^p (Ω[T⁄R])) :
    deRhamDifferential (A := R) p (algebraMap ℚ T q • x) =
      algebraMap ℚ T q • deRhamDifferential (A := R) p x := by
  rw [deRhamDifferential_smul, D_algebraMap_rat, exteriorPower.wedgeLeft_zero,
    LinearMap.zero_apply, zero_add]

/-- For `w > 0` and a `T`-module `M`, `w⁻¹ • (w • x) = x`. -/
theorem rat_inv_smul_nsmul (w : ℕ) (hw : 0 < w) {M : Type*} [AddCommGroup M] [Module T M]
    (x : M) : algebraMap ℚ T (w : ℚ)⁻¹ • (w • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul T w, smul_smul, ← map_natCast (algebraMap ℚ T) w, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast hw.ne'), map_one, one_smul]

end Homotopy

section Retraction

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra T S] [IsScalarTower R T S]
  (gr : ℕ → Submodule R T) [GradedAlgebra gr]

/-- The standing hypotheses of the graded Poincaré lemma: `S → T → S` is the identity, `T_0` is
the image of `S`, and `T → S` kills the forms of positive weight. -/
structure Retraction : Prop where
  /-- `S → T → S` is the identity. -/
  retract : ∀ s : S, algebraMap T S (algebraMap S T s) = s
  /-- Every element of `T_0` comes from `S`. -/
  degreeZero : ∀ t ∈ gr 0, ∃ s : S, algebraMap S T s = t
  /-- `T → S` kills `T_n` for `n > 0`. -/
  positive : ∀ n, 0 < n → ∀ t ∈ gr n, algebraMap T S t = 0

variable {gr}

omit [IsScalarTower R S T] [GradedAlgebra gr] in
/-- `T → S` kills the forms of positive weight. -/
theorem Retraction.mapExteriorPower_eq_zero (h : Retraction (S := S) gr) (p w : ℕ) (hw : 0 < w)
    {x : ⋀[T]^p (Ω[T⁄R])} (hx : x ∈ gradedDifferentialFormComponent gr p w) :
    mapExteriorPower R T S p x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨degree, a, rfl, rfl⟩ := hx
    rw [mapExteriorPower_smul_ιMulti_D R T S p (fun i ↦ (a i : T))]
    obtain ⟨i, hi⟩ : ∃ i, 0 < degree i := by
      by_contra! hne
      exact hw.ne' (Finset.sum_eq_zero fun i _ ↦ Nat.le_zero.1 (hne i))
    refine Fin.cases (motive := fun i ↦ 0 < degree i → _) ?_ (fun j hj ↦ ?_) i hi
    · intro h0
      rw [h.positive _ h0 _ (a 0).2, zero_smul]
    · rw [(exteriorPower.ιMulti S p).map_coord_zero j (by
        simp [h.positive _ hj _ (a j.succ).2]), smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower, hx, smul_zero]

omit [GradedAlgebra gr] in
/-- `S → T` followed by `T → S` is the identity on the weight-zero forms. -/
theorem Retraction.mapExteriorPower_mapExteriorPower (h : Retraction (S := S) gr) (p : ℕ)
    {x : ⋀[T]^p (Ω[T⁄R])} (hx : x ∈ gradedDifferentialFormComponent gr p 0) :
    mapExteriorPower R S T p (mapExteriorPower R T S p x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨degree, a, hdeg, rfl⟩ := hx
    have hd : ∀ i, degree i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff.1 hdeg.symm) i (Finset.mem_univ i)
    have hb : ∀ i, algebraMap S T (algebraMap T S (a i : T)) = a i := by
      intro i
      have hai : (a i : T) ∈ gr 0 := by
        convert (a i).2 using 2
        exact (hd i).symm
      obtain ⟨s, hs⟩ := h.degreeZero _ hai
      rw [← hs, h.retract]
    rw [mapExteriorPower_smul_ιMulti_D R T S p (fun i ↦ (a i : T)),
      mapExteriorPower_smul_ιMulti_D R S T p (fun i ↦ algebraMap T S (a i : T))]
    simp only [hb]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hx]

variable [Algebra ℚ T]

/-- On a weight-`w` form, `w⁻¹ L_E` plus the retraction projection is the identity. -/
private theorem Retraction.rat_inv_smul_cartan_add (h : Retraction (S := S) gr) (p w : ℕ)
    {x : ⋀[T]^p (Ω[T⁄R])} (hx : x ∈ gradedDifferentialFormComponent gr p w) :
    algebraMap ℚ T (w : ℚ)⁻¹ • cartan gr p x +
        mapExteriorPower R S T p (mapExteriorPower R T S p x) = x := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [h.mapExteriorPower_mapExteriorPower p hx]
  · rw [h.mapExteriorPower_eq_zero p w hw hx, map_zero, add_zero, cartan_of_mem gr p w hx,
      rat_inv_smul_nsmul w hw]

/-- The homotopy identity in degree zero, on one weight component. -/
theorem Retraction.comm_zero_of_mem (h : Retraction (S := S) gr) (w : ℕ)
    {x : ⋀[T]^0 (Ω[T⁄R])} (hx : x ∈ gradedDifferentialFormComponent gr 0 w) :
    homotopyMap gr 0 (deRhamDifferential (A := R) 0 x) +
        mapExteriorPower R S T 0 (mapExteriorPower R T S 0 x) = x := by
  rw [homotopyMap_of_mem gr 0 w (deRhamDifferential_mem gr 0 w hx), ← cartan_zero_apply]
  exact h.rat_inv_smul_cartan_add 0 w hx

/-- The homotopy identity in positive degree, on one weight component. -/
theorem Retraction.comm_succ_of_mem (h : Retraction (S := S) gr) (p w : ℕ)
    {x : ⋀[T]^(p + 1) (Ω[T⁄R])} (hx : x ∈ gradedDifferentialFormComponent gr (p + 1) w) :
    homotopyMap gr (p + 1) (deRhamDifferential (A := R) (p + 1) x) +
        deRhamDifferential (A := R) p (homotopyMap gr p x) +
        mapExteriorPower R S T (p + 1) (mapExteriorPower R T S (p + 1) x) = x := by
  rw [homotopyMap_of_mem gr (p + 1) w (deRhamDifferential_mem gr (p + 1) w hx),
    homotopyMap_of_mem gr p w hx, deRhamDifferential_algebraMap_rat_smul, ← smul_add,
    ← cartan_succ_apply]
  exact h.rat_inv_smul_cartan_add (p + 1) w hx

omit [Algebra ℚ T] in
/-- An `R`-linear endomorphism of `Ω^p_{T/R}` which is the identity on every weight component is
the identity. -/
theorem eq_of_forall_mem (p : ℕ) (F : ⋀[T]^p (Ω[T⁄R]) →ₗ[R] ⋀[T]^p (Ω[T⁄R]))
    (hF : ∀ w x, x ∈ gradedDifferentialFormComponent gr p w → F x = x)
    (x : ⋀[T]^p (Ω[T⁄R])) : F x = x := by
  have hx : x ∈ ⨆ w, gradedDifferentialFormComponent gr p w := by
    rw [(isInternal_forms gr p).submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem w x hx => exact hF w x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]

/-- The homotopy identity in degree zero. -/
theorem Retraction.comm_zero (h : Retraction (S := S) gr) (x : ⋀[T]^0 (Ω[T⁄R])) :
    homotopyMap gr 0 (deRhamDifferential (A := R) 0 x) +
        mapExteriorPower R S T 0 (mapExteriorPower R T S 0 x) = x :=
  eq_of_forall_mem (gr := gr) 0 (homotopyMap gr 0 ∘ₗ deRhamDifferential (A := R) 0 +
      (mapExteriorPower R S T 0).restrictScalars R ∘ₗ (mapExteriorPower R T S 0).restrictScalars R)
    (fun w _ hx ↦ h.comm_zero_of_mem w hx) x

/-- The homotopy identity in positive degree. -/
theorem Retraction.comm_succ (h : Retraction (S := S) gr) (p : ℕ)
    (x : ⋀[T]^(p + 1) (Ω[T⁄R])) :
    homotopyMap gr (p + 1) (deRhamDifferential (A := R) (p + 1) x) +
        deRhamDifferential (A := R) p (homotopyMap gr p x) +
        mapExteriorPower R S T (p + 1) (mapExteriorPower R T S (p + 1) x) = x :=
  eq_of_forall_mem (gr := gr) (p + 1)
    (homotopyMap gr (p + 1) ∘ₗ deRhamDifferential (A := R) (p + 1) +
      deRhamDifferential (A := R) p ∘ₗ homotopyMap gr p +
      (mapExteriorPower R S T (p + 1)).restrictScalars R ∘ₗ
        (mapExteriorPower R T S (p + 1)).restrictScalars R)
    (fun w _ hx ↦ h.comm_succ_of_mem p w hx) x

/-- The homotopy of the graded Poincaré lemma, from the identity of `Ω^•_{T/R}` to the
composite `Ω^•_{T/R} → Ω^•_{S/R} → Ω^•_{T/R}`. -/
def Retraction.homotopy (h : Retraction (S := S) gr) :
    Homotopy (𝟙 (deRhamComplex R T)) (deRhamComplexMap R T S ≫ deRhamComplexMap R S T) where
  hom i j :=
    if hij : j + 1 = i then
      (eqToHom (by rw [hij]) : (deRhamComplex R T).X i ⟶ (deRhamComplex R T).X (j + 1)) ≫
        ModuleCat.ofHom (homotopyMap gr j)
    else 0
  zero _ _ w := by rw [dite_eq_right]; exact w
  comm i := by
    match i with
    | 0 =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, add_zero]
        ext x
        simp only [deRhamComplex_X, HomologicalComplex.id_f, ModuleCat.hom_id, Nat.reduceAdd,
          deRhamComplex_d, zero_add, ↓reduceDIte, HomologicalComplex.comp_f]
        exact (h.comm_zero x).symm
    | (p + 1) =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        ext x
        simp only [deRhamComplex_X, HomologicalComplex.id_f, ModuleCat.hom_id, deRhamComplex_d,
          ↓reduceDIte, Category.assoc, HomologicalComplex.comp_f]
        exact (h.comm_succ p x).symm

omit [Algebra R S] [IsScalarTower R S T] [IsScalarTower R T S] [GradedAlgebra gr] [Algebra ℚ T] in
/-- For a retraction `S → T → S`, the algebras `S`, `T`, `S` form a scalar tower. -/
theorem Retraction.isScalarTower (h : Retraction (S := S) gr) : IsScalarTower S T S :=
  IsScalarTower.of_algebraMap_eq fun s ↦ (h.retract s).symm

/-- **The graded Poincaré lemma.** Let `T = ⊕_{n ≥ 0} T_n` be an `ℕ`-graded `R`-algebra
containing `ℚ`, and `S → T → S` maps of `R`-algebras composing to the identity, such that `S`
maps onto `T_0` and `T → S` kills `T_n` for `n > 0`. Then `Ω^•_{S/R} → Ω^•_{T/R}` is a homotopy
equivalence of complexes of `R`-modules, with homotopy inverse `Ω^•_{T/R} → Ω^•_{S/R}`. -/
def Retraction.homotopyEquiv (h : Retraction (S := S) gr) :
    HomotopyEquiv (deRhamComplex R S) (deRhamComplex R T) where
  hom := deRhamComplexMap R S T
  inv := deRhamComplexMap R T S
  homotopyHomInvId := by
    haveI := h.isScalarTower
    exact Homotopy.ofEq (by rw [deRhamComplexMap_comp, deRhamComplexMap_self])
  homotopyInvHomId := h.homotopy.symm

/-- **The graded Poincaré lemma**, as a quasi-isomorphism. -/
theorem Retraction.quasiIso (h : Retraction (S := S) gr) :
    QuasiIso (deRhamComplexMap R S T) :=
  h.homotopyEquiv.quasiIso_hom

end Retraction

end GradedDeRham
