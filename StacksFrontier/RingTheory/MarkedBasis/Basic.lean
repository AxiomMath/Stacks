module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.LinearCombination

/-!
# Quotients of a base-changed algebra with a marked basis

Let `R` be a commutative ring, `A` an `R`-algebra and `W : Fin d → A` a family of `d` elements.
For an `R`-algebra `C` consider the ideals `J` of `C ⊗[R] A` such that the images of the
`1 ⊗ W l` form a `C`-basis of `(C ⊗[R] A) ⧸ J`. This is the algebra underlying the affine charts
`F_W` of the Hilbert scheme of points in the proof of [Stacks, Tag 0B99].

Such an ideal is the same thing as *chart data*: an `R`-linear map `p : A → C^d` (the coordinates
of the image of `1 ⊗ a` in the marked basis) with `p (W l) = e_l` and
`p (a * a') = ∑ l, p(a)_l • p (W l * a')`. Chart data are corepresented by an explicit
`R`-algebra, `Stacks.MarkedBasis.univRing`, a quotient of the polynomial ring on the symbols
`(m, a) ∈ Fin d × A`. This avoids the structure constants of the source: no relation expressing
associativity or commutativity is needed, those being inherited from `A`.

## Main definitions

* `Stacks.MarkedBasis.ChartData`: chart data over an `R`-algebra `C`.
* `Stacks.MarkedBasis.univRing`: the universal ring of chart data.
* `Stacks.MarkedBasis.chartIdeal`: the ideal of `C ⊗[R] A` of chart data.
* `Stacks.MarkedBasis.markedMap`: the map `C^d → (C ⊗[R] A) ⧸ J`, `c ↦ ∑ c_l (1 ⊗ W l)`.

## Main results

* `Stacks.MarkedBasis.univHomEquiv`: `R`-algebra maps `univRing ⟶ C` are chart data over `C`.
* `Stacks.MarkedBasis.bijective_markedMap_chartIdeal`: the marked elements form a basis modulo
  the chart ideal.
* `Stacks.MarkedBasis.chartDataEquiv`: chart data over `C` are the ideals of `C ⊗[R] A` modulo
  which the marked elements form a basis.
* `Stacks.MarkedBasis.map_chartIdeal`: formation of the chart ideal commutes with base change.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace Stacks.MarkedBasis

variable (R : Type u) {A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} (W : Fin d → A)

/-! ### Chart data -/

/-- **Chart data** over an `R`-algebra `C`: the coordinates, in the marked basis, of the images of
the elements of `A`. -/
structure ChartData (C : Type u) [CommRing C] [Algebra R C] where
  /-- The coordinates of the image of `1 ⊗ a`. -/
  coord : A →ₗ[R] (Fin d → C)
  /-- The marked elements have the standard coordinates. -/
  coord_W : ∀ l, coord (W l) = Pi.single l 1
  /-- Coordinates are compatible with multiplication. -/
  coord_mul : ∀ a a', coord (a * a') = ∑ l, coord a l • coord (W l * a')

variable {R W}

/-- Two chart data with the same coordinates are equal. -/
@[ext]
theorem ChartData.ext {C : Type u} [CommRing C] [Algebra R C] {D D' : ChartData R W C}
    (h : ∀ a, D.coord a = D'.coord a) : D = D' := by
  obtain ⟨c, _, _⟩ := D
  obtain ⟨c', _, _⟩ := D'
  have : c = c' := LinearMap.ext h
  subst this
  rfl

/-- Extension of scalars of chart data along an `R`-algebra map. -/
def ChartData.map {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
    (φ : C →ₐ[R] C') (D : ChartData R W C) : ChartData R W C' where
  coord := φ.toLinearMap.compLeft (Fin d) ∘ₗ D.coord
  coord_W l := by
    funext m
    change φ (D.coord (W l) m) = (Pi.single l (1 : C') : Fin d → C') m
    rw [D.coord_W l, Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  coord_mul a a' := by
    funext m
    change φ (D.coord (a * a') m) = (∑ l, (φ (D.coord a l)) • (fun m ↦ φ (D.coord (W l * a') m))) m
    rw [D.coord_mul, Finset.sum_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

/-- The coordinates of the extension of scalars of chart data are the images of its coordinates. -/
@[simp]
theorem ChartData.map_coord {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C']
    [Algebra R C'] (φ : C →ₐ[R] C') (D : ChartData R W C) (a : A) (m : Fin d) :
    (D.map φ).coord a m = φ (D.coord a m) :=
  rfl

/-- Extension of scalars along the identity does nothing. -/
@[simp]
theorem ChartData.map_id {C : Type u} [CommRing C] [Algebra R C] (D : ChartData R W C) :
    D.map (AlgHom.id R C) = D :=
  ChartData.ext fun _ ↦ rfl

/-- Extension of scalars along a composite is the composite of the extensions. -/
theorem ChartData.map_comp {C C' C'' : Type u} [CommRing C] [Algebra R C] [CommRing C']
    [Algebra R C'] [CommRing C''] [Algebra R C''] (φ : C →ₐ[R] C') (ψ : C' →ₐ[R] C'')
    (D : ChartData R W C) : (D.map φ).map ψ = D.map (ψ.comp φ) :=
  ChartData.ext fun _ ↦ rfl

/-! ### The universal ring -/

variable (R W)

/-- The relations defining the universal ring of chart data: additivity, `R`-linearity, the
normalisation on the marked elements and compatibility with multiplication. -/
def relations : Set (MvPolynomial (Fin d × A) R) :=
  {x | ∃ (m : Fin d) (a a' : A),
    x = MvPolynomial.X (m, a + a') - MvPolynomial.X (m, a) - MvPolynomial.X (m, a')} ∪
  {x | ∃ (m : Fin d) (r : R) (a : A),
    x = MvPolynomial.X (m, r • a) - MvPolynomial.C r * MvPolynomial.X (m, a)} ∪
  {x | ∃ (m l : Fin d), x = MvPolynomial.X (m, W l) - if m = l then 1 else 0} ∪
  {x | ∃ (m : Fin d) (a a' : A), x = MvPolynomial.X (m, a * a') -
    ∑ l, MvPolynomial.X (l, a) * MvPolynomial.X (m, W l * a')}

/-- **The universal ring of chart data.** -/
abbrev univRing : Type u := MvPolynomial (Fin d × A) R ⧸ Ideal.span (relations R W)

variable {R W}

section Universal

variable {C : Type u} [CommRing C] [Algebra R C] (ψ : univRing R W →ₐ[R] C)

/-- The value of an `R`-algebra map out of the universal ring on the symbol `(m, a)`. -/
def symbolValue (a : A) (m : Fin d) : C :=
  ψ (Ideal.Quotient.mk _ (MvPolynomial.X (m, a)))

/-- An `R`-algebra map out of the universal ring kills the relations. -/
theorem map_relation_eq_zero {x : MvPolynomial (Fin d × A) R} (hx : x ∈ relations R W) :
    ψ (Ideal.Quotient.mk _ x) = 0 := by
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span hx), map_zero]

/-- The symbol values are additive in the element of `A`. -/
theorem symbolValue_add (a a' : A) (m : Fin d) :
    symbolValue ψ (a + a') m = symbolValue ψ a m + symbolValue ψ a' m := by
  have h := map_relation_eq_zero ψ (Or.inl (Or.inl (Or.inl ⟨m, a, a', rfl⟩)))
  simp only [map_sub] at h
  unfold symbolValue
  linear_combination h

/-- The symbol values are `R`-linear in the element of `A`. -/
theorem symbolValue_smul (r : R) (a : A) (m : Fin d) :
    symbolValue ψ (r • a) m = algebraMap R C r * symbolValue ψ a m := by
  have h := map_relation_eq_zero ψ (Or.inl (Or.inl (Or.inr ⟨m, r, a, rfl⟩)))
  have hC : ψ (Ideal.Quotient.mk _ (MvPolynomial.C r)) = algebraMap R C r := ψ.commutes r
  simp only [map_sub, map_mul, hC] at h
  unfold symbolValue
  linear_combination h

/-- The symbol values on the marked elements are the standard coordinates. -/
theorem symbolValue_W (l m : Fin d) :
    symbolValue ψ (W l) m = if m = l then 1 else 0 := by
  have h := map_relation_eq_zero ψ (Or.inl (Or.inr ⟨m, l, rfl⟩))
  simp only [map_sub] at h
  unfold symbolValue
  split_ifs at h ⊢
  · rw [map_one, map_one] at h; exact sub_eq_zero.mp h
  · simpa using h

/-- The symbol values are compatible with multiplication. -/
theorem symbolValue_mul (a a' : A) (m : Fin d) :
    symbolValue ψ (a * a') m = ∑ l, symbolValue ψ a l * symbolValue ψ (W l * a') m := by
  have h := map_relation_eq_zero ψ (Or.inr ⟨m, a, a', rfl⟩)
  simp only [map_sub, map_sum, map_mul] at h
  unfold symbolValue
  linear_combination h

/-- The chart data attached to an `R`-algebra map out of the universal ring. -/
def chartDataOfHom : ChartData R W C where
  coord :=
    { toFun := fun a m ↦ symbolValue ψ a m
      map_add' := fun a a' ↦ funext fun m ↦ symbolValue_add ψ a a' m
      map_smul' := fun r a ↦ funext fun m ↦ by
        rw [symbolValue_smul]
        simp [Algebra.smul_def] }
  coord_W l := funext fun m ↦ by
    change symbolValue ψ (W l) m = (Pi.single l (1 : C) : Fin d → C) m
    rw [symbolValue_W, Pi.single_apply]
  coord_mul a a' := funext fun m ↦ by
    change symbolValue ψ (a * a') m =
      (∑ l, symbolValue ψ a l • (fun m ↦ symbolValue ψ (W l * a') m)) m
    rw [symbolValue_mul, Finset.sum_apply]
    rfl

/-- The coordinates of `chartDataOfHom ψ` are the values of `ψ` on the symbols. -/
@[simp]
theorem chartDataOfHom_coord (a : A) (m : Fin d) :
    (chartDataOfHom ψ).coord a m = ψ (Ideal.Quotient.mk _ (MvPolynomial.X (m, a))) :=
  rfl

end Universal

/-- The `R`-algebra map out of the universal ring attached to chart data. -/
def homOfChartData {C : Type u} [CommRing C] [Algebra R C] (D : ChartData R W C) :
    univRing R W →ₐ[R] C :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun x ↦ D.coord x.2 x.1) (by
    intro x hx
    refine Submodule.span_induction (p := fun x _ ↦ MvPolynomial.aeval _ x = 0) ?_ ?_ ?_ ?_ hx
    · rintro x (((⟨m, a, a', rfl⟩ | ⟨m, r, a, rfl⟩) | ⟨m, l, rfl⟩) | ⟨m, a, a', rfl⟩)
      · simp [map_add]
      · have h := congrFun (D.coord.map_smul r a) m
        simp only [Pi.smul_apply, Algebra.smul_def] at h
        simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h,
          Algebra.smul_def, sub_self]
      · simp only [map_sub, MvPolynomial.aeval_X, D.coord_W, Pi.single_apply]
        split_ifs <;> simp
      · have h := congrFun (D.coord_mul a a') m
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
        simp only [map_sub, MvPolynomial.aeval_X, map_sum, map_mul, h, sub_self]
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro c x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

/-- The map attached to chart data sends the symbol `(m, a)` to the `m`-th coordinate of `a`. -/
@[simp]
theorem homOfChartData_mk_X {C : Type u} [CommRing C] [Algebra R C] (D : ChartData R W C)
    (m : Fin d) (a : A) :
    homOfChartData D (Ideal.Quotient.mk _ (MvPolynomial.X (m, a))) = D.coord a m :=
  (Ideal.Quotient.lift_mk _ _ _).trans (MvPolynomial.aeval_X _ _)

/-- **The universal property of the universal ring**: `R`-algebra maps out of it are chart
data. -/
def univHomEquiv (C : Type u) [CommRing C] [Algebra R C] :
    (univRing R W →ₐ[R] C) ≃ ChartData R W C where
  toFun := chartDataOfHom
  invFun := homOfChartData
  left_inv ψ := by
    refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun x ↦ ?_)
    obtain ⟨m, a⟩ := x
    change homOfChartData (chartDataOfHom ψ) (Ideal.Quotient.mk _ (MvPolynomial.X (m, a))) = _
    rw [homOfChartData_mk_X]
    rfl
  right_inv D := ChartData.ext fun a ↦ funext fun m ↦ by
    change homOfChartData D (Ideal.Quotient.mk _ (MvPolynomial.X (m, a))) = _
    rw [homOfChartData_mk_X]

/-- The universal property is natural in the target. -/
theorem univHomEquiv_comp {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C']
    [Algebra R C'] (ψ : univRing R W →ₐ[R] C) (φ : C →ₐ[R] C') :
    univHomEquiv C' (φ.comp ψ) = (univHomEquiv C ψ).map φ :=
  ChartData.ext fun _ ↦ funext fun _ ↦ rfl

/-! ### The chart ideal -/

variable (C : Type u) [CommRing C] [Algebra R C]

/-- The element `1 ⊗ a - ∑ p(a)_l (1 ⊗ W l)` of `C ⊗[R] A`. -/
def chartRelation (D : ChartData R W C) (a : A) : C ⊗[R] A :=
  (1 : C) ⊗ₜ a - ∑ l, D.coord a l ⊗ₜ W l

/-- **The chart ideal** of chart data: generated by the differences between the elements of `A`
and their expansions in the marked basis. -/
def chartIdeal (D : ChartData R W C) : Ideal (C ⊗[R] A) :=
  Ideal.span (Set.range (chartRelation C D))

variable (W) in
/-- The map `C^d → (C ⊗[R] A) ⧸ J`, `c ↦ ∑ c_l (1 ⊗ W l)`, as a `C`-linear map. -/
def markedMap (J : Ideal (C ⊗[R] A)) : (Fin d → C) →ₗ[C] (C ⊗[R] A) ⧸ J where
  toFun c := ∑ l, Ideal.Quotient.mk J (c l ⊗ₜ W l)
  map_add' c c' := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    change Ideal.Quotient.mk J (r • (c l ⊗ₜ[R] W l)) = _
    rw [← Ideal.Quotient.mkₐ_eq_mk C, map_smul]

variable {C}

/-- The marked expansion of `c` is the class of `∑ c_l ⊗ W l`. -/
private theorem markedMap_apply (J : Ideal (C ⊗[R] A)) (c : Fin d → C) :
    markedMap W C J c = Ideal.Quotient.mk J (∑ l, c l ⊗ₜ[R] W l) := by
  simp [markedMap]

/-- The `C`-linear map `C ⊗[R] A → C^d`, `c ⊗ a ↦ c • p(a)`. -/
def coordMap (D : ChartData R W C) : C ⊗[R] A →ₗ[C] (Fin d → C) :=
  D.coord.liftBaseChange C

/-- The coordinate map sends `c ⊗ a` to `c • p(a)`. -/
@[simp]
theorem coordMap_tmul (D : ChartData R W C) (c : C) (a : A) :
    coordMap D (c ⊗ₜ a) = c • D.coord a :=
  rfl

/-- The coordinate map kills the chart ideal. -/
theorem coordMap_eq_zero_of_mem (D : ChartData R W C) {y : C ⊗[R] A}
    (hy : y ∈ chartIdeal C D) : coordMap D y = 0 := by
  let K : Ideal (C ⊗[R] A) :=
    { carrier := {y | ∀ x, coordMap D (x * y) = 0}
      add_mem' := fun ha hb x ↦ by rw [mul_add, map_add, ha x, hb x, add_zero]
      zero_mem' := fun x ↦ by rw [mul_zero, map_zero]
      smul_mem' := fun z y hy x ↦ by rw [smul_eq_mul, ← mul_assoc]; exact hy (x * z) }
  have hle : chartIdeal C D ≤ K := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩ x
    induction x using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero]
    | add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]
    | tmul c a' =>
      simp only [chartRelation, mul_sub, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, map_sub, map_sum, coordMap_tmul]
      rw [sub_eq_zero, mul_comm a' a, D.coord_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [mul_comm a' (W l), smul_smul]
  simpa using hle hy 1

/-- Every element is congruent, modulo the chart ideal, to the expansion of its coordinates. -/
theorem sub_markedSum_mem (D : ChartData R W C) (y : C ⊗[R] A) :
    y - ∑ l, coordMap D y l ⊗ₜ W l ∈ chartIdeal C D := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have := Ideal.add_mem _ hx hy
    convert this using 1
    simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
    abel
  | tmul c a =>
    have h := Ideal.mul_mem_left (chartIdeal C D) (c ⊗ₜ (1 : A))
      (Ideal.subset_span ⟨a, rfl⟩ : chartRelation C D a ∈ chartIdeal C D)
    convert h using 1
    simp only [chartRelation, mul_sub, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, coordMap_tmul, Pi.smul_apply, smul_eq_mul]

/-- The class of an element modulo the chart ideal is the marked expansion of its coordinates. -/
theorem mk_eq_markedMap_coordMap (D : ChartData R W C) (y : C ⊗[R] A) :
    Ideal.Quotient.mk (chartIdeal C D) y = markedMap W C (chartIdeal C D) (coordMap D y) := by
  rw [markedMap_apply, Ideal.Quotient.eq]
  exact sub_markedSum_mem D y

/-- The coordinate map is a left inverse of the marked expansion. -/
theorem coordMap_markedSum (D : ChartData R W C) (c : Fin d → C) :
    coordMap D (∑ l, c l ⊗ₜ W l) = c := by
  ext m
  simp only [map_sum, coordMap_tmul, D.coord_W, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- **The marked elements form a basis modulo the chart ideal.** -/
theorem bijective_markedMap_chartIdeal (D : ChartData R W C) :
    Function.Bijective (markedMap W C (chartIdeal C D)) := by
  constructor
  · intro c c' h
    rw [markedMap_apply, markedMap_apply, Ideal.Quotient.eq] at h
    have := coordMap_eq_zero_of_mem D h
    rwa [map_sub, coordMap_markedSum, coordMap_markedSum, sub_eq_zero] at this
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨coordMap D y, (mk_eq_markedMap_coordMap D y).symm⟩

/-- The chart ideal is the kernel of the coordinate map. -/
theorem mem_chartIdeal_iff (D : ChartData R W C) (y : C ⊗[R] A) :
    y ∈ chartIdeal C D ↔ coordMap D y = 0 := by
  refine ⟨coordMap_eq_zero_of_mem D, fun h ↦ ?_⟩
  simpa [h] using sub_markedSum_mem D y

/-! ### Chart data from an ideal -/

section OfIdeal

variable (J : Ideal (C ⊗[R] A)) (hJ : Function.Bijective (markedMap W C J))

/-- The coordinates of the class of an element in the marked basis. -/
def coordOf (y : C ⊗[R] A) : Fin d → C :=
  (LinearEquiv.ofBijective _ hJ).symm (Ideal.Quotient.mk J y)

/-- The marked expansion of the coordinates of `y` is the class of `y`. -/
theorem markedMap_coordOf (y : C ⊗[R] A) :
    markedMap W C J (coordOf J hJ y) = Ideal.Quotient.mk J y :=
  (LinearEquiv.ofBijective _ hJ).apply_symm_apply _

/-- A vector is the coordinate vector of `y` exactly when its marked expansion is the class of
`y`. -/
theorem coordOf_eq_iff (y : C ⊗[R] A) (c : Fin d → C) :
    coordOf J hJ y = c ↔ markedMap W C J c = Ideal.Quotient.mk J y := by
  constructor
  · rintro rfl; exact markedMap_coordOf J hJ y
  · intro h; exact hJ.1 ((markedMap_coordOf J hJ y).trans h.symm)

/-- The class of `c ⊗ a` is `c` times the class of `1 ⊗ a`. -/
theorem mk_tmul_eq_smul (c : C) (a : A) :
    Ideal.Quotient.mk J (c ⊗ₜ[R] a) = c • Ideal.Quotient.mk J ((1 : C) ⊗ₜ[R] a) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk C, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hJ in
/-- The chart data of an ideal modulo which the marked elements form a basis: the coordinates
of the classes of the `1 ⊗ a`. -/
def chartDataOfIdeal : ChartData R W C where
  coord :=
    { toFun := fun a ↦ coordOf J hJ ((1 : C) ⊗ₜ a)
      map_add' := fun a a' ↦ by
        rw [coordOf_eq_iff, map_add, markedMap_coordOf, markedMap_coordOf, ← map_add,
          TensorProduct.tmul_add]
      map_smul' := fun r a ↦ by
        rw [coordOf_eq_iff, RingHom.id_apply, ← algebraMap_smul C r, map_smul,
          markedMap_coordOf, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          mk_tmul_eq_smul, Algebra.smul_def r (1 : C), mul_one]
        rw [mk_tmul_eq_smul J (algebraMap R C r) a]
        exact congrArg (algebraMap R C r • ·) (one_smul C _) }
  coord_W l := by
    change coordOf J hJ _ = _
    rw [coordOf_eq_iff]
    simp only [markedMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single l (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp
  coord_mul a a' := by
    change coordOf J hJ ((1 : C) ⊗ₜ (a * a')) =
      ∑ l, coordOf J hJ ((1 : C) ⊗ₜ a) l • coordOf J hJ ((1 : C) ⊗ₜ (W l * a'))
    rw [coordOf_eq_iff, map_sum]
    simp only [map_smul, markedMap_coordOf]
    have hmul : Ideal.Quotient.mk J ((1 : C) ⊗ₜ (a * a')) =
        Ideal.Quotient.mk J ((1 : C) ⊗ₜ a) * Ideal.Quotient.mk J ((1 : C) ⊗ₜ a') := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hmul, ← markedMap_coordOf J hJ ((1 : C) ⊗ₜ a)]
    simp only [markedMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mk_tmul_eq_smul J (coordOf J hJ ((1 : C) ⊗ₜ a) l) (W l * a')]

/-- The coordinates of the chart data of an ideal are the coordinates of the classes of the
`1 ⊗ a`. -/
@[simp]
theorem chartDataOfIdeal_coord (a : A) :
    (chartDataOfIdeal J hJ).coord a = coordOf J hJ ((1 : C) ⊗ₜ a) :=
  rfl

end OfIdeal

variable (C)

/-- **Chart data are the ideals modulo which the marked elements form a basis.** -/
def chartDataEquiv :
    ChartData R W C ≃ {J : Ideal (C ⊗[R] A) // Function.Bijective (markedMap W C J)} where
  toFun D := ⟨chartIdeal C D, bijective_markedMap_chartIdeal D⟩
  invFun J := chartDataOfIdeal J.1 J.2
  left_inv D := by
    refine ChartData.ext fun a ↦ ?_
    rw [chartDataOfIdeal_coord, coordOf_eq_iff, mk_eq_markedMap_coordMap D, coordMap_tmul,
      one_smul]
  right_inv J := by
    obtain ⟨J, hJ⟩ := J
    set D := chartDataOfIdeal J hJ
    have hrel : ∀ a, Ideal.Quotient.mk J ((1 : C) ⊗ₜ a) = markedMap W C J (D.coord a) := fun a ↦
      (markedMap_coordOf J hJ _).symm
    have hle : chartIdeal C D ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem, chartRelation, map_sub, hrel a,
        sub_eq_zero]
      simp [markedMap]
    refine Subtype.ext (le_antisymm hle fun y hy ↦ ?_)
    have h1 := mk_eq_markedMap_coordMap D y
    have h2 : Ideal.Quotient.mk J y = markedMap W C J (coordMap D y) := by
      have := congrArg (Ideal.Quotient.factor hle) h1
      simpa [markedMap, Ideal.Quotient.factor_mk] using this
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy] at h2
    have h3 : coordMap D y = 0 := hJ.1 (h2.symm.trans (map_zero _).symm)
    exact (mem_chartIdeal_iff D y).mpr h3

/-! ### Base change -/

variable {C} {C' : Type u} [CommRing C'] [Algebra R C']

/-- **Formation of the chart ideal commutes with base change.** -/
theorem map_chartIdeal (D : ChartData R W C) (φ : C →ₐ[R] C') :
    Ideal.map (Algebra.TensorProduct.map φ (AlgHom.id R A)) (chartIdeal C D) =
      chartIdeal C' (D.map φ) := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext a
  simp [chartRelation, map_sub, map_sum, Algebra.TensorProduct.map_tmul]

end Stacks.MarkedBasis

end
