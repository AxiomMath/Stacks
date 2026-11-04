module

public import StacksFrontier.RingTheory.OrderOfVanishing.Norm

/-!
# The order of a determinant whose cokernel is a residue-field vector space

Let `A` be a discrete valuation ring with residue field `κ` and let `T` be an `r × r` matrix
over `A` whose cokernel `A^r ⧸ T·A^r` is annihilated by the maximal ideal and has length at most
`s`.  Then `det T ≠ 0` and the order of vanishing `ord_A(det T) = length_A (A ⧸ (det T))` is at
most `min s r`; when the cokernel is exactly `κ^⊕ s` the order is exactly `s` and `s ≤ r`.

This is the discrete-valuation-ring computation behind the bound `k ≤ min(s, r)` of Tag 0B3T.
In that proof one is given a right exact sequence `M → M' → N → 0` of finite `A`-modules with
`M`, `M'` of generic rank `r` and `N ≅ κ^⊕ s`, and the comparison map of determinant line
bundles is the determinant of the induced map `M ⧸ tors → M' ⧸ tors` of free modules of rank
`r`; `length_span_det_torsionQuotient_le_min` is exactly that statement.

## Main results

* `Stacks.OrderOfVanishing.det_ne_zero_of_smul_mem_range` and
  `Stacks.OrderOfVanishing.length_span_det_le_min_of_smul_mem_range`: the determinant is nonzero
  and its order of vanishing is at most `min s r`.
* `Stacks.OrderOfVanishing.length_span_det_eq_of_quotientRangeEquiv` and
  `Stacks.OrderOfVanishing.le_of_quotientRangeEquiv`: for a cokernel isomorphic to `κ^⊕ s` the
  order of vanishing is exactly `s`, and `s ≤ r`.
* `Stacks.OrderOfVanishing.length_span_det_torsionQuotient_le_min`: the bound for the induced
  map on torsion-free quotients in a right exact sequence with residual cokernel, and
  `Stacks.OrderOfVanishing.length_coker_torsionQuotient_le_min_of_finrank`: its basis-free form
  under the generic-rank hypothesis.

## Implementation notes

The residue field kills the cokernel, so a uniformizer `ϖ` satisfies `ϖ·A^r ⊆ T·A^r`; writing
preimages of `ϖ·eᵢ` as the columns of a matrix `S` gives `T · S = ϖ · 1` and hence
`det T · det S = ϖ^r`.  Nonvanishing of the determinant and the bound by `r` both come from that
identity, through the additivity `length_span_mul` of `length (A ⧸ (·))` under multiplication,
while the bound by `s` is the cokernel-length identity `matrix_cokerLen_eq_spanLen` of Tag 02QH.

For the module-level statement the bases of `M ⧸ tors` and `M' ⧸ tors` indexed by `Fin r` are
taken as data: over a discrete valuation ring such a basis exists exactly when the generic rank
of the module is `r`, and the determinant of the induced map is only defined relative to a
choice of bases.  Its order of vanishing does not depend on that choice, the two determinants
differing by a unit, and the bound is stated for every choice.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.OrderOfVanishing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- An element of the maximal ideal acts as zero on the residue field. -/
theorem smul_residueField_eq_zero {a : A} (ha : a ∈ maximalIdeal A) (c : ResidueField A) :
    a • c = 0 := by
  rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff a).mpr ha, zero_mul]

/-- The residue field is a simple module over the ring, so it has length one. -/
theorem length_residueField : Module.length A (ResidueField A) = 1 := by
  have : IsSimpleModule A (ResidueField A) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨maximalIdeal A, inferInstance, ⟨LinearEquiv.refl A (ResidueField A)⟩⟩
  exact Module.length_eq_one A (ResidueField A)

/-- A finite-dimensional residue-field vector space has length its dimension. -/
theorem length_pi_residueField (s : ℕ) :
    Module.length A (Fin s → ResidueField A) = (s : ℕ∞) := by
  rw [Module.length_pi_of_fintype A fun _ : Fin s => ResidueField A]
  simp [length_residueField]

/-- The maximal ideal annihilates a residue-field vector space. -/
theorem smul_pi_residueField_eq_zero {s : ℕ} {a : A} (ha : a ∈ maximalIdeal A)
    (v : Fin s → ResidueField A) : a • v = 0 := by
  funext i
  exact smul_residueField_eq_zero ha _

variable [IsDomain A]

omit [IsLocalRing A] [IsDomain A] in
/-- A square matrix all of whose multiples by `c` lie in its range factors `c · 1`: the
preimages of `c · eᵢ` are the columns of a matrix `S` with `T * S = c • 1`. -/
theorem exists_mul_eq_smul_one {r : ℕ} (T : Matrix (Fin r) (Fin r) A) (c : A)
    (h : ∀ x : Fin r → A, c • x ∈ LinearMap.range (Matrix.toLin' T)) :
    ∃ S : Matrix (Fin r) (Fin r) A, T * S = c • (1 : Matrix (Fin r) (Fin r) A) := by
  choose v hv using fun i : Fin r => h (Pi.single i 1)
  refine ⟨Matrix.of fun j i => v i j, ?_⟩
  ext j i
  have hji := congrFun (hv i) j
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] at hji
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [hji]

omit [IsLocalRing A] [IsDomain A] in
/-- A scalar annihilating the cokernel of a matrix carries every vector into its range. -/
theorem smul_mem_range_of_smul_quotient_eq_zero {r : ℕ} {T : Matrix (Fin r) (Fin r) A} {a : A}
    (h : ∀ q : (Fin r → A) ⧸ LinearMap.range (Matrix.toLin' T), a • q = 0) (x : Fin r → A) :
    a • x ∈ LinearMap.range (Matrix.toLin' T) := by
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact h _

variable [IsDiscreteValuationRing A]

/-- A uniformizer lies in the maximal ideal. -/
theorem irreducible_mem_maximalIdeal {ϖ : A} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal A := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact Ideal.mem_span_singleton_self ϖ

omit [IsLocalRing A] in
/-- The length of `A ⧸ (ϖ)` at a uniformizer is one. -/
theorem length_span_irreducible {ϖ : A} (hϖ : Irreducible ϖ) :
    Module.length A (A ⧸ Ideal.span {ϖ}) = 1 := by
  have hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    infer_instance
  have : IsSimpleModule A (A ⧸ Ideal.span {ϖ}) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨Ideal.span {ϖ}, hmax, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one A _

variable {r s : ℕ} {T : Matrix (Fin r) (Fin r) A}

/-- **The determinant is nonzero** when the maximal ideal annihilates the cokernel: the
factorization `T · S = ϖ · 1` of a uniformizer multiple of the identity forces
`det T · det S = ϖ^r ≠ 0`. -/
theorem det_ne_zero_of_smul_mem_range
    (hann : ∀ a ∈ maximalIdeal A, ∀ x : Fin r → A, a • x ∈ LinearMap.range (Matrix.toLin' T)) :
    T.det ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨S, hS⟩ := exists_mul_eq_smul_one T ϖ (hann ϖ (irreducible_mem_maximalIdeal hϖ))
  intro hdet
  refine pow_ne_zero r hϖ.ne_zero ?_
  have h := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hdet,
    zero_mul] at h
  exact h.symm

/-- The order of vanishing of the determinant is at most the rank, when the maximal ideal
annihilates the cokernel: `ord(det T) + ord(det S) = r` for the factorization `T · S = ϖ · 1`. -/
theorem length_span_det_le_rank
    (hann : ∀ a ∈ maximalIdeal A, ∀ x : Fin r → A, a • x ∈ LinearMap.range (Matrix.toLin' T)) :
    Module.length A (A ⧸ Ideal.span {T.det}) ≤ (r : ℕ∞) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨S, hS⟩ := exists_mul_eq_smul_one T ϖ (hann ϖ (irreducible_mem_maximalIdeal hϖ))
  have hprod : T.det * S.det = ϖ ^ r := by
    have h := congrArg Matrix.det hS
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
  have hsum : Module.length A (A ⧸ Ideal.span {S.det})
      + Module.length A (A ⧸ Ideal.span {T.det}) = (r : ℕ∞) := by
    rw [← length_span_mul A T.det S.det (det_ne_zero_of_smul_mem_range hann), hprod,
      spanLen_pow A ϖ hϖ.ne_zero r, length_span_irreducible hϖ, mul_one]
  exact hsum ▸ le_add_self

/-- **The order of the determinant is at most `min s r`** for an `r × r` matrix whose cokernel
is annihilated by the maximal ideal and has length at most `s`.  This is the
discrete-valuation-ring bound behind the exponent range of Tag 0B3T. -/
theorem length_span_det_le_min_of_smul_mem_range
    (hann : ∀ a ∈ maximalIdeal A, ∀ x : Fin r → A, a • x ∈ LinearMap.range (Matrix.toLin' T))
    (hlen : Module.length A ((Fin r → A) ⧸ LinearMap.range (Matrix.toLin' T)) ≤ (s : ℕ∞)) :
    Module.length A (A ⧸ Ideal.span {T.det}) ≤ (min s r : ℕ) := by
  have hs : Module.length A (A ⧸ Ideal.span {T.det}) ≤ (s : ℕ∞) := by
    rwa [← matrix_cokerLen_eq_spanLen A r T (det_ne_zero_of_smul_mem_range hann)]
  rcases le_total s r with h | h
  · rw [min_eq_left h]; exact hs
  · rw [min_eq_right h]; exact length_span_det_le_rank hann

/-! ### The cokernel a residue-field vector space -/

section Residual

variable (e : ((Fin r → A) ⧸ LinearMap.range (Matrix.toLin' T)) ≃ₗ[A] (Fin s → ResidueField A))

include e

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- A cokernel isomorphic to `κ^⊕ s` is annihilated by the maximal ideal. -/
theorem smul_mem_range_of_quotientRangeEquiv (a : A) (ha : a ∈ maximalIdeal A) (x : Fin r → A) :
    a • x ∈ LinearMap.range (Matrix.toLin' T) := by
  refine smul_mem_range_of_smul_quotient_eq_zero (fun q => ?_) x
  refine e.map_eq_zero_iff.mp ?_
  rw [map_smul]
  exact smul_pi_residueField_eq_zero ha _

/-- **The determinant is nonzero** when the cokernel is a residue-field vector space. -/
theorem det_ne_zero_of_quotientRangeEquiv : T.det ≠ 0 :=
  det_ne_zero_of_smul_mem_range fun a ha => smul_mem_range_of_quotientRangeEquiv e a ha

/-- **The order of the determinant is the dimension of the cokernel.**  This is the
cokernel-length identity of Tag 02QH together with the length `s` of `κ^⊕ s`. -/
theorem length_span_det_eq_of_quotientRangeEquiv :
    Module.length A (A ⧸ Ideal.span {T.det}) = (s : ℕ∞) := by
  rw [← matrix_cokerLen_eq_spanLen A r T (det_ne_zero_of_quotientRangeEquiv e), e.length_eq,
    length_pi_residueField]

/-- **The dimension of the cokernel is at most the rank.** -/
theorem le_of_quotientRangeEquiv : s ≤ r := by
  have hle := length_span_det_le_rank
    (T := T) fun a ha => smul_mem_range_of_quotientRangeEquiv e a ha
  rw [length_span_det_eq_of_quotientRangeEquiv e] at hle
  exact_mod_cast hle

/-- **The order of the determinant is at most `min s r`** when the cokernel is the residue-field
vector space of dimension `s`. -/
theorem length_span_det_le_min_of_quotientRangeEquiv :
    Module.length A (A ⧸ Ideal.span {T.det}) ≤ (min s r : ℕ) := by
  rw [length_span_det_eq_of_quotientRangeEquiv e]
  exact_mod_cast le_min le_rfl (le_of_quotientRangeEquiv e)

end Residual

/-! ### The induced map on torsion-free quotients

The algebraic reformulation of Tag 0B3T over a discrete valuation ring: a right exact sequence
`M → M' → N → 0` of finite modules with `N ≅ κ^⊕ s`, in which `M` and `M'` have generic rank
`r`, induces a map of free modules of rank `r` on the torsion-free quotients whose determinant
has order of vanishing at most `min(s, r)`.
-/

section Modules

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] in
/-- A linear map carries the torsion submodule into the torsion submodule. -/
theorem torsion_le_comap_torsion (f : M →ₗ[A] M') :
    Submodule.torsion A M ≤ Submodule.comap f (Submodule.torsion A M') := by
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  refine Submodule.mem_comap.mpr ((Submodule.mem_torsion_iff (f x)).mpr ⟨a, ?_⟩)
  show (a : A) • f x = 0
  rw [← f.map_smul, show (a : A) • x = 0 from ha, map_zero]

/-- The map induced on the quotients by the torsion submodules. -/
def torsionQuotientMap (f : M →ₗ[A] M') :
    (M ⧸ Submodule.torsion A M) →ₗ[A] (M' ⧸ Submodule.torsion A M') :=
  Submodule.mapQ _ _ f (torsion_le_comap_torsion f)

/-- The cokernel of a map surjects onto the cokernel of the induced map on torsion-free
quotients. -/
def cokerTorsionQuotientMap (f : M →ₗ[A] M') :
    (M' ⧸ LinearMap.range f) →ₗ[A]
      ((M' ⧸ Submodule.torsion A M') ⧸ LinearMap.range (torsionQuotientMap f)) :=
  Submodule.liftQ _
    ((LinearMap.range (torsionQuotientMap f)).mkQ.comp (Submodule.torsion A M').mkQ) (by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨Submodule.Quotient.mk x, rfl⟩)

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] in
/-- That surjection onto the cokernel of the induced map on torsion-free quotients. -/
theorem cokerTorsionQuotientMap_surjective (f : M →ₗ[A] M') :
    Function.Surjective (cokerTorsionQuotientMap f) := by
  intro c
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (torsionQuotientMap f)) c
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Submodule.torsion A M') y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

variable {P P' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P']

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] in
/-- Passing to coordinates turns a linear map into its matrix. -/
theorem equivFun_comp_eq_toLin'_comp (b : Module.Basis (Fin r) A P) (b' : Module.Basis (Fin r) A P')
    (g : P →ₗ[A] P') :
    (b'.equivFun : P' →ₗ[A] (Fin r → A)) ∘ₗ g
      = Matrix.toLin' (LinearMap.toMatrix b b' g) ∘ₗ (b.equivFun : P →ₗ[A] (Fin r → A)) := by
  refine b.ext fun i => ?_
  have hbi : b.equivFun (b i) = Pi.single i 1 := by
    funext k
    rw [b.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hbi,
    Matrix.toLin'_apply, Matrix.mulVec_single_one]
  funext j
  rw [Matrix.col_apply]
  exact (LinearMap.toMatrix_apply b b' g j i).symm

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] in
/-- The coordinates carry the range of a linear map onto the range of its matrix. -/
theorem map_range_eq_range_toLin' (b : Module.Basis (Fin r) A P) (b' : Module.Basis (Fin r) A P')
    (g : P →ₗ[A] P') :
    Submodule.map (b'.equivFun : P' →ₗ[A] (Fin r → A)) (LinearMap.range g)
      = LinearMap.range (Matrix.toLin' (LinearMap.toMatrix b b' g)) := by
  rw [← LinearMap.range_comp, equivFun_comp_eq_toLin'_comp b b' g, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

/-- The cokernel of a linear map of free modules of rank `r` is the cokernel of its matrix. -/
noncomputable def quotientRangeEquivToLin' (b : Module.Basis (Fin r) A P)
    (b' : Module.Basis (Fin r) A P') (g : P →ₗ[A] P') :
    (P' ⧸ LinearMap.range g) ≃ₗ[A]
      ((Fin r → A) ⧸ LinearMap.range (Matrix.toLin' (LinearMap.toMatrix b b' g))) :=
  Submodule.Quotient.equiv _ _ b'.equivFun (map_range_eq_range_toLin' b b' g)

variable (f : M →ₗ[A] M')
  (e : (M' ⧸ LinearMap.range f) ≃ₗ[A] (Fin s → ResidueField A))

include e

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The maximal ideal annihilates the cokernel of the induced map on torsion-free quotients,
because that cokernel is a quotient of `κ^⊕ s`. -/
theorem smul_coker_torsionQuotient_eq_zero {a : A} (ha : a ∈ maximalIdeal A)
    (c : ((M' ⧸ Submodule.torsion A M') ⧸ LinearMap.range (torsionQuotientMap f))) :
    a • c = 0 := by
  obtain ⟨q, rfl⟩ := cokerTorsionQuotientMap_surjective f c
  have hq : a • q = 0 :=
    e.map_eq_zero_iff.mp (by rw [map_smul]; exact smul_pi_residueField_eq_zero ha _)
  rw [← map_smul, hq, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The cokernel of the induced map on torsion-free quotients has length at most `s`, being a
quotient of `κ^⊕ s`. -/
theorem length_coker_torsionQuotient_le :
    Module.length A ((M' ⧸ Submodule.torsion A M') ⧸ LinearMap.range (torsionQuotientMap f))
      ≤ (s : ℕ∞) := by
  refine le_trans (Module.length_le_of_surjective _ (cokerTorsionQuotientMap_surjective f)) ?_
  rw [e.length_eq, length_pi_residueField]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The maximal ideal carries `A^r` into the range of the matrix of the induced map. -/
theorem smul_mem_range_toLin'_toMatrix
    (b : Module.Basis (Fin r) A (M ⧸ Submodule.torsion A M))
    (b' : Module.Basis (Fin r) A (M' ⧸ Submodule.torsion A M'))
    {a : A} (ha : a ∈ maximalIdeal A) (x : Fin r → A) :
    a • x ∈
      LinearMap.range (Matrix.toLin' (LinearMap.toMatrix b b' (torsionQuotientMap f))) := by
  refine smul_mem_range_of_smul_quotient_eq_zero (fun q => ?_) x
  obtain ⟨c, rfl⟩ := (quotientRangeEquivToLin' b b' (torsionQuotientMap f)).surjective q
  rw [← map_smul, smul_coker_torsionQuotient_eq_zero f e ha c, map_zero]

/-- **The order of the determinant in a right exact sequence over a discrete valuation ring.**
For `M → M' → N → 0` exact with `N ≅ κ^⊕ s` and torsion-free quotients free of rank `r`, the
determinant of the induced map on those quotients has order of vanishing at most `min s r`. -/
theorem length_span_det_torsionQuotient_le_min
    (b : Module.Basis (Fin r) A (M ⧸ Submodule.torsion A M))
    (b' : Module.Basis (Fin r) A (M' ⧸ Submodule.torsion A M')) :
    Module.length A (A ⧸ Ideal.span {(LinearMap.toMatrix b b' (torsionQuotientMap f)).det})
      ≤ (min s r : ℕ) := by
  refine length_span_det_le_min_of_smul_mem_range
    (fun a ha => smul_mem_range_toLin'_toMatrix f e b b' ha) ?_
  rw [← (quotientRangeEquivToLin' b b' (torsionQuotientMap f)).length_eq]
  exact length_coker_torsionQuotient_le f e

/-- **The basis-free form of the bound.**  The length of the cokernel of the induced map on
torsion-free quotients is at most `min s r`; it is the order of vanishing of the determinant,
and does not refer to a choice of bases. -/
theorem length_coker_torsionQuotient_le_min
    (b : Module.Basis (Fin r) A (M ⧸ Submodule.torsion A M))
    (b' : Module.Basis (Fin r) A (M' ⧸ Submodule.torsion A M')) :
    Module.length A ((M' ⧸ Submodule.torsion A M') ⧸ LinearMap.range (torsionQuotientMap f))
      ≤ (min s r : ℕ) := by
  rcases le_total s r with h | h
  · rw [min_eq_left h]
    exact length_coker_torsionQuotient_le f e
  · rw [min_eq_right h,
      (quotientRangeEquivToLin' b b' (torsionQuotientMap f)).length_eq,
      matrix_cokerLen_eq_spanLen A r _ (det_ne_zero_of_smul_mem_range
        fun a ha => smul_mem_range_toLin'_toMatrix f e b b' ha)]
    exact length_span_det_le_rank fun a ha => smul_mem_range_toLin'_toMatrix f e b b' ha

/-- **The bound at the generic rank.**  For finite modules whose torsion-free quotients have
rank `r`, the cokernel of the induced map on those quotients has length at most `min s r`; the
quotients are free because a discrete valuation ring is a principal ideal domain. -/
theorem length_coker_torsionQuotient_le_min_of_finrank
    [Module.Finite A M] [Module.Finite A M']
    (hr : Module.finrank A (M ⧸ Submodule.torsion A M) = r)
    (hr' : Module.finrank A (M' ⧸ Submodule.torsion A M') = r) :
    Module.length A ((M' ⧸ Submodule.torsion A M') ⧸ LinearMap.range (torsionQuotientMap f))
      ≤ (min s r : ℕ) :=
  length_coker_torsionQuotient_le_min f e (Module.finBasisOfFinrankEq A _ hr)
    (Module.finBasisOfFinrankEq A _ hr')

end Modules

end Stacks.OrderOfVanishing

end
