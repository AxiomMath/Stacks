module

public import StacksFrontier.RingTheory.FormsTrace.UniversalChart

/-!
# Finite syntomic algebras are covered by universal nice charts

Let `B` be a finite free `A`-algebra of rank `d ≥ 1` with a basis `e` whose first vector is `1`,
and let `c : A_d → A` be the map classifying the structure constants of `e`. If `A → B` is
syntomic, the classifying morphism `Spec(A) → X_d` lands in the open `U_d` of Tag 0FL0, which is
covered by the principal opens `D(g)` it contains; hence the elements `c(g)`, for `g`
syntomic-good, generate the unit ideal of `A`. Over an `A`-algebra `A'` in which `c(g)` is
invertible, the map `N_g = A_d[1/g] → A'` induced by `c` exhibits `A' ⊗_A B`, with the basis
`1 ⊗ e`, as the base change of the universal family over `N_g`.

## Main definitions

* `Stacks.FormsTrace.carrierCongr`: the identity isomorphism between the algebras of two equal
  tables.
* `Stacks.FormsTrace.chartBaseLift`: the map `N_g → A'` induced by the classifying map.
* `Stacks.FormsTrace.algEquivCarrierOfBasis'`: the identification of `B` with the algebra of the
  table of its classifying map.
* `Stacks.FormsTrace.chartBaseChangeAlgEquiv`: the identification of `A' ⊗_A B` with the base
  change of the universal carrier over `N_g` along `N_g → A'`.

## Main results

* `Stacks.FormsTrace.tableOfHom_classify`: the table of a classifying map is the table itself.
* `Stacks.FormsTrace.span_classify_isSyntomicGood_eq_top`: the classifying images of the good
  elements generate the unit ideal.
* `Stacks.FormsTrace.chartBaseLift_comp`: `N_g → A'` composed with `A_d → N_g` is the
  classifying map followed by `A → A'`.
* `Stacks.FormsTrace.chartBaseChangeAlgEquiv_tmul_basis`: the identification matches the bases.

## References

* [Stacks Project, Tag 0FL4](https://stacks.math.columbia.edu/tag/0FL4)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section Congr

variable {R : Type*} [CommRing R]

/-- The identity map between the algebras of two equal tables, as an algebra isomorphism. -/
def carrierCongr {m n : FiniteFreeAlgebra R d} (h : m = n) : Carrier m ≃ₐ[R] Carrier n := by
  subst h
  exact AlgEquiv.refl

/-- `Stacks.FormsTrace.carrierCongr` does not change coordinates. -/
@[simp] theorem carrierCongr_apply {m n : FiniteFreeAlgebra R d} (h : m = n) (x : Carrier m)
    (k : Fin d) : carrierCongr h x k = x k := by
  subst h
  rfl

/-- The table of the classifying map of a table is that table. -/
theorem tableOfHom_classify (m : FiniteFreeAlgebra R d) : tableOfHom m.classify = m :=
  ext_coeff fun i j k => by rw [tableOfHom_coeff, classify_universalStructureConstant]

end Congr

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The universal nice charts cover a finite syntomic algebra** (Stacks 0FL4). If `B` is free
over `A` on a basis `e` with `e 0 = 1` and `A → B` is syntomic, the images under the classifying
map of `e` of the syntomic-good elements generate the unit ideal of `A`. -/
theorem span_classify_isSyntomicGood_eq_top (e : Module.Basis (Fin d) A B) (he : e 0 = 1)
    [Algebra.Syntomic A B] :
    Ideal.span {a : A | ∃ g : universalRing d, IsSyntomicGood.{u} d g ∧
      (ofBasis e he).classify g = a} = ⊤ := by
  classical
  set c := (ofBasis e he).classify
  have : Algebra.Syntomic A (Carrier (tableOfHom c)) := by
    rw [tableOfHom_classify]
    exact Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv (algEquivCarrierOfBasis e he)
  have hU := (syntomic_tableOfHom_iff c).mp inferInstance
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let t : Spec (.of A) := ⟨m, hm.isPrime⟩
  let x : PrimeSpectrum (ULift.{u} (universalRing d)) :=
    Spec.map (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
      ULift.{u} (universalRing d) →+* universalRing d))) t
  have hxU : (x : scheme.{u} d) ∈ (universalSyntomicOpen.{u} d : Set (scheme.{u} d)) := hU t
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := ULift.{u} (universalRing d))).exists_subset_of_mem_open hxU
      (universalSyntomicOpen.{u} d).isOpen
  exact hxf (hle (Ideal.subset_span ⟨f.down, fun y hy => hfU hy, rfl⟩))

variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The map `N_g = A_d[1/g] → A'` induced by the classifying map of a basis, when the image of `g`
in `A'` is a unit. -/
def chartBaseLift (e : Module.Basis (Fin d) A B) (he : e 0 = 1) {g : universalRing d}
    (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g))) :
    universalChartBase.{u} g →+* A' :=
  let ι : ULift.{u} (universalRing d) →+* universalRing d := ULift.ringEquiv.toRingHom
  IsLocalization.Away.lift (ULift.up g)
    (g := ((algebraMap A A').comp (ofBasis e he).classify).comp ι) (by exact hu)

variable {A'}

/-- `N_g → A'` composed with `A_d → N_g` is the classifying map followed by `A → A'`. -/
theorem chartBaseLift_comp (e : Module.Basis (Fin d) A B) (he : e 0 = 1) {g : universalRing d}
    (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g))) :
    (chartBaseLift A' e he hu).comp (universalChartBaseClassify.{u} g) =
      (algebraMap A A').comp (ofBasis e he).classify := by
  refine RingHom.ext fun a => ?_
  change chartBaseLift A' e he hu (algebraMap _ _ (ULift.up a)) = _
  exact IsLocalization.Away.lift_eq (ULift.up g) hu (ULift.up a)

/-- The table of the base change to `A'` of the universal family over `N_g` is the base change
of the table of `e`. -/
theorem tableOfHom_chartBaseLift (e : Module.Basis (Fin d) A B) (he : e 0 = 1)
    {g : universalRing d} (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g))) :
    FiniteFreeAlgebra.map (chartBaseLift A' e he hu) (tableOfHom (universalChartBaseClassify.{u}
        g)) =
      FiniteFreeAlgebra.map (algebraMap A A') (ofBasis e he) := by
  rw [map_tableOfHom, chartBaseLift_comp, ← map_tableOfHom, tableOfHom_classify]

/-- The first vector of the base changed basis `1 ⊗ e` of `A' ⊗_A B` is `1`. -/
theorem baseChange_basis_zero_eq_one (e : Module.Basis (Fin d) A B) (he : e 0 = 1) :
    e.baseChange A' 0 = 1 := by
  rw [Module.Basis.baseChange_apply, he]
  rfl

/-- The table of `1 ⊗ e` is the base change of the table of `e`. -/
theorem ofBasis_baseChange_eq_map (e : Module.Basis (Fin d) A B) (he : e 0 = 1) :
    ofBasis (e.baseChange A') (baseChange_basis_zero_eq_one e he) =
      FiniteFreeAlgebra.map (algebraMap A A') (ofBasis e he) := by
  refine (ofBasis_map (algebraMap A A')
    (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom (fun r => ?_)
    e he (e.baseChange A') (baseChange_basis_zero_eq_one e he) (fun i => ?_)).symm
  · change Algebra.TensorProduct.includeRight (algebraMap A B r) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A A' (A' ⊗[A] B)]
  · simp [Module.Basis.baseChange_apply]

/-- **The base change identification** (Stacks 0FL4). When `c(g)` is a unit in `A'`, the algebra
`A' ⊗_A B` is the base change along `N_g → A'` of the universal carrier over `N_g`: an
`A'`-algebra isomorphism `A' ⊗_A B ≃ Carrier (m_g.map (N_g → A'))`, carrying `1 ⊗ e i` to the
`i`-th standard basis vector (`Stacks.FormsTrace.chartBaseChangeAlgEquiv_tmul_basis`). -/
def chartBaseChangeAlgEquiv (e : Module.Basis (Fin d) A B) (he : e 0 = 1) {g : universalRing d}
    (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g))) :
    A' ⊗[A] B ≃ₐ[A'] Carrier (FiniteFreeAlgebra.map (chartBaseLift A' e he hu)
      (tableOfHom (universalChartBaseClassify.{u} g))) :=
  (algEquivCarrierOfBasis (e.baseChange A') (baseChange_basis_zero_eq_one e he)).trans
    (carrierCongr ((ofBasis_baseChange_eq_map e he).trans (tableOfHom_chartBaseLift e he hu).symm))

/-- The base change identification carries `1 ⊗ e i` to the `i`-th standard basis vector. -/
theorem chartBaseChangeAlgEquiv_tmul_basis (e : Module.Basis (Fin d) A B) (he : e 0 = 1)
    {g : universalRing d} (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g))) (i : Fin d) :
    chartBaseChangeAlgEquiv e he hu (1 ⊗ₜ[A] e i) = Carrier.basisVector _ i := by
  classical
  refine Carrier.ext fun k => ?_
  simp only [chartBaseChangeAlgEquiv, AlgEquiv.trans_apply, carrierCongr_apply,
    Carrier.basisVector_apply]
  change (e.baseChange A').repr (1 ⊗ₜ[A] e i) k = _
  rw [← Module.Basis.baseChange_apply, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- The base change identification in coordinates:
`x = ∑ₖ (chartBaseChangeAlgEquiv x)ₖ · (1 ⊗ e k)`. -/
theorem chartBaseChangeAlgEquiv_symm_apply (e : Module.Basis (Fin d) A B) (he : e 0 = 1)
    {g : universalRing d} (hu : IsUnit (algebraMap A A' ((ofBasis e he).classify g)))
    (x : Carrier (FiniteFreeAlgebra.map (chartBaseLift A' e he hu)
      (tableOfHom (universalChartBaseClassify.{u} g)))) :
    (chartBaseChangeAlgEquiv e he hu).symm x = ∑ k, x k • (1 ⊗ₜ[A] e k) := by
  classical
  apply (chartBaseChangeAlgEquiv e he hu).injective
  rw [AlgEquiv.apply_symm_apply, map_sum]
  refine Carrier.ext fun k => ?_
  rw [Carrier.sum_apply]
  simp only [map_smul, chartBaseChangeAlgEquiv_tmul_basis, Carrier.smul_apply,
    Carrier.basisVector_apply]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp

end Stacks.FormsTrace

end
