module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingSmooth
public import StacksFrontier.RingTheory.FormsTrace.UniversalClassification

/-!
# Comparing two universal nice charts of one finite syntomic algebra

Let `B` be a finite free `A`-algebra with two bases `e`, `e'` whose first vectors are `1`, and let
`g`, `g'` be syntomic-good elements of the universal ring `A_d` whose images under the classifying
maps `c`, `c'` of `e`, `e'` are units of `A`. The two charts `N_g → A` and `N_{g'} → A` are
compared through a single ring `R''`, built from the unit-fixing group `G ⊆ GL_d` of Stacks 05YQ:

* `R_0 = N_g ⊗_ℤ 𝒪(G)` carries the base change `m₁` of the universal table to `N_g` and the
  tautological unit-fixing matrix `γ`; let `act₀ : A_d → R_0` classify the conjugate
  `a(γ, m₁)` of `m₁` by `γ` (Stacks 05YP);
* `R'' = R_0[1/act₀(g')]`, with the maps `pr : N_g → R''` and `act : N_{g'} → R''`.

Then:

* the base changes of the universal carriers along `pr` and along `act` are isomorphic
  `R''`-algebras (`Stacks.FormsTrace.comparisonEquiv`), by the matrix `γ⁻¹`;
* `act(Δ_{g'}) = v · pr(Δ_g)` for a unit `v`, `Δ` denoting the discriminants
  (`Stacks.FormsTrace.comparisonAct_discr`);
* the change of basis matrix `P` from `e` to `e'` and the inverses of `c(g)`, `c'(g')` define
  `ψ : R'' → A` with `ψ ∘ pr` and `ψ ∘ act` the two charts (`Stacks.FormsTrace.comparisonPsi`),
  and after `ψ` the isomorphism of carriers becomes the identity of `B`
  (`Stacks.FormsTrace.exists_comparisonEquiv_compatible`);
* `R''` is smooth over `ℤ`, and for every set of variables `σ` the discriminant `pr(Δ_g)` is a
  nice element for the base change of the universal family to `R''[x_σ]`
  (`Stacks.FormsTrace.discr_comparisonChartRing_nice`).

## Main definitions

* `Stacks.FormsTrace.changeMatrix`: the unit-fixing change of basis matrix of two bases.
* `Stacks.FormsTrace.carrierLift`: the ring map from the algebra of a table to a free algebra
  whose basis has the base changed table.
* `Stacks.FormsTrace.comparisonBase`, `Stacks.FormsTrace.comparisonRing`,
  `Stacks.FormsTrace.comparisonPr`, `Stacks.FormsTrace.comparisonAct`,
  `Stacks.FormsTrace.comparisonEquiv`, `Stacks.FormsTrace.comparisonPsi`: the comparison ring
  and its structure.
* `Stacks.FormsTrace.comparisonChartRing`, `Stacks.FormsTrace.comparisonChartClassify`: the
  polynomial rings over `R''` and their classifying maps.

## Main results

* `Stacks.FormsTrace.ofBasis_eq_conjugationAction`: the table of `e'` is the conjugate of the
  table of `e` by the change of basis matrix.
* `Stacks.FormsTrace.comparisonAct_discr`, `Stacks.FormsTrace.comparisonPsi_comp_pr`,
  `Stacks.FormsTrace.comparisonPsi_comp_act`,
  `Stacks.FormsTrace.exists_comparisonEquiv_compatible`.
* `Stacks.FormsTrace.smooth_comparisonRing`,
  `Stacks.FormsTrace.discr_comparisonChartRing_mem_nonZeroDivisors`,
  `Stacks.FormsTrace.discr_comparisonChartRing_nice`.

## Implementation notes

As for the charts themselves, the comparison ring, the coordinate ring of `G` used in it, and the
polynomial rings over `R''` are type synonyms carrying only their ring and algebra structures, so
that their `ℤ`-algebra structure is the canonical one, which generic statements about
`Ω[A⁄ℤ]` and tensor products over `ℤ` see.

## References

* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section Conjugation

/-- The inverse of a unit-fixing matrix commutes with extension of scalars, entrywise. -/
theorem unitFixingMatrix_map_inv_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : UnitFixingMatrix R d) (k l : Fin d) :
    (UnitFixingMatrix.map f g).1⁻¹ k l = f (g.1⁻¹ k l) := by
  change (Matrix.GeneralLinearGroup.map f g.1)⁻¹ k l = _
  rw [← Matrix.GeneralLinearGroup.map_inv]
  rfl

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Conjugation commutes with extension of scalars** (Stacks 05YP). -/
theorem map_conjugationAction (f : R →+* S) (g : UnitFixingMatrix R d)
    (m : FiniteFreeAlgebra R d) :
    FiniteFreeAlgebra.map f (conjugationAction conjugationPreservesAlgebraLaws g m) =
      conjugationAction conjugationPreservesAlgebraLaws (UnitFixingMatrix.map f g)
        (FiniteFreeAlgebra.map f m) := by
  refine ext_coeff fun i j k => ?_
  change f (conjugationCoefficients g m i j k) =
    conjugationCoefficients (UnitFixingMatrix.map f g) (FiniteFreeAlgebra.map f m) i j k
  simp only [conjugationCoefficients, map_sum, map_mul, unitFixingMatrix_map_inv_apply,
    FiniteFreeAlgebra.map_coeff]
  rfl

/-- **Classifying maps commute with extension of scalars.** -/
theorem classify_map_eq_comp (f : R →+* S) (m : FiniteFreeAlgebra R d) :
    (FiniteFreeAlgebra.map f m).classify = f.comp m.classify :=
  hom_ext_of_tableOfHom_eq (by rw [tableOfHom_classify, ← map_tableOfHom, tableOfHom_classify])

/-- The coordinates of the `i`th vector of the standard basis of a carrier. -/
private theorem carrier_basis_apply_coord {R : Type*} [CommRing R] (m : FiniteFreeAlgebra R d)
    (i k : Fin d) : Carrier.basis m i k = if k = i then 1 else 0 := by
  rw [Carrier.basis_apply, Carrier.basisVector_apply]

end Conjugation

section ChangeOfBasis

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The change of basis matrix** of two bases `e`, `e'` of `B` over `A` with first vector `1`:
the matrix `P` with `e' j = ∑ᵢ P i j • e i`, inverse to the change of basis matrix from `e'` to
`e`. It fixes the first standard basis vector, since `e' 0 = e 0 = 1`. -/
def changeMatrix (e e' : Module.Basis (Fin d) A B) (he : e 0 = 1) (he' : e' 0 = 1) :
    UnitFixingMatrix A d :=
  ⟨⟨e.toMatrix e', e'.toMatrix e, e.toMatrix_mul_toMatrix_flip e',
      e'.toMatrix_mul_toMatrix_flip e⟩, fun k => by
    change e.toMatrix e' k 0 = _
    rw [Module.Basis.toMatrix_apply, he', ← he, e.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl⟩

/-- The entries of the change of basis matrix are the coordinates of `e'` in `e`. -/
theorem changeMatrix_apply (e e' : Module.Basis (Fin d) A B) (he : e 0 = 1) (he' : e' 0 = 1)
    (i j : Fin d) :
    ((changeMatrix e e' he he').1 : Matrix (Fin d) (Fin d) A) i j = e.repr (e' j) i := rfl

/-- The entries of the inverse change of basis matrix are the coordinates of `e` in `e'`. -/
theorem changeMatrix_inv_apply (e e' : Module.Basis (Fin d) A B) (he : e 0 = 1)
    (he' : e' 0 = 1) (i j : Fin d) :
    (((changeMatrix e e' he he').1⁻¹ : Matrix.GeneralLinearGroup (Fin d) A) :
      Matrix (Fin d) (Fin d) A) i j = e'.repr (e j) i := rfl

/-- **The table of `e'` is the conjugate of the table of `e`** by the change of basis matrix
(Stacks 05YQ, clause (a) of the proof). -/
theorem ofBasis_eq_conjugationAction (e e' : Module.Basis (Fin d) A B) (he : e 0 = 1)
    (he' : e' 0 = 1) :
    ofBasis e' he' = conjugationAction conjugationPreservesAlgebraLaws
      (changeMatrix e e' he he') (ofBasis e he) := by
  classical
  let n := conjugationAction conjugationPreservesAlgebraLaws (changeMatrix e e' he he')
    (ofBasis e he)
  let Ψ : B ≃ₐ[A] Carrier n := (algEquivCarrierOfBasis e he).trans
    (conjugationIso conjugationPreservesAlgebraLaws (changeMatrix e e' he he')
      (ofBasis e he)).toAlgEquiv
  refine (ofBasis_eq_of_algEquiv Ψ e' (Carrier.basis n) he' (Carrier.basis_zero n)
    fun i => ?_).trans (ofBasis_carrierBasis n)
  refine Carrier.ext fun k => ?_
  have hP : (e'.toMatrix e * e.toMatrix e') k i = (1 : Matrix (Fin d) (Fin d) A) k i := by
    rw [e'.toMatrix_mul_toMatrix_flip e]
  rw [Matrix.mul_apply, Matrix.one_apply] at hP
  simp only [Module.Basis.toMatrix_apply] at hP
  rw [carrier_basis_apply_coord]
  exact hP

end ChangeOfBasis

section CarrierLift

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra A B]

/-- **The ring map from the algebra of a table to a free algebra with the base changed table.**
If `ψ : R → A` carries the table `m` to the table of a basis `b` of `B` over `A` with first vector
`1`, then `x ↦ ∑ₖ ψ(x k) • b k` is a ring map `Carrier m → B`
(`Stacks.FormsTrace.carrierLift_apply`): it exhibits `B` as the base change of `Carrier m`. -/
def carrierLift (ψ : R →+* A) (m : FiniteFreeAlgebra R d) (b : Module.Basis (Fin d) A B)
    (hb : b 0 = 1) (h : FiniteFreeAlgebra.map ψ m = ofBasis b hb) : Carrier m →+* B :=
  (algEquivCarrierOfBasis b hb).symm.toRingHom.comp
    ((carrierCongr h).toRingHom.comp (Carrier.mapRingHom ψ m))

/-- `Stacks.FormsTrace.carrierLift` in coordinates. -/
theorem carrierLift_apply (ψ : R →+* A) (m : FiniteFreeAlgebra R d)
    (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) (h : FiniteFreeAlgebra.map ψ m = ofBasis b hb)
    (x : Carrier m) : carrierLift ψ m b hb h x = ∑ k, ψ (x k) • b k := by
  classical
  change (algEquivCarrierOfBasis b hb).symm (carrierCongr h (Carrier.mapRingHom ψ m x)) = _
  rw [AlgEquiv.symm_apply_eq]
  refine Carrier.ext fun j => ?_
  refine (carrierCongr_apply h _ j).trans ((Carrier.mapRingHom_apply ψ m x j).trans ?_)
  change ψ (x j) = b.repr (∑ k, ψ (x k) • b k) j
  simp only [map_sum, map_smul, b.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `Stacks.FormsTrace.carrierLift` is semilinear along `ψ`. -/
theorem carrierLift_algebraMap (ψ : R →+* A) (m : FiniteFreeAlgebra R d)
    (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) (h : FiniteFreeAlgebra.map ψ m = ofBasis b hb)
    (r : R) : carrierLift ψ m b hb h (algebraMap R (Carrier m) r) = algebraMap A B (ψ r) := by
  classical
  rw [carrierLift_apply]
  have hc : ∀ k, (algebraMap R (Carrier m) r) k = if k = 0 then r else 0 :=
    fun k => Carrier.algebraMap_coord (m := m) r k
  simp only [hc]
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk])
    (absurd (Finset.mem_univ 0))]
  simp [hb, Algebra.algebraMap_eq_smul_one]

/-- `Stacks.FormsTrace.carrierLift` carries the standard basis to the given basis. -/
theorem carrierLift_basis (ψ : R →+* A) (m : FiniteFreeAlgebra R d)
    (b : Module.Basis (Fin d) A B) (hb : b 0 = 1) (h : FiniteFreeAlgebra.map ψ m = ofBasis b hb)
    (i : Fin d) : carrierLift ψ m b hb h (Carrier.basis m i) = b i := by
  classical
  rw [carrierLift_apply]
  simp only [carrier_basis_apply_coord]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk])
    (absurd (Finset.mem_univ i))]
  simp

end CarrierLift

section StructureIso

/-- The algebra isomorphism of an isomorphism of structures, in coordinates: multiplication by
its matrix. -/
theorem structureIso_toAlgEquiv_apply {R : Type*} [CommRing R] {m n : FiniteFreeAlgebra R d}
    (e : StructureIso m n) (x : Carrier m) (k : Fin d) :
    e.toAlgEquiv x k = ∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * x i := rfl

end StructureIso

section ComparisonRing

variable (d) in
/-- **The coordinate ring of the unit-fixing group** `G ⊆ GL_d` of Stacks 05YQ, as a type synonym
carrying only its commutative ring structure, so that its `ℤ`-algebra structure is the canonical
one. -/
def unitFixingRing : Type u := unitFixingCoordinateRing.{u} d

/-- The ring structure of the coordinate ring of `G`. -/
instance : CommRing (unitFixingRing.{u} d) :=
  inferInstanceAs (CommRing (unitFixingCoordinateRing.{u} d))

variable (d) in
/-- The identification of the coordinate ring of `G` with its type synonym. -/
def unitFixingRingEquiv : unitFixingCoordinateRing.{u} d ≃+* unitFixingRing.{u} d :=
  RingEquiv.refl _

variable (d) in
/-- **The unit-fixing group is smooth over `ℤ`** (Stacks 05YQ). -/
theorem smooth_unitFixingRing : Algebra.Smooth ℤ (unitFixingRing.{u} d) := by
  have h1 : (algebraMap (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d)).Smooth :=
    RingHom.smooth_algebraMap.mpr (smooth_unitFixingCoordinateRing.{u} d)
  have h0 : (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom.Smooth :=
    RingHom.Smooth.of_bijective (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).bijective
  have h2 : (algebraMap ℤ (unitFixingRing.{u} d)).Smooth := by
    have he : algebraMap ℤ (unitFixingRing.{u} d) =
        ((algebraMap (ULift.{u} ℤ) (unitFixingCoordinateRing.{u} d)).comp
          (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom :
            ℤ →+* unitFixingRing.{u} d) := RingHom.ext_int _ _
    rw [he]
    exact h0.comp h1
  exact RingHom.smooth_algebraMap.mp h2

variable (g g' : universalRing d)

/-- The ring `R₀ = N_g ⊗_ℤ 𝒪(G)` of pairs of a point of `D(g)` and a unit-fixing matrix. -/
abbrev comparisonBase : Type u := universalChartBase.{u} g ⊗[ℤ] unitFixingRing.{u} d

/-- The tautological unit-fixing matrix over `R₀`. -/
def comparisonMatrix : UnitFixingMatrix (comparisonBase.{u} g) d :=
  unitFixingHomEquiv d _ ((Algebra.TensorProduct.includeRight :
    unitFixingRing.{u} d →ₐ[ℤ] comparisonBase.{u} g).toRingHom.comp
      (unitFixingRingEquiv.{u} d).toRingHom)

/-- The base change `m₁` of the universal table to `R₀` along `N_g → R₀`. -/
def comparisonTable : FiniteFreeAlgebra (comparisonBase.{u} g) d :=
  tableOfHom ((algebraMap (universalChartBase.{u} g) (comparisonBase.{u} g)).comp
    (universalChartBaseClassify.{u} g))

/-- The conjugate `a(γ, m₁)` of `m₁` by the tautological matrix `γ` (Stacks 05YP). -/
def comparisonConj : FiniteFreeAlgebra (comparisonBase.{u} g) d :=
  conjugationAction conjugationPreservesAlgebraLaws (comparisonMatrix.{u} g) (comparisonTable.{u} g)

/-- The map `act₀ : A_d → R₀` classifying `a(γ, m₁)`. -/
def comparisonAct₀ : universalRing d →+* comparisonBase.{u} g :=
  (comparisonConj.{u} g).classify

/-- **The comparison ring** `R'' = R₀[1/act₀(g')]`, a type synonym for the localization carrying
only its ring structure, its `R₀`-algebra structure and the localization property. -/
def comparisonRing : Type u := Localization.Away (comparisonAct₀.{u} g g')

/-- The ring structure of the comparison ring. -/
instance : CommRing (comparisonRing.{u} g g') :=
  inferInstanceAs (CommRing (Localization.Away (comparisonAct₀.{u} g g')))

/-- The comparison ring is an algebra over `R₀`. -/
instance : Algebra (comparisonBase.{u} g) (comparisonRing.{u} g g') :=
  inferInstanceAs (Algebra _ (Localization.Away (comparisonAct₀.{u} g g')))

/-- The comparison ring is the localization of `R₀` away from `act₀(g')`. -/
instance : IsLocalization.Away (comparisonAct₀.{u} g g') (comparisonRing.{u} g g') :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (comparisonAct₀.{u} g g')))

/-- The comparison ring is flat over `R₀`. -/
instance : Module.Flat (comparisonBase.{u} g) (comparisonRing.{u} g g') :=
  IsLocalization.flat _ (Submonoid.powers (comparisonAct₀.{u} g g'))

/-- **The first projection** `pr : N_g → R''`. -/
def comparisonPr : universalChartBase.{u} g →+* comparisonRing.{u} g g' :=
  (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')).comp
    (algebraMap (universalChartBase.{u} g) (comparisonBase.{u} g))

/-- **The action map** `act : N_{g'} → R''`, induced by `act₀`, under which `g'` is inverted. -/
def comparisonAct : universalChartBase.{u} g' →+* comparisonRing.{u} g g' :=
  let ι : ULift.{u} (universalRing d) →+* universalRing d := ULift.ringEquiv.toRingHom
  IsLocalization.Away.lift (ULift.up g')
    (g := ((algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')).comp (comparisonAct₀.{u}
        g)).comp ι)
    (by exact IsLocalization.Away.algebraMap_isUnit (comparisonAct₀.{u} g g'))

/-- `act` composed with `A_d → N_{g'}` is `act₀` followed by `R₀ → R''`. -/
theorem comparisonAct_comp :
    (comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g') =
      (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')).comp (comparisonAct₀.{u} g) :=
          by
  refine RingHom.ext fun a => ?_
  change comparisonAct.{u} g g' (algebraMap _ _ (ULift.up a)) = _
  exact IsLocalization.Away.lift_eq (ULift.up g')
    (IsLocalization.Away.algebraMap_isUnit (comparisonAct₀.{u} g g')) (ULift.up a)

/-- The table of the base change along `pr` of the universal family over `N_g`. -/
theorem tableOfHom_comparisonPr :
    tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g)) =
      FiniteFreeAlgebra.map (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g'))
        (comparisonTable.{u} g) := by
  rw [comparisonTable, map_tableOfHom]
  rfl

/-- The table of the base change along `act` of the universal family over `N_{g'}`. -/
theorem tableOfHom_comparisonAct :
    tableOfHom ((comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g')) =
      FiniteFreeAlgebra.map (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g'))
        (comparisonConj.{u} g) := by
  rw [comparisonAct_comp, ← map_tableOfHom, comparisonAct₀, tableOfHom_classify]

/-- **The isomorphism of the two base changed universal carriers** over `R''`: the base change
along `pr` of the universal carrier over `N_g` and the base change along `act` of the universal
carrier over `N_{g'}` are isomorphic `R''`-algebras, by the matrix `γ⁻¹`
(`Stacks.FormsTrace.comparisonEquiv_apply`). -/
def comparisonEquiv :
    Carrier (tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g)))
        ≃ₐ[comparisonRing.{u} g g']
      Carrier (tableOfHom ((comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g'))) :=
  (carrierCongr (tableOfHom_comparisonPr g g')).trans
    ((StructureIso.map (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g'))
      (conjugationIso conjugationPreservesAlgebraLaws (comparisonMatrix.{u} g)
        (comparisonTable.{u} g))).toAlgEquiv.trans
      (carrierCongr (tableOfHom_comparisonAct g g').symm))

/-- `Stacks.FormsTrace.comparisonEquiv` in coordinates: multiplication by `γ⁻¹`. -/
theorem comparisonEquiv_apply
    (x : Carrier (tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g))))
    (k : Fin d) :
    comparisonEquiv.{u} g g' x k = ∑ j, algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')
      ((comparisonMatrix.{u} g).1⁻¹ k j) * x j := by
  rw [comparisonEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  refine (carrierCongr_apply _ _ k).trans ((structureIso_toAlgEquiv_apply _ _ k).trans ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg₂ (· * ·) rfl (carrierCongr_apply _ x j)

/-- **Discriminants of the two charts agree up to a unit** in `R''`:
`act(Δ_{g'}) = v · pr(Δ_g)` with `v` a unit (in fact `v = det(γ)²`). -/
theorem comparisonAct_discr :
    ∃ v : comparisonRing.{u} g g', IsUnit v ∧
      comparisonAct.{u} g g' (universalChartBaseClassify.{u} g' (universalDiscr d)) =
        v * comparisonPr.{u} g g' (universalChartBaseClassify.{u} g (universalDiscr d)) := by
  classical
  set R'' := comparisonRing.{u} g g'
  let ι'' := algebraMap (comparisonBase.{u} g) R''
  let T₁ := tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g))
  let T₂ := tableOfHom ((comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g'))
  let M : Matrix (Fin d) (Fin d) R'' :=
    (Matrix.GeneralLinearGroup.map ι'' (comparisonMatrix.{u} g).1⁻¹ :
      Matrix.GeneralLinearGroup _ R'')
  have hΦ : (comparisonEquiv.{u} g g') ∘ (Carrier.basis T₁) =
      Matrix.vecMul (Carrier.basis T₂) (M.map (algebraMap R'' (Carrier T₂))) := by
    funext i
    refine Carrier.ext fun k => ?_
    rw [Function.comp_apply, comparisonEquiv_apply]
    simp only [carrier_basis_apply_coord, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    change _ = (∑ j, Carrier.basis T₂ j * algebraMap R'' (Carrier T₂) (M j i)) k
    rw [Carrier.sum_apply]
    have hterm : ∀ j, (Carrier.basis T₂ j * algebraMap R'' (Carrier T₂) (M j i)) k =
        M j i * (if k = j then 1 else 0) := fun j => by
      rw [mul_comm, ← Algebra.smul_def, Carrier.smul_apply,
        carrier_basis_apply_coord]
    simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have hdisc : Algebra.discr R'' (Carrier.basis T₁) =
      M.det ^ 2 * Algebra.discr R'' (Carrier.basis T₂) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (Carrier.basis T₁) (comparisonEquiv.{u} g g'), hΦ,
      Algebra.discr_of_matrix_vecMul]
  have hunit : IsUnit (M.det ^ 2) :=
    ((Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit _)).pow 2
  rw [discr_tableOfHom, discr_tableOfHom] at hdisc
  refine ⟨↑hunit.unit⁻¹, hunit.unit⁻¹.isUnit, ?_⟩
  change (comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g') (universalDiscr d) = _
  rw [show (comparisonPr.{u} g g') (universalChartBaseClassify.{u} g (universalDiscr d)) =
    ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g)) (universalDiscr d) from rfl,
    hdisc, ← mul_assoc, hunit.val_inv_mul, one_mul]

end ComparisonRing

section Psi

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (e e' : Module.Basis (Fin d) A B) (he : e 0 = 1) (he' : e' 0 = 1) {g g' : universalRing d}
  (hu : IsUnit ((ofBasis e he).classify g)) (hu' : IsUnit ((ofBasis e' he').classify g'))

/-- The chart `N_g → A` of a basis whose classifying map inverts `g`. -/
abbrev chartOfBasis (e : Module.Basis (Fin d) A B) (he : e 0 = 1) {g : universalRing d}
    (hu : IsUnit ((ofBasis e he).classify g)) : universalChartBase.{u} g →+* A :=
  chartBaseLift A e he (g := g) (by exact hu)

omit [Algebra A B] in
/-- The chart of a basis, composed with `A_d → N_g`, is the classifying map. -/
theorem chartOfBasis_comp [Algebra A B] (e : Module.Basis (Fin d) A B) (he : e 0 = 1)
    {g : universalRing d} (hu : IsUnit ((ofBasis e he).classify g)) :
    (chartOfBasis e he hu).comp (universalChartBaseClassify.{u} g) = (ofBasis e he).classify := by
  rw [chartOfBasis, chartBaseLift_comp, Algebra.algebraMap_self, RingHom.id_comp]

/-- The point `𝒪(G) → A` of the unit-fixing group given by the change of basis matrix. -/
def changeMatrixHom : unitFixingRing.{u} d →+* A :=
  ((unitFixingHomEquiv d A).symm (changeMatrix e e' he he')).comp
    (unitFixingRingEquiv.{u} d).symm.toRingHom

/-- The map `R₀ = N_g ⊗ 𝒪(G) → A` given by the chart of `e` and the change of basis matrix. -/
def comparisonPsi₀ : comparisonBase.{u} g →+* A :=
  (Algebra.TensorProduct.lift (chartOfBasis e he hu).toIntAlgHom
    (changeMatrixHom e e' he he').toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom

/-- `ψ₀` restricted to `N_g` is the chart of `e`. -/
theorem comparisonPsi₀_left :
    (comparisonPsi₀ e e' he he' hu).comp
        (algebraMap (universalChartBase.{u} g) (comparisonBase.{u} g)) = chartOfBasis e he hu := by
  refine RingHom.ext fun x => ?_
  change (Algebra.TensorProduct.lift (chartOfBasis e he hu).toIntAlgHom
    (changeMatrixHom e e' he he').toIntAlgHom (fun _ _ => Commute.all _ _)) (x ⊗ₜ 1) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

/-- `ψ₀` carries the tautological matrix `γ` to the change of basis matrix `P`. -/
theorem comparisonPsi₀_matrix :
    UnitFixingMatrix.map (comparisonPsi₀ e e' he he' hu) (comparisonMatrix.{u} g) =
      changeMatrix e e' he he' := by
  rw [comparisonMatrix, ← unitFixingHomEquiv_comp]
  have h : (comparisonPsi₀ e e' he he' hu).comp (((Algebra.TensorProduct.includeRight :
      unitFixingRing.{u} d →ₐ[ℤ] comparisonBase.{u} g).toRingHom).comp
        (unitFixingRingEquiv.{u} d).toRingHom) =
      (unitFixingHomEquiv d A).symm (changeMatrix e e' he he') := by
    refine RingHom.ext fun y => ?_
    change (Algebra.TensorProduct.lift (chartOfBasis e he hu).toIntAlgHom
      (changeMatrixHom e e' he he').toIntAlgHom (fun _ _ => Commute.all _ _))
        (1 ⊗ₜ (unitFixingRingEquiv.{u} d y)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  rw [h]
  exact (unitFixingHomEquiv d A).apply_symm_apply (changeMatrix e e' he he')

/-- `ψ₀` carries the table `m₁` to the table of `e`. -/
theorem comparisonPsi₀_table :
    FiniteFreeAlgebra.map (comparisonPsi₀ e e' he he' hu) (comparisonTable.{u} g) = ofBasis e he :=
        by
  rw [comparisonTable, map_tableOfHom, ← RingHom.comp_assoc, comparisonPsi₀_left,
    chartOfBasis_comp, tableOfHom_classify]

/-- `ψ₀ ∘ act₀` is the classifying map of `e'`: the conjugate of the table of `e` by `P` is the
table of `e'`. -/
theorem comparisonPsi₀_act₀ :
    (comparisonPsi₀ e e' he he' hu).comp (comparisonAct₀.{u} g) = (ofBasis e' he').classify := by
  rw [comparisonAct₀, ← classify_map_eq_comp, comparisonConj, map_conjugationAction,
    comparisonPsi₀_matrix, comparisonPsi₀_table, ← ofBasis_eq_conjugationAction]

/-- **The map `ψ : R'' → A`** determined by the two bases: on `N_g` the chart of `e`, on `𝒪(G)`
the change of basis matrix from `e` to `e'`; it inverts `act₀(g')` because that element maps to
`c'(g')`, a unit. -/
def comparisonPsi : comparisonRing.{u} g g' →+* A :=
  IsLocalization.Away.lift (comparisonAct₀.{u} g g') (g := comparisonPsi₀ e e' he he' hu) (by
    rwa [← RingHom.comp_apply, comparisonPsi₀_act₀])

/-- `ψ` extends `ψ₀`. -/
theorem comparisonPsi_comp_algebraMap :
    (comparisonPsi e e' he he' hu hu').comp
        (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')) =
      comparisonPsi₀ e e' he he' hu :=
  IsLocalization.Away.lift_comp _ _

/-- **`ψ ∘ pr` is the chart of `e`.** -/
theorem comparisonPsi_comp_pr :
    (comparisonPsi e e' he he' hu hu').comp (comparisonPr.{u} g g') = chartOfBasis e he hu := by
  rw [comparisonPr, ← RingHom.comp_assoc, comparisonPsi_comp_algebraMap, comparisonPsi₀_left]

/-- **`ψ ∘ act` is the chart of `e'`.** -/
theorem comparisonPsi_comp_act :
    (comparisonPsi e e' he he' hu hu').comp (comparisonAct.{u} g g') = chartOfBasis e' he' hu' := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (ULift.up.{u} g')) ?_
  refine RingHom.ext fun a => ?_
  have h1 := congrArg (fun φ : universalRing d →+* A => φ a.down)
    (congrArg (fun φ => (comparisonPsi e e' he he' hu hu').comp φ) (comparisonAct_comp g g'))
  have h2 := congrArg (fun φ : universalRing d →+* A => φ a.down) (chartOfBasis_comp e' he' hu')
  have h3 := congrArg (fun φ : universalRing d →+* A => φ a.down)
    (comparisonPsi₀_act₀ e e' he he' hu)
  have h4 := congrArg (fun φ => φ (comparisonAct₀.{u} g a.down))
    (comparisonPsi_comp_algebraMap e e' he he' hu hu')
  simp only [RingHom.comp_apply] at h1 h2 h3 h4
  change comparisonPsi e e' he he' hu hu' (comparisonAct.{u} g g'
    (universalChartBaseClassify.{u} g' a.down)) =
      chartOfBasis e' he' hu' (universalChartBaseClassify.{u} g' a.down)
  rw [h1, h4, h3, h2]

/-- The base change along `ψ` of the table of `pr` is the table of `e`. -/
theorem map_tableOfHom_comparisonPr :
    FiniteFreeAlgebra.map (comparisonPsi e e' he he' hu hu')
        (tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g))) =
      ofBasis e he := by
  rw [map_tableOfHom, ← RingHom.comp_assoc, comparisonPsi_comp_pr, chartOfBasis_comp,
    tableOfHom_classify]

/-- The base change along `ψ` of the table of `act` is the table of `e'`. -/
theorem map_tableOfHom_comparisonAct :
    FiniteFreeAlgebra.map (comparisonPsi e e' he he' hu hu')
        (tableOfHom ((comparisonAct.{u} g g').comp (universalChartBaseClassify.{u} g'))) =
      ofBasis e' he' := by
  rw [map_tableOfHom, ← RingHom.comp_assoc, comparisonPsi_comp_act, chartOfBasis_comp,
    tableOfHom_classify]

/-- **After `ψ`, the comparison isomorphism is the identity of `B`.** The ring maps
`χ₁, χ₂` from the two base changed universal carriers to `B`, semilinear along `ψ` and carrying the
standard bases to `e` and to `e'` (so that each exhibits `B` as the base change along `ψ` of the
corresponding carrier), satisfy `χ₂ ∘ Φ = χ₁` for the comparison isomorphism `Φ`. -/
theorem exists_comparisonEquiv_compatible :
    ∃ (χ₁ : Carrier (tableOfHom ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g)))
        →+* B)
      (χ₂ : Carrier (tableOfHom ((comparisonAct.{u} g g').comp
        (universalChartBaseClassify.{u} g'))) →+* B),
      (∀ r, χ₁ (algebraMap _ _ r) = algebraMap A B (comparisonPsi e e' he he' hu hu' r)) ∧
      (∀ r, χ₂ (algebraMap _ _ r) = algebraMap A B (comparisonPsi e e' he he' hu hu' r)) ∧
      (∀ i, χ₁ (Carrier.basis _ i) = e i) ∧ (∀ i, χ₂ (Carrier.basis _ i) = e' i) ∧
      ∀ x, χ₂ (comparisonEquiv.{u} g g' x) = χ₁ x := by
  classical
  set ψ := comparisonPsi e e' he he' hu hu'
  refine ⟨carrierLift ψ _ e he (map_tableOfHom_comparisonPr e e' he he' hu hu'),
    carrierLift ψ _ e' he' (map_tableOfHom_comparisonAct e e' he he' hu hu'),
    carrierLift_algebraMap _ _ _ _ _, carrierLift_algebraMap _ _ _ _ _,
    carrierLift_basis _ _ _ _ _, carrierLift_basis _ _ _ _ _, fun x => ?_⟩
  rw [carrierLift_apply, carrierLift_apply]
  have hψ : ∀ y, ψ (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g') y) =
      comparisonPsi₀ e e' he he' hu y := fun y =>
    congrArg (fun φ => φ y) (comparisonPsi_comp_algebraMap e e' he he' hu hu')
  have hP : ∀ k j, comparisonPsi₀ e e' he he' hu ((comparisonMatrix.{u} g).1⁻¹ k j) =
      e'.repr (e j) k := fun k j => by
    rw [← unitFixingMatrix_map_inv_apply, comparisonPsi₀_matrix, changeMatrix_inv_apply]
  simp only [comparisonEquiv_apply, map_sum, map_mul, hψ, hP]
  calc ∑ k, (∑ j, e'.repr (e j) k * ψ (x j)) • e' k
      = ∑ j, ψ (x j) • ∑ k, e'.repr (e j) k • e' k := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm]
        exact Finset.sum_comm
    _ = ∑ j, ψ (x j) • e j := by
        simp only [e'.sum_repr]

end Psi

section ComparisonCharts

variable (g g' : universalRing d)

/-- **The comparison ring is smooth over `ℤ`** when `g` is syntomic-good: it is a localization of
`N_g ⊗_ℤ 𝒪(G)`, with `N_g` and `𝒪(G)` smooth over `ℤ`. -/
theorem smooth_comparisonRing {g : universalRing d} (hg : IsSyntomicGood.{u} d g) :
    Algebra.Smooth ℤ (comparisonRing.{u} g g') := by
  have := smooth_unitFixingRing.{u} d
  have h1 : (algebraMap ℤ (universalChartBase.{u} g)).Smooth :=
    RingHom.smooth_algebraMap.mpr (smooth_universalChartBase g hg)
  have h2 : (algebraMap (universalChartBase.{u} g) (comparisonBase.{u} g)).Smooth :=
    RingHom.smooth_algebraMap.mpr inferInstance
  have h3 : (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')).Smooth :=
    RingHom.smooth_algebraMap.mpr (Algebra.Smooth.of_isLocalization_Away (comparisonAct₀.{u} g g'))
  have h : algebraMap ℤ (comparisonRing.{u} g g') =
      (algebraMap (comparisonBase.{u} g) (comparisonRing.{u} g g')).comp
        ((algebraMap (universalChartBase.{u} g) (comparisonBase.{u} g)).comp
          (algebraMap ℤ (universalChartBase.{u} g))) := RingHom.ext_int _ _
  have h4 := (h1.comp h2).comp h3
  rw [← h] at h4
  exact RingHom.smooth_algebraMap.mp h4

/-- **The comparison ring is Noetherian** when `g` is syntomic-good. -/
theorem isNoetherianRing_comparisonRing {g : universalRing d} (hg : IsSyntomicGood.{u} d g) :
    IsNoetherianRing (comparisonRing.{u} g g') := by
  have := smooth_comparisonRing g' hg
  exact Algebra.FiniteType.isNoetherianRing ℤ (comparisonRing.{u} g g')

/-- **`pr(Δ_g)` is a nonzerodivisor of the comparison ring** when `g` is syntomic-good: `Δ_g` is
one in `N_g`, and `N_g → R''` is flat. -/
theorem comparisonPr_discr_mem_nonZeroDivisors {g : universalRing d}
    (hg : IsSyntomicGood.{u} d g) :
    comparisonPr.{u} g g' (universalChartBaseClassify.{u} g (universalDiscr d)) ∈
      (comparisonRing.{u} g g')⁰ := by
  have := smooth_unitFixingRing.{u} d
  have h := discr_universalChartBase_mem_nonZeroDivisors g hg
  rw [discr_tableOfHom] at h
  have h1 := algebraMap_mem_nonZeroDivisors_of_flat (B := comparisonBase.{u} g) h
  exact algebraMap_mem_nonZeroDivisors_of_flat (B := comparisonRing.{u} g g') h1

variable (σ : Type u)

/-- **The polynomial rings over the comparison ring** `R''[x_σ]`, for any type of variables. -/
abbrev comparisonChartRing : Type u := polynomialChart σ (comparisonRing.{u} g g')

/-- The classifying map `A_d → R''[x_σ]` of the base change along `pr` of the universal family. -/
def comparisonChartClassify : universalRing d →+* comparisonChartRing g g' σ :=
  (algebraMap (comparisonRing.{u} g g') (comparisonChartRing g g' σ)).comp
    ((comparisonPr.{u} g g').comp (universalChartBaseClassify.{u} g))

variable {g g'}

/-- **The polynomial rings over the comparison ring are formally smooth over `ℤ`**, so their
modules of differentials are projective. -/
theorem comparisonChartRing_formallySmooth (hg : IsSyntomicGood.{u} d g) :
    Algebra.FormallySmooth ℤ (comparisonChartRing g g' σ) := by
  have := smooth_comparisonRing g' hg
  exact polynomialChart_formallySmooth

/-- **The polynomial rings over the comparison ring have projective differentials over `ℤ`.** -/
theorem comparisonChartRing_projective_kaehler (hg : IsSyntomicGood.{u} d g) :
    Module.Projective (comparisonChartRing g g' σ) Ω[comparisonChartRing g g' σ⁄ℤ] := by
  have := comparisonChartRing_formallySmooth (g' := g') σ hg
  infer_instance

/-- **The polynomial rings over the comparison ring in finitely many variables are Noetherian.** -/
theorem comparisonChartRing_isNoetherianRing [Finite σ] (hg : IsSyntomicGood.{u} d g) :
    IsNoetherianRing (comparisonChartRing g g' σ) := by
  have := isNoetherianRing_comparisonRing g' hg
  exact polynomialChart_isNoetherianRing

/-- **The base change of the universal family to `R''[x_σ]` along `pr` is syntomic.** -/
theorem comparisonChartRing_syntomic (hg : IsSyntomicGood.{u} d g) :
    Algebra.Syntomic (comparisonChartRing g g' σ)
      (Carrier (tableOfHom (comparisonChartClassify g g' σ))) := by
  have := (isSyntomicGood_iff g).mp hg
  have := syntomic_tableOfHom_comp (universalChartBaseClassify.{u} g) (comparisonPr.{u} g g')
  exact syntomic_tableOfHom_comp _ _

/-- **`pr(Δ_g)` is a nonzerodivisor of `R''[x_σ]`**: the discriminant of the base change along
`pr` of the universal family to `R''[x_σ]` is a nonzerodivisor. -/
theorem discr_comparisonChartRing_mem_nonZeroDivisors (hg : IsSyntomicGood.{u} d g) :
    Algebra.discr (comparisonChartRing g g' σ)
        (Carrier.basis (tableOfHom (comparisonChartClassify g g' σ))) ∈
      (comparisonChartRing g g' σ)⁰ := by
  rw [comparisonChartClassify, discr_polynomialChart, discr_tableOfHom]
  exact algebraMap_mem_nonZeroDivisors_of_flat (comparisonPr_discr_mem_nonZeroDivisors g' hg)

/-- **`pr(Δ_g)` is a nice element on `R''[x_σ]`** (Stacks 0FLB, 0FLC): for any type of variables
`σ`, the discriminant of the base change along `pr` of the universal family to `R''[x_σ]`, which
is the image of `pr(Δ_g)`, is a nice element. -/
theorem discr_comparisonChartRing_nice (hg : IsSyntomicGood.{u} d g) :
    IsNiceElement (comparisonChartRing g g' σ)
      (Carrier (tableOfHom (comparisonChartClassify g g' σ)))
      (Algebra.discr (comparisonChartRing g g' σ)
        (Carrier.basis (tableOfHom (comparisonChartClassify g g' σ)))) := by
  have := smooth_comparisonRing g' hg
  refine discr_polynomialChart_nice _ ?_
  rw [discr_tableOfHom]
  exact comparisonPr_discr_mem_nonZeroDivisors g' hg

end ComparisonCharts

end Stacks.FormsTrace

end
