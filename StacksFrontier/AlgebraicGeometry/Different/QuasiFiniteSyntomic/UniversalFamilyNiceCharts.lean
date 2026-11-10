module

public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamilyProperties
public import StacksFrontier.RingTheory.CompleteIntersection.CotangentDeterminant
public import StacksFrontier.RingTheory.QuasiFinite.BaseChange
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

/-!
# Square presentations are locally base changes of nice universal charts

Let `B = A[x_1, …, x_n]/(g_1, …, g_n)` be a square presentation and `q` a prime of `B` at which
`B` is quasi-finite over `A`. Then, near `q`, the presentation is the base change of a chart
`A₀ → B₀[1/h]` of the universal family of Example 0FK8 along a ring map `A₀ → A`, where `A₀` is
a polynomial ring over `ℤ` and the chart is "nice" in the sense of the proof of Tag 0FLA:
`B₀[1/h]` is a domain in which the Jacobian determinant of the universal polynomials is nonzero,
and it is quasi-finite and syntomic over `A₀`. Unlike the universal family itself, which lives in
`Type`, the chart is produced in the universe of `A` and `B`.

## Main definitions

* `Algebra.Presentation.tensorEquivOfRelation`: if the relations of a presentation `P` of `B`
  over `A` are the images of those of a presentation `P₀` of `B₀` over `A₀`, then
  `A ⊗[A₀] B₀ ≃ₐ[A] B`.

## Main results

* `Algebra.Presentation.relationJacobiMatrix_det_eq`: the determinant of the Jacobian matrix of a
  square presentation is the image of the Jacobian determinant of its relations.
* `Algebra.Presentation.syntomic_localizationAway`: a localization `B[1/b]` of an algebra with a
  square presentation is syntomic as soon as it is quasi-finite.
* `AlgebraicGeometry.exists_universalChart_of_quasiFiniteAt`: the existence of the nice universal
  chart, in any universe.

## Implementation notes

The universal family of Example 0FK8 is built over `ℤ[a_{i,E}]`, a ring in `Type`. To produce the
chart in `Type u`, the coefficient ring is replaced by the isomorphic polynomial ring over `ℤ` in
the variables `ULift.{u} (Fin n × MultiIndex n d)`, the universal polynomials by their images, and
the universal quotient ring by the corresponding quotient. Of the properties of the universal
family only two are transported along these isomorphisms: the universal quotient ring is a domain
(it is a polynomial ring over `ℤ`), and the Jacobian determinant of the universal polynomials is
nonzero in it (Stacks 0FK9). Everything else is proved for the lifted family directly, by results
that hold in any universe.

The point `q` is moved into the quasi-finite locus of the universal family by Stacks 00PP
(`Algebra.quasiFiniteAt_baseChange_iff`), which is the ring-theoretic form of Stacks 01TM used in
the proof of Tag 0FKA. The element `h` comes from Zariski's main theorem: a finite type algebra
quasi-finite at a prime is quasi-finite after inverting an element outside it (Stacks 00QA). The
chart `B₀[1/h]` is then a domain because `h` is nonzero, and syntomic because a square
presentation of a quasi-finite algebra is a relative global complete intersection (Stacks 00SW).

## References

* [Stacks Project, Tag 0FLA](https://stacks.math.columbia.edu/tag/0FLA)
* [Stacks Project, Tag 0FKA](https://stacks.math.columbia.edu/tag/0FKA)
* [Stacks Project, Tag 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
* [Stacks Project, Tag 0FK9](https://stacks.math.columbia.edu/tag/0FK9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.Presentation

/-- The determinant of the Jacobian matrix of a square presentation is the image in `B` of the
Jacobian determinant `det (∂ fⱼ / ∂ xᵢ)` of its relations. -/
theorem relationJacobiMatrix_det_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n)) :
    P.relationJacobiMatrix.det =
      algebraMap P.Ring B (AlgebraicGeometry.FullRankJacobianSituation.jacobianDet P.relation) := by
  rw [AlgebraicGeometry.FullRankJacobianSituation.jacobianDet, RingHom.map_det,
    ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [relationJacobiMatrix_apply, Algebra.Generators.algebraMap_apply]

/-- If the relations of `P` are the images of those of `P₀`, the base change of `P₀` and `P`
have the same kernel. -/
theorem ker_baseChange_eq_of_relation {A₀ B₀ A B : Type*} [CommRing A₀] [CommRing B₀] [CommRing A]
    [CommRing B] [Algebra A₀ B₀] [Algebra A₀ A] [Algebra A B] {ι σ : Type*}
    (P₀ : Algebra.Presentation A₀ B₀ ι σ) (P : Algebra.Presentation A B ι σ)
    (hrel : ∀ i, MvPolynomial.map (algebraMap A₀ A) (P₀.relation i) = P.relation i) :
    (P₀.baseChange A).ker = P.ker := by
  rw [← (P₀.baseChange A).span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
  exact congrArg (Ideal.span ·) (congrArg Set.range (funext hrel))

/-- **Base change of a presentation.** If the relations of a presentation `P` of `B` over `A`
are the images of the relations of a presentation `P₀` of `B₀` over `A₀` along `A₀ → A`, then `B`
is the base change `A ⊗[A₀] B₀`. -/
def tensorEquivOfRelation {A₀ B₀ A B : Type*} [CommRing A₀] [CommRing B₀] [CommRing A]
    [CommRing B] [Algebra A₀ B₀] [Algebra A₀ A] [Algebra A B] {ι σ : Type*}
    (P₀ : Algebra.Presentation A₀ B₀ ι σ) (P : Algebra.Presentation A B ι σ)
    (hrel : ∀ i, MvPolynomial.map (algebraMap A₀ A) (P₀.relation i) = P.relation i) :
    A ⊗[A₀] B₀ ≃ₐ[A] B :=
  ((P₀.baseChange A).quotientEquiv.restrictScalars A).symm.trans
    (((Ideal.quotientEquivAlgOfEq (P₀.baseChange A).Ring
      (ker_baseChange_eq_of_relation P₀ P hrel)).restrictScalars A).trans
      (P.quotientEquiv.restrictScalars A))

/-- The class of the variable `xᵢ` in the quotient ring of `P` corresponds to `P.val i`. -/
private theorem quotientEquiv_mk_X {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι σ : Type*} (P : Algebra.Presentation A B ι σ) (i : ι) :
    P.quotientEquiv (Ideal.Quotient.mk _ (MvPolynomial.X i)) = P.val i := by
  rw [quotientEquiv_mk, Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_X]

/-- The base change equivalence of `Algebra.Presentation.tensorEquivOfRelation` is compatible
with the presentations: it carries `1 ⊗ xᵢ` to `xᵢ`. -/
theorem tensorEquivOfRelation_one_tmul_val {A₀ B₀ A B : Type*} [CommRing A₀] [CommRing B₀]
    [CommRing A] [CommRing B] [Algebra A₀ B₀] [Algebra A₀ A] [Algebra A B] {ι σ : Type*}
    (P₀ : Algebra.Presentation A₀ B₀ ι σ) (P : Algebra.Presentation A B ι σ)
    (hrel : ∀ i, MvPolynomial.map (algebraMap A₀ A) (P₀.relation i) = P.relation i) (i : ι) :
    P₀.tensorEquivOfRelation P hrel (1 ⊗ₜ P₀.val i) = P.val i := by
  rw [tensorEquivOfRelation, show (1 : A) ⊗ₜ[A₀] P₀.val i = _ from
    (quotientEquiv_mk_X (P₀.baseChange A) i).symm]
  change P.quotientEquiv (Ideal.quotientEquivAlgOfEq _ (ker_baseChange_eq_of_relation P₀ P hrel)
    ((P₀.baseChange A).quotientEquiv.symm
    ((P₀.baseChange A).quotientEquiv (Ideal.Quotient.mk _ (MvPolynomial.X i))))) = P.val i
  rw [AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlgOfEq_mk, quotientEquiv_mk_X]

/-- **Localizations of square presentations.** If `B` has a presentation over `A` with as many
relations as variables and `B[1/b]` is quasi-finite over `A`, then `B[1/b]` is syntomic over `A`:
adjoining the inverse of `b` as one more variable gives a square presentation of `B[1/b]`, which
is a relative global complete intersection because `B[1/b]` is quasi-finite (Stacks 00SW). -/
theorem syntomic_localizationAway {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin n)) (b : B)
    [Algebra.QuasiFinite A (Localization.Away b)] :
    Algebra.Syntomic A (Localization.Away b) := by
  obtain ⟨c, rfl⟩ := P.algebraMap_surjective b
  let e : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    (finSuccEquiv' (0 : Fin (n + 1))).trans
      ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
  have _ : Algebra.IsRelativeGlobalCompleteIntersection A
      (Localization.Away (algebraMap P.Ring B c)) :=
    ⟨⟨n + 1, n + 1,
      (P.localizationAwayComp c (Localization.Away (algebraMap P.Ring B c))).reindex e e,
      isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl⟩⟩
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _

end Algebra.Presentation

namespace AlgebraicGeometry

/-! ### The universal family in an arbitrary universe -/

section Lifted

variable (n d : ℕ)

/-- The universal coefficient variables `a_{i,E}`, lifted to the universe `u`. -/
private abbrev LiftedVars : Type u := ULift.{u} (Fin n × MultiIndex n d)

/-- The universal coefficient ring is isomorphic to the polynomial ring over `ℤ` in the lifted
variables. -/
private def liftEquiv : universalCoefficientRing n d ≃+* MvPolynomial (LiftedVars.{u} n d) ℤ :=
  (MvPolynomial.renameEquiv ℤ Equiv.ulift.symm).toRingEquiv

/-- The universal polynomials over the lifted coefficient ring. -/
private def liftedPolynomial (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (LiftedVars.{u} n d) ℤ) :=
  MvPolynomial.map (liftEquiv.{u} n d : _ →+* _) (universalPolynomial n d i)

/-- The universal quotient ring over the lifted coefficient ring. -/
private abbrev LiftedQuotientRing : Type u :=
  MvPolynomial (Fin n) (MvPolynomial (LiftedVars.{u} n d) ℤ) ⧸
    Ideal.span (Set.range (liftedPolynomial.{u} n d))

/-- The universal quotient ring is isomorphic to its lift. -/
private def liftedQuotientEquiv : universalQuotientRing n d ≃+* LiftedQuotientRing.{u} n d :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv (Fin n) (liftEquiv.{u} n d)) (by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl)

private theorem isDomain_liftedQuotientRing : IsDomain (LiftedQuotientRing.{u} n d) :=
  have : IsDomain (universalQuotientRing n d) :=
    (Classical.choice (universalQuotientRing_polynomial n d)).isDomain_iff.mpr inferInstance
  (liftedQuotientEquiv.{u} n d).symm.toMulEquiv.isDomain _

/-- The Jacobian determinant of the lifted universal polynomials is nonzero in the lifted
universal quotient ring. -/
private theorem liftedJacobian_ne_zero [NeZero n] [NeZero d] :
    Ideal.Quotient.mk (Ideal.span (Set.range (liftedPolynomial.{u} n d)))
      (FullRankJacobianSituation.jacobianDet (liftedPolynomial.{u} n d)) ≠ 0 := by
  have h : FullRankJacobianSituation.jacobianDet (liftedPolynomial.{u} n d) =
      MvPolynomial.mapEquiv (Fin n) (liftEquiv.{u} n d)
        (FullRankJacobianSituation.jacobianDet (universalPolynomial n d)) := by
    rw [MvPolynomial.mapEquiv_apply, FullRankJacobianSituation.jacobianDet,
      FullRankJacobianSituation.jacobianDet, RingHom.map_det]
    congr 1
    ext i j
    simp [liftedPolynomial, MvPolynomial.pderiv_map]
  rw [h]
  exact (map_ne_zero_iff _ (liftedQuotientEquiv.{u} n d).injective).mpr
    (universalJacobian_ne_zero n d)

end Lifted

/-! ### The nice universal chart -/

/-- **The nice universal charts of the proof of Tag 0FLA, in any universe.** Let
`P : B = A[x_1, …, x_n]/(g_1, …, g_n)` be a square presentation and `q` a prime of `B` at which
`B` is quasi-finite over `A`. Then there are a polynomial ring `A₀ = ℤ[σ]`, a square presentation
`P₀` of an `A₀`-algebra `B₀`, a ring map `φ : A₀ → A` carrying the relations of `P₀` to those of
`P` (so that `B = A ⊗[A₀] B₀` by `Algebra.Presentation.tensorEquivOfRelation`), and `h ∈ B₀`
such that
* `B₀[1/h]` is a domain in which the Jacobian determinant of `P₀` is nonzero,
* `B₀[1/h]` is quasi-finite and syntomic over `A₀`, and
* the image of `h` in `B` does not lie in `q`.

Here `A₀ → B₀` is (a lift to the universe of `A` of) the universal family of Example 0FK8, and
`Ω[A₀⁄ℤ]` is free since `A₀` is a polynomial ring. -/
theorem exists_universalChart_of_quasiFiniteAt {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {n : ℕ} [NeZero n] (P : Algebra.Presentation A B (Fin n) (Fin n))
    (q : Ideal B) [q.IsPrime] [Algebra.QuasiFiniteAt A q] :
    ∃ (σ B₀ : Type u) (_ : CommRing B₀) (_ : Algebra (MvPolynomial σ ℤ) B₀)
      (P₀ : Algebra.Presentation (MvPolynomial σ ℤ) B₀ (Fin n) (Fin n))
      (φ : MvPolynomial σ ℤ →+* A)
      (hφ : ∀ i, MvPolynomial.map φ (P₀.relation i) = P.relation i) (h : B₀),
      IsDomain (Localization.Away h) ∧
        algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0 ∧
        Algebra.QuasiFinite (MvPolynomial σ ℤ) (Localization.Away h) ∧
        Algebra.Syntomic (MvPolynomial σ ℤ) (Localization.Away h) ∧
        letI : Algebra (MvPolynomial σ ℤ) A := φ.toAlgebra
        P₀.tensorEquivOfRelation P hφ (1 ⊗ₜ h) ∉ q := by
  classical
  obtain ⟨d, hd, φ₀, hφ₀⟩ := exists_universalCoefficientSpecialization n P.relation
  let A₀ := MvPolynomial (LiftedVars.{u} n d) ℤ
  let B₀ := LiftedQuotientRing.{u} n d
  let P₀ : Algebra.Presentation A₀ B₀ (Fin n) (Fin n) :=
    Algebra.Presentation.naive (v := liftedPolynomial.{u} n d)
  let φ : A₀ →+* A := φ₀.comp (liftEquiv.{u} n d).symm.toRingHom
  have hφ : ∀ i, MvPolynomial.map φ (P₀.relation i) = P.relation i := fun i ↦ by
    rw [Algebra.Presentation.naive_relation_apply, liftedPolynomial, MvPolynomial.map_map,
      RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, RingHom.comp_id, hφ₀]
  let _ : Algebra A₀ A := φ.toAlgebra
  let E := P₀.tensorEquivOfRelation P hφ
  -- the prime of `B₀` below `q`, at which `B₀` is quasi-finite over `A₀` by Stacks 00PP
  let q' : Ideal (A ⊗[A₀] B₀) := q.comap E.toRingHom
  let q₀ : Ideal B₀ := q'.comap Algebra.TensorProduct.includeRight.toRingHom
  have : Algebra.QuasiFiniteAt A q' := Algebra.QuasiFiniteAt.comap_algEquiv q E
  have : Algebra.QuasiFiniteAt A₀ q₀ := (Algebra.quasiFiniteAt_baseChange_iff A q₀ q' rfl).mp ‹_›
  -- Zariski's main theorem gives `h ∉ q₀` with `B₀[1/h]` quasi-finite over `A₀`
  have : Algebra.WeaklyQuasiFiniteAt A₀ q₀ := by
    rw [Algebra.weaklyQuasiFiniteAt_iff]
    exact .of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective
  obtain ⟨S', hfg, r, hr, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A₀) q₀
  have : Module.Finite A₀ S' := Module.Finite.iff_fg.mpr hfg
  have hqf : Algebra.QuasiFinite A₀ (Localization.Away (r : B₀)) :=
    (Algebra.QuasiFinite.iff_of_algEquiv
      (AlgEquiv.ofBijective (Localization.awayMapₐ S'.val r) hbij)).mp inferInstance
  have : IsDomain B₀ := isDomain_liftedQuotientRing.{u} n d
  have hle : Submonoid.powers (r : B₀) ≤ nonZeroDivisors B₀ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors fun h0 ↦ hr (h0 ▸ q₀.zero_mem)
  have hdom : IsDomain (Localization.Away (r : B₀)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (r : B₀)) _ hle
  refine ⟨LiftedVars.{u} n d, B₀, inferInstance, inferInstance, P₀, φ, hφ, r, hdom, ?_, hqf,
    P₀.syntomic_localizationAway r, hr⟩
  rw [P₀.relationJacobiMatrix_det_eq]
  exact (map_ne_zero_iff _ (IsLocalization.injective (Localization.Away (r : B₀)) hle)).mpr
    (liftedJacobian_ne_zero.{u} n d)

end AlgebraicGeometry

end
