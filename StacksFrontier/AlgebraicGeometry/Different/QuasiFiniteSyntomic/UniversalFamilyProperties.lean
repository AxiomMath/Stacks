module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamily
public import StacksFrontier.AlgebraicGeometry.Different.Support.UniversalPolynomialPresentation
public import StacksFrontier.AlgebraicGeometry.Different.Support.UniversalSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Open
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.SquareJacobian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# Properties of the universal quasi-finite family

The universal quasi-finite family `Y_{n,d} ⟶ X_{n,d}` of Example 0FK8 is locally quasi-finite
and syntomic, both `X_{n,d}` and `Y_{n,d}` are irreducible and regular schemes, and a dense open
subscheme of `Y_{n,d}` is étale over `X_{n,d}`.

## Main results

* `AlgebraicGeometry.universalBaseScheme_irreducibleSpace`: `X_{n,d}` is irreducible.
* `AlgebraicGeometry.universalBaseScheme_isRegular`: `X_{n,d}` is regular.
* `AlgebraicGeometry.universalQuasiFiniteScheme_irreducibleSpace`: `Y_{n,d}` is irreducible.
* `AlgebraicGeometry.universalQuasiFiniteScheme_isRegular`: `Y_{n,d}` is regular.
* `AlgebraicGeometry.universalQuasiFiniteMorphism_syntomic`: `Y_{n,d} ⟶ X_{n,d}` is syntomic.
* `AlgebraicGeometry.exists_dense_opens_etale_universalQuasiFiniteMorphism`: a dense open
  subscheme of `Y_{n,d}` is étale over `X_{n,d}`.

## Implementation notes

The coefficient scheme is the spectrum of a polynomial ring over `ℤ`, which gives both its
irreducibility and its regularity. Irreducibility of `Y_{n,d}` uses that the universal quotient
ring is itself a polynomial ring, hence a domain, so the ambient affine scheme is irreducible;
`Y_{n,d}` is then a nonempty open subscheme of it, nonempty because the specialized fibre over a
`ℚ`-point supplies a point of the quasi-finite open.

Local quasi-finiteness of the morphism is already part of the construction of `Y_{n,d}`, so the
tag is attached to that instance rather than restated.

Regularity and syntomicity of `Y_{n,d}` are read off from the charts `Spec(B_b) ⊆ Y_{n,d}` given
by the elements `b` of the universal quotient ring `B` whose basic open lies inside the
quasi-finite locus; these cover `Y_{n,d}` because the basic opens are a basis of `Spec(B)`. On
such a chart `B_b` is a localization of the polynomial ring `B`, hence regular, and it is
`A[x_1, …, x_n, 1/b]/(f_1, …, f_n)` — a square presentation after adjoining the inverse of `b` as
one more variable — so it is a relative global complete intersection by Stacks 00SP, the
dimension condition being automatic from quasi-finiteness, and therefore syntomic by Stacks 00SW.
That is the argument of Stacks 0BWE (4) ⟹ (5) ⟹ (1) run on the affine charts.

The dense open is a named chart rather than the whole étale locus: inverting the Jacobian
determinant of the universal polynomials makes the family étale, by the Jacobian criterion
`AlgebraicGeometry.FullRankJacobianSituation.etale_away_jacobianDet`. That determinant is nonzero
in `B` because the specialization of Example 0FK8 sending `f_i` to `x_i^d - 1` carries it to
`∏ d x_i^{d-1}`, which is a unit in `ℚ[x_1, …, x_n]/(x_1^d - 1, …, x_n^d - 1)`; so the chart is a
nonempty open of the irreducible `Y_{n,d}` and is therefore dense.

## References

* [Stacks Project, Tag 0FK9](https://stacks.math.columbia.edu/tag/0FK9)
* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 00SW](https://stacks.math.columbia.edu/tag/00SW)
* [Stacks Project, Tag 024Y](https://stacks.math.columbia.edu/tag/024Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

add_to_stacks 0FK9 "locally_quasi_finite"
  AlgebraicGeometry.universalQuasiFiniteMorphism_locallyQuasiFinite

/-- The universal coefficient scheme `X_{n,d}` is irreducible. -/
@[stacks 0FK9 "x_irreducible"]
instance universalBaseScheme_irreducibleSpace (n d : ℕ) [NeZero n] [NeZero d] :
    IrreducibleSpace (universalBaseScheme n d) := by
  change IrreducibleSpace (AlgebraicGeometry.Spec (.of _))
  infer_instance

/-- The universal coefficient scheme `X_{n,d}` is regular. -/
@[stacks 0FK9 "x_regular"]
theorem universalBaseScheme_isRegular (n d : ℕ) [NeZero n] [NeZero d] :
    IsRegular (universalBaseScheme n d) := by
  intro x
  exact ⟨⟨⊤, isAffineOpen_top (Spec (.of _))⟩, trivial,
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv⟩

private theorem isDomain_universalQuotientRing (n d : ℕ) : IsDomain (universalQuotientRing n d) :=
  (Classical.choice (universalQuotientRing_polynomial n d)).isDomain_iff.mpr inferInstance

/-- The universal quasi-finite open subscheme `Y_{n,d}` is irreducible. -/
@[stacks 0FK9 "y_irreducible"]
instance universalQuasiFiniteScheme_irreducibleSpace
    (n d : ℕ) [NeZero n] [NeZero d] :
    IrreducibleSpace (universalQuasiFiniteScheme n d) := by
  classical
  have _ := isDomain_universalQuotientRing n d
  have _ : IrreducibleSpace (universalAmbientScheme n d) :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (universalQuotientRing n d))))
  have _ : Nontrivial (specializedFiberRing n d) := specializedFiberRing_nontrivial n d
  exact Subtype.irreducibleSpace
    ⟨⟨_, specializedFiberRing_mem_universalQuasiFiniteOpen n d
        (Classical.choice inferInstance)⟩,
      (IrreducibleSpace.isIrreducible_univ _).2.open_subset (universalQuasiFiniteOpen n d).2
        (Set.subset_univ _)⟩

/-! ### The affine charts of the quasi-finite locus

For an element `b` of the universal quotient ring `B` the basic open of `b` in `Spec(B)` is
`Spec(B_b)`; when it lies inside the quasi-finite locus it is a chart of `Y_{n,d}`.
-/

section Charts

variable (n d : ℕ) [NeZero n] [NeZero d]

/-- The chart `Spec(B_b) ⟶ Spec(B)` of the universal family obtained by inverting an element `b`
of the universal quotient ring. -/
private def awayChart (b : universalQuotientRing n d) :
    Spec (.of (Localization.Away b)) ⟶ universalAmbientScheme n d :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (universalQuotientRing n d) (Localization.Away b)))

private instance isOpenImmersion_awayChart (b : universalQuotientRing n d) :
    IsOpenImmersion (awayChart n d b) :=
  Scheme.instIsOpenImmersionMapOfHomAwayAlgebraMap b

private theorem range_awayChart (b : universalQuotientRing n d) :
    Set.range ⇑(awayChart n d b) =
      (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (universalQuotientRing n d))) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away b) b

private theorem awayChart_comp (b : universalQuotientRing n d) :
    awayChart n d b ≫ universalAmbientMorphism n d =
      Spec.map (CommRingCat.ofHom
        (algebraMap (universalCoefficientRing n d) (Localization.Away b))) := by
  have h : CommRingCat.ofHom
        (algebraMap (universalCoefficientRing n d) (Localization.Away b)) =
      CommRingCat.ofHom (algebraMap (universalCoefficientRing n d) (universalQuotientRing n d))
        ≫ CommRingCat.ofHom
          (algebraMap (universalQuotientRing n d) (Localization.Away b)) := by
    rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [h, Spec.map_comp]
  rfl

/-- The elements of the universal quotient ring whose basic open lies in the quasi-finite
locus. -/
private abbrev AwayCond (b : universalQuotientRing n d) : Prop :=
  Set.range ⇑(awayChart n d b) ⊆
    (universalQuasiFiniteOpen n d : Set (universalAmbientScheme n d))

/-- The chart `Spec(B_b) ⟶ Y_{n,d}` cut out by such an element. -/
private def awayLift (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    Spec (.of (Localization.Away b)) ⟶ (universalQuasiFiniteOpen n d).toScheme :=
  IsOpenImmersion.lift (universalQuasiFiniteOpen n d).ι (awayChart n d b)
    (by rwa [Scheme.Opens.range_ι])

private instance isOpenImmersion_awayLift (b : universalQuotientRing n d)
    (hb : AwayCond n d b) : IsOpenImmersion (awayLift n d b hb) := by
  unfold awayLift
  infer_instance

private theorem awayLift_ι (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    awayLift n d b hb ≫ (universalQuasiFiniteOpen n d).ι = awayChart n d b :=
  IsOpenImmersion.lift_fac _ _ _

private theorem awayLift_comp (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    awayLift n d b hb ≫ (universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d =
      Spec.map (CommRingCat.ofHom
        (algebraMap (universalCoefficientRing n d) (Localization.Away b))) := by
  rw [← Category.assoc, awayLift_ι, awayChart_comp]

private theorem exists_awayLift_eq (y : (universalQuasiFiniteOpen n d).toScheme) :
    ∃ (b : universalQuotientRing n d) (hb : AwayCond n d b)
      (z : Spec (.of (Localization.Away b))), awayLift n d b hb z = y := by
  have hy : (universalQuasiFiniteOpen n d).ι y ∈
      (universalQuasiFiniteOpen n d : Set (universalAmbientScheme n d)) := by
    rw [← Scheme.Opens.range_ι]
    exact Set.mem_range_self y
  obtain ⟨_, ⟨b, rfl⟩, hmem, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy
      (universalQuasiFiniteOpen n d).2
  have hb : AwayCond n d b := by rwa [AwayCond, range_awayChart]
  obtain ⟨z, hz⟩ : (universalQuasiFiniteOpen n d).ι y ∈ Set.range ⇑(awayChart n d b) := by
    rwa [range_awayChart]
  refine ⟨b, hb, z, Scheme.Hom.injective (universalQuasiFiniteOpen n d).ι ?_⟩
  calc (universalQuasiFiniteOpen n d).ι (awayLift n d b hb z)
      = (awayLift n d b hb ≫ (universalQuasiFiniteOpen n d).ι) z := rfl
    _ = awayChart n d b z := by rw [awayLift_ι]
    _ = _ := hz

/-- The cover of `Y_{n,d}` by the charts `Spec(B_b)` it contains. -/
private def awayCover : ((universalQuasiFiniteOpen n d).toScheme).OpenCover :=
  Scheme.Cover.mkOfCovers { b : universalQuotientRing n d // AwayCond n d b }
    (fun b => Spec (.of (Localization.Away b.1)))
    (fun b => awayLift n d b.1 b.2)
    (fun y => by
      obtain ⟨b, hb, z, hz⟩ := exists_awayLift_eq n d y
      exact ⟨⟨b, hb⟩, z, hz⟩)

omit [NeZero n] [NeZero d] in
/-- The universal quotient ring is regular, being a polynomial ring over `ℤ`. -/
private theorem isRegularRing_universalQuotientRing :
    IsRegularRing (universalQuotientRing n d) :=
  IsRegularRing.of_ringEquiv (Classical.choice (universalQuotientRing_polynomial n d)).symm

/-- A ring-hom local property holds on the chart `Spec(B_b) ⟶ X_{n,d}` iff it holds for the
algebra map `A ⟶ B_b`. -/
private theorem awayLift_comp_iff {P : MorphismProperty Scheme.{0}}
    {Q : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    P (awayLift n d b hb ≫ (universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d) ↔
      Q (algebraMap (universalCoefficientRing n d) (Localization.Away b)) := by
  rw [awayLift_comp]
  exact HasRingHomProperty.Spec_iff

/-- On a chart of `Y_{n,d}` the universal family is a quasi-finite algebra. -/
private theorem quasiFinite_away (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    Algebra.QuasiFinite (universalCoefficientRing n d) (Localization.Away b) := by
  have _ : LocallyQuasiFinite
      ((universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d) :=
    universalQuasiFiniteMorphism_locallyQuasiFinite n d
  exact RingHom.quasiFinite_algebraMap.mp
    ((awayLift_comp_iff (P := @LocallyQuasiFinite) n d b hb).mp inferInstance)

/-- On a chart of `Y_{n,d}` the universal family is a syntomic algebra: adjoining the inverse of
`b` as one more variable turns `A[x_1, …, x_n]/(f_1, …, f_n)` localized at `b` into a
presentation with as many relations as variables, which is a relative global complete
intersection because the fibres of a quasi-finite algebra are zero-dimensional. -/
private theorem syntomic_away (b : universalQuotientRing n d) (hb : AwayCond n d b) :
    (algebraMap (universalCoefficientRing n d) (Localization.Away b)).Syntomic := by
  rw [RingHom.syntomic_iff,
    show (algebraMap (universalCoefficientRing n d) (Localization.Away b)).toAlgebra
      = (inferInstance : Algebra (universalCoefficientRing n d) (Localization.Away b)) from
      Algebra.algebra_ext _ _ fun r => rfl]
  classical
  have _ := quasiFinite_away n d b hb
  let Q : Algebra.Presentation (universalCoefficientRing n d) (universalQuotientRing n d)
      (Fin n) (Fin n) := Algebra.Presentation.naive (v := universalPolynomial n d)
  obtain ⟨c, hc⟩ := Q.toGenerators.algebraMap_surjective b
  have hloc : IsLocalization.Away (algebraMap Q.Ring (universalQuotientRing n d) c)
      (Localization.Away b) := by
    rw [hc]
    infer_instance
  let eqv : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    (finSuccEquiv' (0 : Fin (n + 1))).trans
      ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
  have : Algebra.IsRelativeGlobalCompleteIntersection (universalCoefficientRing n d)
      (Localization.Away b) := ⟨⟨n + 1, n + 1,
        (Q.localizationAwayComp c (Localization.Away b)).reindex eqv eqv,
        Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl⟩⟩
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _

/-! ### The Jacobian chart -/

/-- The Jacobian determinant of the universal polynomials, read in the universal quotient
ring. -/
abbrev universalJacobian : universalQuotientRing n d :=
  Ideal.Quotient.mk (universalRelationIdeal n d)
    (FullRankJacobianSituation.jacobianDet (universalPolynomial n d))

/-- The specialization of Example 0FK8 carries the Jacobian determinant of the universal
polynomials to `∏ d x_i^{d-1}`. -/
private theorem map_jacobianDet_specialization :
    MvPolynomial.map (specialization n d)
        (FullRankJacobianSituation.jacobianDet (universalPolynomial n d)) =
      ∏ i : Fin n, ((d : MvPolynomial (Fin n) ℚ) * MvPolynomial.X i ^ (d - 1)) := by
  classical
  have hmat : (MvPolynomial.map (specialization n d)).mapMatrix
        (Matrix.of fun i j => (MvPolynomial.pderiv j) (universalPolynomial n d i)) =
      Matrix.diagonal
        (fun i : Fin n => (d : MvPolynomial (Fin n) ℚ) * MvPolynomial.X i ^ (d - 1)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← MvPolynomial.pderiv_map,
      specialization_universalPolynomial]
    obtain rfl | hij := eq_or_ne i j
    · simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [hij]
  rw [FullRankJacobianSituation.jacobianDet, RingHom.map_det, hmat, Matrix.det_diagonal]

/-- The Jacobian determinant of the universal polynomials is nonzero in the universal quotient
ring: its image in `ℚ[x_1, …, x_n]/(x_1^d - 1, …, x_n^d - 1)` is a unit. -/
theorem universalJacobian_ne_zero : universalJacobian n d ≠ 0 := by
  classical
  set J : Ideal (MvPolynomial (Fin n) ℚ) :=
    Ideal.span (Set.range fun i : Fin n => MvPolynomial.X i ^ d - 1) with hJdef
  have hJrel : ∀ i : Fin n, (MvPolynomial.X i ^ d - 1 : MvPolynomial (Fin n) ℚ) ∈ J :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have hker : J ≤ RingHom.ker (MvPolynomial.eval (fun _ : Fin n => (1 : ℚ))) := by
    rw [hJdef, Ideal.span_le]
    rintro p ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  have hnt : Nontrivial (MvPolynomial (Fin n) ℚ ⧸ J) := by
    refine nontrivial_iff.mpr ⟨1, 0, fun h => ?_⟩
    simpa using congrArg (Ideal.Quotient.lift J _ hker) h
  have hXunit : ∀ i : Fin n, IsUnit (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
    intro i
    have h1 : (Ideal.Quotient.mk J (MvPolynomial.X i)) ^ d = 1 := by
      rw [← map_pow, show (MvPolynomial.X i ^ d : MvPolynomial (Fin n) ℚ)
          = (MvPolynomial.X i ^ d - 1) + 1 by ring, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hJrel i), zero_add, map_one]
    exact isUnit_iff_exists_inv.mpr
      ⟨_, by rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos d), h1]⟩
  have hdunit : IsUnit ((d : MvPolynomial (Fin n) ℚ ⧸ J)) := by
    rw [show ((d : MvPolynomial (Fin n) ℚ ⧸ J)) = algebraMap ℚ _ (d : ℚ) by simp]
    exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast (NeZero.ne d))).map (algebraMap ℚ _)
  have hunit : IsUnit (Ideal.Quotient.mk J
      (MvPolynomial.map (specialization n d)
        (FullRankJacobianSituation.jacobianDet (universalPolynomial n d)))) := by
    rw [map_jacobianDet_specialization, map_prod]
    refine IsUnit.prod_univ_iff.mpr fun i => ?_
    rw [map_mul, map_pow]
    exact hdunit.mul ((hXunit i).pow (d - 1))
  have hle : universalRelationIdeal n d ≤
      Ideal.comap (MvPolynomial.map (specialization n d)) J := by
    rw [universalRelationIdeal, Ideal.span_le]
    rintro p ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, specialization_universalPolynomial]
    exact hJrel i
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  intro hmem
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp (hle hmem))] at hunit
  exact not_isUnit_zero hunit

omit [NeZero n] [NeZero d] in
/-- Inverting the Jacobian determinant of the universal polynomials makes the universal family
étale, by the Jacobian criterion of Stacks 024Y. -/
@[sga "4½ Arcata 2.1.1" "special case"]
private theorem etale_away_universalJacobian :
    Algebra.Etale (universalCoefficientRing n d)
      (Localization.Away (universalJacobian n d)) := by
  have h := FullRankJacobianSituation.etale_away_jacobianDet (universalPolynomial n d)
    (I := universalRelationIdeal n d) rfl (Localization.Away (universalJacobian n d))
  rwa [← IsScalarTower.algebraMap_eq, RingHom.etale_algebraMap] at h

/-- The basic open of the Jacobian determinant lies in the quasi-finite locus. -/
private theorem awayCond_universalJacobian : AwayCond n d (universalJacobian n d) := by
  have _ := etale_away_universalJacobian n d
  have _ : LocallyQuasiFinite
      (awayChart n d (universalJacobian n d) ≫ universalAmbientMorphism n d) := by
    rw [awayChart_comp]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
      (RingHom.quasiFinite_algebraMap.mpr inferInstance)
  rintro _ ⟨z, rfl⟩
  show (universalAmbientMorphism n d).QuasiFiniteAt _
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := awayChart n d (universalJacobian n d))
    (g := universalAmbientMorphism n d)).mp
      ((awayChart n d (universalJacobian n d) ≫
        universalAmbientMorphism n d).quasiFiniteAt z)

/-! ### Regularity, syntomicity, and the dense étale open -/

private theorem isRegular_toScheme : IsRegular ((universalQuasiFiniteOpen n d).toScheme) := by
  classical
  have _ := isRegularRing_universalQuotientRing n d
  intro y
  obtain ⟨b, hb, z, hz⟩ := exists_awayLift_eq n d y
  have _ : IsRegularRing (Localization.Away b) :=
    isRegularRing_of_isLocalization (Submonoid.powers b)
  refine ⟨⟨awayLift n d b hb ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩, ?_, ?_⟩
  · show y ∈ (awayLift n d b hb ''ᵁ ⊤ : ((universalQuasiFiniteOpen n d).toScheme).Opens)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, hz⟩
  · exact IsRegularRing.of_ringEquiv
      ((((awayLift n d b hb).appIso ⊤).trans
        (Scheme.ΓSpecIso (.of (Localization.Away b)))).symm).commRingCatIsoToRingEquiv

private theorem syntomic_toScheme :
    Syntomic ((universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d) := by
  have _ : IsZariskiLocalAtSource @Syntomic.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Syntomic)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Syntomic)
    (awayCover n d)).mpr fun b => ?_
  show Syntomic (awayLift n d b.1 b.2 ≫
    (universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d)
  exact (awayLift_comp_iff (P := @Syntomic) n d b.1 b.2).mpr (syntomic_away n d b.1 b.2)

private theorem exists_dense_opens_etale_toScheme :
    ∃ V : ((universalQuasiFiniteOpen n d).toScheme).Opens,
      Dense (V : Set ((universalQuasiFiniteOpen n d).toScheme)) ∧
        Etale (V.ι ≫ (universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d) := by
  classical
  have _ : IrreducibleSpace ((universalQuasiFiniteOpen n d).toScheme) :=
    universalQuasiFiniteScheme_irreducibleSpace n d
  have hb := awayCond_universalJacobian n d
  have _ := isDomain_universalQuotientRing n d
  have _ : IsDomain (Localization.Away (universalJacobian n d)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (M := Submonoid.powers (universalJacobian n d))
      (Localization.Away (universalJacobian n d))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (universalJacobian_ne_zero n d))
  obtain ⟨z⟩ : Nonempty (PrimeSpectrum (Localization.Away (universalJacobian n d))) :=
    inferInstance
  have hEt : Etale (awayLift n d (universalJacobian n d) hb
      ≫ (universalQuasiFiniteOpen n d).ι ≫ universalAmbientMorphism n d) := by
    exact (awayLift_comp_iff (P := @Etale) n d _ hb).mpr
      (RingHom.etale_algebraMap.mpr (etale_away_universalJacobian n d))
  refine ⟨Scheme.Hom.opensRange (awayLift n d (universalJacobian n d) hb),
    (Scheme.Hom.opensRange (awayLift n d (universalJacobian n d) hb)).2.dense
      ⟨_, Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩⟩, ?_⟩
  have hr : Set.range ⇑(Scheme.Hom.opensRange
      (awayLift n d (universalJacobian n d) hb)).ι =
      Set.range ⇑(awayLift n d (universalJacobian n d) hb) := by
    rw [Scheme.Opens.range_ι]
    rfl
  rw [show (Scheme.Hom.opensRange (awayLift n d (universalJacobian n d) hb)).ι
      = (IsOpenImmersion.isoOfRangeEq _ _ hr).hom
        ≫ awayLift n d (universalJacobian n d) hb from
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr).symm, Category.assoc]
  exact Etale.etale_comp _ _

end Charts

/-- The universal quasi-finite open subscheme `Y_{n,d}` is regular. -/
@[stacks 0FK9 "y_regular"]
theorem universalQuasiFiniteScheme_isRegular (n d : ℕ) [NeZero n] [NeZero d] :
    IsRegular (universalQuasiFiniteScheme n d) :=
  isRegular_toScheme n d

/-- The universal quasi-finite family `Y_{n,d} ⟶ X_{n,d}` is syntomic. -/
@[stacks 0FK9 "syntomic"]
theorem universalQuasiFiniteMorphism_syntomic (n d : ℕ) [NeZero n] [NeZero d] :
    Syntomic (universalQuasiFiniteMorphism n d) :=
  syntomic_toScheme n d

/-- There is a dense open subscheme `V ⊆ Y_{n,d}` on which the universal quasi-finite family
restricts to an étale morphism `V ⟶ X_{n,d}`. -/
@[stacks 0FK9 "dense_etale_open"]
theorem exists_dense_opens_etale_universalQuasiFiniteMorphism
    (n d : ℕ) [NeZero n] [NeZero d] :
    ∃ V : (universalQuasiFiniteScheme n d).Opens,
      Dense (V : Set (universalQuasiFiniteScheme n d)) ∧
        Etale (V.ι ≫ universalQuasiFiniteMorphism n d) :=
  exists_dense_opens_etale_toScheme n d

end AlgebraicGeometry

end
