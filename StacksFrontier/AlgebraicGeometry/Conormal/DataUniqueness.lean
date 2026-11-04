module

public import StacksFrontier.AlgebraicGeometry.Conormal.ChartGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle

/-!
# The conormal algebra of an immersion is unique up to a canonical isomorphism

A `Stacks.Conormal.ConormalAlgebraData i` is a sheaf of graded algebras on the source of an
immersion `i : Z ⟶ X` together with local associated-graded presentations: over an affine open
`U` of `X` on which `i` restricts to a closed immersion with kernel ideal `I = I(U)`, a surjection
`Iⁿ ↠ 𝒞ₙ(i⁻¹U)` whose kernel is exactly `Iⁿ⁺¹`, compatible with restriction, with the action of
the functions on `U`, with the multiplication and with the unit.

Any two such data for one immersion are isomorphic as sheaves of graded algebras, by the unique
isomorphism carrying the one presentation to the other.

## Main definitions

* `Stacks.Conormal.ConormalAlgebraData.chartMap`: the comparison of the degree-`n` sections over
  the preimage of a chart, for `n : ℕ`, sending the class of a representative to the class of the
  same representative.
* `Stacks.Conormal.ConormalAlgebraData.chartLinearEquiv` and
  `Stacks.Conormal.ConormalAlgebraData.chartIso`: the same as a linear equivalence and, extended
  by the zero map in negative degrees, as an isomorphism of the sections in every integer degree.
* `Stacks.Conormal.ConormalAlgebraData.iso`: the isomorphism of sheaves of graded algebras.
* `Stacks.Conormal.ConormalAlgebraData.unitalHom`: the isomorphism as a unital homomorphism of
  sheaves of graded algebras.

## Main results

* `Stacks.Conormal.ConormalAlgebraData.chartMap_localMap` and
  `Stacks.Conormal.ConormalAlgebraData.iso_hom_localMap`: the comparison, and the glued
  isomorphism, carry the one presentation to the other.
* `Stacks.Conormal.ConormalAlgebraData.isIso_unitalHom_app`: the unital homomorphism is invertible
  in every degree.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0631](https://stacks.math.columbia.edu/tag/0631)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]

omit [IsImmersion i] in
/-- If `i` restricts to a closed immersion `i⁻¹U ⟶ U` over an affine open `U` of `X`, the map
`i.app U` on sections over `U` is surjective. -/
theorem surjective_app_of_isClosedImmersion_resLE (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    Function.Surjective (i.app U.1).hom := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hU
  obtain ⟨I, e, he⟩ := exists_affineModel_of_isClosedImmersion_restrict i U.1 U.2 hU
  rw [Scheme.Hom.app_eq_appLE]
  exact surjective_appLE_of_affineModel i U.1 U.2 I e he

namespace ConormalAlgebraData

variable (A B : ConormalAlgebraData i) (U : X.affineOpens)
  (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ)

omit [IsImmersion i] in
/-- The two presentations of a chart kill the same representatives. -/
theorem localMap_eq_zero_iff_localMap_eq_zero (a : ↥(chartIdeal i U ^ n)) :
    A.localMap U hU n a = 0 ↔ B.localMap U hU n a = 0 :=
  (A.localMap_eq_zero_iff U hU n a).trans (B.localMap_eq_zero_iff U hU n a).symm

omit [IsImmersion i] in
/-- The two presentations of a chart identify the same pairs of representatives. -/
theorem localMap_eq_of_localMap_eq {a b : ↥(chartIdeal i U ^ n)}
    (h : A.localMap U hU n a = A.localMap U hU n b) :
    B.localMap U hU n a = B.localMap U hU n b := by
  have h0 : A.localMap U hU n (a - b) = 0 := by rw [map_sub, h, sub_self]
  have h1 : B.localMap U hU n (a - b) = 0 :=
    (localMap_eq_zero_iff_localMap_eq_zero A B U hU n (a - b)).mp h0
  rwa [map_sub, sub_eq_zero] at h1

/-- The underlying function of the chart comparison: the class of a representative of the
section, read through the other presentation. -/
def chartFun (x : (A.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1))) :
    (B.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) :=
  B.localMap U hU n (Function.surjInv (A.localMap_surjective U hU n) x)

omit [IsImmersion i] in
/-- The chart comparison carries the one presentation to the other. -/
theorem chartFun_localMap (a : ↥(chartIdeal i U ^ n)) :
    chartFun A B U hU n (A.localMap U hU n a) = B.localMap U hU n a :=
  localMap_eq_of_localMap_eq A B U hU n
    (Function.surjInv_eq (A.localMap_surjective U hU n) _)

/-- The chart comparison of the degree-`n` sections determined by two presentations. -/
def chartMap :
    (A.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) →+
      (B.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) where
  toFun := chartFun A B U hU n
  map_zero' := by
    have h := chartFun_localMap A B U hU n 0
    rwa [map_zero, map_zero] at h
  map_add' x y := by
    obtain ⟨a, ha⟩ := A.localMap_surjective U hU n x
    obtain ⟨b, hb⟩ := A.localMap_surjective U hU n y
    subst ha hb
    rw [← map_add, chartFun_localMap, chartFun_localMap, chartFun_localMap, map_add]

omit [IsImmersion i] in
/-- The chart comparison carries the one presentation to the other. -/
@[simp]
theorem chartMap_localMap (a : ↥(chartIdeal i U ^ n)) :
    chartMap A B U hU n (A.localMap U hU n a) = B.localMap U hU n a :=
  chartFun_localMap A B U hU n a

omit [IsImmersion i] in
/-- The chart comparison is linear over the functions on the preimage of the chart. -/
theorem chartMap_smul (r : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)))
    (x : (A.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1))) :
    chartMap A B U hU n (r • x) = r • chartMap A B U hU n x := by
  obtain ⟨a, ha⟩ := A.localMap_surjective U hU n x
  obtain ⟨t, ht⟩ := surjective_app_of_isClosedImmersion_resLE U hU r
  have hval : ((t • a : ↥(chartIdeal i U ^ n)) : Γ(X, U)) = t * (a : Γ(X, U)) := rfl
  have hA := A.localMap_smul U hU n t a (t • a) hval
  have hB := B.localMap_smul U hU n t a (t • a) hval
  rw [ht] at hA hB
  rw [← ha, ← hA, chartMap_localMap, hB, chartMap_localMap]

/-- The chart comparison, as a linear equivalence.  Its inverse is the comparison with the two
data exchanged. -/
def chartLinearEquiv :
    (A.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) ≃ₗ[Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1))]
      (B.algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ U.1)) where
  toFun := chartMap A B U hU n
  map_add' := (chartMap A B U hU n).map_add
  map_smul' := chartMap_smul A B U hU n
  invFun := chartMap B A U hU n
  left_inv x := by
    obtain ⟨a, ha⟩ := A.localMap_surjective U hU n x
    subst ha
    rw [chartMap_localMap, chartMap_localMap]
  right_inv y := by
    obtain ⟨a, ha⟩ := B.localMap_surjective U hU n y
    subst ha
    rw [chartMap_localMap, chartMap_localMap]

/-- The degree-`n` sections over the preimage of a chart, compared in every integer degree: by
`chartLinearEquiv` in a nonnegative degree, and by the zero map in a negative one, where both
sides are trivial. -/
def chartIso : ∀ m : ℤ,
    (A.algebra.piece m).val.obj (op (i ⁻¹ᵁ U.1)) ≅ (B.algebra.piece m).val.obj (op (i ⁻¹ᵁ U.1))
  | (k : ℕ) => (chartLinearEquiv A B U hU k).toModuleIso
  | .negSucc k =>
    { hom := 0
      inv := 0
      hom_inv_id := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (A.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ _).symm
      inv_hom_id := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (B.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ _).symm }

/-- In a nonnegative degree, `chartIso` is the chart comparison `chartMap`. -/
theorem chartIso_hom_apply (k : ℕ) (x : (A.algebra.piece (k : ℤ)).val.obj (op (i ⁻¹ᵁ U.1))) :
    (chartIso A B U hU (k : ℤ)).hom x = chartMap A B U hU k x := rfl

/-- In a nonnegative degree, `chartIso` carries the one presentation to the other. -/
@[simp]
theorem chartIso_hom_localMap (k : ℕ) (a : ↥(chartIdeal i U ^ k)) :
    (chartIso A B U hU (k : ℤ)).hom (A.localMap U hU k a) = B.localMap U hU k a :=
  chartMap_localMap A B U hU k a

omit [IsImmersion i] in
/-- The chart comparison commutes with restriction to a smaller chart of the ambient scheme. -/
theorem chartMap_restrict (V W : X.affineOpens)
    (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
    (hW : IsClosedImmersion (i.resLE W.1 (i ⁻¹ᵁ W.1) le_rfl))
    (hWV : W.1 ≤ V.1) (hZ : (i ⁻¹ᵁ W.1) ≤ (i ⁻¹ᵁ V.1)) (k : ℕ)
    (s : (A.algebra.piece (k : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartMap A B W hW k ((A.algebra.piece (k : ℤ)).val.map (homOfLE hZ).op s) =
      (B.algebra.piece (k : ℤ)).val.map (homOfLE hZ).op (chartMap A B V hV k s) := by
  obtain ⟨a, ha⟩ := A.localMap_surjective V hV k s
  subst ha
  refine Eq.trans (congrArg (chartMap A B W hW k)
    (A.localMap_naturality V W hWV hZ hV hW k a
      ⟨X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)), map_mem_chartIdeal_pow i hWV k a.2⟩
      rfl)) ?_
  rw [chartMap_localMap, chartMap_localMap]
  exact (B.localMap_naturality V W hWV hZ hV hW k a _ rfl).symm

/-- The chart hypothesis attached to a `ConormalChart`. -/
theorem isClosedImmersion_resLE_chart (V : ConormalChart i) :
    IsClosedImmersion (i.resLE V.1.1 (i ⁻¹ᵁ V.1.1) le_rfl) :=
  isClosedImmersion_resLE_of_le_coborderRange i V.1.1 V.2

/-- The chart comparison commutes with restriction between the preimages of two charts. -/
theorem chartMap_restrict_of_le (V W : ConormalChart i)
    (hZ : (i ⁻¹ᵁ W.1.1) ≤ (i ⁻¹ᵁ V.1.1)) (k : ℕ)
    (s : (A.algebra.piece (k : ℤ)).val.obj (op (i ⁻¹ᵁ V.1.1))) :
    chartMap A B W.1 (isClosedImmersion_resLE_chart W) k
        ((A.algebra.piece (k : ℤ)).val.map (homOfLE hZ).op s) =
      (B.algebra.piece (k : ℤ)).val.map (homOfLE hZ).op
        (chartMap A B V.1 (isClosedImmersion_resLE_chart V) k s) := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover (B.algebra.piece (k : ℤ))
    (fun C : { C : ConormalChart i // C.1.1 ≤ V.1.1 ∧ C.1.1 ≤ W.1.1 } => i ⁻¹ᵁ C.1.1.1)
    (fun C => i.preimage_mono C.2.2) (fun z hz => ?_) _ _ fun C => ?_
  · have hzW : i z ∈ W.1.1 := by simpa using hz
    have hzV : i z ∈ V.1.1 := by
      have hz' : z ∈ i ⁻¹ᵁ W.1.1 := hz
      simpa using hZ hz'
    obtain ⟨-, ⟨D, hD, rfl⟩, hzD, hDVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show i z ∈ (V.1.1 : Set X) ∩ (W.1.1 : Set X) from ⟨hzV, hzW⟩)
        (V.1.1.2.inter W.1.1.2)
    have hDV : (⟨D, hD⟩ : X.affineOpens).1 ≤ V.1.1 := fun y hy => (hDVW hy).1
    have hDW : (⟨D, hD⟩ : X.affineOpens).1 ≤ W.1.1 := fun y hy => (hDVW hy).2
    exact ⟨⟨⟨⟨D, hD⟩, hDV.trans V.2⟩, hDV, hDW⟩, hzD⟩
  · have hCV : (i ⁻¹ᵁ C.1.1.1) ≤ (i ⁻¹ᵁ V.1.1) := i.preimage_mono C.2.1
    have hcompA := (A.algebra.piece (k : ℤ)).val.map_comp_apply
      (homOfLE hZ).op (homOfLE (i.preimage_mono C.2.2)).op s
    have hcompB := (B.algebra.piece (k : ℤ)).val.map_comp_apply
      (homOfLE hZ).op (homOfLE (i.preimage_mono C.2.2)).op
      (chartMap A B V.1 (isClosedImmersion_resLE_chart V) k s)
    have hop : (homOfLE hZ).op ≫ (homOfLE (i.preimage_mono C.2.2)).op = (homOfLE hCV).op :=
      Subsingleton.elim _ _
    rw [hop] at hcompA hcompB
    have h1 := chartMap_restrict A B W.1 C.1.1 (isClosedImmersion_resLE_chart W)
      (isClosedImmersion_resLE_chart C.1) C.2.2 (i.preimage_mono C.2.2) k
      ((A.algebra.piece (k : ℤ)).val.map (homOfLE hZ).op s)
    have h2 := chartMap_restrict A B V.1 C.1.1 (isClosedImmersion_resLE_chart V)
      (isClosedImmersion_resLE_chart C.1) C.2.1 hCV k s
    exact h1.symm.trans ((congrArg (chartMap A B C.1.1 (isClosedImmersion_resLE_chart C.1) k)
      hcompA.symm).trans (h2.trans hcompB))

/-- The chart comparison, read on `chartIso`, commutes with restriction between the preimages of
two charts. -/
theorem chartIso_hom_restrict (V W : ConormalChart i)
    (hZ : (i ⁻¹ᵁ W.1.1) ≤ (i ⁻¹ᵁ V.1.1)) (m : ℤ)
    (s : (A.algebra.piece m).val.obj (op (i ⁻¹ᵁ V.1.1))) :
    (chartIso A B W.1 (isClosedImmersion_resLE_chart W) m).hom
        ((A.algebra.piece m).val.map (homOfLE hZ).op s) =
      (B.algebra.piece m).val.map (homOfLE hZ).op
        ((chartIso A B V.1 (isClosedImmersion_resLE_chart V) m).hom s) := by
  match m with
  | .negSucc k =>
    exact (B.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ _).trans
      (B.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ _).symm
  | (k : ℕ) => exact chartMap_restrict_of_le A B V W hZ k s

/-- The chart comparison, read on `chartIso`, is multiplicative. -/
theorem chartIso_hom_mul (p q : ℤ)
    (x : (A.algebra.piece p).val.obj (op (i ⁻¹ᵁ U.1)))
    (y : (A.algebra.piece q).val.obj (op (i ⁻¹ᵁ U.1))) :
    (chartIso A B U hU (p + q)).hom ((A.algebra.mul p q).app (op (i ⁻¹ᵁ U.1)) x y) =
      (B.algebra.mul p q).app (op (i ⁻¹ᵁ U.1)) ((chartIso A B U hU p).hom x)
        ((chartIso A B U hU q).hom y) := by
  match p, q with
  | .negSucc k, q =>
    rw [A.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ x]
    simp only [map_zero, AddMonoidHom.zero_apply]
  | (n : ℕ), .negSucc k =>
    rw [A.eq_zero_of_neg (.negSucc k) (Int.negSucc_lt_zero k) _ y]
    simp only [map_zero]
  | (n : ℕ), (m : ℕ) =>
    obtain ⟨a, ha⟩ := A.localMap_surjective U hU n x
    obtain ⟨b, hb⟩ := A.localMap_surjective U hU m y
    subst ha hb
    have hmem : ((a : Γ(X, U)) * (b : Γ(X, U))) ∈ chartIdeal i U ^ (n + m) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.2 b.2
    have hA := A.localMap_mul U hU n m a b ⟨_, hmem⟩ rfl
    have hB := B.localMap_mul U hU n m a b ⟨_, hmem⟩ rfl
    show (chartIso A B U hU ((n + m : ℕ) : ℤ)).hom _ = _
    rw [← hA, chartIso_hom_localMap, chartIso_hom_localMap, chartIso_hom_localMap, hB]

end ConormalAlgebraData

namespace ConormalAlgebraData

variable (A B : ConormalAlgebraData i)

/-- The isomorphism of sheaves of graded algebras between two conormal algebra data for one
immersion, carrying the one presentation to the other. -/
def iso : A.algebra ≅ B.algebra :=
  gradedAlgebraIsoOfChartIso i A.algebra B.algebra
    (fun m V => chartIso A B V.1 (isClosedImmersion_resLE_chart V) m)
    (fun m V W hZ s => chartIso_hom_restrict A B V W hZ m s)
    fun p q V x y => chartIso_hom_mul A B V.1 (isClosedImmersion_resLE_chart V) p q x y

/-- The degree-`m` component of the isomorphism over the preimage of a chart is the chart
comparison. -/
theorem iso_hom_app_app (m : ℤ) (V : ConormalChart i) :
    ((iso A B).hom.app m).val.app (op (i ⁻¹ᵁ V.1.1)) =
      (chartIso A B V.1 (isClosedImmersion_resLE_chart V) m).hom :=
  gradedAlgebraIsoOfChartIso_hom_app_app i A.algebra B.algebra _ _ _ m V

/-- The isomorphism carries the one presentation to the other. -/
theorem iso_hom_localMap (V : ConormalChart i) (k : ℕ) (a : ↥(chartIdeal i V.1 ^ k)) :
    ((iso A B).hom.app (k : ℤ)).val.app (op (i ⁻¹ᵁ V.1.1))
        (A.localMap V.1 (isClosedImmersion_resLE_chart V) k a) =
      B.localMap V.1 (isClosedImmersion_resLE_chart V) k a := by
  rw [iso_hom_app_app]
  exact chartIso_hom_localMap A B V.1 _ k a

/-- The isomorphism carries the graded unit to the graded unit, over every open. -/
theorem iso_hom_one (W : (Opens ↥Z)ᵒᵖ) :
    ((iso A B).hom.app 0).val.app W (A.algebra.one.eval W) = B.algebra.one.eval W := by
  obtain ⟨W⟩ := W
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover (B.algebra.piece 0)
    (fun V : { V : ConormalChart i // (i ⁻¹ᵁ V.1.1) ≤ W } => i ⁻¹ᵁ V.1.1.1)
    (fun V => V.2) (fun z hz => ?_) _ _ fun V => ?_
  · obtain ⟨D, hzD, hDW, hDc⟩ := exists_chart_near i W z hz
    exact ⟨⟨⟨D, hDc⟩, hDW⟩, hzD⟩
  · have hone : (1 : Γ(X, V.1.1)) ∈ chartIdeal i V.1.1 ^ 0 := by simp
    have hA := A.localMap_one V.1.1 (isClosedImmersion_resLE_chart V.1) ⟨1, hone⟩ rfl
    have hB := B.localMap_one V.1.1 (isClosedImmersion_resLE_chart V.1) ⟨1, hone⟩ rfl
    rw [← PresheafOfModules.naturality_apply ((iso A B).hom.app 0).val (homOfLE V.2).op
      (A.algebra.one.eval (op W)),
      PresheafOfModules.sections_property A.algebra.one (homOfLE V.2).op,
      PresheafOfModules.sections_property B.algebra.one (homOfLE V.2).op]
    exact (congrArg (fun z => ((iso A B).hom.app 0).val.app (op (i ⁻¹ᵁ V.1.1.1)) z)
      hA.symm).trans ((iso_hom_localMap A B V.1 0 ⟨1, hone⟩).trans hB)

/-- The isomorphism `iso`, as a unital homomorphism of sheaves of graded algebras. -/
def unitalHom : SheafOfModules.GradedAlgebra.UnitalHom A.algebra B.algebra :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHom (iso A B).hom
    ((SheafOfModules.GradedAlgebra.UnitalHom.map_one_iff (iso A B).hom).1 (iso_hom_one A B))

/-- The components of `unitalHom` are those of the isomorphism `iso`. -/
@[simp]
theorem unitalHom_app (m : ℤ) : (unitalHom A B).app m = (iso A B).hom.app m := rfl

/-- The unital homomorphism `unitalHom` is an isomorphism in every degree. -/
instance isIso_unitalHom_app (m : ℤ) : IsIso ((unitalHom A B).app m) := by
  rw [unitalHom_app]
  exact ⟨(iso A B).inv.app m, by
      rw [← SheafOfModules.GradedAlgebra.categoryStruct_comp_app, (iso A B).hom_inv_id]; rfl,
    by rw [← SheafOfModules.GradedAlgebra.categoryStruct_comp_app, (iso A B).inv_hom_id]; rfl⟩

end ConormalAlgebraData

end Stacks.Conormal

end
