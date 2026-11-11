module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Theory

/-!
# Transporting the correspondence `H^*(X) = G(h(X))` along isomorphisms

The relation `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds` between classical
Weil cohomology theories and realizations `(G, F[2] ≅ G(𝟏(1)))` of Stacks 0FH3 is compatible with
isomorphisms on both sides, and two theories corresponding to the same realization are isomorphic:
the composite of the two identifications with `G(h(X))` is an isomorphism of theories.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds.nonempty_iso`: theories
  corresponding to the same realization are isomorphic.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds.of_iso`: along an isomorphism
  of theories.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds.of_realizationIso`: along an
  isomorphism of realizations.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite CategoryTheory.GradedCategory
  Stacks.Chow
open Stacks.WeilCohomology.ChowMotiveCat (h tate)

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

local notation "𝐎" =>
  (GradedCompositionData.Obj.mk :
    CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
      CorrespondenceCategory _)

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK

open ClassicalWeilCohomologyTheory.Iso (degreeCast_linearEquiv)

namespace ClassicalMotiveRealization

variable (R : ClassicalMotiveRealization k F)

/-- The trace of `R` does not depend on how the dimension is written. -/
theorem trace_degreeCast (X : (SmoothProjective k).FullSubcategory) {d d' : ℕ} (hd : d = d')
    (hX : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d)
    (hX' : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d')
    (z : (R.toWeilRealization.functor.obj
      (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X))))
      (2 * (d : ℤ))) :
    R.trace X d' hX' (ExternallyGraded.degreeCast (R := F)
      (X := fun n ↦
        (R.toWeilRealization.functor.obj
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X)))) n)
      (by rw [hd]) z) = R.trace X d hX z := by
  subst hd
  rfl

/-- An isomorphism of realizations carries the generators `eₙ` of `R` to those of `R'`. -/
theorem Iso.app_tateGen {R R' : ClassicalMotiveRealization k F} (e : Iso R R') (n : ℤ) :
    e.iso.hom.app (TwistedKaroubi.tateTriple ℚ _ n) (-2 * n) (R.tateGen n) = R'.tateGen n := by
  have : NatTrans.IsMonoidal e.iso.hom := e.isMonoidal
  have he : e.iso.hom.app (tate k 1) (-2 * 1) R.tateVec = R'.tateVec := by
    have h := congr($(e.tateIso_hom_comp) (-2))
    simp only [GradedObject.categoryOfGradedObjects_comp] at h
    exact ConcreteCategory.congr_hom h
      ((GradedObject.singleObjApplyIso (-2) (ModuleCat.of F F)).inv.hom 1)
  have he' : e.iso.hom.app (tate k 1) (-2 * 1) R.tateVec ≠ 0 := he ▸ R'.tateVec_ne_zero
  have key : ∀ (x y : R'.toWeilRealization.tateLine) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      TwistedKaroubi.tateGen (G := R'.toWeilRealization.functorTK)
        R'.toWeilRealization.tate_degree hx n =
      TwistedKaroubi.tateGen (G := R'.toWeilRealization.functorTK)
        R'.toWeilRealization.tate_degree hy n := by
    rintro x _ hx hy rfl
    rfl
  exact (TwistedKaroubi.app_tateGen e.iso.hom R.toWeilRealization.tate_degree
    R'.toWeilRealization.tate_degree R.tateVec_ne_zero he' n).trans
    (key _ _ he' R'.tateVec_ne_zero he)

/-- A morphism of graded objects commutes with the identifications of equal degrees. -/
theorem _root_.Stacks.WeilCohomology.gradedHom_eqToHom
    {A B : GradedObject ℤ (ModuleCat.{v} F)} (f : A ⟶ B) {i j : ℤ} (hij : i = j) (x : A i) :
    f j ((eqToHom (congrArg A hij)).hom x) = (eqToHom (congrArg B hij)).hom (f i x) := by
  subst hij
  rfl

/-- An isomorphism of realizations carries the cycle classes of `R` to those of `R'`. -/
theorem Iso.app_cycleClass {R R' : ClassicalMotiveRealization k F} (e : Iso R R')
    (X : (SmoothProjective k).FullSubcategory) (r : ℤ) (α : (chowCycleData k).group X r) :
    e.iso.hom.app _ (2 * r) (R.cycleClass X r α) = R'.cycleClass X r α := by
  exact (NatTrans.app_map_apply e.iso.hom _ _ _).trans (congrArg _
    ((gradedHom_eqToHom (e.iso.hom.app _) (show -2 * -r = 2 * r by ring) (R.tateGen (-r))).trans
      (congrArg _ (e.app_tateGen (-r)))))

/-- An isomorphism of realizations carries the traces of `R` to those of `R'`. -/
theorem Iso.trace_app {R R' : ClassicalMotiveRealization k F} (e : Iso R R')
    (X : (SmoothProjective k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d) (x) :
    R'.trace X d hX (e.iso.hom.app _ (2 * d) x) = R.trace X d hX x := by
  have : NatTrans.IsMonoidal e.iso.hom := e.isMonoidal
  exact (congrArg (fun e' ↦ R'.toWeilRealization.functorTK.gradedTrace
    (ChowMotiveCat.fundamentalClassMot hX.relativeDimension) e' (2 * d) (by ring)
      (e.iso.hom.app _ (2 * d) x)) (e.app_tateGen d).symm).trans
    (WeilRealization.gradedTrace_fundamentalClassMot_app e.iso.hom hX.relativeDimension
      (R.tateGen d) x)

end ClassicalMotiveRealization

namespace ClassicalWeilCohomologyTheory

variable {T T' : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k)}
  {R R' : ClassicalMotiveRealization k F}

/-- **Two theories corresponding to the same realization are isomorphic.** -/
theorem Corresponds.nonempty_iso (hT : T.Corresponds R) (hT' : T'.Corresponds R) :
    Nonempty (Iso T T') := by
  obtain ⟨E⟩ := hT
  obtain ⟨E'⟩ := hT'
  refine ⟨{ equiv := fun X n ↦ (E.iso X n).trans (E'.iso X n).symm
            equiv_pullback := fun {X Y} f n a ↦ ?_
            equiv_one := fun X ↦ ?_
            equiv_mul := fun X i j a b ↦ ?_
            equiv_cycleClass := fun X r α ↦ ?_
            integration_equiv := fun X a ↦ ?_ }⟩
  · apply (E'.iso X n).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [E.iso_pullback, E'.iso_pullback, LinearEquiv.apply_symm_apply]
  · apply (E'.iso X 0).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [E.iso_one, E'.iso_one]
  · apply (E'.iso X (i + j)).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [E.iso_mul, E'.iso_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · apply (E'.iso X (2 * r)).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [E.iso_cycleClass, E'.iso_cycleClass]
  · have h1 := E.trace_iso X a
    have h2 := E'.trace_iso X (ExternallyGraded.degreeCast (R := F) (X := (T'.H X).piece)
      (by rw [dimension_eq_dimension T T' X]) ((E'.iso X _).symm (E.iso X _ a)))
    refine h2.symm.trans (Eq.trans ?_ h1)
    rw [degreeCast_linearEquiv (fun n ↦ E'.iso X n), LinearEquiv.apply_symm_apply]
    exact R.trace_degreeCast X (dimension_eq_dimension T T' X) _ _ _

/-- The correspondence transported along an isomorphism of theories. -/
theorem Corresponds.of_iso (hT : T.Corresponds R) (e : Iso T T') : T'.Corresponds R := by
  obtain ⟨E⟩ := hT
  refine ⟨{ iso := fun X n ↦ (e.equiv X n).symm.trans (E.iso X n)
            iso_pullback := fun {X Y} f n a ↦ ?_
            iso_one := fun X ↦ ?_
            iso_mul := fun X i j a b ↦ ?_
            iso_cycleClass := fun X r α ↦ ?_
            trace_iso := fun X a ↦ ?_ }⟩
  · have h : (e.equiv X n).symm (T'.pullback f n a) = T.pullback f n ((e.equiv Y n).symm a) := by
      apply (e.equiv X n).injective
      rw [LinearEquiv.apply_symm_apply, e.equiv_pullback, LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h, E.iso_pullback]
  · have h : (e.equiv X 0).symm (T'.H X).one = (T.H X).one := by
      apply (e.equiv X 0).injective
      rw [LinearEquiv.apply_symm_apply, e.equiv_one]
    simp only [LinearEquiv.trans_apply]
    rw [h, E.iso_one]
  · have h : (e.equiv X (i + j)).symm ((T'.H X).mul i j a b) =
        (T.H X).mul i j ((e.equiv X i).symm a) ((e.equiv X j).symm b) := by
      apply (e.equiv X (i + j)).injective
      rw [LinearEquiv.apply_symm_apply, e.equiv_mul, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.trans_apply]
    rw [h, E.iso_mul]
  · have h : (e.equiv X (2 * r)).symm (T'.cycleClass X r α) = T.cycleClass X r α := by
      apply (e.equiv X (2 * r)).injective
      rw [LinearEquiv.apply_symm_apply, e.equiv_cycleClass]
    simp only [LinearEquiv.trans_apply]
    rw [h, E.iso_cycleClass]
  · have h := e.symm.integration_equiv X a
    refine Eq.trans ?_ h
    rw [← E.trace_iso X]
    simp only [LinearEquiv.trans_apply]
    symm
    exact (congrArg _ (degreeCast_linearEquiv (fun n ↦ E.iso X n) _ _)).trans
      (R.trace_degreeCast X (dimension_eq_dimension T' T X) _ _ _)

/-- The correspondence transported along an isomorphism of realizations. -/
theorem Corresponds.of_realizationIso (hT : T.Corresponds R)
    (e : ClassicalMotiveRealization.Iso R R') : T.Corresponds R' := by
  have : NatTrans.IsMonoidal e.iso.hom := e.isMonoidal
  obtain ⟨E⟩ := hT
  refine ⟨{ iso := fun X n ↦ (E.iso X n).trans ((GradedObject.eval n).mapIso
              (e.iso.app (TwistedKaroubi.ofObj (R := ℚ)
                (𝐎 ((SmoothProjective.toSchemeCat k).obj X))))).toLinearEquiv
            iso_pullback := fun {X Y} f n a ↦ ?_
            iso_one := fun X ↦ ?_
            iso_mul := fun X i j a b ↦ ?_
            iso_cycleClass := fun X r α ↦ ?_
            trace_iso := fun X a ↦ ?_ }⟩
  · change e.iso.hom.app _ n (E.iso X n _) = R'.toWeilRealization.functor.map _ n
      (e.iso.hom.app _ n (E.iso Y n a))
    rw [E.iso_pullback]
    exact NatTrans.app_map_apply e.iso.hom _ _ _
  · change e.iso.hom.app _ 0 (E.iso X 0 _) = _
    rw [E.iso_one]
    exact NatTrans.app_cohomologyAlgebra_one e.iso.hom _
  · change e.iso.hom.app _ (i + j) (E.iso X (i + j) _) =
      (R'.toWeilRealization.cohAlg _).mul i j
        (e.iso.hom.app _ i (E.iso X i a)) (e.iso.hom.app _ j (E.iso X j b))
    rw [E.iso_mul]
    exact NatTrans.app_cohomologyAlgebra_mul e.iso.hom _ i j _ _
  · change e.iso.hom.app _ (2 * r) (E.iso X (2 * r) _) = _
    rw [E.iso_cycleClass]
    exact e.app_cycleClass X r α
  · change R'.trace X _ _ (e.iso.hom.app _ _ (E.iso X _ a)) = _
    exact (e.trace_app X _ _ _).trans (E.trace_iso X a)

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
