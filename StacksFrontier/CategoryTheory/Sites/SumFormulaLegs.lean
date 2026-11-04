module

public import StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula

/-!
# The summand inclusions of the lower-shriek sum formula

Either of the two criteria of `StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula` produces
an isomorphism between lower shriek along `v_n` followed by restriction along `v_m` and a
coproduct of functors indexed by a family of comparison transformations. That isomorphism is
built by `CategoryTheory.Limits.colimit.isoColimitCocone` out of an explicit colimit cofan, and
this file identifies its summand inclusions with the legs of that cofan.

For the ran criterion the leg is the conjugate, under the two adjunctions, of the comparison
`ranRestrictSheafComparison` of right adjoints, so the transposition formula
`CategoryTheory.Adjunction.homEquiv_conjugateInj` applies to it. For the lan criterion the leg is
the presheaf comparison `lanRestrictComparison`, sheafified and transported along
`sheafificationCompPushforwardContinuousIso`.

## Main results

* `CategoryTheory.Functor.sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv`: the
  summand inclusion of the ran criterion's isomorphism is the conjugate of the comparison of
  right adjoints.
* `CategoryTheory.Functor.homEquiv_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv`:
  the corresponding transposition formula.
* `CategoryTheory.Functor.sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfLan_inv`: the
  summand inclusion of the lan criterion's isomorphism.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Functor

universe w v₁ u₁ v₂ u₂ v₃ u₃ v u

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E]
  (A : Type u) [Category.{v} A]
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)

section Ran

variable (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cn ⥤ Cm)) (τ : ∀ i, t i ⋙ vm ⟶ vn)
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [ht : ∀ i, (t i).IsContinuous Jn Jm]
  [HasWeakSheafify L A] [HasWeakSheafify Jm A]
  [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F]
  [∀ i, ∀ F : Cnᵒᵖ ⥤ A, (t i).op.HasLeftKanExtension F]
  [HasLimitsOfShape (Discrete I) A]
  [HasCoproduct fun i => sheafPullbackConstruction.sheafPullback (t i) A Jn Jm]
  (hfan : ∀ (P : Cmᵒᵖ ⥤ A) (U : Cn),
    IsLimit (Fan.mk ((vm.op.ran.obj P).obj (op (vn.obj U)))
      fun i => (vm.op.ran.obj P).map ((τ i).app U).op ≫
        (vm.op.ranCounit.app P).app (op ((t i).obj U))))

/-- The `i`th summand inclusion into the ran criterion's coproduct formula, followed by the
inverse of that formula, is the conjugate of the comparison `ranRestrictSheafComparison` of
right adjoints. -/
theorem sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv (i : I) :
    Sigma.ι (fun i => sheafPullbackConstruction.sheafPullback (t i) A Jn Jm) i ≫
        (sheafPullbackCompPushforwardIsoCoproductOfRan A Jn Jm L vn vm t τ hfan).inv =
      Adjunction.conjugateInj
        ((sheafPullbackConstruction.sheafAdjunctionContinuous vn A Jn L).comp
          (vm.sheafAdjunctionCocontinuous A Jm L))
        (fun i => sheafPullbackConstruction.sheafAdjunctionContinuous (t i) A Jn Jm)
        (ranRestrictSheafComparison A Jn Jm L vn vm t τ) i :=
  colimit.isoColimitCocone_ι_hom _ (⟨i⟩ : Discrete I)

/-- Transposing along the adjunction of the `i`th summand, after precomposing with the `i`th
summand inclusion of the ran criterion's coproduct formula, is transposing along the composite
adjunction and then postcomposing with the comparison of right adjoints. -/
theorem homEquiv_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv (i : I)
    (X : Sheaf Jn A) (T : Sheaf Jm A)
    (f : (sheafPullbackConstruction.sheafPullback vn A Jn L ⋙
      vm.sheafPushforwardContinuous A Jm L).obj X ⟶ T) :
    (sheafPullbackConstruction.sheafAdjunctionContinuous (t i) A Jn Jm).homEquiv X T
        ((Sigma.ι (fun i => sheafPullbackConstruction.sheafPullback (t i) A Jn Jm) i ≫
          (sheafPullbackCompPushforwardIsoCoproductOfRan A Jn Jm L vn vm t τ hfan).inv).app X ≫
            f) =
      ((sheafPullbackConstruction.sheafAdjunctionContinuous vn A Jn L).comp
            (vm.sheafAdjunctionCocontinuous A Jm L)).homEquiv X T f ≫
        (ranRestrictSheafComparison A Jn Jm L vn vm t τ i).app T := by
  rw [sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv A Jn Jm L vn vm t τ hfan i]
  exact Adjunction.homEquiv_conjugateInj
    ((sheafPullbackConstruction.sheafAdjunctionContinuous vn A Jn L).comp
      (vm.sheafAdjunctionCocontinuous A Jm L))
    (fun i => sheafPullbackConstruction.sheafAdjunctionContinuous (t i) A Jn Jm)
    (ranRestrictSheafComparison A Jn Jm L vn vm t τ) i f

end Ran

section Lan

variable (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cm ⥤ Cn)) (σ : ∀ i, vm ⟶ t i ⋙ vn)
  [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F]
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [HasWeakSheafify L A] [HasWeakSheafify Jm A]
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]
  [HasCoproduct fun i => (t i).sheafPullbackCocontinuous A Jm Jn]
  (hcofan : ∀ (P : Cnᵒᵖ ⥤ A) (V : Cm),
    IsColimit (Cofan.mk ((vn.op.lan.obj P).obj (op (vm.obj V)))
      fun i => (vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
        (vn.op.lan.obj P).map ((σ i).app V).op))

omit [vn.IsContinuous Jn L] in
/-- The `i`th summand inclusion into the lan criterion's coproduct formula, followed by the
inverse of that formula, is the presheaf comparison `lanRestrictComparison` sheafified and
transported along `sheafificationCompPushforwardContinuousIso`. -/
theorem sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfLan_inv (i : I) :
    Sigma.ι (fun i => (t i).sheafPullbackCocontinuous A Jm Jn) i ≫
        (sheafPullbackCompPushforwardIsoCoproductOfLan A Jn Jm L vn vm t σ hcofan).inv =
      whiskerLeft (sheafToPresheaf Jn A)
          (whiskerRight (lanRestrictComparison A vn vm t σ i) (presheafToSheaf Jm A)) ≫
        (isoWhiskerLeft (sheafToPresheaf Jn A ⋙ vn.op.lan)
          (sheafificationCompPushforwardContinuousIso vm A Jm L)).inv :=
  colimit.isoColimitCocone_ι_hom _ (⟨i⟩ : Discrete I)

end Lan

end CategoryTheory.Functor

end
