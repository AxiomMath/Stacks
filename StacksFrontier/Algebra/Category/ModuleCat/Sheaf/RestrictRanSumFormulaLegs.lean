module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanSumFormula

/-!
# The summand inclusions of the module sum formula: the ran criterion

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RestrictRanSumFormula.lean` produces, from the ran
criterion, an isomorphism between a coproduct of module pullbacks along a family of transitions
and lower shriek of modules along `v_n` followed by restriction along `v_m`. That isomorphism is
built by `CategoryTheory.Limits.colimit.isoColimitCocone` out of an explicit colimit cofan, so its
summand inclusions are the legs of that cofan, which
`StacksFrontier/CategoryTheory/Adjunction/ConjugateCoproduct.lean` names `conjugateInj`.

This is the only handle on the isomorphism there is: it is otherwise opaque, and every statement
about which summand a given map lands in — the summand-inclusion identification of Stacks 0D72 (6)
in case (A), for instance — is a statement about `Sigma.ι i ≫ iso.hom`.

The leg is the conjugate, under the two adjunctions, of the comparison `ranComparisonSheaf` of
right adjoints, so the transposition formula `CategoryTheory.Adjunction.homEquiv_conjugateInj`
applies to it; that is the form in which the summand inclusion is usable, since it replaces a
statement about an opaque left-adjoint comparison by one about the comparison of right adjoints,
whose underlying transformation of presheaves of abelian groups is the Kan extension leg at the
index attached to `τ i`.

This is the module counterpart of
`CategoryTheory.Functor.sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfRan_inv` in
`StacksFrontier/CategoryTheory/Sites/SumFormulaLegs.lean`. The abelian criterion there is stated as
an isomorphism *from* lower shriek *to* the coproduct, so its summand inclusions are read against
`.inv`; the module criterion is stated in the opposite orientation, from the coproduct, so they
are read against `.hom`.

## Main results

* `Stacks.SheafOfModules.RestrictRan.sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom`: the
  summand inclusion of the module ran criterion's isomorphism is the conjugate of the comparison
  of right adjoints.
* the corresponding transposition formula:
`Stacks.SheafOfModules.RestrictRan.homEquiv_sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom`

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Stacks.SheafOfModules.RestrictRan

universe w v r v₁ u₁ v₂ u₂ v₃ u₃

section Comparison

variable {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E] (vn : Cn ⥤ E) (vm : Cm ⥤ E)
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  (O : Sheaf L RingCat.{r}) (t : Cn ⥤ Cm) (τ : t ⋙ vm ⟶ vn) [t.IsContinuous Jn Jm]
  [∀ F : Cmᵒᵖ ⥤ RingCat.{r}, vm.op.HasPointwiseRightKanExtension F]
  [∀ F : Cmᵒᵖ ⥤ AddCommGrpCat.{v}, vm.op.HasPointwiseRightKanExtension F]

/-- **The comparison of right adjoints is restriction along `τ`.** The unit of the adjunction of
the cocontinuous `v_m` on sheaves of modules, restricted along `v_n` and followed by the
comparison `ranComparisonSheaf`, is on underlying presheaves of abelian groups the restriction
along `τ`: the unit of the Kan-extension adjunction followed by the leg of the limit cone at the
index attached to `τ` is that restriction.

This is the module counterpart of
`CategoryTheory.Functor.map_sheafAdjunctionCocontinuous_unit_comp_ranRestrictSheafComparison`.
It is stated on underlying presheaves of abelian groups rather than as an equality of morphisms
of sheaves of modules, because there is no generic name in this library for the restriction of a
sheaf of modules along `τ`, and the one use site has its own. -/
theorem toPresheaf_map_sheafAdjunction_unit_comp_ranComparisonSheaf
    (B : _root_.SheafOfModules.{v} O) :
    (PresheafOfModules.toPresheaf _).map
        (((_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).map
              ((sheafAdjunction.{v} vm Jm L O).unit.app B) ≫
            (ranComparisonSheaf.{v} vn vm Jn Jm L O t τ).app
              ((_root_.SheafOfModules.pushforward.{v} (F := vm)
                (𝟙 (ringSheaf vm Jm L O))).obj B)).val) =
      Functor.whiskerRight (NatTrans.op τ) B.val.presheaf := by
  refine NatTrans.ext (funext fun U => ?_)
  have step2 : ((PresheafOfModules.toPresheaf (ringSheaf vn Jn L O).obj).map
        (((_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).map
          ((sheafAdjunction.{v} vm Jm L O).unit.app B)).val)).app U
      = ((vm.op.ranAdjunction AddCommGrpCat.{v}).unit.app B.val.presheaf).app
        (vn.op.obj U) := by
    have hA : ((PresheafOfModules.toPresheaf (ringSheaf vn Jn L O).obj).map
          (((_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).map
            ((sheafAdjunction.{v} vm Jm L O).unit.app B)).val)).app U
        = ((PresheafOfModules.toPresheaf O.obj).map
            ((sheafAdjunction.{v} vm Jm L O).unit.app B).val).app (vn.op.obj U) := rfl
    have hB : (PresheafOfModules.toPresheaf O.obj).map
            ((adjunction.{v} vm O.obj).unit.app B.val)
        = (vm.op.ranAdjunction AddCommGrpCat.{v}).unit.app B.val.presheaf :=
      (congrArg ((vm.op.ranAdjunction AddCommGrpCat.{v}).homEquiv B.val.presheaf
          (vm.op ⋙ B.val.presheaf))
        (presheafMap_id ((PresheafOfModules.pushforward₀.{v} vm O.obj).obj B.val))).trans
        ((vm.op.ranAdjunction AddCommGrpCat.{v}).homEquiv_id B.val.presheaf)
    rw [hA, sheafAdjunction_unit_app_val.{v} vm Jm L O B]
    exact congrArg (fun z : B.val.presheaf ⟶ vm.op.ran.obj (vm.op ⋙ B.val.presheaf) =>
      z.app (vn.op.obj U)) hB
  have hsplit : ((PresheafOfModules.toPresheaf (ringSheaf vn Jn L O).obj).map
        (((_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).map
              ((sheafAdjunction.{v} vm Jm L O).unit.app B) ≫
            (ranComparisonSheaf.{v} vn vm Jn Jm L O t τ).app
              ((_root_.SheafOfModules.pushforward.{v} (F := vm)
                (𝟙 (ringSheaf vm Jm L O))).obj B)).val)).app U
      = ((PresheafOfModules.toPresheaf (ringSheaf vn Jn L O).obj).map
            (((_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).map
              ((sheafAdjunction.{v} vm Jm L O).unit.app B)).val)).app U ≫
          ranπ vm.op (vm.op ⋙ B.val.presheaf) (vn.op.obj U) (commaIndex vn vm t τ U) := rfl
  exact hsplit.trans ((congrArg
      (fun z => z ≫ ranπ vm.op (vm.op ⋙ B.val.presheaf) (vn.op.obj U)
        (commaIndex vn vm t τ U)) step2).trans
    (Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ vm.op B.val.presheaf
      (vn.op.obj U) (commaIndex vn vm t τ U)))

end Comparison

section Criterion

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E] (vn : Cn ⥤ E) (vm : Cm ⥤ E)
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  (O : Sheaf L RingCat.{r}) (t : I → (Cn ⥤ Cm)) (τ : ∀ i, t i ⋙ vm ⟶ vn)
  [ht : ∀ i, (t i).IsContinuous Jn Jm]
  [∀ F : Cmᵒᵖ ⥤ RingCat.{r}, vm.op.HasPointwiseRightKanExtension F]
  [∀ F : Cmᵒᵖ ⥤ AddCommGrpCat.{v}, vm.op.HasPointwiseRightKanExtension F]
  [Small.{v} I]
  [(_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).IsRightAdjoint]
  [∀ i, (_root_.SheafOfModules.pushforward.{v}
    (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))).IsRightAdjoint]
  [HasCoproduct fun i => _root_.SheafOfModules.pullback.{v}
    (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))]
  (hfan : ∀ (P : Cmᵒᵖ ⥤ AddCommGrpCat.{v}) (U : Cn),
    IsLimit (Fan.mk ((vm.op.ran.obj P).obj (op (vn.obj U)))
      fun i => (vm.op.ran.obj P).map ((τ i).app U).op ≫
        (vm.op.ranCounit.app P).app (op ((t i).obj U))))

/-- The `i`th summand inclusion into the module ran criterion's coproduct formula, followed by
that formula, is the conjugate of the comparison `ranComparisonSheaf` of right adjoints. -/
theorem sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom (i : I) :
    Sigma.ι (fun i => _root_.SheafOfModules.pullback.{v}
          (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))) i ≫
        (pullbackCompRestrictIsoCoproductOfRan vn vm Jn Jm L O t τ hfan).hom =
      Adjunction.conjugateInj
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
            (F := vn) (𝟙 (ringSheaf vn Jn L O))).comp (sheafAdjunction.{v} vm Jm L O))
        (fun i => _root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
          (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i)))
        (fun i => ranComparisonSheaf.{v} vn vm Jn Jm L O (t i) (τ i)) i :=
  colimit.isoColimitCocone_ι_hom _ (⟨i⟩ : Discrete I)

/-- Transposing along the adjunction of the `i`th summand, after precomposing with the `i`th
summand inclusion of the module ran criterion's coproduct formula, is transposing along the
composite adjunction and then postcomposing with the comparison of right adjoints.

This is the usable form of
`Stacks.SheafOfModules.RestrictRan.sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom`: the
right-hand side mentions only `ranComparisonSheaf`, whose underlying transformation of presheaves
of abelian groups is the Kan extension leg at the index attached to `τ i`. -/
theorem homEquiv_sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom (i : I)
    (X : _root_.SheafOfModules.{v} (ringSheaf vn Jn L O))
    (T : _root_.SheafOfModules.{v} (ringSheaf vm Jm L O))
    (f : (_root_.SheafOfModules.pullback.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O)) ⋙
      _root_.SheafOfModules.pushforward.{v} (F := vm) (𝟙 (ringSheaf vm Jm L O))).obj X ⟶ T) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
          (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))).homEquiv X T
        ((Sigma.ι (fun i => _root_.SheafOfModules.pullback.{v}
            (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))) i ≫
          (pullbackCompRestrictIsoCoproductOfRan vn vm Jn Jm L O t τ hfan).hom).app X ≫ f) =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
              (F := vn) (𝟙 (ringSheaf vn Jn L O))).comp
            (sheafAdjunction.{v} vm Jm L O)).homEquiv X T f ≫
        (ranComparisonSheaf.{v} vn vm Jn Jm L O (t i) (τ i)).app T := by
  rw [sigma_ι_comp_pullbackCompRestrictIsoCoproductOfRan_hom vn vm Jn Jm L O t τ hfan i]
  exact Adjunction.homEquiv_conjugateInj
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
        (F := vn) (𝟙 (ringSheaf vn Jn L O))).comp (sheafAdjunction.{v} vm Jm L O))
    (fun i => _root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
      (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i)))
    (fun i => ranComparisonSheaf.{v} vn vm Jn Jm L O (t i) (τ i)) i f

end Criterion

end Stacks.SheafOfModules.RestrictRan

end
