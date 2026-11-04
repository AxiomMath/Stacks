module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization

/-!
# Restriction of coefficient modules along a weakly étale morphism

Let `j : U ⟶ X` be a weakly étale morphism of schemes, for instance an open immersion or the
inclusion of a clopen piece. Composition with `j` is a functor `U_proét ⥤ X_proét` which is left
adjoint to base change `V ↦ V ×_X U`. Restriction of sheaves along it is the inverse image
`j⁻¹` of sheaves of modules over the constant coefficient ring sheaves, and the adjunction of
sites makes it left adjoint to the pushforward `j_*` along the canonical comparison
`\underline{Λ} ⟶ j_* \underline{Λ}`. Being a restriction along a continuous functor, `j⁻¹` is
left exact, and being a left adjoint it is right exact. This is the restriction datum
`AlgebraicGeometry.ProEtale.CoefficientRestriction` for `j`, which is how the restriction
`K ↦ K|_U` to an open of `X` is taken in the statements on `D(X_proét, Λ)`.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetalePostcomposeAdjunction`: composition with a weakly étale
  `j` is left adjoint to base change along `j`, on small pro-étale sites.
* `AlgebraicGeometry.ProEtale.constantCoefficientRestrictionComparison`: the canonical map
  `\underline{Λ}_U ⟶ \underline{Λ}_X ∘ j` of constant coefficient ring sheaves.
* `AlgebraicGeometry.ProEtale.coefficientRestriction`: the inverse image of sheaves of
  coefficient modules along a weakly étale morphism.
* `AlgebraicGeometry.ProEtale.CoefficientRestriction.ofWeaklyEtale`: the restriction datum of
  a weakly étale morphism.

## Main results

* `AlgebraicGeometry.ProEtale.coefficientRestrictionAdjunction`: `j⁻¹ ⊣ j_*`.
* `AlgebraicGeometry.ProEtale.coefficientRestriction_obj_val_obj`: the sections of `j⁻¹ F` over
  an object `V` of `U_proét` are the sections of `F` over `V` viewed over `X`.

## References

* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

/-- Composition with a weakly étale morphism `j : U ⟶ X` is left adjoint to base change along
`j`, as functors between the small pro-étale sites. -/
def proetalePostcomposeAdjunction :
    proetalePostcompose j ⊣ Scheme.proetaleBaseChange j := by
  have : MorphismProperty.HasPullbacksAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) j := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) j :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale : MorphismProperty Scheme.{u}) ⊤ j
    (inferInstanceAs (WeaklyEtale j)) trivial

attribute [local instance] proetalePostcompose_isContinuous

variable (Λ : Type r) [CommRing Λ]

/-- The canonical comparison `\underline{Λ}_U ⟶ \underline{Λ}_X ∘ j` of constant coefficient
ring sheaves along composition with a weakly étale `j : U ⟶ X`, adjoint to the sheafification
map of the constant presheaf of coefficient rings on `X`. -/
def constantCoefficientRestrictionComparison :
    (constantCoefficientRingedSite.{u, r, w} U Λ).O ⟶
      ((proetalePostcompose j).sheafPushforwardContinuous
          CommRingCat.{max (u + 1) r w} (Scheme.ProEt.topology U)
          (Scheme.ProEt.topology X)).obj
        (constantCoefficientRingedSite.{u, r, w} X Λ).O :=
  ((sheafificationAdjunction (Scheme.ProEt.topology U)
      CommRingCat.{max (u + 1) r w}).homEquiv _ _).symm
    (Functor.whiskerLeft (proetalePostcompose j).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))))

/-- The comparison of constant coefficient ring sheaves along composition with `j`, as a
morphism of sheaves of rings. -/
def coefficientRestrictionComparison :
    (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} U Λ).O) ⟶
      ((proetalePostcompose j).sheafPushforwardContinuous
          RingCat.{max (u + 1) r w} (Scheme.ProEt.topology U)
          (Scheme.ProEt.topology X)).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, r, w} X Λ).O)) :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max (u + 1) r w} RingCat.{max (u + 1) r w})).map
      (constantCoefficientRestrictionComparison.{u, r, w} j Λ)

/-- The sheafification map followed by the sheaf map adjoint to `g` is `g`. -/
private theorem toSheafify_comp_homEquiv_symm_hom {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} [HasWeakSheafify J D] (P : Cᵒᵖ ⥤ D) (F : Sheaf J D)
    (g : P ⟶ F.obj) :
    toSheafify J P ≫ (((sheafificationAdjunction J D).homEquiv P F).symm g).hom = g := by
  rw [← sheafificationAdjunction_unit_app]
  exact ((sheafificationAdjunction _ _).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply ((sheafificationAdjunction _ _).homEquiv _ _) _)

/-- The sheafification map of the constant presheaf on `U` followed by the comparison
`\underline{Λ}_U ⟶ \underline{Λ}_X ∘ j` is the sheafification map on `X` precomposed with `j`. -/
theorem toSheafify_comp_constantCoefficientRestrictionComparison :
    toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))) ≫
      (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom =
    Functor.whiskerLeft (proetalePostcompose j).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))) := by
  apply toSheafify_comp_homEquiv_symm_hom

omit [WeaklyEtale j] in
/-- The sheafification map of the constant presheaf on `X` followed by the comparison
`\underline{Λ}_X ⟶ \underline{Λ}_U ∘ (- ×_X U)` is the sheafification map on `U` precomposed
with base change along `j`. -/
theorem toSheafify_comp_constantCoefficientRingComparison :
    toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ))) ≫
      (constantCoefficientRingComparison.{u, r, w} Λ j).hom =
    Functor.whiskerLeft (Scheme.proetaleBaseChange j).op
      (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))) := by
  apply toSheafify_comp_homEquiv_symm_hom

/-- The first compatibility of the comparisons of constant coefficient ring sheaves with the
adjunction `proetalePostcompose j ⊣ proetaleBaseChange j`: restriction along its counit is the
composite of the two comparisons. -/
theorem whiskerRight_counit_constantCoefficientRingedSite :
    Functor.whiskerRight (NatTrans.op (proetalePostcomposeAdjunction j).counit)
        (constantCoefficientRingedSite.{u, r, w} X Λ).O.obj =
      (constantCoefficientRingComparison.{u, r, w} Λ j).hom ≫
        Functor.whiskerLeft (Scheme.proetaleBaseChange j).op
          (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom := by
  refine sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (((Scheme.proetaleBaseChange j).sheafPushforwardContinuous CommRingCat.{max (u + 1) r w}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology U)).obj
        (((proetalePostcompose j).sheafPushforwardContinuous CommRingCat.{max (u + 1) r w}
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).obj
            (constantCoefficientRingedSite.{u, r, w} X Λ).O)).property ?_
  refine NatTrans.ext (funext fun W ↦ ?_)
  have h1 : (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app W ≫
      (constantCoefficientRingComparison.{u, r, w} Λ j).hom.app W =
      (toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((Scheme.proetaleBaseChange j).obj W.unop)) :=
    congr_app (toSheafify_comp_constantCoefficientRingComparison.{u, r, w} j Λ) W
  have h2 : (toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((Scheme.proetaleBaseChange j).obj W.unop)) ≫
      (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom.app
        (op ((Scheme.proetaleBaseChange j).obj W.unop)) =
      (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((proetalePostcompose j).obj ((Scheme.proetaleBaseChange j).obj W.unop))) :=
    congr_app (toSheafify_comp_constantCoefficientRestrictionComparison.{u, r, w} j Λ) _
  show (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app W ≫
      (sheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).map
        ((proetalePostcomposeAdjunction j).counit.app W.unop).op =
    (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app W ≫
      (constantCoefficientRingComparison.{u, r, w} Λ j).hom.app W ≫
        (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom.app
          (op ((Scheme.proetaleBaseChange j).obj W.unop))
  exact (((toSheafify _ _).naturality _).symm.trans (Category.id_comp _)).trans
    ((h2.symm.trans (congrArg (· ≫ _) h1.symm)).trans (Category.assoc _ _ _))

/-- The second compatibility of the comparisons of constant coefficient ring sheaves with the
adjunction `proetalePostcompose j ⊣ proetaleBaseChange j`: the composite of the two comparisons
followed by restriction along its unit is the identity. -/
theorem comparison_comp_whiskerRight_unit_constantCoefficientRingedSite :
    (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom ≫
        Functor.whiskerLeft (proetalePostcompose j).op
          (constantCoefficientRingComparison.{u, r, w} Λ j).hom ≫
        Functor.whiskerRight (NatTrans.op (proetalePostcomposeAdjunction j).unit)
          (constantCoefficientRingedSite.{u, r, w} U Λ).O.obj =
      𝟙 _ := by
  refine sheafify_hom_ext (Scheme.ProEt.topology U) _ _
    (constantCoefficientRingedSite.{u, r, w} U Λ).O.property ?_
  refine NatTrans.ext (funext fun V ↦ ?_)
  have h1 : (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app V ≫
      (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom.app V =
      (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((proetalePostcompose j).obj V.unop)) :=
    congr_app (toSheafify_comp_constantCoefficientRestrictionComparison.{u, r, w} j Λ) V
  have h2 : (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((proetalePostcompose j).obj V.unop)) ≫
      (constantCoefficientRingComparison.{u, r, w} Λ j).hom.app
        (op ((proetalePostcompose j).obj V.unop)) =
      (toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app
        (op ((Scheme.proetaleBaseChange j).obj ((proetalePostcompose j).obj V.unop))) :=
    congr_app (toSheafify_comp_constantCoefficientRingComparison.{u, r, w} j Λ) _
  show (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app V ≫
      (constantCoefficientRestrictionComparison.{u, r, w} j Λ).hom.app V ≫
        (constantCoefficientRingComparison.{u, r, w} Λ j).hom.app
          (op ((proetalePostcompose j).obj V.unop)) ≫
          (sheafify (Scheme.ProEt.topology U)
              ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).map
            ((proetalePostcomposeAdjunction j).unit.app V.unop).op =
    (toSheafify (Scheme.ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).app V ≫ 𝟙 _
  refine (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) ((congrArg (· ≫ _) h1).trans h2)).trans ?_
  exact (((toSheafify _ _).naturality _).symm.trans (Category.id_comp _)).trans
    (Category.comp_id _).symm

/-- **Restriction of coefficient modules along a weakly étale morphism** `j : U ⟶ X`: the
inverse image `j⁻¹` of sheaves of modules over the constant coefficient ring sheaves, given by
restriction along composition with `j`. -/
def coefficientRestriction :
    RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} U Λ) :=
  SheafOfModules.pushforward (coefficientRestrictionComparison.{u, r, w} j Λ)

/-- The sections of `j⁻¹ F` over an object `V` of `U_proét` are those of `F` over `V` viewed
over `X`. -/
@[simp]
theorem coefficientRestriction_obj_val_obj
    (F : RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)) (V : U.ProEtᵒᵖ) :
    ((coefficientRestriction.{u, r, w} j Λ).obj F).val.obj V =
      (ModuleCat.restrictScalars
        ((coefficientRestrictionComparison.{u, r, w} j Λ).hom.app V).hom).obj
        (F.val.obj (op ((proetalePostcompose j).obj V.unop))) :=
  rfl

/-- **`j⁻¹ ⊣ j_*`**: restriction of coefficient modules along a weakly étale `j` is left adjoint
to the pushforward along the canonical comparison `\underline{Λ}_X ⟶ j_* \underline{Λ}_U`. -/
def coefficientRestrictionAdjunction :
    coefficientRestriction.{u, r, w} j Λ ⊣
      SheafOfModules.pushforward (coefficientRingComparison.{u, r, w} Λ j) := by
  refine SheafOfModules.pushforwardPushforwardAdj (proetalePostcomposeAdjunction j) _ _ ?_ ?_
  · refine NatTrans.ext (funext fun W ↦ ?_)
    exact congrArg (forget₂ CommRingCat RingCat).map
      (congr_app (whiskerRight_counit_constantCoefficientRingedSite.{u, r, w} j Λ) W)
  · refine NatTrans.ext (funext fun V ↦ ?_)
    have h := congrArg (forget₂ CommRingCat RingCat).map
      (congr_app (comparison_comp_whiskerRight_unit_constantCoefficientRingedSite.{u, r, w}
        j Λ) V)
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp] at h
    exact h

instance coefficientRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (coefficientRestriction.{u, r, w} j Λ) :=
  SheafOfModules.preservesFiniteLimits_pushforward _

instance coefficientRestriction_preservesColimits :
    PreservesColimitsOfSize (coefficientRestriction.{u, r, w} j Λ) :=
  (coefficientRestrictionAdjunction.{u, r, w} j Λ).leftAdjoint_preservesColimits

instance coefficientRestriction_additive :
    (coefficientRestriction.{u, r, w} j Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The restriction datum of a weakly étale morphism** `j : U ⟶ X`: restriction of
coefficient modules along composition with `j`, which is exact and left adjoint to `j_*`. -/
def CoefficientRestriction.ofWeaklyEtale : CoefficientRestriction.{u, r, w} Λ j where
  functor := coefficientRestriction.{u, r, w} j Λ
  additive := inferInstance
  preservesFiniteLimits := inferInstance
  preservesFiniteColimits := inferInstance
  adj := coefficientRestrictionAdjunction.{u, r, w} j Λ

end AlgebraicGeometry.ProEtale

end
