module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarComponent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLeg
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaSituation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLowerShriek

/-!
# The terms of the simplex-coefficient resolution of a cartesian module are lower shrieks

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`M` a sheaf of `O`-modules on the total site. The degree-`n` term `B_n(M)` of the
simplex-coefficient resolution of `M` receives a canonical map

`g_{n!}(M|_n) ⟶ B_n(M)`

from the lower shriek of Stacks 0D72 of the restriction of `M` to the degree-`n` component: the
transpose under `g_{n!} ⊣ g_n^*` of the inclusion of `M|_n` as the summand of `B_n(M)|_n`
labelled by the identity simplex map. When `M` is cartesian it is an isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleBarLowerShriekMap`: the canonical map
  `g_{n!}(M|_n) ⟶ B_n(M)`.
* `CategoryTheory.SimplicialSiteSituation.isColimitModuleSumFormulaLegCofan`: the direct-sum
  formula of Stacks 0D72 on the component of degree `m`, as a colimit cofan.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleBarSummand_comp_restrictTransitionModules`: the
  identity-labelled summand inclusion, transported along the direct-image transition of a simplex
  map `φ`, is the `φ`-labelled summand inclusion.
* `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg_comp_moduleBarLowerShriekMap`: on
  the `φ`th summand of the direct-sum formula, the canonical map is the transition followed by
  the `φ`th summand inclusion.
* `CategoryTheory.SimplicialSiteSituation.isIso_moduleBarLowerShriekMap`: for a cartesian module
  the canonical map `g_{n!}(M|_n) ⟶ B_n(M)` is an isomorphism.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor AlgebraicGeometry
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] SimplicialSite.totalPseudofunctor
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete totalCategory Quiver.Hom.toLoc
  CoGrothendieck.category CoGrothendieck.categoryStruct CoGrothendieck.ι Cat.str
  Grothendieck.ι Grothendieck.instCategory uliftFunctor componentFunctor component
  simplexIndices totalSimplexDegree PresheafOfModules.presheaf

section General

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  (M : SheafOfModules.{u} O)

/-- Restriction in `B_n(M)` along an arrow of the total category from an object of degree `m` to
an object of degree `n` carries the identity-labelled summand to the `φ`-labelled one, as soon as
the arrow relabels the identity as `φ`. -/
theorem moduleBarPresheaf_map_single_barLabel_id {n m : SimplexCategory} (φ : n ⟶ m)
    {V : S.component n} {U : S.component m}
    (g : (componentFunctor S m).obj U ⟶ (componentFunctor S n).obj V)
    (hg : (simplexIndices.{u, u} S n).map g.op (barLabel (𝟙 n) V) = barLabel φ U)
    (x : M.val.obj (Opposite.op ((componentFunctor S n).obj V))) :
    (moduleBarPresheaf M n).map g.op (Finsupp.single (barLabel (𝟙 n) V) x) =
      Finsupp.single (barLabel φ U) (M.val.map g.op x) := by
  rw [PresheafOfModules.copowerObj_map_apply, Finsupp.mapRange_single,
    Finsupp.mapDomain_single, hg]

/-- The identity-labelled summand, transported along the direct-image transition of `φ`, is the
`φ`-labelled summand: the statement on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_moduleBarSummand_comp_restrictTransition {n m : SimplexCategory}
    (φ : n ⟶ m) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (S.componentRingSheaf O n)).map
        (moduleBarSummand M (𝟙 n)) ≫
      (S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} O (moduleBarSheaf M n)) =
    (S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} O M) ≫
      (S.transitionMorphism φ).pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u} (S.componentRingSheaf O m)).map
          (moduleBarSummand M φ)) := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C =>
    apply (sheafToPresheaf _ _).map_injective
    apply NatTrans.ext
    funext V
    ext x
    refine moduleBarPresheaf_map_single_barLabel_id M φ
      ((continuousInclusionTransition C φ).app V.unop) ?_ x
    apply ULift.ext
    show (𝟙 n ≫ 𝟙 n) ≫ φ = φ ≫ 𝟙 m
    simp
  | inr C =>
    apply Sheaf.hom_ext
    refine Eq.trans (ObjectProperty.FullSubcategory.comp_hom _ _ _) ?_
    refine Eq.trans ?_ (ObjectProperty.FullSubcategory.comp_hom _ _ _).symm
    refine ((((C.underlying.map φ.op).toFunctor).op.ranAdjunction (Type u)).homEquiv
      _ _).symm.injective ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _) ?_
    refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _).symm
    apply NatTrans.ext
    funext Y
    obtain ⟨U⟩ := Y
    ext x
    have key : ∀ (F : Sheaf (SimplicialSiteSituation.totalTopology ⟨Sum.inr C⟩) (Type u)) y,
        (ConcreteCategory.hom (((((C.underlying.map φ.op).toFunctor.op.ranAdjunction
          (Type u)).homEquiv _ _).symm
            ((restrictTransition ⟨Sum.inr C⟩ φ).app F).hom).app (Opposite.op U))) y =
          (ConcreteCategory.hom (F.obj.map
            ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U).op)) y :=
      fun F y => ConcreteCategory.congr_hom (restrictTransition_inr_app C φ F U) y
    have hg : (simplexIndices.{u, u} _ n).map
        ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U).op
          (barLabel (S := ⟨Sum.inr C⟩) (𝟙 n) ((C.underlying.map φ.op).toFunctor.obj U)) =
            barLabel (S := ⟨Sum.inr C⟩) φ U := by
      apply ULift.ext
      show (𝟙 n ≫ 𝟙 n) ≫ φ = φ ≫ 𝟙 m
      simp
    refine Eq.trans ?_ (Eq.trans (moduleBarPresheaf_map_single_barLabel_id M φ
      ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U) hg x) ?_)
    · exact key _ _
    · exact congrArg (Finsupp.single (barLabel (S := ⟨Sum.inr C⟩) φ U))
        (key (Sheaf.moduleSheaf.{u, u, u} O M) x).symm

end General

variable {S : SimplicialSiteSituation.{u}} (P : Sheaf S.totalTopology CommRingCat.{u})
  (M : SheafOfModules.{u} (S.totalRingSheaf P))

/-- For a simplex map `φ : [n] ⟶ [m]`, including `M|_n` into `B_n(M)|_n`
at the identity label and then passing to `(f_φ)_*(B_n(M)|_m)` along the transition of
Stacks 09WF agrees with passing to `(f_φ)_*(M|_m)` first and then including at the label `φ`. -/
theorem moduleBarSummand_comp_restrictTransitionModules {n m : SimplexCategory} (φ : n ⟶ m) :
    moduleBarSummand M (𝟙 n) ≫ (S.restrictTransitionModules P φ).app (moduleBarSheaf M n) =
      (S.restrictTransitionModules P φ).app M ≫
        (S.transitionRingedToposHom P φ).pushforwardModules.map (moduleBarSummand M φ) := by
  apply (Sheaf.moduleSheafFunctor.{u, u, u}
    (S.componentRingSheaf (S.totalRingSheaf P) n)).map_injective
  refine (Functor.map_comp _ _ _).trans (Eq.trans ?_ (Functor.map_comp _ _ _).symm)
  exact moduleSheafFunctor_map_moduleBarSummand_comp_restrictTransition M φ

/-- The canonical map `g_{n!}(M|_n) ⟶ B_n(M)`: the transpose under `g_{n!} ⊣ g_n^*` of the
inclusion of `M|_n` as the summand of `B_n(M)|_n` labelled by the identity simplex map. -/
def moduleBarLowerShriekMap (n : SimplexCategory) :
    (S.componentModuleLowerShriek (S.totalRingSheaf P) n).obj
        ((S.componentModuleRestriction (S.totalRingSheaf P) n).obj M) ⟶ moduleBarSheaf M n :=
  ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf P) n).homEquiv _ _).symm
    (moduleBarSummand M (𝟙 n))

/-- The unit of `g_{n!} ⊣ g_n^*` followed by the restriction of the canonical map is the
identity-labelled summand inclusion. -/
theorem unit_comp_map_moduleBarLowerShriekMap (n : SimplexCategory) :
    (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf P) n).unit.app
        ((S.componentModuleRestriction (S.totalRingSheaf P) n).obj M) ≫
      (S.componentModuleRestriction (S.totalRingSheaf P) n).map (moduleBarLowerShriekMap P M n) =
    moduleBarSummand M (𝟙 n) :=
  ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf P) n).homEquiv_unit _ _ _).symm.trans
    (((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf P) n).homEquiv _ _).apply_symm_apply
      _)

/-- For a simplex map `φ : [n] ⟶ [m]`, the canonical leg `f_φ^*(M|_n) ⟶ g_m^*g_{n!}(M|_n)` of the
direct-sum formula of Stacks 0D72 followed by the restriction to degree `m` of
`g_{n!}(M|_n) ⟶ B_n(M)` is the transition `f_φ^*(M|_n) ⟶ M|_m` of Stacks 09WF followed by the
inclusion of `M|_m` at the label `φ`. -/
theorem moduleSumFormulaLeg_comp_moduleBarLowerShriekMap {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.moduleSumFormulaLeg P φ).app ((S.componentModuleRestriction (S.totalRingSheaf P) n).obj M) ≫
      (S.componentModuleRestriction (S.totalRingSheaf P) m).map (moduleBarLowerShriekMap P M n) =
    S.fiberTransitionModules P φ M ≫ moduleBarSummand M φ := by
  apply ((S.transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv _ _).injective
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  refine (congrArg (fun t => t ≫ _) (S.homEquiv_moduleSumFormulaLeg_app P φ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => _ ≫ t)
    ((S.restrictTransitionModules P φ).naturality (moduleBarLowerShriekMap P M n)).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _) (unit_comp_map_moduleBarLowerShriekMap P M n)).trans ?_
  refine (moduleBarSummand_comp_restrictTransitionModules P M φ).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right
    (S.transitionRingedToposHom P φ).pullbackAdjPushforwardModules
    (S.fiberTransitionModules P φ M) (moduleBarSummand M φ)).symm
  exact congrArg (fun t => t ≫ _) (S.fiberTransitionModules_adj P φ M).symm

/-! ### The comparison is an isomorphism for a cartesian module -/

/-- A morphism between the points of two colimit cofans which, leg by leg, is an isomorphism of
the summands followed by the leg, is an isomorphism. -/
private theorem isIso_of_isColimit_cofan {C : Type*} [Category* C] {ι : Type*}
    {X Y : ι → C} {c₁ : Cofan X} {c₂ : Cofan Y} (h₁ : IsColimit c₁) (h₂ : IsColimit c₂)
    (e : ∀ i, X i ≅ Y i) (t : c₁.pt ⟶ c₂.pt) (ht : ∀ i, c₁.inj i ≫ t = (e i).hom ≫ c₂.inj i) :
    IsIso t := by
  refine ⟨Cofan.IsColimit.desc h₂ (fun i => (e i).inv ≫ c₁.inj i), ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext h₁ _ _ fun i => ?_
    rw [reassoc_of% (ht i), Cofan.IsColimit.fac, Iso.hom_inv_id_assoc, Category.comp_id]
  · refine Cofan.IsColimit.hom_ext h₂ _ _ fun i => ?_
    rw [Cofan.IsColimit.fac_assoc, Category.assoc, ht i, Iso.inv_hom_id_assoc, Category.comp_id]

attribute [local instance] hasWeakSheafifyComponent

/-- Over the component of degree `m`, the direct-sum formula of Stacks 0D72 presents the
restriction of `g_{n!}X` as the direct sum of the `f_φ^*X`, with the canonical legs. -/
def isColimitModuleSumFormulaLegCofan (n m : SimplexCategory)
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf P) n)) :
    IsColimit (Cofan.mk ((S.componentModuleRestriction (S.totalRingSheaf P) m).obj
        ((S.componentModuleLowerShriek (S.totalRingSheaf P) n).obj X))
      (fun φ : n ⟶ m => (S.moduleSumFormulaLeg P φ).app X)) := by
  let F := fun φ : n ⟶ m => S.transitionPullbackModules' P φ
  let e := S.moduleSumFormula P n m
  have h₁ : IsColimit (Cofan.mk (S.componentModuleLowerShriek (S.totalRingSheaf P) n ⋙
      S.componentModuleRestriction (S.totalRingSheaf P) m) fun φ => Sigma.ι F φ ≫ e.inv) :=
    (coproductIsCoproduct F).ofIsoColimit (Cofan.ext e.symm fun φ => rfl)
  have h₂ := (Cofan.isColimitMapCoconeEquiv ((evaluation _ _).obj X) F _).1
    (isColimitOfPreserves ((evaluation _ _).obj X) h₁)
  refine h₂.ofIsoColimit (Cofan.ext (Iso.refl _) fun φ => ?_)
  change (Sigma.ι F φ ≫ e.inv).app X ≫ 𝟙 _ = (S.moduleSumFormulaLeg P φ).app X
  rw [Category.comp_id, S.moduleSumFormulaLegEq P φ]

/-- For a cartesian module `M`, the canonical map `g_{n!}(M|_n) ⟶ B_n(M)` is an isomorphism. -/
theorem isIso_moduleBarLowerShriekMap (hM : S.IsCartesianModule P M) (n : SimplexCategory) :
    IsIso (moduleBarLowerShriekMap P M n) :=
  (isIso_iff_forall_isIso_componentModuleRestriction S (S.totalRingSheaf P) _).2 fun m =>
    isIso_of_isColimit_cofan (isColimitModuleSumFormulaLegCofan P n m _)
      (isColimitModuleBarComponentCofan M n m)
      (fun φ => @asIso _ _ _ _ (S.fiberTransitionModules P φ M) (hM φ)) _
      (moduleSumFormulaLeg_comp_moduleBarLowerShriekMap P M)

end CategoryTheory.SimplicialSiteSituation

end
