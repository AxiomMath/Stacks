module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableTransitionRestriction
public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegCaseBSections
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompMate
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfUnitComm

/-!
# Composition of the relocalization restrictions of a simplicial semi-representable ringed site

Let `(C, O_C)` be a ringed site, `K` a simplicial semi-representable object of `C` and
`O = a⁻¹O_C` the structure sheaf of Remark 0D9W on the total site of the simplicial site
`n ↦ C/K_n`. For a simplex map `φ : [m] ⟶ [n]` the pullback `f_φ^*` of modules along the
transition morphism is restriction along the relocalization functor `r_φ : C/K_n ⥤ C/K_m`
(`CategoryTheory.SimplicialSemiRepresentable.transitionPullbackModulesIso`).

This file shows that these identifications are compatible with composition. For composable
simplex maps `ψ` and `φ` the compositor `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` of Stacks 09WE, which is
defined as the adjoint mate of the compositor of direct images, corresponds to the comparison
`r_ψ^{-1} ⋙ r_φ^{-1} ≅ r_{ψ ≫ φ}^{-1}` of restrictions, and the latter is the identity on
sections, up to the identification of the two relocalizations `r_ψ(r_φ(V))` and `r_{ψ ≫ φ}(V)`
of an object `V` of `C/K_n`. This is the sense in which the decomposition
`Mod(O_n) = ∏_i Mod(O_{U_{n,i}})` is "compatible with the morphisms in the simplicial
semi-representable object `K`" in the proof of Stacks 0DCA.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.transitionRestrictionPushforwardAdjunction`:
  restriction along `r_φ` is left adjoint to the direct image along `f_φ`.
* `CategoryTheory.SimplicialSemiRepresentable.transitionRestrictionCompIso`: the comparison
  `r_ψ^{-1} ⋙ r_φ^{-1} ≅ r_{ψ ≫ φ}^{-1}` of restrictions of modules.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.moduleSheafFunctor_map_unit_app`: on underlying
  sheaves of sets, the unit of `r_φ^{-1} ⊣ (f_φ)_*` is the unit of the restriction–direct-image
  adjunction of sheaves of sets.
* `CategoryTheory.SimplicialSemiRepresentable.transitionRestrictionCompIso_hom_app_heq`: the
  comparison of restrictions is the identity on sections.
* `CategoryTheory.SimplicialSemiRepresentable.transitionPullbackModulesCompIso_comm`: the
  compositor of pullbacks corresponds to the comparison of restrictions.

## Implementation notes

The comparison of restrictions is computed after forgetting to sheaves of sets, where it is
Mathlib's `CategoryTheory.Functor.sheafPushforwardContinuousComp'` by
`CategoryTheory.leftAdjointCompIso_sheafPushforwardCocontinuousCompIso`. The passage is
`CategoryTheory.conjugateEquiv_symm_of_unit_comm_app`, for the forgetful functors with the
identity commutation isomorphisms `moduleSheafTransitionRestrictionIso` and
`moduleSheafTransitionPushforwardIso`. Every equation is stated with those isomorphisms between
the module-side and the set-side spellings of an object rather than across the two spellings:
the two are definitionally equal, but checking that for a composite of two direct images is
unaffordable, while each commutation isomorphism is checked at one functor only.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory

/-- The comparison of restrictions of sheaves of sets along a composable pair of continuous
functors and along their composite is the identity on sections. -/
theorem Functor.sheafPushforwardContinuousComp'_eqToIso_hom_app_heq {C₂ : Type u} [SmallCategory C₂]
    {C₁ : Type u} [SmallCategory C₁] {C₀ : Type u} [SmallCategory C₀]
    (J₂ : GrothendieckTopology C₂) (J₁ : GrothendieckTopology C₁) (J₀ : GrothendieckTopology C₀)
    (u' : C₂ ⥤ C₁) (v : C₁ ⥤ C₀) {w : C₂ ⥤ C₀} [u'.IsContinuous J₂ J₁] [v.IsContinuous J₁ J₀]
    [w.IsContinuous J₂ J₀] (h : u' ⋙ v = w) (P : Sheaf J₀ (Type u)) (V : C₂ᵒᵖ)
    (x : ((u'.sheafPushforwardContinuous (Type u) J₂ J₁).obj
      ((v.sheafPushforwardContinuous (Type u) J₁ J₀).obj P)).obj.obj V) :
    HEq (((Functor.sheafPushforwardContinuousComp' (eqToIso h) (Type u) J₂ J₁ J₀).hom.app P).hom.app
        V x) x := by
  subst h
  refine heq_of_eq ?_
  simp only [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, NatTrans.op_id, Functor.whiskerRight_id']
  rfl

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **Restriction along `r_φ` is left adjoint to the direct image along `f_φ`.** -/
def transitionRestrictionPushforwardAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionRestriction X K φ ⊣
      (situation X.J K).transitionPushforwardModules (structureSheaf X K) φ :=
  (transitionRestrictionAdjunction X K φ).ofNatIsoRight
    (CocontinuousSimplicialSite.transitionPushforwardModulesIsoB
      (simplicialSite X.J K) (structureSheaf X K) φ)

/-- The unit of `transitionRestrictionPushforwardAdjunction` is the unit of
`transitionRestrictionAdjunction` followed by the comparison of the two direct images. -/
theorem transitionRestrictionPushforwardAdjunction_unit_app {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K m)) :
    (transitionRestrictionPushforwardAdjunction X K φ).unit.app M =
      (transitionRestrictionAdjunction X K φ).unit.app M ≫
        (CocontinuousSimplicialSite.transitionPushforwardModulesIsoB
          (simplicialSite X.J K) (structureSheaf X K) φ).hom.app _ := by
  rw [← Adjunction.homEquiv_id]
  exact (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans
    (congrArg (fun k => k ≫ _) (Adjunction.homEquiv_id _ _))

/-- The unit of the scalars equivalence at the restriction of `M`, with its target spelled as the
restriction of scalars of the underlying presheaf of modules of `r_φ^{-1} M`. -/
def transitionScalarsUnit {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K m)) :
    (PresheafOfModules.pushforward₀ (transitionSiteFunctor X K φ) (componentRing X K m).obj).obj
        M.val ⟶
      (PresheafOfModules.restrictScalars.{u} (transitionRingInv X K φ)).obj
        ((transitionRestriction X K φ).obj M).val :=
  (transitionScalarsEquivalence X K φ).unit.app _

/-- The unit of `transitionRestrictionAdjunction` on underlying presheaves of modules: the
adjunct of the unit of the scalars equivalence, followed by the comparison moving the
restriction of scalars past the right Kan extension. -/
theorem transitionRestrictionAdjunction_unit_app_val {m n : SimplexCategory} (φ : m ⟶ n) (M :
    SheafOfModules.{u} (componentRing X K m)) :
    ((transitionRestrictionAdjunction X K φ).unit.app M).val =
      (Stacks.SheafOfModules.RestrictRan.adjunction (transitionSiteFunctor X K φ)
          (componentRing X K m).obj).homEquiv M.val
        ((PresheafOfModules.restrictScalars.{u} (transitionRingInv X K φ)).obj
          ((transitionRestriction X K φ).obj M).val)
        (transitionScalarsUnit X K φ M) ≫
      (Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso.{u}
        (transitionSiteFunctor X K φ)
        (transitionRingInv X K φ)).hom.app ((transitionRestriction X K φ).obj M).val := by
  refine (forget_map_transitionRestrictionAdjunction_unit_app X K φ M).trans ?_
  refine congrArg (fun k => k ≫ _) ?_
  rw [transitionPresheafAdjunction, Adjunction.comp_unit_app]
  exact (Adjunction.homEquiv_unit _ _ _ _).symm

/-- The leg at `(U, ψ)` of the unit of `r_φ^{-1} ⊣ (f_φ)_*`, on a section `y`, is the
restriction of `y` along `ψ`. -/
theorem ranπ_moduleSheafFunctor_map_unit_app {m n : SimplexCategory} (φ : m ⟶ n) (M :
    SheafOfModules.{u} (componentRing X K m))
    (V : ((CocontinuousSimplicialSite.situation (simplicialSite X.J K)).component m)ᵒᵖ)
    (j : StructuredArrow V (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K)
        φ).op)
    (y : (Sheaf.moduleSheaf (componentRing X K m) M).obj.obj V) :
    Stacks.SheafOfModules.ranπ (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K)
        φ).op
        (Sheaf.moduleSheaf (componentRing X K n) ((transitionRestriction X K φ).obj M)).obj V j
        (((Sheaf.moduleSheafFunctor (componentRing X K m)).map
          ((transitionRestrictionPushforwardAdjunction X K φ).unit.app M)).hom.app V y) =
      (Sheaf.moduleSheaf (componentRing X K m) M).obj.map j.hom y := by
  rw [transitionRestrictionPushforwardAdjunction_unit_app]
  open CocontinuousSimplicialSite in
  refine ((congrArg (fun z => Stacks.SheafOfModules.ranπ
      (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K) φ).op
      (Sheaf.moduleSheaf (componentRing X K n) ((transitionRestriction X K φ).obj M)).obj V j z)
    (moduleSheafFunctor_map_comp_transitionRingedToposPushforwardModulesIsoB_hom_app
      (simplicialSite X.J K) (structureSheaf X K) φ M ((transitionRestriction X K φ).obj M)
      ((transitionRestrictionAdjunction X K φ).unit.app M) V y)).symm).trans ?_
  exact CocontinuousSimplicialSite.ranπ_moduleSheafFunctor_map_comp_eq_sourceMap
    (simplicialSite X.J K) (structureSheaf X K) φ M ((transitionRestriction X K φ).obj M)
    ((transitionRestrictionAdjunction X K φ).unit.app M) _
        (transitionRestrictionAdjunction_unit_app_val X K φ M) V j y

/-- **On underlying sheaves of sets, the unit of `r_φ^{-1} ⊣ (f_φ)_*` is the unit of the
restriction–direct-image adjunction of sheaves of sets** along the continuous and cocontinuous
functor `r_φ`. -/
theorem moduleSheafFunctor_map_unit_app {m n : SimplexCategory} (φ : m ⟶ n) (M : SheafOfModules.{u}
    (componentRing X K m)) :
    (Sheaf.moduleSheafFunctor (componentRing X K m)).map
        ((transitionRestrictionPushforwardAdjunction X K φ).unit.app M) =
    ((transitionSiteFunctor X K φ).sheafAdjunctionCocontinuous (Type u)
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J).unit.app
        ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj M) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun y => ?_)
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (NatTrans.congr_app
    (Functor.sheafAdjunctionCocontinuous_unit_app_hom (transitionSiteFunctor X K φ) (Type u)
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J
      ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj M)).symm V) y)
  refine Stacks.SheafOfModules.ranπ_ext (L' := (CocontinuousSimplicialSite.transitionFunctorB
      (simplicialSite X.J K) φ).op)
    (N' := (Sheaf.moduleSheaf (componentRing X K n) ((transitionRestriction X K φ).obj M)).obj)
    fun j => ?_
  refine (ranπ_moduleSheafFunctor_map_unit_app X K φ M V j y).trans ?_
  have h := ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ
    (transitionSiteFunctor X K φ).op ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj M).obj V
        j) y
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm

/-- Restriction of sheaves of sets along `r_φ` is left adjoint to the direct image. -/
abbrev transitionSheafAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :=
  (transitionSiteFunctor X K φ).sheafAdjunctionCocontinuous (Type u)
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J

/-- The relocalization functors compose: `r_φ ⋙ r_ψ = r_{ψ ≫ φ}`. -/
theorem transitionSiteFunctor_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    transitionSiteFunctor X K φ ⋙ transitionSiteFunctor X K ψ = transitionSiteFunctor X K (ψ ≫ φ) :=
  (congrArg Cat.Hom.toFunctor ((simplicialSite X.J K).underlying.map_comp φ.op ψ.op)).symm

/-- A composite of relocalization functors is cocontinuous. -/
instance transitionSiteFunctor_comp_isCocontinuous {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    (transitionSiteFunctor X K φ ⋙ transitionSiteFunctor X K ψ).IsCocontinuous
      (componentRingedTopos X K n).J (componentRingedTopos X K l).J :=
  CategoryTheory.isCocontinuous_comp _ _ _ (componentRingedTopos X K m).J

/-- On sheaves of sets, the compositor of restrictions attached to the compositor of direct
images of Stacks 09WE is `CategoryTheory.Functor.sheafPushforwardContinuousComp'`. -/
theorem leftAdjointCompIso_transitionSheafAdjunction {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶
    n) :
    Adjunction.leftAdjointCompIso (transitionSheafAdjunction X K ψ) (transitionSheafAdjunction X K
        φ) (transitionSheafAdjunction X K (ψ ≫ φ))
      ((situation X.J K).pushforwardCompSymm ψ φ) =
    Functor.sheafPushforwardContinuousComp' (eqToIso (transitionSiteFunctor_comp X K ψ φ)) (Type u)
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J (componentRingedTopos X K l).J
          :=
  leftAdjointCompIso_sheafPushforwardCocontinuousCompIso _ _ _ _ _ (transitionSiteFunctor_comp X K ψ
      φ)



/-- The direct image of sheaves of sets along the cocontinuous relocalization functor `r_φ`. -/
abbrev transitionSheafPushforward {m n : SimplexCategory} (φ : m ⟶ n) :=
  (transitionSiteFunctor X K φ).sheafPushforwardCocontinuous (Type u)
    (componentRingedTopos X K n).J (componentRingedTopos X K m).J

/-- Forgetting the module structure commutes with restriction along `r_φ`, on the nose. -/
def moduleSheafTransitionRestrictionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf.moduleSheafFunctor (componentRing X K m) ⋙
        (transitionSiteFunctor X K φ).sheafPushforwardContinuous (Type u)
          (componentRingedTopos X K n).J (componentRingedTopos X K m).J ≅
      transitionRestriction X K φ ⋙ Sheaf.moduleSheafFunctor (componentRing X K n) :=
  Iso.refl _

/-- Forgetting the module structure commutes with the direct image along `f_φ`, on the nose. -/
def moduleSheafTransitionPushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf.moduleSheafFunctor (componentRing X K n) ⋙
        (transitionSiteFunctor X K φ).sheafPushforwardCocontinuous (Type u)
          (componentRingedTopos X K n).J (componentRingedTopos X K m).J ≅
      (situation X.J K).transitionPushforwardModules (structureSheaf X K) φ ⋙
        Sheaf.moduleSheafFunctor (componentRing X K m) :=
  Iso.refl _

/-- The units of `r_φ^{-1} ⊣ (f_φ)_*` and of its counterpart on sheaves of sets correspond
through the identity commutation isomorphisms. -/
theorem moduleSheafFunctor_map_unit_app_comm {m n : SimplexCategory} (φ : m ⟶ n) (M :
    SheafOfModules.{u} (componentRing X K m)) :
    (Sheaf.moduleSheafFunctor (componentRing X K m)).map
        ((transitionRestrictionPushforwardAdjunction X K φ).unit.app M) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app ((transitionRestriction X K φ).obj M) =
      (transitionSheafAdjunction X K φ).unit.app ((Sheaf.moduleSheafFunctor (componentRing X K
          m)).obj M) ≫
        ((transitionSiteFunctor X K φ).sheafPushforwardCocontinuous (Type u)
          (componentRingedTopos X K n).J (componentRingedTopos X K m).J).map
              ((moduleSheafTransitionRestrictionIso X K φ).hom.app M) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun y => ?_)
  refine Stacks.SheafOfModules.ranπ_ext
    (L' := (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K) φ).op)
    (N' := (Sheaf.moduleSheaf (componentRing X K n) ((transitionRestriction X K φ).obj M)).obj)
    fun j => ?_
  refine (ranπ_moduleSheafFunctor_map_unit_app X K φ M V j y).trans ?_
  refine Eq.trans ?_ (Stacks.SheafOfModules.ranπ_map_functor_apply
    (transitionSiteFunctor X K φ) ((moduleSheafTransitionRestrictionIso X K φ).hom.app M).hom V j
        _).symm
  have h := ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranAdjunction_unit_app_app_comp_ranπ
    (transitionSiteFunctor X K φ).op ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj M).obj V
        j) y
  simp only [ConcreteCategory.comp_apply] at h
  refine h.symm.trans ?_
  exact congrArg (fun z => Stacks.SheafOfModules.ranπ (transitionSiteFunctor X K φ).op
      ((transitionSiteFunctor X K φ).op ⋙ ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj
          M).obj) V j z)
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (Functor.sheafAdjunctionCocontinuous_unit_app_hom (transitionSiteFunctor X K φ) (Type u)
        (componentRingedTopos X K n).J (componentRingedTopos X K m).J
        ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj M)).symm V) y)


/-- The composite commutation isomorphism of two direct images, unfolded. -/
theorem commIsoComp_moduleSheafTransitionPushforwardIso_inv_app_eq {l m n : SimplexCategory} (ψ : l
    ⟶ m) (φ : m ⟶ n) (N : SheafOfModules.{u} (componentRing X K n)) :
    (commIsoComp (moduleSheafTransitionPushforwardIso X K φ) (moduleSheafTransitionPushforwardIso X
        K ψ)).inv.app N =
      (moduleSheafTransitionPushforwardIso X K ψ).inv.app (((situation X.J
          K).transitionPushforwardModules (structureSheaf X K) φ).obj N) ≫
          (transitionSheafPushforward X K ψ).map ((moduleSheafTransitionPushforwardIso X K
          φ).inv.app N) :=
  commIsoComp_inv_app _ _ N

/-- The direct image of an identity commutation isomorphism is the identity. -/
theorem transitionSheafPushforward_map_moduleSheafTransitionPushforwardIso_inv_app {l m n :
    SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (N : SheafOfModules.{u} (componentRing X K n)) :
    (transitionSheafPushforward X K ψ).map ((moduleSheafTransitionPushforwardIso X K φ).inv.app N) =
        𝟙 _ :=
  Functor.map_id _ _

/-- The commutation isomorphism of the direct image is the identity. -/
theorem moduleSheafTransitionPushforwardIso_inv_app {l m : SimplexCategory} (ψ : l ⟶ m) (N :
    SheafOfModules.{u} (componentRing X K m)) :
    (moduleSheafTransitionPushforwardIso X K ψ).inv.app N = 𝟙 _ := rfl


/-- The composite commutation isomorphism of two direct images is the identity. -/
theorem commIsoComp_moduleSheafTransitionPushforwardIso_inv_app {l m n : SimplexCategory} (ψ : l ⟶
    m) (φ : m ⟶ n) (N : SheafOfModules.{u} (componentRing X K n)) :
    (commIsoComp (moduleSheafTransitionPushforwardIso X K φ) (moduleSheafTransitionPushforwardIso X
        K ψ)).inv.app N = 𝟙 _ := by
  rw [commIsoComp_moduleSheafTransitionPushforwardIso_inv_app_eq,
      transitionSheafPushforward_map_moduleSheafTransitionPushforwardIso_inv_app,
      moduleSheafTransitionPushforwardIso_inv_app]
  exact Category.comp_id _


/-- The geometric compositor of direct images, spelled through the relocalization functors. -/
def transitionSheafPushforwardCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    transitionSheafPushforward X K φ ⋙ transitionSheafPushforward X K ψ ≅ transitionSheafPushforward
        X K (ψ ≫ φ) :=
  (situation X.J K).pushforwardCompSymm ψ φ

/-- On underlying sheaves of sets, the inverse of the comparison of direct images of modules is
the inverse of the geometric compositor of Stacks 09WE. -/
theorem moduleSheafFunctor_map_transitionPushforwardModulesCompIso_inv_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (N : SheafOfModules.{u} (componentRing X K n)) :
    (Sheaf.moduleSheafFunctor (componentRing X K l)).map
        (((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ).inv.app N)
            =
      (transitionSheafPushforwardCompIso X K ψ φ).inv.app ((Sheaf.moduleSheafFunctor (componentRing
          X K n)).obj N) := by
  have e1 : (Sheaf.moduleSheafFunctor (componentRing X K l)).map
        (((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ).hom.app N)
            =
      (transitionSheafPushforwardCompIso X K ψ φ).hom.app ((Sheaf.moduleSheafFunctor (componentRing
          X K n)).obj N) :=
    (situation X.J K).moduleSheaf_transitionPushforwardModulesCompIso_hom (structureSheaf X K) ψ φ N
  exact congrArg Iso.inv (Iso.ext (α := (Sheaf.moduleSheafFunctor (componentRing X K l)).mapIso
      (((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ).app N))
      (β := (transitionSheafPushforwardCompIso X K ψ φ).app ((Sheaf.moduleSheafFunctor
          (componentRing X K n)).obj N)) e1)

/-- The comparison of direct images of modules and the geometric compositor correspond through
the commutation isomorphisms. -/
theorem moduleSheafFunctor_map_transitionPushforwardModulesCompIso_inv_app_comm {l m n :
    SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (N : SheafOfModules.{u} (componentRing X K n)) :
    (moduleSheafTransitionPushforwardIso X K (ψ ≫ φ)).inv.app N ≫ (transitionSheafPushforwardCompIso
        X K ψ φ).inv.app
        ((Sheaf.moduleSheafFunctor (componentRing X K n)).obj N) =
      (Sheaf.moduleSheafFunctor (componentRing X K l)).map
        (((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ).inv.app N)
            ≫
        (commIsoComp (moduleSheafTransitionPushforwardIso X K φ)
            (moduleSheafTransitionPushforwardIso X K ψ)).inv.app N := by
  rw [commIsoComp_moduleSheafTransitionPushforwardIso_inv_app,
      moduleSheafTransitionPushforwardIso_inv_app,
    moduleSheafFunctor_map_transitionPushforwardModulesCompIso_inv_app]
  exact (Category.id_comp ((transitionSheafPushforwardCompIso X K ψ φ).inv.app
      ((Sheaf.moduleSheafFunctor (componentRing X K n)).obj N))).trans
    (Category.comp_id ((transitionSheafPushforwardCompIso X K ψ φ).inv.app
        ((Sheaf.moduleSheafFunctor (componentRing X K n)).obj N))).symm


/-- **The literal comparison `r_ψ^{-1} ⋙ r_φ^{-1} ≅ r_{ψ ≫ φ}^{-1}` of restrictions of modules**,
the compositor of left adjoints which `CategoryTheory.Adjunction.leftAdjointCompIso` attaches to
the comparison of direct images of Stacks 09WE. It is the identity on sections up to the
identification of the two relocalizations of an object
(`CategoryTheory.SimplicialSemiRepresentable.transitionRestrictionCompIso_hom_app_heq`). -/
def transitionRestrictionCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    transitionRestriction X K ψ ⋙ transitionRestriction X K φ ≅ transitionRestriction X K (ψ ≫ φ) :=
  Adjunction.leftAdjointCompIso (transitionRestrictionPushforwardAdjunction X K ψ)
    (transitionRestrictionPushforwardAdjunction X K φ)
    (transitionRestrictionPushforwardAdjunction X K (ψ ≫ φ))
    ((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ)

/-- **On underlying sheaves of sets, the comparison of restrictions is
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`**, through the commutation
isomorphisms. -/
theorem moduleSheafFunctor_map_transitionRestrictionCompIso_hom_app {l m n : SimplexCategory} (ψ : l
    ⟶ m) (φ : m ⟶ n) (M : SheafOfModules.{u} (componentRing X K l)) :
    (Functor.sheafPushforwardContinuousComp' (eqToIso (transitionSiteFunctor_comp X K ψ φ)) (Type u)
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J (componentRingedTopos X K
          l).J).hom.app
        ((Sheaf.moduleSheafFunctor (componentRing X K l)).obj M) ≫
            (moduleSheafTransitionRestrictionIso X K (ψ ≫ φ)).hom.app M =
      (commIsoComp (moduleSheafTransitionRestrictionIso X K ψ) (moduleSheafTransitionRestrictionIso
          X K φ)).hom.app M ≫
        (Sheaf.moduleSheafFunctor (componentRing X K n)).map
          ((transitionRestrictionCompIso X K ψ φ).hom.app M) := by
  rw [← leftAdjointCompIso_transitionSheafAdjunction, transitionRestrictionCompIso]
  exact conjugateEquiv_symm_of_unit_comm_app (transitionSheafAdjunction X K (ψ ≫ φ))
      ((transitionSheafAdjunction X K ψ).comp (transitionSheafAdjunction X K φ))
    (transitionRestrictionPushforwardAdjunction X K (ψ ≫ φ))
    ((transitionRestrictionPushforwardAdjunction X K ψ).comp
        (transitionRestrictionPushforwardAdjunction X K φ))
    (moduleSheafTransitionRestrictionIso X K (ψ ≫ φ)) (moduleSheafTransitionPushforwardIso X K (ψ ≫
        φ))
    (commIsoComp (moduleSheafTransitionRestrictionIso X K ψ) (moduleSheafTransitionRestrictionIso X
        K φ)) (commIsoComp (moduleSheafTransitionPushforwardIso X K φ)
        (moduleSheafTransitionPushforwardIso X K ψ))
    (moduleSheafFunctor_map_unit_app_comm X K (ψ ≫ φ))
    (unit_comm_comp (transitionSheafAdjunction X K ψ) (transitionSheafAdjunction X K φ)
        (transitionRestrictionPushforwardAdjunction X K ψ)
      (transitionRestrictionPushforwardAdjunction X K φ) (moduleSheafTransitionRestrictionIso X K ψ)
          (moduleSheafTransitionPushforwardIso X K ψ) (moduleSheafTransitionRestrictionIso X K φ)
          (moduleSheafTransitionPushforwardIso X K φ)
      (moduleSheafFunctor_map_unit_app_comm X K ψ) (moduleSheafFunctor_map_unit_app_comm X K φ))
    (transitionSheafPushforwardCompIso X K ψ φ).inv
    ((situation X.J K).transitionPushforwardModulesCompIso (structureSheaf X K) ψ φ).inv
    (moduleSheafFunctor_map_transitionPushforwardModulesCompIso_inv_app_comm X K ψ φ) M

/-- The composite commutation isomorphism of two restrictions fixes sections. -/
theorem commIsoComp_moduleSheafTransitionRestrictionIso_hom_app_apply {l m n : SimplexCategory} (ψ :
    l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K l)) (V : ((componentRingedTopos X K n).C)ᵒᵖ)
    (x : ((transitionRestriction X K φ).obj ((transitionRestriction X K ψ).obj M)).val.obj V) :
    ((commIsoComp (moduleSheafTransitionRestrictionIso X K ψ) (moduleSheafTransitionRestrictionIso X
        K φ)).hom.app M).hom.app V x = x := by
  rw [commIsoComp_hom_app]
  rfl

/-- **The comparison of restrictions is the identity on sections**, up to the identification of
the two relocalizations of an object. -/
theorem transitionRestrictionCompIso_hom_app_heq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K l))
    (V : ((componentRingedTopos X K n).C)ᵒᵖ)
    (x : ((transitionRestriction X K φ).obj ((transitionRestriction X K ψ).obj M)).val.obj V) :
    HEq (((Sheaf.moduleSheafFunctor (componentRing X K n)).map
          ((transitionRestrictionCompIso X K ψ φ).hom.app M)).hom.app V x) x := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom)
      (moduleSheafFunctor_map_transitionRestrictionCompIso_hom_app X K ψ φ M)) V) x
  refine HEq.trans (heq_of_eq (congrArg (((Sheaf.moduleSheafFunctor (componentRing X K n)).map
          ((transitionRestrictionCompIso X K ψ φ).hom.app M)).hom.app V)
      (commIsoComp_moduleSheafTransitionRestrictionIso_hom_app_apply X K ψ φ M V x).symm)) ?_
  refine HEq.trans (heq_of_eq h.symm) ?_
  exact Functor.sheafPushforwardContinuousComp'_eqToIso_hom_app_heq
    (componentRingedTopos X K n).J (componentRingedTopos X K m).J (componentRingedTopos X K l).J _ _
    (transitionSiteFunctor_comp X K ψ φ) ((Sheaf.moduleSheafFunctor (componentRing X K l)).obj M) V
        x


/-- **The pullback of modules along `f_φ` is restriction along the relocalization `r_φ`**: the
comparison of the two left adjoints of the direct image `(f_φ)_*`. -/
def transitionPullbackModulesIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
      φ).toModulesHom.pullbackModules ≅
      transitionRestriction X K φ :=
  Adjunction.leftAdjointUniq ((situation X.J K).transitionPullbackAdj (structureSheaf X K) φ)
    (transitionRestrictionPushforwardAdjunction X K φ)

/-- **The compositor of pullbacks of modules is the comparison of restrictions.** Under the
identifications `transitionPullbackModulesIso` of `f_φ^*` with restriction along `r_φ`, the
compositor `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` of Stacks 09WE is the comparison
`transitionRestrictionCompIso`. -/
theorem transitionPullbackModulesCompIso_comm {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K l)) :
    ((situation X.J K).transitionPullbackModulesCompIso (structureSheaf X K) ψ φ).inv.app M ≫
        (transitionPullbackModulesIso X K (ψ ≫ φ)).hom.app M =
      ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesHom.pullbackModules.map
          ((transitionPullbackModulesIso X K ψ).hom.app M) ≫
        (transitionPullbackModulesIso X K φ).hom.app ((transitionRestriction X K ψ).obj M) ≫
          (transitionRestrictionCompIso X K ψ φ).hom.app M := by
  rw [(situation X.J K).transitionPullbackModulesCompIso_eq_leftAdjointCompIso, Iso.symm_inv]
  exact leftAdjointCompIso_hom_app_comp_leftAdjointUniq_hom_app _ _ _ _ _ _ _ M

end CategoryTheory.SimplicialSemiRepresentable
