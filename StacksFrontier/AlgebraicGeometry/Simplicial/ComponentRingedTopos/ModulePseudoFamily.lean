module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoHomEquiv
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialPseudoFamily

/-!
# The pseudofunctorial family of modules on the components of a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
The categories of modules on the component ringed topoi, the pullbacks `f_φ^*` of sheaves of
modules along the transition morphisms, the compositor of those pullbacks and the identification
`f_𝟙^* ≅ 𝟭` form a `CategoryTheory.SimplicialPseudoFamily`. A cartesian sheaf of `O`-modules on
the total site, with its restrictions to the components and its transitions, is a cartesian system
of this family.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionPushforwardModulesIdIso`: the
  identification `(f_𝟙)_* ≅ 𝟭` of the direct image of sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.modulePseudoFamily`: the family.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleSystem`: the cartesian system of a
  cartesian module.

## Main results

* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesIdIso_eq_leftAdjointIdIso`:
  the identification `f_𝟙^* ≅ 𝟭` is the left-adjoint transport of `(f_𝟙)_* ≅ 𝟭`.
* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso_comp_id` and
  `.transitionPullbackModulesCompIso_id_comp`: the two unit laws for the compositor of pullbacks
  of sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.isCocycle_of_isModuleCocycle`: a cocycle of a pair of
  modules is a cocycle of the family.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The unit of the direct images of sheaves of modules -/

/-- The identification `(f_𝟙)_* ≅ 𝟭` of the direct image of sheaves of modules along the
transition morphism of an identity simplex map with the identity functor. -/
def transitionPushforwardModulesIdIso (n : SimplexCategory) :
    S.transitionPushforwardModules O (𝟙 n) ≅ 𝟭 _ :=
  (S.transitionRingedToposHom O (𝟙 n)).toModulesPushforwardIso ≪≫
    ((S.transitionRingedToposHom O (𝟙 n)).pushforwardModulesIsoId (S.pushforwardId n).symm
      (S.transitionFSharpId O n)).symm

/-- On underlying sheaves of sets the identification `(f_𝟙)_* ≅ 𝟭` of sheaves of modules is the
unit comparison of direct images of Stacks 09WE. -/
theorem componentModuleSheaf_transitionPushforwardModulesIdIso_hom (n : SimplexCategory)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O n).map ((S.transitionPushforwardModulesIdIso O n).hom.app M) =
      (S.pushforwardId n).hom.app ((S.componentModuleSheaf O n).obj M) := by
  change 𝟙 _ ≫ (S.pushforwardId n).hom.app ((S.componentModuleSheaf O n).obj M) = _
  exact Category.id_comp _

/-- On underlying sheaves of sets the transport of a direct image of sheaves of modules along an
equality of simplex maps is the transport of the direct image of sheaves of sets. -/
theorem componentModuleSheaf_transitionPushforwardModulesCongr_hom {m n : SimplexCategory}
    {φ₁ φ₂ : m ⟶ n} (h : φ₁ = φ₂)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O m).map ((S.transitionPushforwardModulesCongr O h).hom.app M) =
      (S.pushforwardCongr h).hom.app ((S.componentModuleSheaf O n).obj M) := by
  subst h
  rfl

/-- The underlying morphism of sheaves of sets of the left-hand side of the right unit law. -/
theorem componentModuleSheaf_comp_id_left {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O m).map
        ((S.transitionPushforwardModulesCompIso O φ (𝟙 n)).hom.app M ≫
          (S.transitionPushforwardModulesCongr O (Category.comp_id φ)).hom.app M) =
      (S.pushforwardCompSymm φ (𝟙 n)).hom.app ((S.componentModuleSheaf O n).obj M) ≫
        (S.pushforwardCongr (Category.comp_id φ)).hom.app
          ((S.componentModuleSheaf O n).obj M) := by
  rw [Functor.map_comp, S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom,
    S.componentModuleSheaf_transitionPushforwardModulesCongr_hom]
  rfl

/-- The underlying morphism of sheaves of sets of the right-hand side of the right unit law. -/
theorem componentModuleSheaf_comp_id_right {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O m).map ((S.transitionPushforwardModules O φ).map
        ((S.transitionPushforwardModulesIdIso O n).hom.app M)) =
      (S.transitionMorphism φ).pushforward.map
        ((S.pushforwardId n).hom.app ((S.componentModuleSheaf O n).obj M)) := by
  rw [S.componentModuleSheaf_transitionPushforwardModules_map,
    S.componentModuleSheaf_transitionPushforwardModulesIdIso_hom]
  rfl

/-- The right unit law for the direct-image compositors of Stacks 09WE, read at a sheaf. -/
theorem pushforwardCompSymm_comp_id_app {m n : SimplexCategory} (φ : m ⟶ n)
    (X : Sheaf (S.componentTopology n) (Type u)) :
    (S.pushforwardCompSymm φ (𝟙 n)).hom.app X ≫
        (S.pushforwardCongr (Category.comp_id φ)).hom.app X =
      (S.transitionMorphism φ).pushforward.map ((S.pushforwardId n).hom.app X) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (S.pushforwardCompSymm_comp_id φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  exact h

/-- The right unit law for the comparison of direct images of sheaves of modules, read at a
module. -/
theorem transitionPushforwardModulesCompIso_comp_id_app {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.transitionPushforwardModulesCompIso O φ (𝟙 n)).hom.app M ≫
        (S.transitionPushforwardModulesCongr O (Category.comp_id φ)).hom.app M =
      (S.transitionPushforwardModules O φ).map
        ((S.transitionPushforwardModulesIdIso O n).hom.app M) :=
  S.componentModuleSheaf_hom_ext O ((S.componentModuleSheaf_comp_id_left O φ M).trans
    ((S.pushforwardCompSymm_comp_id_app φ ((S.componentModuleSheaf O n).obj M)).trans
      (S.componentModuleSheaf_comp_id_right O φ M).symm))

/-- The underlying morphism of sheaves of sets of the left-hand side of the left unit law. -/
theorem componentModuleSheaf_id_comp_left {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O m).map
        ((S.transitionPushforwardModulesCompIso O (𝟙 m) φ).hom.app M ≫
          (S.transitionPushforwardModulesCongr O (Category.id_comp φ)).hom.app M) =
      (S.pushforwardCompSymm (𝟙 m) φ).hom.app ((S.componentModuleSheaf O n).obj M) ≫
        (S.pushforwardCongr (Category.id_comp φ)).hom.app
          ((S.componentModuleSheaf O n).obj M) := by
  rw [Functor.map_comp, S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom,
    S.componentModuleSheaf_transitionPushforwardModulesCongr_hom]
  rfl

/-- The left unit law for the direct-image compositors of Stacks 09WE, read at a sheaf. -/
theorem pushforwardCompSymm_id_comp_app {m n : SimplexCategory} (φ : m ⟶ n)
    (X : Sheaf (S.componentTopology n) (Type u)) :
    (S.pushforwardCompSymm (𝟙 m) φ).hom.app X ≫
        (S.pushforwardCongr (Category.id_comp φ)).hom.app X =
      (S.pushforwardId m).hom.app ((S.transitionMorphism φ).pushforward.obj X) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (S.pushforwardCompSymm_id_comp φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  exact h

/-- The left unit law for the comparison of direct images of sheaves of modules, read at a
module. -/
theorem transitionPushforwardModulesCompIso_id_comp_app {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.transitionPushforwardModulesCompIso O (𝟙 m) φ).hom.app M ≫
        (S.transitionPushforwardModulesCongr O (Category.id_comp φ)).hom.app M =
      (S.transitionPushforwardModulesIdIso O m).hom.app
        ((S.transitionPushforwardModules O φ).obj M) :=
  S.componentModuleSheaf_hom_ext O ((S.componentModuleSheaf_id_comp_left O φ M).trans
    ((S.pushforwardCompSymm_id_comp_app φ ((S.componentModuleSheaf O n).obj M)).trans
      (S.componentModuleSheaf_transitionPushforwardModulesIdIso_hom O m
        ((S.transitionPushforwardModules O φ).obj M)).symm))

/-- The right unit law for the comparison of direct images of sheaves of modules. -/
theorem transitionPushforwardModulesCompIso_comp_id {m n : SimplexCategory} (φ : m ⟶ n) :
    S.transitionPushforwardModulesCompIso O φ (𝟙 n) ≪≫
        S.transitionPushforwardModulesCongr O (Category.comp_id φ) =
      Functor.isoWhiskerRight (S.transitionPushforwardModulesIdIso O n)
          (S.transitionPushforwardModules O φ) ≪≫ Functor.leftUnitor _ :=
  Iso.ext (NatTrans.ext (funext fun M =>
    (S.transitionPushforwardModulesCompIso_comp_id_app O φ M).trans (Category.comp_id _).symm))

/-- The left unit law for the comparison of direct images of sheaves of modules. -/
theorem transitionPushforwardModulesCompIso_id_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    S.transitionPushforwardModulesCompIso O (𝟙 m) φ ≪≫
        S.transitionPushforwardModulesCongr O (Category.id_comp φ) =
      Functor.isoWhiskerLeft (S.transitionPushforwardModules O φ)
          (S.transitionPushforwardModulesIdIso O m) ≪≫ Functor.rightUnitor _ :=
  Iso.ext (NatTrans.ext (funext fun M =>
    (S.transitionPushforwardModulesCompIso_id_comp_app O φ M).trans (Category.comp_id _).symm))

/-! ### The unit of the pullbacks of sheaves of modules -/

/-- The transpose of the identification `f_𝟙^* ≅ 𝟭` of sheaves of modules is the inverse of the
identification `(f_𝟙)_* ≅ 𝟭`. -/
theorem homEquiv_transitionPullbackModulesIdIso_hom_app (n : SimplexCategory)
    (X : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.transitionPullbackAdj O (𝟙 n)).homEquiv X X
        ((S.transitionPullbackModulesIdIso O n).hom.app X) =
      (S.transitionPushforwardModulesIdIso O n).inv.app X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((S.transitionRingedToposHom O (𝟙 n)).pullbackAdjPushforwardModules.ofNatIsoRight
      ((S.transitionRingedToposHom O (𝟙 n)).pushforwardModulesIsoId (S.pushforwardId n).symm
        (S.transitionFSharpId O n)).symm)
    Adjunction.id X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  change ((S.transitionPullbackAdj O (𝟙 n)).ofNatIsoRight
    (S.transitionRingedToposHom O (𝟙 n)).toModulesPushforwardIso).homEquiv X X
      ((S.transitionPullbackModulesIdIso O n).hom.app X) ≫ _ = _ at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Iso.symm_hom, Category.assoc] at h
  rw [transitionPushforwardModulesIdIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    ← Category.id_comp (((S.transitionRingedToposHom O (𝟙 n)).pushforwardModulesIsoId
      (S.pushforwardId n).symm (S.transitionFSharpId O n)).hom.app X), ← h]
  simp

/-- **The identification `f_𝟙^* ≅ 𝟭` of the pullback of sheaves of modules is the left-adjoint
transport of the identification `(f_𝟙)_* ≅ 𝟭` of the direct image.** -/
theorem transitionPullbackModulesIdIso_eq_leftAdjointIdIso (n : SimplexCategory) :
    S.transitionPullbackModulesIdIso O n =
      Adjunction.leftAdjointIdIso (S.transitionPullbackAdj O (𝟙 n))
        (S.transitionPushforwardModulesIdIso O n) := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  apply ((S.transitionPullbackAdj O (𝟙 n)).homEquiv X X).injective
  rw [S.homEquiv_transitionPullbackModulesIdIso_hom_app,
    Adjunction.homEquiv_leftAdjointIdIso_hom_app]

/-- The compositor of pullbacks of sheaves of modules, transported along an equality of simplex
maps, is the left-adjoint transport of the corresponding comparison of direct images. -/
private theorem transitionPullbackModulesCompIso_symm_trans_congr {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) {χ : l ⟶ n} (h : ψ ≫ φ = χ) :
    (S.transitionPullbackModulesCompIso O ψ φ).symm ≪≫ S.transitionPullbackModulesCongr O h =
      Adjunction.leftAdjointCompIso (S.transitionPullbackAdj O ψ) (S.transitionPullbackAdj O φ)
        (S.transitionPullbackAdj O χ)
        (S.transitionPushforwardModulesCompIso O ψ φ ≪≫
          S.transitionPushforwardModulesCongr O h) := by
  rw [S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso, Iso.symm_symm_eq,
    show S.transitionPullbackModulesCongr O h =
      eqToIso (congrArg (fun α => (S.transitionRingedToposHom O α).toModulesHom.pullbackModules)
        h) from rfl,
    Adjunction.leftAdjointCompIso_congr (fun α => S.transitionPullbackAdj O α) _ _ h]

/-- The right unit law for the compositor of pullbacks of sheaves of modules. -/
theorem transitionPullbackModulesCompIso_comp_id {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionPullbackModulesCompIso O φ (𝟙 n)).symm ≪≫
        S.transitionPullbackModulesCongr O (Category.comp_id φ) =
      Functor.isoWhiskerLeft (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
          (S.transitionPullbackModulesIdIso O n) ≪≫ Functor.rightUnitor _ := by
  rw [S.transitionPullbackModulesCompIso_symm_trans_congr O φ (𝟙 n) (Category.comp_id φ),
    S.transitionPullbackModulesIdIso_eq_leftAdjointIdIso]
  exact Adjunction.leftAdjointCompIso_comp_id _ _ _ (S.transitionPushforwardModulesIdIso O n)
    (S.transitionPushforwardModulesCompIso_comp_id O φ)

/-- The left unit law for the compositor of pullbacks of sheaves of modules. -/
theorem transitionPullbackModulesCompIso_id_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionPullbackModulesCompIso O (𝟙 m) φ).symm ≪≫
        S.transitionPullbackModulesCongr O (Category.id_comp φ) =
      Functor.isoWhiskerRight (S.transitionPullbackModulesIdIso O m)
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ≪≫
        Functor.leftUnitor _ := by
  rw [S.transitionPullbackModulesCompIso_symm_trans_congr O (𝟙 m) φ (Category.id_comp φ),
    S.transitionPullbackModulesIdIso_eq_leftAdjointIdIso]
  exact Adjunction.leftAdjointCompIso_id_comp _ _ _ (S.transitionPushforwardModulesIdIso O m)
    (S.transitionPushforwardModulesCompIso_id_comp O φ)

/-! ### The family -/

/-- The cocycle law for the compositor of pullbacks of sheaves of modules, in the form of the
field of `CategoryTheory.SimplicialPseudoFamily`. -/
theorem pasteModules_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : (S.componentRingedTopos O k).Modules) :
    (S.pasteModules O ψ φ ((S.componentModulePullback O χ).obj X)).hom ≫
        (S.pasteModules O χ (ψ ≫ φ) X).hom =
      (S.componentModulePullback O φ).map (S.pasteModules O χ ψ X).hom ≫
        (S.pasteModules O (χ ≫ ψ) φ X).hom ≫
          eqToHom (congrArg (fun t => (S.componentModulePullback O t).obj X)
            (Category.assoc χ ψ φ)) := by
  have h := S.transitionPullbackModulesCompIso_inv_assoc_congr_app O χ ψ φ X
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToHom_app] at h
  exact h.symm

/-- The right unit law for the compositor of pullbacks of sheaves of modules, read at a
module. -/
theorem pasteModules_comp_id {m n : SimplexCategory} (φ : m ⟶ n)
    (X : (S.componentRingedTopos O m).Modules) :
    (S.pasteModules O φ (𝟙 n) X).hom ≫
        eqToHom (congrArg (fun k => (S.componentModulePullback O k).obj X) (Category.comp_id φ)) =
      (S.transitionPullbackModulesIdIso O n).hom.app ((S.componentModulePullback O φ).obj X) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (S.transitionPullbackModulesCompIso_comp_id O φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToHom_app,
    Functor.rightUnitor_hom_app] at h
  exact h

/-- The left unit law for the compositor of pullbacks of sheaves of modules, read at a
module. -/
theorem pasteModules_id_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (X : (S.componentRingedTopos O m).Modules) :
    (S.pasteModules O (𝟙 m) φ X).hom ≫
        eqToHom (congrArg (fun k => (S.componentModulePullback O k).obj X) (Category.id_comp φ)) =
      (S.componentModulePullback O φ).map ((S.transitionPullbackModulesIdIso O m).hom.app X) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (S.transitionPullbackModulesCompIso_id_comp O φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToHom_app,
    Functor.leftUnitor_hom_app] at h
  exact h

/-- **The pseudofunctorial family of modules on the components.** In degree `n` it is the
category of modules over the component structure sheaf `O_n`, the functor attached to a simplex
map is the pullback of sheaves of modules along the transition morphism of ringed topoi, and the
compositor and unit are the canonical ones. -/
def modulePseudoFamily : SimplicialPseudoFamily.{u, u + 1} where
  obj n := (S.componentRingedTopos O n).Modules
  map φ := S.componentModulePullback O φ
  paste ψ φ X := S.pasteModules O ψ φ X
  paste_naturality ψ φ _ _ f := (S.transitionPullbackModulesCompIso O ψ φ).inv.naturality f
  unit n X := (S.transitionPullbackModulesIdIso O n).app X
  unit_naturality n _ _ f := (S.transitionPullbackModulesIdIso O n).hom.naturality f
  paste_assoc χ ψ φ X := S.pasteModules_assoc O χ ψ φ X
  paste_comp_id φ X := S.pasteModules_comp_id O φ X
  paste_id_comp φ X := S.pasteModules_id_comp O φ X

/-- The first identification of the cocycle condition of the family is that of a pair of
modules. -/
theorem modulePseudoFamily_glueLeft (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.modulePseudoFamily O).glueLeft F = S.glueModulesLeft O F := rfl

/-- The middle identification of the cocycle condition of the family is that of a pair of
modules. -/
theorem modulePseudoFamily_glueMiddle (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.modulePseudoFamily O).glueMiddle F = S.glueModulesMiddle O F := rfl

/-- The last identification of the cocycle condition of the family is that of a pair of
modules. -/
theorem modulePseudoFamily_glueRight (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.modulePseudoFamily O).glueRight F = S.glueModulesRight O F := rfl

/-- The cocycle condition of a pair of modules is the cocycle condition of the family. -/
theorem isCocycle_of_isModuleCocycle (F : (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F)
    (h : S.IsModuleCocycle O F α) : (S.modulePseudoFamily O).IsCocycle F α := by
  unfold IsModuleCocycle at h
  unfold SimplicialPseudoFamily.IsCocycle
  rw [S.modulePseudoFamily_glueLeft O, S.modulePseudoFamily_glueMiddle O,
    S.modulePseudoFamily_glueRight O]
  exact h

/-- **The cartesian system of a cartesian module**: its restrictions to the components, with its
transitions. -/
def cartesianModuleSystem (M : S.CartesianModuleSheaf O) :
    (S.modulePseudoFamily O).CartesianSystem where
  obj n := S.componentModule O M.obj n
  trans φ := S.componentTransitionIso O M φ
  trans_id n := S.fiberTransitionModules_id O n M.obj
  trans_comp ψ φ := S.pasteModules_comp_componentTransition O M.obj ψ φ

end CategoryTheory.SimplicialSiteSituation

end
