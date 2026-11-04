module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Ringed

/-!
# Modules on the ringed site of a semi-representable object

Let `X` be a ringed site and `K` a semi-representable object of its underlying site. Modules over
the structure sheaf `O_K` on the localization `C / K` are the same thing as families of modules,
one over each localized ringed site `X / U i`: the equivalence restricts a module and its linear
maps to each component, and its inverse assembles a family into a single module on the disjoint
union.

The structure-sheaf comparison map on a component is sectionwise the identity, because `O_K` and
the structure sheaf of `X / U i` are both the structure sheaf of `X` read at the same objects.
The restriction functor therefore transports the full module structure and all module-linear
restriction maps, with nothing to compare.

The primed declarations are the same constructions for a ringed site `X : RingedSite.{u, v, r}`
in arbitrary universes, over `AlgebraicGeometry.RingedSite.localization'`.

## Main definitions

* `AlgebraicGeometry.RingedSite.componentStructureMap`: the structure-sheaf map for restriction
  to one localized component.
* `AlgebraicGeometry.RingedSite.componentwiseModuleRestriction`: restriction of a module and its
  linear maps to every component.
* `AlgebraicGeometry.RingedSite.assembledModuleMap`,
  `AlgebraicGeometry.RingedSite.assembledModulePresheaf`,
  `AlgebraicGeometry.RingedSite.assembleModuleFamily`: the inverse construction.

## Main results

* `AlgebraicGeometry.RingedSite.moduleSheavesProductEquivalence`: modules on `C / K` are
  componentwise modules. The source states an equality of categories; here it is an equivalence
  whose forward functor is `AlgebraicGeometry.RingedSite.componentwiseModuleRestriction`.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentable

namespace AlgebraicGeometry.RingedSite

universe u v w

universe r t

attribute [local implicit_reducible] AlgebraicGeometry.RingedSite.localization
  CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor
  CategoryTheory.Sigma.desc CategoryTheory.Functor.sheafPushforwardContinuous
  CategoryTheory.sheafCompose

attribute [local implicit_reducible] AlgebraicGeometry.RingedSite.localization'

/-- The inclusion of a localized component into the disjoint union is continuous. -/
local instance componentIncl_isContinuous (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).IsContinuous
      (X.J.over (K.obj i)) (componentwiseTopology X.J K) :=
  incl_isContinuous X.J K i

/-- The inclusion of a localized component into the disjoint union is continuous. -/
local instance componentIncl_isContinuous' (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).IsContinuous
      (X.J.over (K.obj i)) (componentwiseTopology X.J K) :=
  incl_isContinuous X.J K i

/-- The structure-sheaf map for restriction to one localized component: sectionwise the
identity. -/
noncomputable def componentStructureMap (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O ⟶
      ((CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).sheafPushforwardContinuous
        RingCat.{u} (X.J.over (K.obj i)) (componentwiseTopology X.J K)).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O) :=
  ⟨{ app := fun _ => 𝟙 _, naturality := by intros; rfl }⟩

/-- The structure-sheaf map for restriction to one localized component: sectionwise the
identity. -/
noncomputable def componentStructureMap' (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) (i : K.I) :
    Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O ⟶
      ((CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i).sheafPushforwardContinuous
        RingCat.{r} (X.J.over (K.obj i)) (componentwiseTopology X.J K)).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O) :=
  ⟨{ app := fun _ => 𝟙 _, naturality := by intros; rfl }⟩

/-- Restriction of a module sheaf and its linear maps to every component. -/
noncomputable def componentwiseModuleRestriction
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O) ⥤
      ((i : K.I) → SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :=
  Functor.pi' (fun i =>
    SheafOfModules.pushforward
      (F := CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i)
      (J := X.J.over (K.obj i))
      (K := componentwiseTopology X.J K)
      (componentStructureMap X K i))

/-- Restriction of a module sheaf and its linear maps to every component. -/
noncomputable def componentwiseModuleRestriction'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C) :
    SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O) ⥤
      ((i : K.I) → SheafOfModules.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :=
  Functor.pi' (fun i =>
    SheafOfModules.pushforward
      (F := CategoryTheory.Sigma.incl (C := fun j : K.I => Over (K.obj j)) i)
      (J := X.J.over (K.obj i))
      (K := componentwiseTopology X.J K)
      (componentStructureMap' X K i))

/-- The structure-sheaf restriction map on a component agrees with its local map. -/
lemma componentRingSheafMap (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{w} X.C) (i : K.I) (A B : Over (K.obj i))
    (g : B ⟶ A) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O).obj.map
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun j : K.I => Over (K.obj j)) g)) =
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O).obj.map
        (Quiver.Hom.op g) := by ext z; rfl

/-- The structure-sheaf restriction map on a component agrees with its local map. -/
lemma componentRingSheafMap' (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) (i : K.I) (A B : Over (K.obj i))
    (g : B ⟶ A) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O).obj.map
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun j : K.I => Over (K.obj j)) g)) =
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O).obj.map
        (Quiver.Hom.op g) := by ext z; rfl

/-- The restriction map for a family of modules assembled over the disjoint union. -/
noncomputable def assembledModuleMap
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    {U V : (X.localization K).Cᵒᵖ} (f : U ⟶ V) :
    (G U.unop.1).val.obj (Opposite.op U.unop.2) ⟶
      (ModuleCat.restrictScalars
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O).obj.map f).hom).obj
        ((G V.unop.1).val.obj (Opposite.op V.unop.2)) := by
  rcases U with ⟨⟨i, A⟩⟩
  rcases V with ⟨⟨j, B⟩⟩
  rcases f with ⟨⟨g⟩⟩
  have hR := componentRingSheafMap X K i A B g
  change (G i).val.obj (Opposite.op A) ⟶
    (ModuleCat.restrictScalars
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O).obj.map
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun j : K.I => Over (K.obj j)) g))).hom).obj
      ((G i).val.obj (Opposite.op B))
  rw [hR]
  exact (G i).val.map (Opposite.op g)

/-- The restriction map for a family of modules assembled over the disjoint union. -/
noncomputable def assembledModuleMap'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    {U V : (X.localization' K).Cᵒᵖ} (f : U ⟶ V) :
    (G U.unop.1).val.obj (Opposite.op U.unop.2) ⟶
      (ModuleCat.restrictScalars
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O).obj.map f).hom).obj
        ((G V.unop.1).val.obj (Opposite.op V.unop.2)) := by
  rcases U with ⟨⟨i, A⟩⟩
  rcases V with ⟨⟨j, B⟩⟩
  rcases f with ⟨⟨g⟩⟩
  have hR := componentRingSheafMap' X K i A B g
  change (G i).val.obj (Opposite.op A) ⟶
    (ModuleCat.restrictScalars
      ((Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O).obj.map
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun j : K.I => Over (K.obj j)) g))).hom).obj
      ((G i).val.obj (Opposite.op B))
  rw [hR]
  exact (G i).val.map (Opposite.op g)

/-- On a component, the assembled restriction map is the original restriction map. -/
lemma assembledModuleMap_sigma
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    (i : K.I) {A B : Over (K.obj i)} (f : B ⟶ A) :
    assembledModuleMap X K G
      (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
        (C := fun j : K.I => Over (K.obj j)) f)) =
      (G i).val.map (Opposite.op f) := by cases f; rfl

/-- On a component, the assembled restriction map is the original restriction map. -/
lemma assembledModuleMap_sigma'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    (i : K.I) {A B : Over (K.obj i)} (f : B ⟶ A) :
    assembledModuleMap' X K G
      (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
        (C := fun j : K.I => Over (K.obj j)) f)) =
      (G i).val.map (Opposite.op f) := by cases f; rfl

/-- The assembled restriction map along a component inclusion is componentwise. -/
lemma assembledModuleMap_incl
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    (i : K.I) {A B : Over (K.obj i)} (f : A ⟶ B) :
    assembledModuleMap X K G
        ((CategoryTheory.Sigma.incl
          (C := fun j : K.I => Over (K.obj j)) i).op.map f.op) =
      (G i).val.map f.op := by
  cases f; rfl

/-- The assembled restriction map along a component inclusion is componentwise. -/
lemma assembledModuleMap_incl'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O))
    (i : K.I) {A B : Over (K.obj i)} (f : A ⟶ B) :
    assembledModuleMap' X K G
        ((CategoryTheory.Sigma.incl
          (C := fun j : K.I => Over (K.obj j)) i).op.map f.op) =
      (G i).val.map f.op := by
  cases f; rfl

/-- The presheaf of `O_K`-modules assembled from a family of modules on the components. -/
noncomputable def assembledModulePresheaf
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O).obj where
  obj U := (G U.unop.1).val.obj (Opposite.op U.unop.2)
  map := assembledModuleMap X K G
  map_id := by
    rintro ⟨⟨i, A⟩⟩
    have h : assembledModuleMap X K G (𝟙 (Opposite.op (⟨i, A⟩ : ComponentOver K))) =
        (G i).val.map (Opposite.op (𝟙 A)) :=
      assembledModuleMap_sigma X K G i (𝟙 A)
    rw [h]
    exact (G i).val.map_id (Opposite.op A)
  map_comp := by
    rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨k, Cc⟩⟩ ⟨⟨f⟩⟩ ⟨⟨g⟩⟩
    have hop :
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk f) :
            Opposite.op (⟨i, A⟩ : ComponentOver K) ⟶
              Opposite.op (⟨i, B⟩ : ComponentOver K)) ≫
          (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk g) :
            Opposite.op (⟨i, B⟩ : ComponentOver K) ⟶
              Opposite.op (⟨i, Cc⟩ : ComponentOver K)) =
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk (g ≫ f)) :
          Opposite.op (⟨i, A⟩ : ComponentOver K) ⟶
            Opposite.op (⟨i, Cc⟩ : ComponentOver K)) := rfl
    have hcomp : assembledModuleMap X K G
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk f) ≫
          Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk g)) =
        (G i).val.map (Opposite.op (g ≫ f)) := by
      cases hop
      exact assembledModuleMap_sigma X K G i (g ≫ f)
    have hf := assembledModuleMap_sigma X K G i f
    have hg := assembledModuleMap_sigma X K G i g
    refine hcomp.trans (((G i).val.map_comp (Opposite.op f) (Opposite.op g)).trans ?_)
    rw [← hf, ← hg]
    rfl

/-- The presheaf of `O_K`-modules assembled from a family of modules on the components. -/
noncomputable def assembledModulePresheaf'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :
    PresheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O).obj where
  obj U := (G U.unop.1).val.obj (Opposite.op U.unop.2)
  map := assembledModuleMap' X K G
  map_id := by
    rintro ⟨⟨i, A⟩⟩
    have h : assembledModuleMap' X K G (𝟙 (Opposite.op (⟨i, A⟩ : ComponentOver K))) =
        (G i).val.map (Opposite.op (𝟙 A)) :=
      assembledModuleMap_sigma' X K G i (𝟙 A)
    rw [h]
    exact (G i).val.map_id (Opposite.op A)
  map_comp := by
    rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨k, Cc⟩⟩ ⟨⟨f⟩⟩ ⟨⟨g⟩⟩
    have hop :
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk f) :
            Opposite.op (⟨i, A⟩ : ComponentOver K) ⟶
              Opposite.op (⟨i, B⟩ : ComponentOver K)) ≫
          (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk g) :
            Opposite.op (⟨i, B⟩ : ComponentOver K) ⟶
              Opposite.op (⟨i, Cc⟩ : ComponentOver K)) =
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk (g ≫ f)) :
          Opposite.op (⟨i, A⟩ : ComponentOver K) ⟶
            Opposite.op (⟨i, Cc⟩ : ComponentOver K)) := rfl
    have hcomp : assembledModuleMap' X K G
        (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk f) ≫
          Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk g)) =
        (G i).val.map (Opposite.op (g ≫ f)) := by
      cases hop
      exact assembledModuleMap_sigma' X K G i (g ≫ f)
    have hf := assembledModuleMap_sigma' X K G i f
    have hg := assembledModuleMap_sigma' X K G i g
    refine hcomp.trans (((G i).val.map_comp (Opposite.op f) (Opposite.op g)).trans ?_)
    rw [← hf, ← hg]
    rfl

/-- The family of modules on the components, assembled into a module on `C / K`. -/
noncomputable def assembleModuleFamily
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O) := by
  refine ⟨assembledModulePresheaf X K G, ?_⟩
  intro E
  refine isSheaf_componentwise (J := X.J) (K := K)
    ((assembledModulePresheaf X K G).presheaf ⋙ coyoneda.obj (Opposite.op E)) ?_
  intro i
  have hcomp :
      ((CategoryTheory.Sigma.incl
        (C := fun j : K.I => Over (K.obj j)) i).op ⋙
        (assembledModulePresheaf X K G).presheaf ⋙ coyoneda.obj (Opposite.op E)) =
      (G i).val.presheaf ⋙ coyoneda.obj (Opposite.op E) := by
    refine CategoryTheory.Functor.ext (fun U => ?_) (fun U V f => ?_)
    · rfl
    · simp only [Functor.comp_obj, Functor.op_obj, Sigma.incl_obj, Functor.flip_obj_obj,
        yoneda_obj_obj, Functor.comp_map, Functor.op_map, Sigma.incl_map, Functor.flip_obj_map,
        yoneda_map_app]
      ext z
      congr 1
  rw [hcomp]
  exact (G i).isSheaf E

/-- The family of modules on the components, assembled into a module on `C / K`. -/
noncomputable def assembleModuleFamily'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) :
    SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O) := by
  refine ⟨assembledModulePresheaf' X K G, ?_⟩
  intro E
  refine isSheaf_componentwise (J := X.J) (K := K)
    ((assembledModulePresheaf' X K G).presheaf ⋙ coyoneda.obj (Opposite.op E)) ?_
  intro i
  have hcomp :
      ((CategoryTheory.Sigma.incl
        (C := fun j : K.I => Over (K.obj j)) i).op ⋙
        (assembledModulePresheaf' X K G).presheaf ⋙ coyoneda.obj (Opposite.op E)) =
      (G i).val.presheaf ⋙ coyoneda.obj (Opposite.op E) := by
    refine CategoryTheory.Functor.ext (fun U => ?_) (fun U V f => ?_)
    · rfl
    · simp only [Functor.comp_obj, Functor.op_obj, Sigma.incl_obj, Functor.flip_obj_obj,
        yoneda_obj_obj, Functor.comp_map, Functor.op_map, Sigma.incl_map, Functor.flip_obj_map,
        yoneda_map_app]
      ext z
      congr 1
  rw [hcomp]
  exact (G i).isSheaf E

/-- Restricting the assembled module family recovers each component. -/
noncomputable def assembleComponentIso
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) (i : K.I) :
    ((componentwiseModuleRestriction X K).obj (assembleModuleFamily X K G)) i ≅ G i := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U => Iso.refl _) ?_
  intro U V f; rfl

/-- Restricting the assembled module family recovers each component. -/
noncomputable def assembleComponentIso'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (G : (i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) (i : K.I) :
    ((componentwiseModuleRestriction' X K).obj (assembleModuleFamily' X K G)) i ≅ G i := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U => Iso.refl _) ?_
  intro U V f; rfl

/-- Assembling the componentwise restrictions recovers the original module sheaf. -/
noncomputable def assembledRestrictionIso
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O)) :
    assembleModuleFamily X K ((componentwiseModuleRestriction X K).obj M) ≅ M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U => Iso.refl _) ?_
  rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨f⟩⟩
  cases f
  rfl

/-- Assembling the componentwise restrictions recovers the original module sheaf. -/
noncomputable def assembledRestrictionIso'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C)
    (M : SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O)) :
    assembleModuleFamily' X K ((componentwiseModuleRestriction' X K).obj M) ≅ M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U => Iso.refl _) ?_
  rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨f⟩⟩
  cases f
  rfl

/-- Modules on the disjoint union of localized ringed sites are componentwise modules, via the
canonical componentwise restriction functor. -/
@[stacks 0D9U "module_product"]
noncomputable def moduleSheavesProductEquivalence
    (X : RingedSite.{u, u, u}) (K : FormalCoproduct.{w} X.C) :
    { e : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O) ≌
      ((i : K.I) → SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) //
      e.functor = componentwiseModuleRestriction X K } := by
  let F := componentwiseModuleRestriction X K
  let G : ((i : K.I) → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization K).O) :=
    { obj := fun Q => assembleModuleFamily X K Q
      map := fun {M N} f =>
        { val :=
            { app := fun U => f U.unop.1 |>.val.app (Opposite.op U.unop.2)
              naturality := by
                rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨h⟩⟩
                change assembledModuleMap X K M
                    (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk h)) ≫ _ =
                  _ ≫ assembledModuleMap X K N
                    (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk h))
                rw [assembledModuleMap_sigma, assembledModuleMap_sigma]
                cases componentRingSheafMap X K i A B h
                exact (f i).val.naturality (Opposite.op h) } }
      map_id := by
        intro M
        apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext
        rintro ⟨⟨i, B⟩⟩
        rfl
      map_comp := by
        intro M N P f g
        apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext
        rintro ⟨⟨i, B⟩⟩
        rfl }
  let η : 𝟭 _ ≅ F ⋙ G :=
    NatIso.ofComponents (fun M => (assembledRestrictionIso X K M).symm) (by
      intro M N f
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
      rfl)
  let ε : G ⋙ F ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M => Pi.isoMk (fun i => assembleComponentIso X K M i)) (by
      intro M N f
      apply Pi.ext
      intro i
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
      rfl)
  refine ⟨⟨F, G, η, ε, ?_⟩, ?_⟩
  · intro M
    apply Pi.ext
    intro i
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
    rfl
  · rfl

/-- Modules on the disjoint union of localized ringed sites are componentwise modules, via the
canonical componentwise restriction functor. -/
@[stacks 0D9U "module_product"]
noncomputable def moduleSheavesProductEquivalence'
    (X : RingedSite.{u, v, r}) (K : FormalCoproduct.{w} X.C) :
    { e : SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O) ≌
      ((i : K.I) → SheafOfModules.{t}
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) //
      e.functor = componentwiseModuleRestriction' X K } := by
  let F := componentwiseModuleRestriction' X K
  let G : ((i : K.I) → SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (K.obj i)).O)) ⥤
      SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization' K).O) :=
    { obj := fun Q => assembleModuleFamily' X K Q
      map := fun {M N} f =>
        { val :=
            { app := fun U => f U.unop.1 |>.val.app (Opposite.op U.unop.2)
              naturality := by
                rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ ⟨⟨h⟩⟩
                change assembledModuleMap' X K M
                    (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk h)) ≫ _ =
                  _ ≫ assembledModuleMap' X K N
                    (Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk h))
                rw [assembledModuleMap_sigma', assembledModuleMap_sigma']
                cases componentRingSheafMap' X K i A B h
                exact (f i).val.naturality (Opposite.op h) } }
      map_id := by
        intro M
        apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext
        rintro ⟨⟨i, B⟩⟩
        rfl
      map_comp := by
        intro M N P f g
        apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext
        rintro ⟨⟨i, B⟩⟩
        rfl }
  let η : 𝟭 _ ≅ F ⋙ G :=
    NatIso.ofComponents (fun M => (assembledRestrictionIso' X K M).symm) (by
      intro M N f
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
      rfl)
  let ε : G ⋙ F ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M => Pi.isoMk (fun i => assembleComponentIso' X K M i)) (by
      intro M N f
      apply Pi.ext
      intro i
      apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
      rfl)
  refine ⟨⟨F, G, η, ε, ?_⟩, ?_⟩
  · intro M
    apply Pi.ext
    intro i
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U
    rfl
  · rfl

end AlgebraicGeometry.RingedSite

end
