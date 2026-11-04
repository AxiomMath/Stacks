module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarLowerShriek

/-!
# Functoriality of the simplex-coefficient resolution in the module

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. The
simplex-coefficient resolution `n ↦ B_n(M)` of a sheaf of `O`-modules `M` has, over an object of
degree `k`, the sections `⨁_{α : [n] ⟶ [k]} M(U)`. A morphism `f : M ⟶ M'` acts on each summand,
which makes `M ↦ B_n(M)` a functor, compatibly with everything the resolution is built from: the
relabelling face maps, the augmentation summing the summands, the summand inclusions over a
component, and the canonical map `g_{n!}(M|_n) ⟶ B_n(M)` of Stacks 0D72.

## Main definitions

* `PresheafOfModules.copowerObjMap`: the morphism of copowers induced by a morphism of presheaves
  of modules.
* `CategoryTheory.SimplicialSiteSituation.moduleBarSheafMap`: `B_n(f) : B_n(M) ⟶ B_n(M')`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarSheafFunctor`: `M ↦ B_n(M)` as a functor.
* `CategoryTheory.SimplicialSiteSituation.moduleBarSimplicialMap`: `B_•(f)` as a morphism of
  simplicial sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.moduleBarLowerShriekNatTrans`: the canonical map
  `g_{n!}(M|_n) ⟶ B_n(M)`, natural in `M`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleBarComplex_d_naturality`: the differentials of the
  resolution are natural in `M`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarAugmentation_naturality`: so is the
  augmentation.

## References

* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Tag 0D7D](https://stacks.math.columbia.edu/tag/0D7D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor AlgebraicGeometry
open scoped Simplicial

universe v v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The copower is functorial in the module**: a morphism of presheaves of modules acts on every
summand. -/
def copowerObjMap {M M' : PresheafOfModules.{v} R} (φ : M ⟶ M') (E : Cᵒᵖ ⥤ Type v) :
    copowerObj M E ⟶ copowerObj M' E where
  app X := ModuleCat.copowerDesc fun e => φ.app X ≫ ModuleCat.copowerMk e
  naturality {X Y} f := by
    refine ModuleCat.copower_hom_ext fun e => ?_
    rw [← Category.assoc, copowerMk_comp_copowerObj_map, Category.assoc, ← Functor.map_comp,
      ModuleCat.copowerMk_comp_desc, Functor.map_comp, ← Category.assoc, φ.naturality,
      ← Category.assoc, ModuleCat.copowerMk_comp_desc, Category.assoc, Category.assoc,
      copowerMk_comp_copowerObj_map]

/-- The morphism of copowers places the image of a section in the same summand. -/
@[reassoc (attr := simp)]
lemma copowerMk_comp_copowerObjMap_app {M M' : PresheafOfModules.{v} R} (φ : M ⟶ M')
    (E : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) (e : E.obj X) :
    ModuleCat.copowerMk e ≫ (copowerObjMap φ E).app X = φ.app X ≫ ModuleCat.copowerMk e :=
  ModuleCat.copowerMk_comp_desc _ e

/-- Morphisms out of a copower agree when they agree on every summand. -/
private theorem copowerObj_hom_ext {M N : PresheafOfModules.{v} R} {E : Cᵒᵖ ⥤ Type v}
    {f g : copowerObj M E ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (e : E.obj X),
      ModuleCat.copowerMk e ≫ f.app X = ModuleCat.copowerMk e ≫ g.app X) :
    f = g := by
  ext X : 1
  exact ModuleCat.copower_hom_ext (h X)

/-- The morphism of copowers induced by the identity is the identity. -/
@[simp]
lemma copowerObjMap_id (M : PresheafOfModules.{v} R) (E : Cᵒᵖ ⥤ Type v) :
    copowerObjMap (𝟙 M) E = 𝟙 _ := by
  refine copowerObj_hom_ext fun X e => ?_
  simp

/-- The morphism of copowers induced by a composite is the composite of the induced morphisms. -/
@[simp]
lemma copowerObjMap_comp {M M' M'' : PresheafOfModules.{v} R} (φ : M ⟶ M') (ψ : M' ⟶ M'')
    (E : Cᵒᵖ ⥤ Type v) :
    copowerObjMap (φ ≫ ψ) E = copowerObjMap φ E ≫ copowerObjMap ψ E := by
  refine copowerObj_hom_ext fun X e => ?_
  simp

/-- Acting on the summands commutes with relabelling them. -/
lemma copowerObjMap_comp_copowerMap {M M' : PresheafOfModules.{v} R} (φ : M ⟶ M')
    {E E' : Cᵒᵖ ⥤ Type v} (g : E ⟶ E') :
    copowerObjMap φ E ≫ copowerMap M' g = copowerMap M g ≫ copowerObjMap φ E' := by
  refine copowerObj_hom_ext fun X e => ?_
  simp [copowerMk_comp_copowerMap_app, copowerMk_comp_copowerMap_app_assoc]

/-- Acting on the summands commutes with summing them. -/
lemma copowerObjMap_comp_copowerSum {M M' : PresheafOfModules.{v} R} (φ : M ⟶ M')
    (E : Cᵒᵖ ⥤ Type v) : copowerObjMap φ E ≫ copowerSum M' E = copowerSum M E ≫ φ := by
  refine copowerObj_hom_ext fun X e => ?_
  simp

end PresheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] SimplicialSite.totalPseudofunctor
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete totalCategory Quiver.Hom.toLoc
  CoGrothendieck.category CoGrothendieck.categoryStruct CoGrothendieck.ι Cat.str
  Grothendieck.ι Grothendieck.instCategory uliftFunctor componentFunctor component
  simplexIndices totalSimplexDegree PresheafOfModules.presheaf

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}

/-- `B_n(f) : B_n(M) ⟶ B_n(M')`, acting on every summand. -/
def moduleBarSheafMap {M M' : SheafOfModules.{u} O} (f : M ⟶ M') (n : SimplexCategory) :
    moduleBarSheaf M n ⟶ moduleBarSheaf M' n :=
  ⟨PresheafOfModules.copowerObjMap f.val (simplexIndices.{u, u} S n)⟩

variable (O) in
/-- **The degree-`n` term `M ↦ B_n(M)` of the simplex-coefficient resolution, as a functor.** -/
def moduleBarSheafFunctor (n : SimplexCategory) : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O where
  obj M := moduleBarSheaf M n
  map f := moduleBarSheafMap f n
  map_id M := (SheafOfModules.forget O).map_injective (PresheafOfModules.copowerObjMap_id M.val _)
  map_comp f g :=
    (SheafOfModules.forget O).map_injective (PresheafOfModules.copowerObjMap_comp f.val g.val _)

/-- `B_•(f)`, as a morphism of simplicial sheaves of modules: acting on the summands commutes with
relabelling them. -/
def moduleBarSimplicialMap {M M' : SheafOfModules.{u} O} (f : M ⟶ M') :
    moduleBarSimplicial M ⟶ moduleBarSimplicial M' where
  app n := moduleBarSheafMap f n.unop
  naturality _ _ _ :=
    (SheafOfModules.forget O).map_injective
      (PresheafOfModules.copowerObjMap_comp_copowerMap f.val _).symm

/-- **The differentials of the simplex-coefficient resolution are natural in the module.** -/
theorem moduleBarComplex_d_naturality {M M' : SheafOfModules.{u} O} (f : M ⟶ M') (i j : ℕ) :
    (moduleBarComplex M).d i j ≫ moduleBarSheafMap f ⦋j⦌ =
      moduleBarSheafMap f ⦋i⦌ ≫ (moduleBarComplex M').d i j :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).map (moduleBarSimplicialMap f)).comm i j).symm

/-- **The augmentation of the simplex-coefficient resolution is natural in the module.** -/
theorem moduleBarAugmentation_naturality {M M' : SheafOfModules.{u} O} (f : M ⟶ M')
    (n : SimplexCategory) :
    moduleBarSheafMap f n ≫ moduleBarAugmentation M' n = moduleBarAugmentation M n ≫ f :=
  (SheafOfModules.forget O).map_injective (PresheafOfModules.copowerObjMap_comp_copowerSum f.val _)

/-- **The summand inclusions over a component are natural in the module.** -/
theorem moduleBarSummand_naturality {M M' : SheafOfModules.{u} O} (f : M ⟶ M')
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (componentModuleRestriction S O m).map f ≫ moduleBarSummand M' φ =
      moduleBarSummand M φ ≫ (componentModuleRestriction S O m).map (moduleBarSheafMap f n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact (congrArg (fun t => t.hom x) (PresheafOfModules.copowerMk_comp_copowerObjMap_app f.val
    (simplexIndices.{u, u} S n) _ (barLabel φ U.unop))).symm

section LowerShriek

variable (P : Sheaf S.totalTopology CommRingCat.{u})

/-- **The canonical map `g_{n!}(M|_n) ⟶ B_n(M)` of Stacks 0D72 is natural in `M`.** -/
theorem moduleBarLowerShriekMap_naturality {M M' : SheafOfModules.{u} (S.totalRingSheaf P)}
    (f : M ⟶ M') (n : SimplexCategory) :
    (S.componentModuleLowerShriek (S.totalRingSheaf P) n).map
        ((S.componentModuleRestriction (S.totalRingSheaf P) n).map f) ≫
      moduleBarLowerShriekMap P M' n =
    moduleBarLowerShriekMap P M n ≫ moduleBarSheafMap f n := by
  refine Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _).symm ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _)
  exact congrArg _ (moduleBarSummand_naturality f (𝟙 n))

/-- The canonical map `g_{n!}(M|_n) ⟶ B_n(M)`, as a natural transformation. -/
def moduleBarLowerShriekNatTrans (n : SimplexCategory) :
    S.componentModuleRestriction (S.totalRingSheaf P) n ⋙
        S.componentModuleLowerShriek (S.totalRingSheaf P) n ⟶
      moduleBarSheafFunctor (S.totalRingSheaf P) n where
  app M := moduleBarLowerShriekMap P M n
  naturality _ _ f := moduleBarLowerShriekMap_naturality P f n

end LowerShriek

end CategoryTheory.SimplicialSiteSituation

end
