module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImagePushforwardCocontinuousAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModulePushforwardExchange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek

/-!
# `g_!` on sheaves of modules for the flat-fppf site, and its localization at a flat object

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of topoi of
Stacks 0788 (2). Its inverse image `g^{-1} = g^*` on sheaves of modules is restriction along the
inclusion of the flat objects, and its left adjoint is `g_!` (Stacks 0789 (2)). This file

* records `g^{-1}` with sections in the universe of the structure sheaf, its left adjoint `g_!`
  and the identity `g^{-1}g_! = id`;
* records the inverse image `f^{-1}` along a 1-morphism `f` of algebraic stacks and along its
  restriction `f'` to the flat sites as restriction of sheaves of modules, left adjoint to the
  direct images of Stacks 07AT;
* deduces from Stacks 07AT (2) on sheaves of modules
  (`AlgebraicGeometry.Stack.FlatFppf.lowerShriekCompInverseImageIso`) the identity
  `f^{-1}g_! = g'_!(f')^{-1}` for every flat 1-morphism, in particular for the 1-morphism
  `V ⟶ 𝒳` named by a flat object of `𝒳` lying over `V`.

## References

* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

attribute [local instance] instHasPointwiseRightKanExtensionSmall

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LowerShriek

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The inverse image `g^{-1} = g^*` of sheaves of modules along the flat-fppf morphism of
topoi** (Stacks 0788 (2)), with sections in the universe of the structure sheaf: restriction
along the inclusion of the flat objects. -/
abbrev moduleInverseImageU :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) :=
  inverseImage.{u} (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳)

/-- `g^{-1}` has a left adjoint: restriction along a continuous functor out of an essentially
small site does. -/
instance isRightAdjoint_moduleInverseImageU : (moduleInverseImageU B S hS 𝒳).IsRightAdjoint :=
  Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules _ _ _ _

/-- **The functor `g_!` on sheaves of modules for the flat-fppf site** (Stacks 0789 (2)), with
sections in the universe of the structure sheaf: the left adjoint of `g^{-1}`. -/
abbrev moduleLowerShriekU :
    _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) :=
  (moduleInverseImageU B S hS 𝒳).leftAdjoint

/-- **The adjunction `g_! ⊣ g^{-1}`** on sheaves of modules for the flat-fppf site. -/
abbrev moduleLowerShriekAdjunctionU : moduleLowerShriekU B S hS 𝒳 ⊣ moduleInverseImageU B S hS 𝒳 :=
  Adjunction.ofIsRightAdjoint _

/-- **Stacks 0789 (2), `g^{-1}g_! = id`**: the unit of `g_! ⊣ g^{-1}` is an isomorphism, the
inclusion of the flat objects being fully faithful. -/
theorem isIso_moduleLowerShriekAdjunctionU_unit :
    IsIso (moduleLowerShriekAdjunctionU B S hS 𝒳).unit :=
  isIso_unit_of_adjunction_inverseImage _ _ (moduleLowerShriekAdjunctionU B S hS 𝒳)

end LowerShriek

section Morphism

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

attribute [local instance] instIsContinuousHomFunctorFppf instIsCocontinuousHomFunctorFppf

/-- **The inverse image `f^{-1}` of sheaves of modules along a 1-morphism of algebraic stacks**,
for the fppf sites (Stacks 06WE): restriction along `f`, the structure sheaf of the source being
the restriction of that of the target (Stacks 06TW). -/
abbrev moduleRestrictionAlong :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) :=
  _root_.SheafOfModules.pushforward.{u} (F := f.hom.hom.toFunctor)
    (eqToHom (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f).symm)

/-- **`f^{-1} ⊣ f_*`** on sheaves of modules for a 1-morphism of algebraic stacks. -/
def moduleRestrictionAlongAdjunction :
    moduleRestrictionAlong B S hS f ⊣
      pushforwardCocontinuous.{u} f.hom.hom.toFunctor
        (structureMapHomFunctor B S hS B.topology le_rfl f) :=
  pushforwardPushforwardCocontinuousInverseImageRingAdjunction f.hom.hom.toFunctor _
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f)

variable (hf : AlgebraicStacks.IsFlat B S hS f)

/-- Continuity of the site functor of Stacks 07AT for the flat-fppf topologies. -/
local instance instIsContinuousPrimedSiteFunctor :
    (primedSiteFunctor B S hS f hf).IsContinuous (topology B S hS 𝒳) (topology B S hS 𝒴) :=
  siteFunctor_isContinuous B S hS f hf

/-- Cocontinuity of the site functor of Stacks 07AT for the flat-fppf topologies. -/
local instance instIsCocontinuousPrimedSiteFunctor :
    (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳) (topology B S hS 𝒴) :=
  siteFunctor_isCocontinuous B S hS f hf

/-- The structure sheaf of the flat-fppf site of `𝒳` is the restriction along the site functor
`f'` of Stacks 07AT of that of `𝒴`: both are restrictions of the structure sheaf of the base. -/
theorem inverseImageRing_primedSiteFunctor :
    inverseImageRing (topology B S hS 𝒳) (topology B S hS 𝒴) (primedSiteFunctor B S hS f hf)
        (subsiteRingStructureSheaf B S hS 𝒴) = subsiteRingStructureSheaf B S hS 𝒳 :=
  congrArg ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
      (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)).obj
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f)

/-- **The inverse image `(f')^{-1}` of sheaves of modules along the site functor of Stacks 07AT**
between the flat-fppf sites: restriction along `f'`. -/
abbrev restrictedModuleRestrictionAlong :
    _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) :=
  _root_.SheafOfModules.pushforward.{u} (F := primedSiteFunctor B S hS f hf)
    (eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf).symm)

/-- The structure map `(f')^♯` which the square of Stacks 07AT (2) forces is the transpose of the
identification of the structure sheaves of the flat-fppf sites. -/
theorem structureMapSquare_eq_homEquiv :
    haveI : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳)
        (topology B S hS 𝒴) :=
      siteFunctor_isCocontinuous B S hS f hf
    structureMapSquare (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
        (structureMapHomFunctor B S hS B.topology le_rfl f)
        (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
          (flatObject_map B S hS f hf)) =
      ((primedSiteFunctor B S hS f hf).sheafAdjunctionCocontinuous RingCat.{u}
        (topology B S hS 𝒳) (topology B S hS 𝒴)).homEquiv _ _
        (eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf)) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V' ↦ ?_))
  refine ran_hom_ext (primedSiteFunctor B S hS f hf).op _ (fun j ↦ ?_)
  have e1 := homEquiv_eqToHom_app_ranπ (primedSiteFunctor B S hS f hf)
    (subsiteRingStructureSheaf B S hS 𝒴) (inverseImageRing_primedSiteFunctor B S hS f hf) V' j
  have hsq := SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor
    (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
  have e2 := structureBaseChange_π (J' := topology B S hS 𝒳)
    (J := associatedTopology B S hS 𝒳.val.val.p B.topology)
    (OC := ambientRingStructureSheaf B S hS 𝒳) hsq V' j
  have e3 := homEquiv_eqToHom_app_ranπ f.hom.hom.toFunctor (ambientRingStructureSheaf B S hS 𝒴)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f)
    (((objectProperty B S hS 𝒴).ι).op.obj V') (squareIndex hsq j)
  refine Eq.trans ?_ e1.symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) e2).trans ?_
  refine e3.trans ?_
  simp only [squareIndex, StructuredArrow.mk_hom_eq_self, Functor.map_comp]
  have h0 : (Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.app j.right = 𝟙 _ := rfl
  have h0' : (ambientRingStructureSheaf B S hS 𝒴).obj.map
      ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.app j.right) = 𝟙 _ :=
    (congrArg (ambientRingStructureSheaf B S hS 𝒴).obj.map h0).trans
      ((ambientRingStructureSheaf B S hS 𝒴).obj.map_id _)
  refine (congrArg (· ≫ _) ((congrArg (_ ≫ ·) h0').trans (Category.comp_id _))).trans ?_
  rw [show eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf) =
      ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u} (topology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)).map
        (eqToHom (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f))
      from (eqToHom_map ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
        (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology))
        (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f)).symm]
  rfl

/-- **`(f')^{-1} ⊣ f'_*`** on sheaves of modules for the site functor of Stacks 07AT. -/
def restrictedModuleRestrictionAlongAdjunction :
    restrictedModuleRestrictionAlong B S hS f hf ⊣ restrictedModulePushforwardU B S hS f hf := by
  haveI : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳) (topology B S hS 𝒴) :=
    siteFunctor_isCocontinuous B S hS f hf
  rw [restrictedModulePushforwardU, structureMapSquare_eq_homEquiv]
  exact pushforwardPushforwardCocontinuousInverseImageRingAdjunction (primedSiteFunctor B S hS f
      hf) _
    (inverseImageRing_primedSiteFunctor B S hS f hf)

/-- **Stacks 07AT (2) on sheaves of modules, the identity `f^{-1}g_! = g'_!(f')^{-1}`**, for a
flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, `f^{-1}` and `(f')^{-1}` being restriction along
`f` and along its restriction `f'` to the flat-fppf sites. -/
def moduleLowerShriekUCompRestrictionAlongIso :
    moduleLowerShriekU B S hS 𝒴 ⋙ moduleRestrictionAlong B S hS f ≅
      restrictedModuleRestrictionAlong B S hS f hf ⋙ moduleLowerShriekU B S hS 𝒳 :=
  lowerShriekCompInverseImageIso B S hS f hf (moduleLowerShriekAdjunctionU B S hS 𝒴)
    (moduleLowerShriekAdjunctionU B S hS 𝒳) (moduleRestrictionAlongAdjunction B S hS f)
    (restrictedModuleRestrictionAlongAdjunction B S hS f hf)

end Morphism

end FlatFppf

end AlgebraicGeometry.Stack

end
