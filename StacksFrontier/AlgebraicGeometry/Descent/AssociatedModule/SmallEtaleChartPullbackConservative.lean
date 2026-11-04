module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjRestrict
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact

/-!
# Pullback of sheaves of modules along an étale chart is restriction

Let `U` be an object of the small étale site of a scheme `X`, with étale structure morphism
`p_U : U ⟶ X`.  The pullback of sheaves of modules along the morphism of ringed small étale sites
`ε_{p_U}` of **Stacks 070R** (2) is, up to a canonical isomorphism, the restriction of modules
along post-composition with `p_U`, `AlgebraicGeometry.SmallEtale.objRestrictPost`: both are left
adjoint to the direct image along `ε_{p_U}`.  The adjunction for the restriction is Mathlib's
`SheafOfModules.pushforwardPushforwardAdj`, induced by the adjunction of sites
`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction` (post-composition with `p_U` is left
adjoint to base change along `p_U`), and the two compatibilities of structure sheaves it asks for
are statements about pulling back global functions along the counit and the unit of that
adjunction.

Consequently **the pullbacks along the members of a family of objects covering the final object
are jointly conservative** on sheaves of modules: restriction along post-composition is
restriction to the localization followed by an equivalence
(`AlgebraicGeometry.SmallEtale.objRestrictPostIso`), and restrictions to the localizations at a
covering family are jointly conservative
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`).

## Main results

* `AlgebraicGeometry.SmallEtale.objRestrictPostAdjunction`: restriction along post-composition is
  left adjoint to the direct image along `ε_{p_U}`.
* `AlgebraicGeometry.SmallEtale.pullbackStructureMapRingIsoObjRestrictPost`: the pullback along
  `ε_{p_U}` is restriction along post-composition.
* `AlgebraicGeometry.SmallEtale.isIso_of_isIso_pullback_map_of_coversTop`: joint conservativity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- Base change along the structure morphism of `U` is continuous, at the spelling of the two
topologies the restriction along post-composition is formed with. -/
instance isContinuous_smallEtaleBaseChange_chartStructureHom :
    (smallEtaleBaseChange B U.obj.hom).IsContinuous (topology B X hX)
      (topology B (objScheme B X hX U) (contains_objScheme B X hX U)) :=
  smallEtaleBaseChange_isContinuous B U.obj.hom

/-- **Restriction along post-composition with `p_U` is left adjoint to the direct image along
`ε_{p_U}`.** -/
def objRestrictPostAdjunction :
    objRestrictPost B X hX U ⊣
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B U.obj.hom) :=
  SheafOfModules.pushforwardPushforwardAdj (postcomposeBaseChangeAdjunction B X hX U) (𝟙 _)
    (smallEtaleStructureMapRing B U.obj.hom) (by
      ext W : 2
      simp only [Functor.whiskerRight_app, NatTrans.op_app]
      rfl) (by
      ext W : 2
      simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
      refine (NatTrans.comp_app _ _ W).trans ?_
      simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.op_app,
        Functor.op_obj]
      rw [smallEtaleStructureMapRing_hom_app]
      have hu : ((postcompose B X hX U).map
            ((postcomposeBaseChangeAdjunction B X hX U).unit.app W.unop)).hom.left ≫
          pullback.fst ((postcompose B X hX U).obj W.unop).obj.hom U.obj.hom = 𝟙 _ :=
        congrArg (fun g => g.hom.left)
          ((postcomposeBaseChangeAdjunction B X hX U).left_triangle_components W.unop)
      change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (B.inclusion.map
          (pullback.fst ((postcompose B X hX U).obj W.unop).obj.hom U.obj.hom)).op) ≫
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (B.inclusion.map
          ((postcompose B X hX U).map
            ((postcomposeBaseChangeAdjunction B X hX U).unit.app W.unop)).hom.left).op) = 𝟙 _
      have haux : B.inclusion.map ((postcompose B X hX U).map
            ((postcomposeBaseChangeAdjunction B X hX U).unit.app W.unop)).hom.left ≫
          B.inclusion.map (pullback.fst ((postcompose B X hX U).obj W.unop).obj.hom U.obj.hom) =
            𝟙 _ :=
        (B.inclusion.map_comp _ _).symm.trans ((congrArg B.inclusion.map hu).trans
          (B.inclusion.map_id _))
      have h₃ := (Scheme.Γ.map_comp _ _).symm.trans ((congrArg Scheme.Γ.map
        ((op_comp).symm.trans ((congrArg Quiver.Hom.op haux).trans op_id))).trans
          (Scheme.Γ.map_id _))
      rw [← Functor.map_comp]
      exact (congrArg (forget₂ CommRingCat RingCat).map h₃).trans
        ((forget₂ CommRingCat RingCat).map_id _))

/-- **The pullback of sheaves of modules along `ε_{p_U}` is restriction along post-composition
with `p_U`**: both are left adjoint to the direct image along `ε_{p_U}`. -/
def pullbackStructureMapRingIsoObjRestrictPost :
    SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B U.obj.hom) ≅
      objRestrictPost B X hX U :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureMapRing B U.obj.hom)).leftAdjointUniq
    (objRestrictPostAdjunction B X hX U)

/-- **The pullbacks along the members of a family covering the final object are jointly
conservative.**  If `(U i)` covers the final object of the small étale site of `X` and a morphism
`α` of sheaves of modules becomes an isomorphism after pullback along every `ε_{p_{U i}}`, then `α`
is an isomorphism: the pullback is restriction along post-composition, which is restriction to the
localization at `U i` followed by an equivalence, and restrictions to the localizations at a
covering family are jointly conservative. -/
theorem isIso_of_isIso_pullback_map_of_coversTop {ι : Type*} (V : ι → SmallEtale B X hX)
    (hV : (topology B X hX).CoversTop V) {M N : SheafOfModules.{u} (structureSheaf B X hX)}
    (α : M ⟶ N)
    (h : ∀ i, IsIso ((SheafOfModules.pullback.{u}
      (smallEtaleStructureMapRing B (V i).obj.hom)).map α)) :
    IsIso α := by
  refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hV α fun i => ?_
  have h₁ : IsIso ((objRestrictPost B X hX (V i)).map α) :=
    (NatIso.isIso_map_iff (pullbackStructureMapRingIsoObjRestrictPost B X hX (V i)) α).1 (h i)
  have h₂ : IsIso ((objRestrict B X hX (V i)).map α) :=
    (NatIso.isIso_map_iff (objRestrictPostIso B X hX (V i)) α).2 h₁
  have : IsIso ((objRestrictEquivalence B X hX (V i)).functor.map
      ((SheafOfModules.overFunctor.{u} (structureSheaf B X hX) (V i)).map α)) := h₂
  exact isIso_of_reflects_iso _ (objRestrictEquivalence B X hX (V i)).functor

end AlgebraicGeometry.SmallEtale
