module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackCompCocycleProof

/-!
# Global sections of the pullbacks of Stacks 070R (2), and their composition law

For `a : X ⟶ Y` in a big étale site, `ε_a` is the morphism of ringed sites of **Stacks 070R (2)**
from the small étale site of `X` to the small étale site of `Y`, and `ε_a^*` on sheaves of modules
is `SheafOfModules.pullback (AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing B a)`.  The
map

`Γ(Y, M) ⟶ Γ(X, ε_a^*M)`

on sections over the final objects is `AlgebraicGeometry.SmallEtale.finalPullbackUnit`: the unit
of the adjunction at the final object, carried to the final object of the small étale site of `X`
along the canonical arrow of `AlgebraicGeometry.smallEtaleBaseChange_finalIsTerminal`.  It is
**compatible with composition**: for `a₂ : W ⟶ X` and `a₁ : X ⟶ Y`, pulling a section back along
`a₁` and then along `a₂` and reading the result through the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso` is pulling it back along the
composite.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtaleSectionsFunctor` and
  `AlgebraicGeometry.SmallEtale.smallEtaleSectionsApp`: sections over an object of the small étale
  site, as a functor on sheaves of modules and on a morphism.
* `AlgebraicGeometry.SmallEtale.unitSectionsApp`: the unit of the pullback--direct image
  adjunction along `ε_a`, read on sections over an object.
* `AlgebraicGeometry.SmallEtale.finalPullbackUnit`: **pulling a section over the final object back
  along `a`.**

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePullbackUnit_factoredComp`: **the unit law for the
  composition of the pullbacks of Stacks 070R (2).**
* `AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp`: the same law on sections over the
  final object.
* `AlgebraicGeometry.SmallEtale.finalToBaseChange_comp_eq`: the two routes to the iterated base
  change of the final object agree.
* `AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp`: **`finalPullbackUnit` composes.**

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-! ### Sections over an object of the small étale site -/

/-- Sections over an object of the small étale site, as a functor on sheaves of modules. -/
public abbrev smallEtaleSectionsFunctor {X : B.Scheme}
    (W : SmallEtale B X.obj X.property) :
    SheafOfModules.{u} (structureSheaf B X.obj X.property) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
    (evaluation (SmallEtale B X.obj X.property)ᵒᵖ AddCommGrpCat.{u}).obj (op W)

/-- The sections over an object of the small étale site of a morphism of sheaves of modules. -/
public def smallEtaleSectionsApp {X : B.Scheme}
    {M N : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (φ : M ⟶ N)
    (W : SmallEtale B X.obj X.property) :
    M.val.presheaf.obj (op W) ⟶ N.val.presheaf.obj (op W) :=
  (smallEtaleSectionsFunctor B W).map φ

/-- Sections over an object are functorial in the morphism. -/
public theorem smallEtaleSectionsApp_comp {X : B.Scheme}
    {M N P : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (φ : M ⟶ N) (ψ : N ⟶ P)
    (W : SmallEtale B X.obj X.property) :
    smallEtaleSectionsApp B (φ ≫ ψ) W =
      smallEtaleSectionsApp B φ W ≫ smallEtaleSectionsApp B ψ W :=
  (smallEtaleSectionsFunctor B W).map_comp φ ψ

/-- Sections of a morphism of sheaves of modules commute with the restriction maps. -/
@[reassoc]
public theorem smallEtaleSectionsApp_naturality {X : B.Scheme}
    {M N : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (φ : M ⟶ N)
    {U V : SmallEtale B X.obj X.property} (g : U ⟶ V) :
    M.val.presheaf.map g.op ≫ smallEtaleSectionsApp B φ U =
      smallEtaleSectionsApp B φ V ≫ N.val.presheaf.map g.op :=
  ((PresheafOfModules.toPresheaf _).map φ.val).naturality g.op

/-! ### The unit law for the composition of the pullbacks -/

section UnitComp

variable {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (hab : a ≫ b = ab)

/-- **The unit law for the composition of the pullbacks of Stacks 070R (2).**  The unit along `b`,
followed by the direct image along `b` of the unit along `a` and by the two comparisons of a
composite, is the unit along the composite. -/
public theorem smallEtalePullbackUnit_factoredComp
    (𝓖 : SheafOfModules.{u} (structureSheaf B Z.obj Z.property)) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B b)).unit.app 𝓖 ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b)).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing B a)).unit.app
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj 𝓖)) ≫
        (smallEtalePushforwardRightCompIso B a b ab hab).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj 𝓖)) ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B ab)).map
          ((smallEtalePullbackFactoredCompIso B a b ab hab).hom.app 𝓖) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B ab)).unit.app 𝓖 := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B b)).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B a))).ofNatIsoRight
      (smallEtalePushforwardRightCompIso B a b ab hab))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B ab)) 𝓖
  rw [show Adjunction.leftAdjointUniq
      (((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B b)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B a))).ofNatIsoRight
        (smallEtalePushforwardRightCompIso B a b ab hab))
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B ab)) =
      smallEtalePullbackFactoredCompIso B a b ab hab from by
    rw [Adjunction.leftAdjointUniq_ofNatIsoRight_comp,
      ← smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso]] at h
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  exact h

end UnitComp

/-! ### Pulling a section over the final object back -/

section FinalUnit

variable {X Y : B.Scheme} (a : X ⟶ Y)

/-- The unit of the pullback--direct image adjunction along `ε_a`, read on sections over an
object: the sections of the direct image over an object are, on the nose, the sections of the
sheaf over the base change of that object. -/
public def unitSectionsApp (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (U : SmallEtale B Y.obj Y.property) :
    M.val.presheaf.obj (op U) ⟶
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.presheaf.obj
        (op ((smallEtaleBaseChange B a).obj U)) :=
  smallEtaleSectionsApp B
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B a)).unit.app M) U

/-- The sections of a direct image along `ε_a` of a morphism are the sections of that morphism
over the base change of the object. -/
public theorem pushforward_map_sectionsApp
    {M N : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (ψ : M ⟶ N)
    (U : SmallEtale B Y.obj Y.property) :
    smallEtaleSectionsApp B
        ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map ψ) U =
      smallEtaleSectionsApp B ψ ((smallEtaleBaseChange B a).obj U) :=
  rfl

/-- `AlgebraicGeometry.SmallEtale.unitSectionsApp` is natural in the module. -/
public theorem unitSectionsApp_naturality
    {M N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)} (φ : M ⟶ N)
    (U : SmallEtale B Y.obj Y.property) :
    smallEtaleSectionsApp B φ U ≫ unitSectionsApp B a N U =
      unitSectionsApp B a M U ≫
        smallEtaleSectionsApp B
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map φ)
          ((smallEtaleBaseChange B a).obj U) :=
  congrArg (fun t => smallEtaleSectionsApp B t U)
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B a)).unit.naturality φ)

/-- `AlgebraicGeometry.SmallEtale.unitSectionsApp` is natural in the object. -/
@[reassoc]
public theorem unitSectionsApp_naturality_obj
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    {U V : SmallEtale B Y.obj Y.property} (g : U ⟶ V) :
    M.val.presheaf.map g.op ≫ unitSectionsApp B a M U =
      unitSectionsApp B a M V ≫
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.presheaf.map
          ((smallEtaleBaseChange B a).map g).op :=
  smallEtaleSectionsApp_naturality B
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B a)).unit.app M) g

/-- **Pulling a section over the final object back along `a`.**  The unit of the
pullback--direct image adjunction along `ε_a`, read over the final object of the small étale site
of `Y`, followed by restriction along the canonical arrow from the final object of the small étale
site of `X` to the base change of that final object. -/
public def finalPullbackUnit (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) :
    M.val.presheaf.obj (op (final B Y.obj Y.property)) ⟶
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.presheaf.obj
        (op (final B X.obj X.property)) :=
  unitSectionsApp B a M (final B Y.obj Y.property) ≫
    ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M).val.presheaf.map
      ((smallEtaleBaseChange_finalIsTerminal B a).from (final B X.obj X.property)).op

/-- `AlgebraicGeometry.SmallEtale.finalPullbackUnit` is natural in the module. -/
public theorem finalPullbackUnit_naturality
    {M N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)} (φ : M ⟶ N) :
    smallEtaleSectionsApp B φ (final B Y.obj Y.property) ≫ finalPullbackUnit B a N =
      finalPullbackUnit B a M ≫
        smallEtaleSectionsApp B
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map φ)
          (final B X.obj X.property) := by
  rw [finalPullbackUnit, finalPullbackUnit, ← Category.assoc, unitSectionsApp_naturality,
    Category.assoc, Category.assoc, smallEtaleSectionsApp_naturality]

end FinalUnit

/-! ### The composition law -/

section Composition

variable {W X Y : B.Scheme} (a₂ : W ⟶ X) (a₁ : X ⟶ Y) (a : W ⟶ Y) (ha : a₂ ≫ a₁ = a)

/-- The compositor of the direct images, on sections: restriction along the inverse comparison of
Stacks 021J. -/
public theorem pushforwardRightCompIso_sectionsApp
    (N : SheafOfModules.{u} (structureSheaf B W.obj W.property))
    (U : SmallEtale B Y.obj Y.property) :
    smallEtaleSectionsApp B ((smallEtalePushforwardRightCompIso B a₂ a₁ a ha).hom.app N) U =
      N.val.presheaf.map
        ((smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).inv.app U).op :=
  rfl

/-- The iterated base change of the final object is terminal: it is isomorphic, by the comparison
of Stacks 021J, to the base change along the composite, which is terminal. -/
public def isTerminal_baseChange_baseChange_final :
    IsTerminal ((smallEtaleBaseChange B a₂).obj
      ((smallEtaleBaseChange B a₁).obj (final B Y.obj Y.property))) :=
  (smallEtaleBaseChange_finalIsTerminal B a).ofIso
    ((smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).app
      (final B Y.obj Y.property)).symm

/-- **The two routes from the final object below `W` to the iterated base change of the final
object below `Y` agree**, both being arrows into a terminal object. -/
public theorem finalToBaseChange_comp_eq :
    (smallEtaleBaseChange_finalIsTerminal B a₂).from (final B W.obj W.property) ≫
        (smallEtaleBaseChange B a₂).map
          ((smallEtaleBaseChange_finalIsTerminal B a₁).from (final B X.obj X.property)) =
      (smallEtaleBaseChange_finalIsTerminal B a).from (final B W.obj W.property) ≫
        (smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).inv.app
          (final B Y.obj Y.property) :=
  (isTerminal_baseChange_baseChange_final B a₂ a₁ a ha).hom_ext _ _

/-- **The unit law of Stacks 070R (2), read on sections over the final object below `Y`.**  The
middle factor is restriction along the inverse comparison of Stacks 021J. -/
@[reassoc]
public theorem unitSectionsApp_factoredComp
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) :
    unitSectionsApp B a₁ M (final B Y.obj Y.property) ≫
        unitSectionsApp B a₂
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₁)).obj M)
            ((smallEtaleBaseChange B a₁).obj (final B Y.obj Y.property)) ≫
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₂)).obj
              ((SheafOfModules.pullback.{u}
                (smallEtaleStructureMapRing B a₁)).obj M)).val.presheaf.map
              ((smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).inv.app
                (final B Y.obj Y.property)).op ≫
            smallEtaleSectionsApp B
              ((smallEtalePullbackFactoredCompIso B a₂ a₁ a ha).hom.app M)
              ((smallEtaleBaseChange B a).obj (final B Y.obj Y.property)) =
      unitSectionsApp B a M (final B Y.obj Y.property) := by
  have hU := congrArg (fun t => smallEtaleSectionsApp B t (final B Y.obj Y.property))
    (smallEtalePullbackUnit_factoredComp B a₂ a₁ a ha M)
  simp only [smallEtaleSectionsApp_comp] at hU
  rwa [pushforward_map_sectionsApp, pushforwardRightCompIso_sectionsApp,
    pushforward_map_sectionsApp] at hU

/-- **`AlgebraicGeometry.SmallEtale.finalPullbackUnit` composes.**  Pulling a section over the
final object back along `a₁` and then along `a₂`, read through the composition law for the
pullbacks of Stacks 070R (2), is pulling it back along the composite. -/
public theorem finalPullbackUnit_factoredComp
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) :
    finalPullbackUnit B a₁ M ≫
        finalPullbackUnit B a₂
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₁)).obj M) ≫
        smallEtaleSectionsApp B ((smallEtalePullbackFactoredCompIso B a₂ a₁ a ha).hom.app M)
          (final B W.obj W.property) =
      finalPullbackUnit B a M := by
  simp only [finalPullbackUnit, Category.assoc]
  rw [unitSectionsApp_naturality_obj_assoc, ← Functor.map_comp_assoc, ← op_comp,
    finalToBaseChange_comp_eq B a₂ a₁ a ha, op_comp, Functor.map_comp_assoc,
    smallEtaleSectionsApp_naturality, unitSectionsApp_factoredComp_assoc]

end Composition

end AlgebraicGeometry.SmallEtale

end
