module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The canonical leg of the module direct-sum formula

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
The direct-sum formula of Stacks 0D72 (6) for sheaves of modules writes the restriction to
degree `m` of module lower shriek from degree `n` as the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the pullbacks `f_φ^*` along the transition morphisms of ringed topoi. The
isomorphism itself says nothing about which summand a given map lands in; what identifies the
decomposition is that the `φ`th summand inclusion is the *canonical* map attached to `φ`.

This file constructs that canonical map, for an arbitrary situation and so for either case of
it: the unit of `g_{n!} ⊣ g_n^*` followed by the transition of Stacks 09WF for sheaves of
modules. It is the module counterpart of
`CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg'`, which does the same for abelian
coefficients in
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentSumFormulaLeg.lean`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`: the canonical map
  `f_φ^* ⟶ g_{n!} ⋙ g_m^*` attached to a simplex map `φ : [n] ⟶ [m]`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg_app`: at a sheaf of modules the
  canonical map is the unit of `g_{n!} ⊣ g_n^*` carried along `f_φ^*`, followed by the pullback
  transition of Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.homEquiv_moduleSumFormulaLeg_app`: its transpose under
  the Stacks 03D7 adjunction of the transition morphism is the unit of `g_{n!} ⊣ g_n^*` followed
  by the *direct-image* transition of Stacks 09WF.

## Implementation notes

The summand of the direct-sum formula is
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`, and the transition of
Stacks 09WF for sheaves of modules is
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition`, which is a natural
transformation out of a composite ending in
`AlgebraicGeometry.RingedToposHom.pullbackModules`. A statement naming both was not well typed
until the two readings of a morphism of ringed topoi as the four-field datum of the modules
development were identified: the summand used to be the pullback at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` and the transition lives at
`AlgebraicGeometry.RingedToposHom.toModulesHom`, and elaborating a term mentioning both left the
unifier to see through the two inverse-image structure maps, where it exhausted its heartbeats.
With `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom_eq_toModulesHom` available the
summand is defined as the pullback of the two-field morphism itself, and the two spellings differ
by one `δ`-step.

The leg is built for an arbitrary situation rather than once per case, because both cases of
Stacks 0D72 (6) compare their own summand against it.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m)

/-- **The canonical map attached to a simplex map `φ : [n] ⟶ [m]`**, out of the pullback of
sheaves of modules along the transition morphism of ringed topoi and into the degree-`m`
restriction of module lower shriek from degree `n`: the unit of `g_{n!} ⊣ g_n^*` carried along
`f_φ^*`, followed by the pullback transition of Stacks 09WF.

This is the map that Stacks 0D72 (6) asserts the `φ`th summand inclusion of the direct-sum
formula to be. -/
def moduleSumFormulaLeg :
    S.transitionPullbackModules' O φ ⟶
      S.componentModuleLowerShriek (S.totalRingSheaf O) n ⋙
        S.componentModuleRestriction (S.totalRingSheaf O) m :=
  Functor.whiskerRight (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit
      (S.transitionPullbackModules' O φ) ≫
    Functor.whiskerLeft (S.componentModuleLowerShriek (S.totalRingSheaf O) n)
      (S.componentModuleTransition O φ)

/-- On a sheaf of modules the canonical map is the unit of `g_{n!} ⊣ g_n^*` carried along the
transition pullback, followed by the pullback transition of Stacks 09WF. -/
theorem moduleSumFormulaLeg_app
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :
    (S.moduleSumFormulaLeg O φ).app X =
      (S.transitionPullbackModules' O φ).map
          ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app X) ≫
        (S.componentModuleTransition O φ).app
          ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj X) :=
  rfl

/-- **The transpose of the canonical map.** Under the Stacks 03D7 adjunction of the transition
morphism of ringed topoi, the canonical map is the unit of `g_{n!} ⊣ g_n^*` followed by the
direct-image transition of Stacks 09WF. -/
theorem homEquiv_moduleSumFormulaLeg_app
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :
    ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv X
          ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj
            ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj X)))
        ((S.moduleSumFormulaLeg O φ).app X) =
      (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app X ≫
        (S.restrictTransitionModules O φ).app
          ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj X) := by
  refine Eq.trans (congrArg
    ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv X
      ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj
        ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj X)))
    (S.moduleSumFormulaLeg_app O φ X)) ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _) ?_
  refine congrArg (fun g =>
    (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app X ≫ g) ?_
  exact Eq.trans (congrArg
    ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _)
    (S.componentModuleTransition_app O φ _)) (S.fiberTransitionModules_adj O φ _)

end CategoryTheory.SimplicialSiteSituation

end
