module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition
public import StacksFrontier.CategoryTheory.Adjunction.MateNatTrans
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The transition of component modules as a natural transformation

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
A simplex map `φ : m ⟶ n` compares the restrictions of a sheaf of `O`-modules to the components
of degrees `m` and `n`, in direct-image form as a map
`ℱ|_{C_m} ⟶ (f_φ)_* (ℱ|_{C_n})` and, as its mate, in pullback form as a map
`f_φ^* (ℱ|_{C_m}) ⟶ ℱ|_{C_n}`. This module assembles both comparisons into natural
transformations of the restriction functors and records the cocycle law for the second one in
that form.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.restrictTransitionModules`: the direct-image
  transition `g_m^* ⟶ g_n^* ⋙ (f_φ)_*` of restriction functors.
* `CategoryTheory.SimplicialSiteSituation.componentModuleTransition`: its mate, the pullback
  transition `g_m^* ⋙ f_φ^* ⟶ g_n^*`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleTransition_app`: at a sheaf of modules
  the pullback transition is the map of Stacks 09WF,
  `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules`.
* `CategoryTheory.SimplicialSiteSituation.componentModuleTransition_comp`: the cocycle law for
  the pullback transition, stated against the inverse of the pullback compositor of
  Stacks 09WE.

## Implementation notes

*Why the transitions are natural transformations here and maps of single modules in
`ModuleTransition.lean`.* Nothing about one module needs naturality, and the naturality square
of the pullback transition at concretely given restriction functors makes the unifier unfold the
four layers of `Stacks.Sheaves.RingedToposModules.pullbackModules`; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransition.lean`. Both
obstacles are avoided by proving each naturality square one level away from where it is used.
For the direct-image transition the square is proved on sections, where the two sides are
literally restriction of a section of the underlying sheaf of sets along a total-category arrow
and the equation is `CategoryTheory.SimplicialSiteSituation.restrictTransition`'s own
naturality. For the pullback transition the square is not proved here at all: the mate of a
natural transformation is natural by `CategoryTheory.Adjunction.mateNatTrans`, which proves it
once at free variables.

*The cocycle law.* It is the law for direct images — where, again on sections, it is
`CategoryTheory.SimplicialSiteSituation.restrictTransition_comp` of Stacks 09WF — transposed
across the pullback-pushforward adjunctions: the mate of a composite of
comparisons of right adjoints is the composite of the mates, compared by the isomorphism that
uniqueness of a left adjoint produces. That is the shape in which
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`, hence
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso`, is built, so no
comparison is chosen here; the cocycle law of `ModuleTransitionCocycle` hands it to the
abstract lemma by a `rfl`-equation rather than by unification.

*Why the comparison is substituted with `congrArg` at an explicit motive.* The two spellings
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf (S.totalRingSheaf O) n` and
`Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O` of the
structure sheaf of a component are equal by `rfl`, but only after unfolding the category of
sheaves of modules over each; a `rw` whose motive is formed over the whole goal does not
typecheck across them, which is also why the last step of `componentModuleTransition_comp` is an
`exact` of `Iso.inv_hom_id_app_assoc` and not a rewrite.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section Transition

variable {m n : SimplexCategory} (φ : m ⟶ n)

/-- **Stacks 09WF for sheaves of modules, in direct-image form.** The transition
`g_m^* ⟶ g_n^* ⋙ (f_φ)_*` comparing the restrictions of a sheaf of `O`-modules to the
components of degrees `m` and `n`, as a natural transformation of the restriction functors. -/
noncomputable def restrictTransitionModules :
    S.componentModuleRestriction (S.totalRingSheaf O) m ⟶
      S.componentModuleRestriction (S.totalRingSheaf O) n ⋙
        (S.transitionRingedToposHom O φ).pushforwardModules where
  app M := S.restrictTransitionModulesApp O φ M
  naturality {M M'} f := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact congrArg (fun t => (Sheaf.sectionsFunctor (S.componentTopology m) V).map t x)
      ((S.restrictTransition φ).naturality
        ((Sheaf.moduleSheafFunctor (S.totalRingSheaf O)).map f))

/-- **Stacks 09WF for sheaves of modules is Stacks 09WF for the underlying sheaves of sets.** The
direct-image transition of sheaves of modules, read through the underlying sheaf of sets, is the
direct-image transition `CategoryTheory.SimplicialSiteSituation.restrictTransition` of sheaves of
sets, at the underlying sheaf of sets of the module.

It holds by definition: `…restrictTransitionModulesApp` is built by
`Stacks.Sheaves.RingedToposModules.ofSheafHom` from exactly that morphism of sheaves of sets, and
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom` is `rfl`.

This is the form in which the right-hand side of the case-(B) leg equation of Stacks 0D72 (6) is
evaluated on a section: the modules of sections of the direct image are not available
elementwise — the module system does not expose `CategoryTheory.Limits.getLimitCone` — but the
underlying sheaf of sets is the right Kan extension, where
`Stacks.SheafOfModules.ranπ` applies. -/
theorem moduleSheafFunctor_map_restrictTransitionModules_app
    (B : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (Sheaf.moduleSheafFunctor (S.componentRingSheaf (S.totalRingSheaf O) m)).map
        ((S.restrictTransitionModules O φ).app B) =
      (S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) B) :=
  rfl

/-- **Stacks 09WF for sheaves of modules, in pullback form.** The transition
`g_m^* ⋙ f_φ^* ⟶ g_n^*` of the restrictions of a sheaf of `O`-modules, as a natural
transformation: the mate of the direct-image transition under the pullback-pushforward
adjunction of the transition morphism of ringed topoi. -/
noncomputable def componentModuleTransition :
    S.componentModuleRestriction (S.totalRingSheaf O) m ⋙
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ⟶
      S.componentModuleRestriction (S.totalRingSheaf O) n :=
  (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.mateNatTrans _ _
    (S.restrictTransitionModules O φ)

/-- At a sheaf of `O`-modules the pullback transition of restriction functors is the map
`f_φ^*ℱ_m ⟶ ℱ_n` of Stacks 09WF. -/
theorem componentModuleTransition_app (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (S.componentModuleTransition O φ).app M = S.fiberTransitionModules O φ M :=
  Adjunction.mateNatTrans_app_homEquiv_symm _ _ _ (S.restrictTransitionModules O φ) M

end Transition

/-! ### The cocycle law -/

/-- **Stacks 09WF for sheaves of modules: the cocycle law for the pullback transition of
restriction functors.** Precomposed with the inverse of the pullback compositor of Stacks 09WE,
the transition of a composite simplex map is the composite of the two transitions. -/
theorem componentModuleTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (S.transitionPullbackModulesCompIso O ψ φ).inv.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) l).obj M) ≫
        (S.componentModuleTransition O (ψ ≫ φ)).app M =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((S.componentModuleTransition O ψ).app M) ≫
        (S.componentModuleTransition O φ).app M := by
  rw [componentModuleTransition_app, componentModuleTransition_app,
    componentModuleTransition_app, S.fiberTransitionModules_comp O ψ φ M]
  exact Iso.inv_hom_id_app_assoc _ _ _

end CategoryTheory.SimplicialSiteSituation

end
