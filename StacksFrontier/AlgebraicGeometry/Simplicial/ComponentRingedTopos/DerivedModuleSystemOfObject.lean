module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
public import StacksFrontier.CategoryTheory.Localization.LiftedTransition

/-!
# The simplicial system of the derived category of modules of an object of `D(O)` (Stacks 0D9P)

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total site.
Restriction of sheaves of `O`-modules to the degree-`n` component is exact, so it induces a
functor `Lg_n^* : D(O) ⥤ D(O_n)` on unbounded derived categories, and the transition of
restrictions along a simplex map `φ : m ⟶ n` induces a map `Lf_φ^* K_m ⟶ K_n` for every object
`K` of `D(O)`. Stacks 0D9P says that these data form a simplicial system of the derived category
of modules in the sense of Stacks 0D9N, and that the system of a cartesian object is cartesian.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModulesRestriction` and
  `.componentModulesTransition`: restriction of sheaves of modules to a component and its
  pullback transition, read between the modules of the total and the component ringed topos.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction`: the functor
  `Lg_n^* : D(O) ⥤ D(O_n)`, `K ↦ K_n`.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition`: the derived
  transition `Lg_m^* ⋙ Lf_φ^* ⟶ Lg_n^*`, `K ↦ K(φ)`.
* `CategoryTheory.SimplicialSiteSituation.IsCartesianDerivedModule`: **Stacks 07TF (4)**, an
  object of `D(O)` is cartesian when every derived transition at it is an isomorphism.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSystemData`: **Stacks 0D9P**, the
  simplicial system of the derived category of modules attached to an object of `D(O)`, together
  with the equations fixing its objects and its transitions, and `derivedModuleSystem` the
  system itself.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModulesTransition_comp` and
  `.componentModulesTransition_mapHomotopyCategory_cocycle`: the cocycle law of Stacks 09WF for
  modules, and the law it induces on homotopy categories of complexes.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompCounit_app`: the comparison
  built from the two counits and the degreewise compositor, read at an object.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition_comp`: the cocycle
  law for the derived transitions, which is the `map_comp` field of the system.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSystem_cartesian`: **Stacks 0D9P**, the
  system of a cartesian object is cartesian.

## Implementation notes

*Restriction of modules to a component is exact.* It is a direct image of sheaves of modules,
hence a right adjoint and left exact, and the component inclusion is cocontinuous, hence almost
cocontinuous, which is the hypothesis under which a direct image of modules is also right exact.
So `CategoryTheory.Functor.mapDerivedCategory` applies, and additivity is `rfl`.

*Why the restriction and the transition are re-read here.* The structure sheaf of a component
has two spellings — the restriction of the total sheaf of rings, which is what
`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction` is stated over, and the
structure sheaf of the component ringed topos, which is what the pullback of modules along the
transition morphism and hence every derived functor below is stated over. They agree by `rfl`
(`CategoryTheory.SimplicialSiteSituation.componentRingSheaf_structureRingSheaf`) but only after
both sheaves of rings are computed, so a unification that meets the identification repeatedly
exhausts its heartbeats. `componentModulesRestriction` and `componentModulesTransition` pay the
identification once each, and nothing afterwards meets it.

*How the derived transition is built.* `derivedTransitionPullback` is a total *left derived*
functor, so a map out of it is not given by a universal property; what is available is its
canonical comparison out of the localization of degreewise pullback. The transition is therefore
assembled on the homotopy category of complexes of `O`-modules — where it is the comparison of
`Lg_m^*`, the comparison of `Lf_φ^*` and the transition of complexes, in that order — and then
lifted along the localization `DerivedCategory.Qh`. Both steps are
`CategoryTheory.liftedTransition`, stated at free variables, and the cocycle condition is
`CategoryTheory.liftedTransition_cocycle`. No heartbeat limit is raised anywhere.

*Why the two hypotheses of that lemma are supplied as named lemmas rather than inline.* The
first is `CategoryTheory.SimplicialSiteSituation.derivedTransitionComp_fac`, the factorization
that pins the comparison of derived pullbacks, followed by `derivedTransitionCompCounit_app`;
the latter exists because `derivedTransitionCompCounit` is deliberately opaque — unfolding it
inside a larger unification is what its own implementation notes warn about — and because at a
single equation the one delta step it needs is cheap. The second is
`componentModulesTransition_mapHomotopyCategory_cocycle`, an instance of
`CategoryTheory.mapHomotopyCategoryTransition_cocycle` whose statement is written out: supplied
inline, it is elaborated against an expected type still carrying the metavariables of the
surrounding application, and that unification does not terminate inside the budget.

*No `map_id` field.* Stacks 0D9N imposes the cocycle condition and nothing else; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedModuleSystem.lean`.

*The existence of `Lf_φ^*` is Stacks 06YY* and is carried as an instance-implicit hypothesis, in
the shape 06YY supplies it; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedPullback.lean`.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.PushforwardRightExact

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### Restriction and transition of modules of the component ringed topoi -/

/-- Restriction of sheaves of modules to the degree-`n` component, read as a functor from the
modules of the total ringed topos to those of the component ringed topos. This is the functor
`g_n^*` of Stacks 0D72 over the structure sheaves of those ringed topoi. -/
noncomputable def componentModulesRestriction (n : SimplexCategory) :
    (S.totalRingedTopos O).Modules ⥤ (S.componentRingedTopos O n).Modules :=
  S.componentModuleRestriction (S.totalRingSheaf O) n

/-- Restriction of sheaves of modules to a component is additive: on sections it is restriction
of a section along a total-category arrow, which is a map of modules. -/
instance componentModulesRestriction_additive (n : SimplexCategory) :
    (S.componentModulesRestriction O n).Additive where
  map_add := rfl

/-- Restriction of sheaves of modules to a component preserves finite limits, being a direct
image of sheaves of modules and hence a right adjoint. -/
instance componentModulesRestriction_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (S.componentModulesRestriction O n) :=
  SheafOfModules.preservesFiniteLimits_pushforward
    (𝟙 (S.componentRingSheaf (S.totalRingSheaf O) n))

/-- Restriction of sheaves of modules to a component preserves finite colimits: it is a direct
image along the component inclusion, which is cocontinuous, hence almost cocontinuous. -/
instance componentModulesRestriction_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (S.componentModulesRestriction O n) :=
  preservesFiniteColimits_pushforward_of_isAlmostCocontinuous (componentFunctor S n)
    (𝟙 (S.componentRingSheaf (S.totalRingSheaf O) n))
    (isAlmostCocontinuous_of_isCocontinuous (componentFunctor S n) (S.componentTopology n)
      S.totalTopology)

/-- **Stacks 09WF for sheaves of modules.** The pullback transition
`g_m^* ⋙ f_φ^* ⟶ g_n^*` of the restrictions of a sheaf of `O`-modules, read between the modules
of the total and the component ringed topoi. -/
noncomputable def componentModulesTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    S.componentModulesRestriction O m ⋙
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ⟶
      S.componentModulesRestriction O n :=
  S.componentModuleTransition O φ

/-- **Stacks 09WF for sheaves of modules: the cocycle law.** Precomposed with the inverse of the
pullback compositor of Stacks 09WE, the transition of a composite simplex map is the composite
of the two transitions. -/
theorem componentModulesTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : (S.totalRingedTopos O).Modules) :
    (S.transitionPullbackModulesCompIso O ψ φ).inv.app
          ((S.componentModulesRestriction O l).obj M) ≫
        (S.componentModulesTransition O (ψ ≫ φ)).app M =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((S.componentModulesTransition O ψ).app M) ≫
        (S.componentModulesTransition O φ).app M :=
  S.componentModuleTransition_comp O ψ φ M

/-- The cocycle law of Stacks 09WF for modules, carried to the homotopy categories of complexes
by `CategoryTheory.mapHomotopyCategoryTransition_cocycle`. This is the second hypothesis of
`CategoryTheory.liftedTransition_cocycle` below, written out: supplied inline it is elaborated
against an expected type still carrying the metavariables of that application. -/
theorem componentModulesTransition_mapHomotopyCategory_cocycle {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : HomotopyCategory ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
            (ComplexShape.up ℤ)).hom.app
          (((S.componentModulesRestriction O l).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X) ≫
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O l)
          (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom.pullbackModules
          (S.componentModulesRestriction O n) (S.componentModulesTransition O (ψ ≫ φ))).app X =
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          ((mapHomotopyCategoryTransition (ComplexShape.up ℤ)
            (S.componentModulesRestriction O l)
            (S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules
            (S.componentModulesRestriction O m) (S.componentModulesTransition O ψ)).app X) ≫
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
          (S.componentModulesRestriction O n) (S.componentModulesTransition O φ)).app X :=
  mapHomotopyCategoryTransition_cocycle (ComplexShape.up ℤ)
    (S.componentModulesRestriction O l) (S.componentModulesRestriction O m)
    (S.componentModulesRestriction O n)
    (S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom.pullbackModules
    (S.transitionPullbackModulesCompIso O ψ φ).symm (S.componentModulesTransition O ψ)
    (S.componentModulesTransition O φ) (S.componentModulesTransition O (ψ ≫ φ))
    (S.componentModulesTransition_comp O ψ φ) X

/-! ### The derived restriction and the derived transition -/

/-- **Stacks 0D9P, the functor `K ↦ K_n`.** Restriction of an object of the derived category of
`O`-modules to the degree-`n` component: the derived functor of restriction of sheaves of
modules, which is exact. -/
noncomputable def derivedComponentModuleRestriction (n : SimplexCategory) :
    DerivedCategory (S.totalRingedTopos O).Modules ⥤
      DerivedCategory ((S.componentRingedTopos O n).Modules) :=
  (S.componentModulesRestriction O n).mapDerivedCategory

section Derived

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- The comparison from the composite of two derived pullbacks to degreewise pullback along the
transition of the composite simplex map, read at an object: the comparison for `Lf_ψ^*` pushed
forward by `Lf_φ^*`, the comparison for `Lf_φ^*`, and the degreewise compositor. -/
theorem derivedTransitionCompCounit_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (Y : HomotopyCategory ((S.componentRingedTopos O l).Modules) (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompCounit O ψ φ).app Y =
      (S.derivedTransitionPullback O φ).map ((S.derivedTransitionComparison O ψ).app Y) ≫
        (S.derivedTransitionComparison O φ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj Y) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (S.transitionPullbackModulesCompIso O ψ φ).symm (ComplexShape.up ℤ)).hom.app Y) :=
  rfl

/-- **Stacks 0D9P, the map `K(φ)`.** The derived transition `Lg_m^* ⋙ Lf_φ^* ⟶ Lg_n^*` of
restrictions of objects of the derived category of `O`-modules along a simplex map `φ : m ⟶ n`:
the transition of complexes, compared with the two derived functors through their canonical
comparisons and lifted along the localization of the homotopy category of complexes of
`O`-modules. -/
noncomputable def derivedComponentModuleTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    S.derivedComponentModuleRestriction O m ⋙ S.derivedTransitionPullback O φ ⟶
      S.derivedComponentModuleRestriction O n :=
  liftedTransition (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh
    (S.derivedTransitionComparison O φ)
    (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
      (S.componentModulesRestriction O n)
      (S.componentModulesTransition O φ))
    (HomotopyCategory.quasiIso ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ))

/-- **Stacks 0D9P, the cocycle condition.** Composed with the canonical comparison of derived
pullbacks, the derived transition of a composite simplex map is the composite of the two derived
transitions. -/
theorem derivedComponentModuleTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.derivedTransitionCompComparison O ψ φ).app
          ((S.derivedComponentModuleRestriction O l).obj K) ≫
        (S.derivedComponentModuleTransition O (ψ ≫ φ)).app K =
      (S.derivedTransitionPullback O φ).map
          ((S.derivedComponentModuleTransition O ψ).app K) ≫
        (S.derivedComponentModuleTransition O φ).app K := by
  delta derivedComponentModuleTransition derivedComponentModuleRestriction
  exact liftedTransition_cocycle (S.componentModulesRestriction O l).mapDerivedCategoryFactorsh
    (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh
    (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh
    (S.derivedTransitionComparison O ψ) (S.derivedTransitionComparison O φ)
    (S.derivedTransitionComparison O (ψ ≫ φ)) (S.derivedTransitionCompComparison O ψ φ)
    (Functor.mapHomotopyCategoryCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
      (ComplexShape.up ℤ)).hom
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O l)
      (S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules
      (S.componentModulesRestriction O m)
      (S.componentModulesTransition O ψ))
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
      (S.componentModulesRestriction O n)
      (S.componentModulesTransition O φ))
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O l)
      (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom.pullbackModules
      (S.componentModulesRestriction O n) (S.componentModulesTransition O (ψ ≫ φ)))
    (HomotopyCategory.quasiIso ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ))
    (fun Y => (congr_app (S.derivedTransitionComp_fac O ψ φ) Y).trans
      (S.derivedTransitionCompCounit_app O ψ φ Y))
    (fun X => S.componentModulesTransition_mapHomotopyCategory_cocycle O ψ φ X)
    K

/-- **Stacks 07TF (4).** An object `K` of the derived category of `O`-modules on the total site
is *cartesian* when the derived transition `Lf_φ^* K_m ⟶ K_n` of its restrictions along every
simplex map `φ : [m] ⟶ [n]` is an isomorphism.

Parts (1), (2) and (3) of the source definition are
`CategoryTheory.SimplicialSiteSituation.IsCartesianSheaf` and `.IsCartesianAbSheaf`,
`.IsModuleFiberTransitionIso`, and `.IsCartesianDerived'`. -/
@[stacks 07TF "part (4), cartesian objects of D(O): the derived transitions Lf_phi^* K_m -> K_n \
are isomorphisms"]
abbrev IsCartesianDerivedModule (K : DerivedCategory (S.totalRingedTopos O).Modules) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
    IsIso ((S.derivedComponentModuleTransition O φ).app K)

/-- **Stacks 0D9P.** The restrictions `K_n` of an object `K` of the derived category of
`O`-modules on the total site, together with the derived transitions `K(φ)`, form a simplicial
system of the derived category of modules in the sense of Stacks 0D9N. The two equations are
part of the datum, so no unrelated family of transitions can satisfy the cocycle condition in
its place. -/
@[stacks 0D9P "the system (K_n, K(φ)) is a simplicial system of the derived category of modules"]
noncomputable def derivedModuleSystemData
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    { T : SimplicialDerivedModuleSystem S O //
      (∀ n, T.obj n = (S.derivedComponentModuleRestriction O n).obj K) ∧
      (∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
        HEq (T.map φ) ((S.derivedComponentModuleTransition O φ).app K)) } :=
  ⟨{ obj := fun n => (S.derivedComponentModuleRestriction O n).obj K
     map := fun φ => (S.derivedComponentModuleTransition O φ).app K
     map_comp := fun ψ φ => S.derivedComponentModuleTransition_comp O ψ φ K },
    fun _ => rfl, fun _ _ _ => HEq.rfl⟩

/-- The simplicial system of the derived category of modules attached to an object of the
derived category of `O`-modules on the total site. -/
noncomputable def derivedModuleSystem (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    SimplicialDerivedModuleSystem S O :=
  (S.derivedModuleSystemData O K).val

/-- **Stacks 0D9P.** The simplicial system of a cartesian object of the derived category of
`O`-modules is cartesian: its transitions are the derived transitions, which are isomorphisms by
hypothesis. -/
@[stacks 0D9P "if K is cartesian then so is the system"]
theorem derivedModuleSystem_cartesian (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : S.IsCartesianDerivedModule O K) : (S.derivedModuleSystem O K).Cartesian :=
  fun φ => hK φ

end Derived

end CategoryTheory.SimplicialSiteSituation

end
