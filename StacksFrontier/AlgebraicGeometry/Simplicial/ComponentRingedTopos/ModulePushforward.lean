module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Direct images of modules along the simplicial transition morphisms

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Every simplex map `φ : m ⟶ n` induces a morphism of ringed topoi
`f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)`
(`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`), and the assignment
`φ ↦ f_φ` is pseudofunctorial rather than functorial: `f_{ψ ≫ φ}` and `f_ψ ∘ f_φ` are not equal,
only canonically 2-isomorphic.

The direct-image form of the structure map of `f_φ` is the direct-image transition of
Stacks 09WF, and the canonical direct-image compositor of Stacks 09WE is a 2-isomorphism of
ringed topoi `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` in the sense of Stacks 04IC. It induces a comparison
`(f_φ)_* ⋙ (f_ψ)_* ≅ (f_{ψ ≫ φ})_*` of direct images of sheaves of modules.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHomCompTwoIso`: the canonical
  2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of morphisms of ringed topoi, whose underlying
  isomorphism of direct images is the compositor
  `CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm` of Stacks 09WE.
* `CategoryTheory.SimplicialSiteSituation.transitionPushforwardModulesCompIso`: the comparison
  `(f_φ)_* ⋙ (f_ψ)_* ≅ (f_{ψ ≫ φ})_*` of direct images of sheaves of modules.

## Main results

* `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom_forgetFSharp`: the
  direct-image form of the structure map of `f_φ` is, on underlying sheaves of sets, the
  direct-image transition `CategoryTheory.SimplicialSiteSituation.restrictTransition` of
  Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.transitionFSharpSetComp`: the cocycle law for those
  structure maps.
* `CategoryTheory.SimplicialSiteSituation.moduleSheaf_transitionPushforwardModulesCompIso_hom`:
  on underlying sheaves of sets, the comparison of direct images of modules is the compositor
  of Stacks 09WE.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp pushforwardModules
  pushforwardModulesCompIso)

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The direct-image form of the structure map of the ringed morphism induced by a simplex map
`φ : m ⟶ n` is the direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransition` of Stacks 09WF, on the underlying
sheaf of sets of `O`. -/
theorem transitionRingedToposHom_forgetFSharp {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionRingedToposHom O φ).forgetFSharp =
      (S.restrictTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) := by
  refine (forget_map_commRingImageAdjunction_homEquiv (S.transitionMorphism φ)
    (S.componentRingedTopos O m).O (S.componentRingedTopos O n).O
    (S.fiberTransitionCommRing O φ)).trans ?_
  rw [S.fiberTransitionCommRing_forget O φ]
  exact S.fiberTransition_adj φ _

/-- The structure map `Stacks.Sheaves.RingedToposModules.fSharpSet` of
`AlgebraicGeometry.RingedToposHom.toModulesHom` of the transition morphism of ringed topoi of a
simplex map is the direct-image transition of Stacks 09WF. -/
theorem transitionFSharpSet {m n : SimplexCategory} (φ : m ⟶ n) :
    fSharpSet (S.transitionRingedToposHom O φ).toModulesHom =
      (S.restrictTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) :=
  S.transitionRingedToposHom_forgetFSharp O φ

/-- The cocycle law for the structure maps of the transition morphisms of ringed topoi: the
composite structure map, followed by the canonical direct-image compositor of Stacks 09WE, is the
structure map of the transition of the composite simplex map. -/
theorem transitionFSharpSetComp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    fSharpSetComp (S.transitionRingedToposHom O φ).toModulesHom
          (S.transitionRingedToposHom O ψ).toModulesHom ≫
        (S.pushforwardCompSymm ψ φ).hom.app
          ((S.restrict.{u, u} n).obj
            ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) =
      fSharpSet (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom := by
  have hcomp : fSharpSetComp (S.transitionRingedToposHom O φ).toModulesHom
        (S.transitionRingedToposHom O ψ).toModulesHom =
      fSharpSet (S.transitionRingedToposHom O ψ).toModulesHom ≫
        (S.transitionMorphism ψ).pushforward.map
          (fSharpSet (S.transitionRingedToposHom O φ).toModulesHom) := rfl
  rw [hcomp, S.transitionFSharpSet, S.transitionFSharpSet, S.transitionFSharpSet]
  exact (Category.assoc _ _ _).trans
    (S.restrictTransition_comp ψ φ
      ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))

/-- The canonical 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of morphisms of ringed topoi induced by
simplex maps, with underlying isomorphism of direct images the compositor
`CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm` of Stacks 09WE. -/
noncomputable def transitionRingedToposHomCompTwoIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    AlgebraicGeometry.RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
        (S.transitionRingedToposHom O ψ) (S.transitionRingedToposHom O φ))
      (S.transitionRingedToposHom O (ψ ≫ φ)) where
  e := S.pushforwardCompSymm ψ φ
  commutes :=
    (congrArg
        (fun t ↦ t ≫ (S.pushforwardCompSymm ψ φ).hom.app
          ((S.restrict.{u, u} n).obj
            ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)))
        (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
          (S.transitionRingedToposHom O ψ) (S.transitionRingedToposHom O φ))).trans
      (S.transitionFSharpSetComp O ψ φ)

/-- The canonical comparison `(f_φ)_* ⋙ (f_ψ)_* ≅ (f_{ψ ≫ φ})_*` of direct images of sheaves of
modules along the transition morphisms of a composable pair of simplex maps, attached by
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso` to the compositor
`CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm` of Stacks 09WE. -/
noncomputable def transitionPushforwardModulesCompIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :=
  pushforwardModulesCompIso (S.transitionRingedToposHom O φ).toModulesHom
    (S.transitionRingedToposHom O ψ).toModulesHom
    (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom (S.pushforwardCompSymm ψ φ)
    (S.transitionFSharpSetComp O ψ φ)

/-- On underlying sheaves of sets the comparison
`CategoryTheory.SimplicialSiteSituation.transitionPushforwardModulesCompIso` is the compositor
`CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm` of Stacks 09WE. -/
theorem moduleSheaf_transitionPushforwardModulesCompIso_hom {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O l).O)).map
        ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M) =
      (S.pushforwardCompSymm ψ φ).hom.app
        ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)).obj M) :=
  rfl

end CategoryTheory.SimplicialSiteSituation

end
