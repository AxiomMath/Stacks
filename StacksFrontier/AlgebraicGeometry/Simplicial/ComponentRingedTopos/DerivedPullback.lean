module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction

/-!
# Pullbacks of modules along the simplicial transition morphisms, and their derived functors

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. A simplex map `φ : m ⟶ n` induces a morphism of ringed topoi
`f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)`, hence a pullback `f_φ^*` of sheaves of modules
(Stacks 03D6, part (2)) and, assuming degreewise pullback has a total left derived functor
(Stacks 06YY), a derived pullback `Lf_φ^* : D(O_m) ⥤ D(O_n)`. For a composable pair
`ψ : l ⟶ m`, `φ : m ⟶ n` there are a compositor `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` and a canonical
comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso`: the compositor
  `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` of pullbacks of sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback`: the derived pullback
  `Lf_φ^*`, the total left derived functor of degreewise pullback followed by localization,
  with its canonical comparison
  `CategoryTheory.SimplicialSiteSituation.derivedTransitionComparison`.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompCounit`: the comparison from the
  composite of the two derived pullbacks, restricted along the localization, to degreewise
  pullback along the transition of the composite simplex map.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison`: the comparison
  `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionComp_fac`: the derived comparison
  restricts, along the localization, to the comparison built from the two counits and the
  underived compositor.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The canonical compositor `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` of pullbacks of sheaves of modules
along the transition morphisms of a composable pair of simplex maps: the adjoint mate of the
comparison `CategoryTheory.SimplicialSiteSituation.transitionPushforwardModulesCompIso` of direct
images. -/
noncomputable def transitionPullbackModulesCompIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    ((S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom.pullbackModules) ≅
      ((S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules) ⋙
        ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) :=
  Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso
    (S.transitionRingedToposHom O φ).toModulesHom
    (S.transitionRingedToposHom O ψ).toModulesHom
    (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom (S.pushforwardCompSymm ψ φ)
    (S.transitionFSharpSetComp O ψ φ)

section Derived

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- The derived pullback `Lf_φ^* : D(O_m) ⥤ D(O_n)` along
the transition morphism of ringed topoi of a simplex map `φ : m ⟶ n`: the total left derived
functor of degreewise pullback followed by localization. -/
noncomputable def derivedTransitionPullback {m n : SimplexCategory} (φ : m ⟶ n) :
    DerivedCategory (S.componentRingedTopos O m).Modules ⥤
      DerivedCategory (S.componentRingedTopos O n).Modules :=
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).totalLeftDerived DerivedCategory.Qh
    (targetQuasiIso (S.componentRingedTopos O m))

/-- The canonical comparison from the derived pullback along a simplex map to degreewise
pullback. -/
noncomputable def derivedTransitionComparison {m n : SimplexCategory} (φ : m ⟶ n) :
    DerivedCategory.Qh ⋙ S.derivedTransitionPullback O φ ⟶
      pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ) :=
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).totalLeftDerivedCounit
    DerivedCategory.Qh (targetQuasiIso (S.componentRingedTopos O m))

/-- The derived pullback along a simplex map is a left derived functor of degreewise pullback,
with the canonical comparison as its counit. -/
instance isLeftDerivedFunctor_derivedTransitionPullback {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.derivedTransitionPullback O φ).IsLeftDerivedFunctor (S.derivedTransitionComparison O φ)
      (targetQuasiIso (S.componentRingedTopos O m)) :=
  inferInstanceAs
    (((pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ)).totalLeftDerived
        DerivedCategory.Qh
        (targetQuasiIso (S.componentRingedTopos O m))).IsLeftDerivedFunctor
      ((pullbackOnHomotopy.{u, u, u, u, u, u}
          (S.transitionRingedToposHom O φ)).totalLeftDerivedCounit DerivedCategory.Qh
        (targetQuasiIso (S.componentRingedTopos O m)))
      (targetQuasiIso (S.componentRingedTopos O m)))

/-- The comparison from the composite of the two derived pullbacks to degreewise pullback along
the transition of the composite simplex map. Its three factors are the comparison for
`Lf_ψ^*`, pushed forward by `Lf_φ^*`; the comparison for `Lf_φ^*` at the degreewise pullback
along `f_ψ`; and the degreewise compositor
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso`. -/
noncomputable def derivedTransitionCompCounit {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    DerivedCategory.Qh ⋙ (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ) ⟶
      pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O (ψ ≫ φ)) :=
  Functor.whiskerRight (S.derivedTransitionComparison O ψ) (S.derivedTransitionPullback O φ) ≫
    Functor.whiskerLeft (pullbackMapHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O ψ))
      (S.derivedTransitionComparison O φ) ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (S.transitionPullbackModulesCompIso O ψ φ).symm (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh

/-- The canonical comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of derived pullbacks along the
transition morphisms of a composable pair of simplex maps: the unique map restricting to
`derivedTransitionCompCounit` along the localization. -/
noncomputable def derivedTransitionCompComparison {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ ⟶
      S.derivedTransitionPullback O (ψ ≫ φ) :=
  (S.derivedTransitionPullback O (ψ ≫ φ)).leftDerivedLift (S.derivedTransitionComparison O (ψ ≫ φ))
    (targetQuasiIso (S.componentRingedTopos O l))
    (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ)
    (S.derivedTransitionCompCounit O ψ φ)

/-- The canonical comparison of derived pullbacks restricts, along the localization, to the
comparison built from the two counits and the degreewise compositor. -/
theorem derivedTransitionComp_fac {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.whiskerLeft DerivedCategory.Qh (S.derivedTransitionCompComparison O ψ φ) ≫
        S.derivedTransitionComparison O (ψ ≫ φ) =
      S.derivedTransitionCompCounit O ψ φ :=
  (S.derivedTransitionPullback O (ψ ≫ φ)).leftDerived_fac
    (S.derivedTransitionComparison O (ψ ≫ φ)) (targetQuasiIso (S.componentRingedTopos O l))
    (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ)
    (S.derivedTransitionCompCounit O ψ φ)

end Derived

end CategoryTheory.SimplicialSiteSituation

end
