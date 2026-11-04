module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived pullbacks along the simplicial transition morphisms

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. For a composable pair of simplex maps `ψ : l ⟶ m` and `φ : m ⟶ n` the universal
property of the derived pullback along the transition of `ψ ≫ φ` produces the canonical
comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison`. This module shows that
it is invertible (Stacks 0D6D).

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentKFlat`: the K-flat complexes of modules with
  flat terms on the component ringed topos in a given simplicial degree.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompIso`: the natural isomorphism
  `Lf_ψ^* ⋙ Lf_φ^* ≅ Lf_{ψ ≫ φ}^*`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.hasResolutions_componentKFlat`: Stacks 06YS on a
  component ringed topos — every complex of modules is quasi-isomorphic to a K-flat complex with
  flat terms.
* `CategoryTheory.SimplicialSiteSituation.hasLeftDerivedFunctor_transitionPullbackOnHomotopy`:
  degreewise pullback along a transition morphism has a left derived functor.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedTransitionComparison_app`: the canonical
  comparison `Lf_φ^* ⟶ f_φ^*` is invertible at a K-flat complex with flat terms (Stacks 06YY).
* `CategoryTheory.SimplicialSiteSituation.isLeftDerivedFunctor_derivedTransitionPullbackComp`:
  the composite of the two derived pullbacks is a left derived functor of degreewise pullback
  along the transition of the composite simplex map.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedTransitionCompComparison`: the canonical
  comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` is an isomorphism.

## Implementation notes

The simplicial transition morphisms are `AlgebraicGeometry.RingedToposHom`s, not morphisms of
sites: in case (B) of Stacks 09WE the transition datum presents no morphism of the underlying
sites. So Stacks 06YY and Stacks 0G7E are used in their versions for an arbitrary morphism of
ringed topoi, `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat` and
`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The K-flat complexes of modules with flat terms on the component ringed topos in simplicial
degree `n`, as a property of objects of the unbounded homotopy category. -/
abbrev componentKFlat (n : SimplexCategory) :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
    (Y := S.componentRingedTopos O n)

/-- Every complex of modules on the component in degree `n` receives a quasi-isomorphism from a
K-flat complex with flat terms. -/
theorem hasResolutions_componentKFlat (n : SimplexCategory)
    (M : HomotopyCategory (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ)) :
    ∃ (K : HomotopyCategory (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))
      (_ : S.componentKFlat O n K) (s : K ⟶ M),
      targetQuasiIso (S.componentRingedTopos O n) s :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
    (Y := S.componentRingedTopos O n) M

/-- Degreewise pullback along the transition of a simplex map inverts the quasi-isomorphisms
out of a K-flat complex with flat terms. -/
theorem transitionPullbackInvertsQuasiIso {m n : SimplexCategory} (φ : m ⟶ n) :
    Stacks.Cohomology.DerivedPullbackOfToposHom.PullbackInvertsQuasiIso
      (X := S.componentRingedTopos O n) (Y := S.componentRingedTopos O m)
      (S.transitionRingedToposHom O φ) (S.componentKFlat O m) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
    (S.transitionRingedToposHom O φ)

/-- Degreewise pullback along the transition of a simplex map carries a K-flat complex with
flat terms to a K-flat complex with flat terms. -/
theorem componentKFlat_pullbackMapHomotopy {m n : SimplexCategory} (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ))
    (hK : S.componentKFlat O m K) :
    S.componentKFlat O n ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (S.transitionRingedToposHom O φ) K hK

/-- Degreewise pullback along a transition morphism, followed by localization, has an
everywhere-defined left derived functor. -/
instance hasLeftDerivedFunctor_transitionPullbackOnHomotopy {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy_hasLeftDerivedFunctor
    (S.transitionRingedToposHom O φ) (S.componentKFlat O m)
    (S.hasResolutions_componentKFlat O m) (S.transitionPullbackInvertsQuasiIso O φ)

section Derived

/-- The canonical comparison `Lf_φ^* ⟶ f_φ^*` is invertible at a K-flat complex with flat
terms: the derived pullback of such a complex is computed by degreewise pullback. -/
theorem isIso_derivedTransitionComparison_app {m n : SimplexCategory} (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ))
    (hK : S.componentKFlat O m K) :
    IsIso ((S.derivedTransitionComparison O φ).app K) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (targetQuasiIso (S.componentRingedTopos O m)) (S.componentKFlat O m)
    (S.hasResolutions_componentKFlat O m)
    (pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ))
    (fun s hs hK' hM' => S.transitionPullbackInvertsQuasiIso O φ s hs hK' hM')
    DerivedCategory.Qh (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ) K hK

/-- The comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ f_{ψ ≫ φ}^*` is invertible at a K-flat complex with flat
terms. -/
theorem isIso_derivedTransitionCompCounit_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O l).Modules (ComplexShape.up ℤ))
    (hK : S.componentKFlat O l K) :
    IsIso ((S.derivedTransitionCompCounit O ψ φ).app K) := by
  rw [S.derivedTransitionCompCounit_app O ψ φ K]
  have h₁ := S.isIso_derivedTransitionComparison_app O ψ K hK
  have h₂ := S.isIso_derivedTransitionComparison_app O φ _
    (S.componentKFlat_pullbackMapHomotopy O ψ K hK)
  infer_instance

/-- With the comparison `derivedTransitionCompCounit`, the composite `Lf_ψ^* ⋙ Lf_φ^*` is a left
derived functor of degreewise pullback along the transition of `ψ ≫ φ` followed by
localization. -/
theorem isLeftDerivedFunctor_derivedTransitionPullbackComp {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ).IsLeftDerivedFunctor
      (S.derivedTransitionCompCounit O ψ φ) (targetQuasiIso (S.componentRingedTopos O l)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (targetQuasiIso (S.componentRingedTopos O l)) (S.componentKFlat O l)
    (S.hasResolutions_componentKFlat O l)
    (pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O (ψ ≫ φ)))
    (fun s hs hK' hM' => S.transitionPullbackInvertsQuasiIso O (ψ ≫ φ) s hs hK' hM')
    DerivedCategory.Qh (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ)
    (S.derivedTransitionCompCounit O ψ φ)
    (fun K hK => S.isIso_derivedTransitionCompCounit_app O ψ φ K hK)

/-- The canonical comparison from the composite of the derived pullbacks along the transitions
of `ψ` and `φ` to the derived pullback along the transition of `ψ ≫ φ` is an isomorphism, so
`Lf_ψ^* ∘ Lf_φ^* = Lf_{ψ ≫ φ}^*`. -/
@[stacks 0D6D "for the transition morphisms of a simplicial-site situation"]
theorem isIso_derivedTransitionCompComparison {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    IsIso (S.derivedTransitionCompComparison O ψ φ) :=
  ((S.derivedTransitionPullback O (ψ ≫ φ)).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (S.derivedTransitionComparison O (ψ ≫ φ)) (targetQuasiIso (S.componentRingedTopos O l))
      (S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ)
      (S.derivedTransitionCompCounit O ψ φ)).1
    (S.isLeftDerivedFunctor_derivedTransitionPullbackComp O ψ φ)

/-- The natural isomorphism `Lf_ψ^* ⋙ Lf_φ^* ≅ Lf_{ψ ≫ φ}^*` given by the canonical
comparison. -/
@[stacks 0D6D "for the transition morphisms of a simplicial-site situation, as a natural
isomorphism"]
noncomputable def derivedTransitionCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.derivedTransitionPullback O ψ ⋙ S.derivedTransitionPullback O φ ≅
      S.derivedTransitionPullback O (ψ ≫ φ) :=
  have := S.isIso_derivedTransitionCompComparison O ψ φ
  asIso (S.derivedTransitionCompComparison O ψ φ)

/-- The underlying map of `derivedTransitionCompIso` is the canonical comparison
`derivedTransitionCompComparison`. -/
@[simp]
theorem derivedTransitionCompIso_hom {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.derivedTransitionCompIso O ψ φ).hom =
      S.derivedTransitionCompComparison O ψ φ :=
  rfl

end Derived

end CategoryTheory.SimplicialSiteSituation

end
