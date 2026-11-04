module

public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionPullbackExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctorComp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The composition comparison of derived pullbacks along flat simplex maps is degreewise

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. When the transition morphisms of a composable pair `ψ`, `φ` of simplex maps and of
their composite are flat, each derived pullback `Lf^*` is the functor `f^*` induces degreewise
(`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory`). This
file shows that under these identifications the canonical comparison
`Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` is the comparison of degreewise functors induced by the
compositor `f_ψ^* ⋙ f_φ^* ≅ f_{ψ ≫ φ}^*` of pullbacks of sheaves of modules.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackFactors`: along a flat simplex
  map, the derived pullback composed with the localization of cochain complexes is isomorphic to
  degreewise pullback followed by the localization.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison_isInducedBy`: the
  composition comparison of derived pullbacks is induced, along the localizations of cochain
  complexes, by the compositor of pullbacks acting on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

/-- Pullback of sheaves of modules along a transition morphism is right exact, being a left
adjoint. -/
instance transitionPullbackModules_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
  AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
    (S.transitionRingedToposHom O φ)

section

variable {m n : SimplexCategory} (φ : m ⟶ n) (hφ : (S.transitionRingedToposHom O φ).IsFlat)

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))] in
include hφ in
/-- Pullback of sheaves of modules along a flat transition morphism is left exact (Stacks 04JC). -/
theorem transitionPullbackModules_preservesFiniteLimits :
    PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
  ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1

/-- The factorization of the derived pullback along a flat simplex map through the localization of
cochain complexes: it is degreewise pullback. -/
def derivedTransitionPullbackFactors :
    letI := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
    DerivedCategory.Q ⋙ S.derivedTransitionPullback O φ ≅
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  letI := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
  Stacks.Homology.leftDerivedFactors (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ)

end

variable {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
  (hψ : (S.transitionRingedToposHom O ψ).IsFlat) (hφ : (S.transitionRingedToposHom O φ).IsFlat)
  (hψφ : (S.transitionRingedToposHom O (ψ ≫ φ)).IsFlat)

/-- **The composition comparison of derived pullbacks along flat simplex maps is induced
degreewise by the compositor of pullbacks of sheaves of modules.** -/
theorem derivedTransitionCompComparison_isInducedBy :
    letI := S.transitionPullbackModules_preservesFiniteLimits O ψ hψ
    letI := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
    letI := S.transitionPullbackModules_preservesFiniteLimits O (ψ ≫ φ) hψφ
    NatTrans.IsInducedBy
      (Functor.compFactorization (S.derivedTransitionPullbackFactors O ψ hψ)
        (S.derivedTransitionPullbackFactors O φ hφ))
      (S.derivedTransitionPullbackFactors O (ψ ≫ φ) hψφ) (S.derivedTransitionCompComparison O ψ φ)
      (Functor.mapHomologicalComplexCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
        (ComplexShape.up ℤ)).hom :=
  let := S.transitionPullbackModules_preservesFiniteLimits O ψ hψ
  let := S.transitionPullbackModules_preservesFiniteLimits O φ hφ
  let := S.transitionPullbackModules_preservesFiniteLimits O (ψ ≫ φ) hψφ
  Stacks.Homology.isInducedBy_of_leftDerived_comp _ _ _ (S.transitionPullbackModulesCompIso O ψ
      φ).symm
    _ (S.derivedTransitionComparison O ψ) _ (S.derivedTransitionComparison O φ) _
    (S.derivedTransitionComparison O (ψ ≫ φ)) (S.derivedTransitionCompComparison O ψ φ)
    (fun J => (S.derivedTransitionComp_fac_app O ψ φ J).trans
      (congrArg (fun t => _ ≫ _ ≫ DerivedCategory.Qh.map (t.app J))
        (S.transitionPullbackHomotopyComp_eq O ψ φ)))

end CategoryTheory.SimplicialSiteSituation
