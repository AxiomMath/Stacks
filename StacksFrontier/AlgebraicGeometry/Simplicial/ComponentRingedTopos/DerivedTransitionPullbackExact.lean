module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The derived pullback along a flat simplex map is the degreewise one

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. A simplex map `φ : m ⟶ n` has a derived pullback
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback`, which is *defined* as the
total left derived functor of degreewise pullback followed by localization. When the transition
morphism of ringed topoi `f_φ` is flat, pullback of sheaves of modules along it is already exact
— Stacks 04JC, in this tree
`CategoryTheory.SimplicialSiteSituation.exactFunctor_transitionPullbackModules` — so nothing is
derived: the derived pullback is the functor `D(O_m) ⥤ D(O_n)` that the sheaf-level pullback
induces degreewise.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory`:
  the isomorphism `Lf_φ^* ≅ (f_φ^*).mapDerivedCategory`.
* `whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom` and
  `derivedTransitionPullbackIsoMapDerivedCategory_hom_app`: it is *the* canonical identification,
  namely the unique map of left derived functors carrying the comparison
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the degreewise functor back to the
  comparison `CategoryTheory.SimplicialSiteSituation.derivedTransitionComparison` of the derived
  pullback.

## Implementation notes

*Nothing generic is reproved here.* The identification and its universal property are
`Stacks.Homology.leftDerivedIsoMapDerivedCategory` and
`Stacks.Homology.whiskerLeft_leftDerivedIsoMapDerivedCategory_hom`: for an exact functor the
comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` is invertible, so the degreewise
functor is itself a left derived functor of degreewise pullback, and
`CategoryTheory.Functor.leftDerivedUnique` — uniqueness of total left derived functors — supplies
both the isomorphism and the statement that it carries one comparison to the other. Only the
exactness witnesses are specific to the simplicial situation.

*Why the statements carry `letI`s.* Flatness of the transition morphism is a proposition and not
a class, so the exactness of `f_φ^*` it yields cannot be found by instance search. Since
`CategoryTheory.Functor.mapDerivedCategory` takes exactness as instance arguments, the witnesses
must already be in scope in the *statement*; they are introduced there by `letI`, from the
flatness hypothesis and from nothing else. Preservation of finite colimits needs no hypothesis
at all: `f_φ^*` is a left adjoint.

*Why the proofs re-establish the exactness witnesses at `pullbackModules`.*
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` is a `def` whose ascribed type
spells the two module categories through
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf`, while
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback` spells them through
`AlgebraicGeometry.RingedTopos.Modules`. The two spellings agree by `rfl`, but instance search
does not cross the `def`, and the `Preadditive` and `Abelian` arguments hidden inside
`CategoryTheory.Functor.Additive` and `CategoryTheory.HasDerivedCategory` are data: a witness
found at one spelling need not be the term demanded at the other. The proofs therefore build the
generic isomorphism at `AlgebraicGeometry.RingedToposHom.pullbackModules`, where every instance
is found by plain search, and the result is accepted against the statement by the `rfl` above.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section Derived

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The derived pullback along a flat simplex map is the degreewise one.** For a flat
transition morphism the sheaf-level pullback `f_φ^*` is exact, so the functor it induces on the
unbounded derived categories is itself a left derived functor of degreewise pullback; by
uniqueness of total left derived functors it is `Lf_φ^*`.

The identification is pinned down by
`whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom`. -/
noncomputable def derivedTransitionPullbackIsoMapDerivedCategory {m n : SimplexCategory}
    (φ : m ⟶ n) (hφ : (S.transitionRingedToposHom O φ).IsFlat) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.Additive
    letI : PreservesFiniteLimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
    letI : PreservesFiniteColimits (S.transitionPullbackModules' O φ) :=
      AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
        (S.transitionRingedToposHom O φ)
    S.derivedTransitionPullback O φ ≅ (S.transitionPullbackModules' O φ).mapDerivedCategory := by
  letI : PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
  letI : PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O φ)
  exact Stacks.Homology.leftDerivedIsoMapDerivedCategory
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ)

/-- **The identification is the canonical one.** Whiskered along the localization,
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory` carries
the comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the degreewise functor
back to the comparison
`CategoryTheory.SimplicialSiteSituation.derivedTransitionComparison` of the derived pullback.
Together with `CategoryTheory.Functor.leftDerived_ext` this makes it the only map of functors
that does, so it is the canonical identification and not merely some isomorphism. -/
theorem whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom {m n : SimplexCategory}
    (φ : m ⟶ n) (hφ : (S.transitionRingedToposHom O φ).IsFlat) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.Additive
    letI : PreservesFiniteLimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
    letI : PreservesFiniteColimits (S.transitionPullbackModules' O φ) :=
      AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
        (S.transitionRingedToposHom O φ)
    Functor.whiskerLeft DerivedCategory.Qh
        (S.derivedTransitionPullbackIsoMapDerivedCategory O φ hφ).hom ≫
      (S.transitionPullbackModules' O φ).mapDerivedCategoryFactorsh.hom =
      S.derivedTransitionComparison O φ := by
  let : PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
  let : PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O φ)
  exact Stacks.Homology.whiskerLeft_leftDerivedIsoMapDerivedCategory_hom
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ)

/-- `whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom` evaluated at a complex of
modules on the degree-`m` component. -/
theorem derivedTransitionPullbackIsoMapDerivedCategory_hom_app {m n : SimplexCategory}
    (φ : m ⟶ n) (hφ : (S.transitionRingedToposHom O φ).IsFlat)
    (K : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ)) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.Additive
    letI : PreservesFiniteLimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
    letI : PreservesFiniteColimits (S.transitionPullbackModules' O φ) :=
      AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
        (S.transitionRingedToposHom O φ)
    (S.derivedTransitionPullbackIsoMapDerivedCategory O φ hφ).hom.app
          (DerivedCategory.Qh.obj K) ≫
        (S.transitionPullbackModules' O φ).mapDerivedCategoryFactorsh.hom.app K =
      (S.derivedTransitionComparison O φ).app K := by
  let : PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
  let : PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O φ)
  exact Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.derivedTransitionPullback O φ) (S.derivedTransitionComparison O φ) K

end Derived

end CategoryTheory.SimplicialSiteSituation

end
