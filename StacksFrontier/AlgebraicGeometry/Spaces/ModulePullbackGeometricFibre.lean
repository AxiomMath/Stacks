module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative

/-!
# The geometric fibre of a pullback of modules, functorially

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `x̄` be a geometric point of `X`. Stacks 05VQ computes the stalk at `x̄` of a
pullback `f^*G` as the base change `𝒪_{X, x̄} ⊗_{𝒪_{Y, f ∘ x̄}} G_{f ∘ x̄}`;
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso` states that one module at a time.

This file records the same comparison as a **natural isomorphism of functors**, at the fibre of
the point of the small étale site of Stacks 04K0 rather than at the étale local ring — that is
the form in which a map of `𝒪_Y`-modules whose pullback is invertible on fibres can be
recognised as invertible on fibres. It is nothing but
`Stacks.Sheaves.StalkPullback.stalkFunctorIso` fed with the morphism of small étale ringed
topoi of Stacks 03G8 and the fibre comparison of Stacks 04K2, part (4) at the universe of the
structure rings, which is how `geometricModuleStalkPullbackIso` is built as well.

For a closed immersion the homomorphism of stalk rings along which the comparison extends
scalars is surjective; that is the transport of
`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion` along the
comparison of the stalk of the structure sheaf with the étale local ring.

## Main results

* `AlgebraicGeometry.Space.modulePullbackFiberIso`: Stacks 05VQ at the fibre of the point of
  the small étale site, as a natural isomorphism of functors on `𝒪_Y`-modules.
* `AlgebraicGeometry.Space.surjective_smallEtaleStalkPullbackRingMap_of_isClosedImmersion`:
  for a closed immersion the homomorphism of stalk rings is surjective.
* `Stacks.isIso_of_isIso_restrictScalars_map`, `Stacks.isIso_of_subsingleton` and
  `AlgebraicGeometry.Space.isIso_sheafModuleFiber_map_of_isIso_moduleStalkFunctor_map`:
  restriction of scalars reflects isomorphisms of modules, so the fibre functor of
  `Stacks.sheafModuleFiberOfCommRing` detects exactly what `Stacks.sheafModuleFiber` does.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkPullback

universe u

namespace Stacks

/-- Restriction of scalars along a ring homomorphism reflects isomorphisms: it changes neither
the underlying type of a module nor the underlying function of a map of modules. -/
theorem isIso_of_isIso_restrictScalars_map {R' S' : Type u} [Ring R'] [Ring S'] (φ : R' →+* S')
    {M N : ModuleCat.{u} S'} (g : M ⟶ N)
    (hg : IsIso ((ModuleCat.restrictScalars φ).map g)) : IsIso g := by
  rwa [ConcreteCategory.isIso_iff_bijective] at hg ⊢

/-- A map between two modules each of which has at most one element is an isomorphism: it is
injective because its source is a subsingleton and surjective because its target is. -/
theorem isIso_of_subsingleton {R' : Type u} [Ring R'] {M N : ModuleCat.{u} R'}
    (hM : Subsingleton M) (hN : Subsingleton N) (g : M ⟶ N) : IsIso g := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun a b _ ↦ hM.elim a b, fun n ↦ ⟨0, hN.elim _ _⟩⟩

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- **Stacks 05VQ at the fibre of the point of the small étale site, functorially.** Taking the
fibre at a geometric point `x̄` of `X` of the pullback of an `𝒪_Y`-module along `f` is the same
as taking the fibre at the image point and extending scalars along the homomorphism
`(𝒪_Y)_{f ∘ x̄} ⟶ (𝒪_X)_{x̄}` of stalk rings — naturally in the module.

This is `Stacks.Sheaves.StalkPullback.stalkFunctorIso` for the morphism of small étale ringed
topoi of Stacks 03G8, with the matched pair of points of Stacks 04K0 identified by
`AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`, Stacks 04K2, part (4) at the universe
of the structure rings. Objectwise, after transport to the étale local rings, it is
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`. -/
def modulePullbackFiberIso :
    modulePullback B S hS f ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O ≅
      Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f x) :=
  stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
    (etaleSitePoint B S hS X.1 x X.2)
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleInverseImageFiberIso B S hS f x)

/-- **The homomorphism of stalk rings of a closed immersion is surjective.** For a closed
immersion `f : X ⟶ Y` of algebraic spaces and a geometric point `x̄` of `X`, the homomorphism
`(𝒪_Y)_{f ∘ x̄} ⟶ (𝒪_X)_{x̄}` along which Stacks 05V5 extends scalars is surjective.

It is conjugate, by the comparisons of the stalks of the structure sheaves with the étale local
rings, to the homomorphism `𝒪_{Y, f ∘ x̄} ⟶ 𝒪_{X, x̄}` of Stacks 04NG, which is surjective for a
closed immersion. -/
theorem surjective_smallEtaleStalkPullbackRingMap_of_isClosedImmersion
    (hf : IsClosedImmersion B S hS f.hom) :
    Function.Surjective (smallEtaleStalkPullbackRingMap B S hS f x) := by
  intro b
  obtain ⟨a, ha⟩ := surjective_etaleLocalRingMap_of_isClosedImmersion B S hS f hf x
    (pointStalkRingEquiv B S hS X x b)
  refine ⟨(pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm a, ?_⟩
  refine (pointStalkRingEquiv B S hS X x).injective ?_
  rw [← ha, ← smallEtaleStalkPullbackEtaleLocalRingMap_eq B S hS f x]
  rfl

/-- The fibre functor of `Stacks.sheafModuleFiberOfCommRing` detects exactly what the fibre
functor of `Stacks.sheafModuleFiber` detects: the two differ by a restriction of scalars along
a ring isomorphism, which changes no underlying function. -/
theorem isIso_sheafModuleFiber_map_of_isIso_moduleStalkFunctor_map
    {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N)
    (hg : IsIso ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).map g)) :
    IsIso ((Stacks.sheafModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (structureRingSheaf B S hS X)).map g) :=
  Stacks.isIso_of_isIso_restrictScalars_map _ _ hg

end AlgebraicGeometry.Space

end
