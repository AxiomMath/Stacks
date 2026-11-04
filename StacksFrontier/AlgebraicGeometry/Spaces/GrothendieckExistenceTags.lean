module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.GrothendieckExistenceSpaces
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08BC and 08BE: registrations

In Situation 08B7 — `A` a Noetherian ring complete with respect to an ideal `I`,
`f : X ⟶ Spec A` a separated morphism of finite type of algebraic spaces, `𝓘 = I 𝒪_X` — this file
registers two results proved in `GrothendieckExistence.EquivalencePort`:

* `AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_auxiliaryIdeal`:
  **Stacks 08BC**.  For a quasi-coherent sheaf of ideals `𝓚 ⊆ 𝒪_X` and an object `(F_n)` of
  `Coh_{support proper over A}(X, 𝓘)`, if completion is an equivalence on every closed subspace
  cut out by `𝓚^e` (`e ≥ 1`) and there is a map `(F_n) ⟶ 𝓗^∧` from a coherent module `𝓗` with
  support proper over `A` whose kernel and cokernel are annihilated by a power of `𝓚`, then
  `(F_n)` is in the essential image of the completion functor of Stacks 08B8.
* `AlgebraicGeometry.Space.C1573.isEquivalence_completionFunctorProperOver`: **Stacks 08BE**,
  Grothendieck's existence theorem: the completion functor
  `Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, 𝓘)` of Stacks 08B8 is an
  equivalence of categories.

## References

* [Stacks Project, Tag 08BC](https://stacks.math.columbia.edu/tag/08BC)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
-/

@[expose] public section

add_to_stacks 08BC
  AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_auxiliaryIdeal

add_to_stacks 08BE AlgebraicGeometry.Space.C1573.isEquivalence_completionFunctorProperOver

end
