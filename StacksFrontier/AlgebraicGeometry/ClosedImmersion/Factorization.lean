module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Mono
public import StacksCore.Tactic.StacksAttribute

/-!
# Factorizations through a closed immersion are unique

A morphism of locally ringed spaces admits at most one factorization through a closed
immersion.

## Main results

* `isLocallySurjective_c`: the structure-sheaf component `i.c` of a closed immersion `i` of
  ringed spaces is a locally surjective map of presheaves of commutative rings.
* `mono_of_isClosedImmersion`: a closed immersion of locally ringed spaces is a monomorphism.
* `subsingleton_factorizations`: a morphism of locally ringed spaces factors through a closed
  immersion in at most one way.

## Implementation notes

The definition of a closed immersion states surjectivity of the structure-sheaf map as an
`Epi` in the category of sheaves of modules, which implies local surjectivity of the underlying
morphism of presheaves of abelian groups. Local surjectivity of the
`CommRingCat`-valued component `i.c` follows by a change of target category: the underlying
function of `(unitToPushforwardObjUnit (structureSheafHom i)).val.app V` is that of
`i.c.app V`, so the two image sieves agree.

## References

* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- The structure-sheaf component `i.c` of a closed immersion `i` of ringed spaces is a locally
surjective map of presheaves of commutative rings. -/
theorem isLocallySurjective_c {X Z : RingedSpace.{u, u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) i.hom.c := by
  have h := isLocallySurjective_structureSheafHom i
  refine ⟨fun {V} s ↦ ?_⟩
  exact h.imageSieve_mem s

/-- A closed immersion of locally ringed spaces is a monomorphism. -/
instance mono_of_isClosedImmersion {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i.toShHom] : Mono i :=
  mono_of_isClosedEmbedding_of_isLocallySurjective i
    (IsClosedImmersion.isClosedEmbedding (i := i.toShHom))
    (isLocallySurjective_c i.toShHom)

/-- A factorization of a morphism of locally ringed spaces through a closed immersion, when it
exists, is unique. -/
theorem subsingleton_factorizations {X Y Z : LocallyRingedSpace.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i.toShHom] (f : Y ⟶ X) :
    Subsingleton {g : Y ⟶ Z // g ≫ i = f} :=
  subsingleton_factorization i f

end Stacks.ClosedImmersion

end
