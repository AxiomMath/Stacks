module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.PowerSystemComparison

/-!
# The pullback of a system of tensor powers

Let `f : X ⟶ Y` be a morphism of ringed spaces. A `Stacks.Monoidal.PowerSystem` on `Mod(𝒪_Y)` is
an object `gen`, a family `obj : ℕ → Mod(𝒪_Y)` of candidate tensor powers of it, an
identification `obj 0 ≅ 𝒪_Y` and successor comparisons `obj n ⊗ gen ≅ obj (n + 1)`. This file
carries such a system along `f^*`.

**No coherence is needed, and that is the point.** A power system carries no axiom: it is pure
data. So the two chosen comparisons of [Stacks, Tag 01CD] and of the units —
`Stacks.PullbackSheafTensor.sheafTensorComparisonIso` and `sheafTensorUnitIso`, both
isomorphisms and neither a `Nonempty` — suffice to transport one, with no appeal to the monoidal
structure of `f^*`. Everything a power system is *used* for is then available on the image:
`Stacks.Monoidal.PowerSystem.mulIso` and its associativity
`Stacks.Monoidal.PowerSystem.mulIso_assoc`, and the comparison
`Stacks.Monoidal.PowerSystem.compare` of two systems along an isomorphism of their generators
together with its multiplicativity `Stacks.Monoidal.PowerSystem.compare_mul`, are theorems about
an arbitrary power system in an arbitrary monoidal category.

That is what makes a *coherent* family of identifications of the pulled-back pieces reachable
from a single chosen identification in degree one: the choice enters once, as the generator
comparison `β` handed to `compare`, and every higher degree is `β` tensored with itself through
the successor comparisons of the two systems.

## Main definitions

* `Stacks.PullbackSheafTensor.monoidalModules`: the monoidal structure of [Stacks, Tag 01CA] on
  the modules of a ringed space, named at the `structureSheafRing` spelling of the structure
  sheaf of rings.
* `Stacks.PullbackSheafTensor.pullbackPowerSystem`: **the pullback of a power system.**

## Main results

* `Stacks.PullbackSheafTensor.pullbackPowerSystem_gen`,
  `pullbackPowerSystem_obj`, `pullbackPowerSystem_objZeroIso` and `pullbackPowerSystem_succIso`:
  the data of the pulled-back system, so that a consumer never unfolds it.

## Implementation notes

**Why a second name for the monoidal structure.**
`Stacks.PullbackSheafTensor.monoidalSheafTensor` is the same monoidal structure, named at
`Stacks.RingedSpace.structureRingSheaf Z`. That spelling and `structureSheafRing Z` are
definitionally equal, but a goal is keyed into the instance discrimination tree with the head
symbol it is written with, so an instance registered at one of the two is never retrieved at the
other: with only `monoidalSheafTensor` activated, every occurrence of `⊗` on
`SheafOfModules (structureSheafRing Z)` fails to synthesise `MonoidalCategory`.
`Stacks.Divisors.negativeTwist` and `Stacks.Divisors.idealSheafOfModules` are typed at
`structureSheafRing`, so that is the key a statement about ideal sheaves needs, and
`monoidalModules` is the one declaration that supplies it. It is deliberately **not** a global
instance, for the reason `Stacks.PullbackSheafTensor.monoidal` is not: a second monoidal
structure, `Stacks.PullbackGradedAlgebra.monoidalCategory`, lives on the same category, and
registering both would make instance search choose between them silently. A consumer activates
it with `attribute [local instance]`.

**No `stacks` attribute.** Tag 01CA is carried by the monoidal structure and Tag 01CD by
`Stacks.RingedSpace.comparison`; carrying a power system along the latter is a construction on
those, not a further tag.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — the comparison
  `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`.
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the tensor powers of
  an invertible sheaf of modules.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.Monoidal (PowerSystem)

universe u

namespace Stacks.PullbackSheafTensor

/-- **The monoidal structure of [Stacks, Tag 01CA] on the modules of a ringed space**, named at
the `structureSheafRing` spelling of the structure sheaf of rings — the spelling
`Stacks.Divisors.negativeTwist` is typed at. Not a global instance; see the implementation
notes. -/
@[instance_reducible]
public def monoidalModules (Z : RingedSpace.{u, u}) :
    MonoidalCategory (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.monoidalCategorySheafTensor Z.sheaf

attribute [local instance] monoidalModules

/-- **The pullback of a system of tensor powers along a morphism of ringed spaces.** The pieces
and the generator are pulled back, the zeroth-power identification is the pullback of the old
one followed by the comparison `f^*𝒪_Y ≅ 𝒪_X`, and the successor comparison is the comparison of
[Stacks, Tag 01CD] followed by the pullback of the old one. Both comparisons are chosen
isomorphisms, so the resulting system involves no choice beyond the one in the system being
pulled back. -/
public def pullbackPowerSystem {A B : RingedSpace.{u, u}} (f : A ⟶ B)
    (S : PowerSystem (SheafOfModules.{u} (structureSheafRing B))) :
    PowerSystem (SheafOfModules.{u} (structureSheafRing A)) where
  gen := (Stacks.RingedSpace.pullbackFunctor f).obj S.gen
  obj n := (Stacks.RingedSpace.pullbackFunctor f).obj (S.obj n)
  objZeroIso :=
    (Stacks.RingedSpace.pullbackFunctor f).mapIso S.objZeroIso ≪≫ sheafTensorUnitIso f
  succIso n := (sheafTensorComparisonIso f (S.obj n) S.gen).symm ≪≫
    (Stacks.RingedSpace.pullbackFunctor f).mapIso (S.succIso n)

@[simp]
public theorem pullbackPowerSystem_gen {A B : RingedSpace.{u, u}} (f : A ⟶ B)
    (S : PowerSystem (SheafOfModules.{u} (structureSheafRing B))) :
    (pullbackPowerSystem f S).gen = (Stacks.RingedSpace.pullbackFunctor f).obj S.gen := rfl

@[simp]
public theorem pullbackPowerSystem_obj {A B : RingedSpace.{u, u}} (f : A ⟶ B)
    (S : PowerSystem (SheafOfModules.{u} (structureSheafRing B))) (n : ℕ) :
    (pullbackPowerSystem f S).obj n =
      (Stacks.RingedSpace.pullbackFunctor f).obj (S.obj n) := rfl

public theorem pullbackPowerSystem_objZeroIso {A B : RingedSpace.{u, u}} (f : A ⟶ B)
    (S : PowerSystem (SheafOfModules.{u} (structureSheafRing B))) :
    (pullbackPowerSystem f S).objZeroIso =
      (Stacks.RingedSpace.pullbackFunctor f).mapIso S.objZeroIso ≪≫
        sheafTensorUnitIso f := rfl

public theorem pullbackPowerSystem_succIso {A B : RingedSpace.{u, u}} (f : A ⟶ B)
    (S : PowerSystem (SheafOfModules.{u} (structureSheafRing B))) (n : ℕ) :
    (pullbackPowerSystem f S).succIso n =
      (sheafTensorComparisonIso f (S.obj n) S.gen).symm ≪≫
        (Stacks.RingedSpace.pullbackFunctor f).mapIso (S.succIso n) := rfl

end Stacks.PullbackSheafTensor

end
