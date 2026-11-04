module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraMonoidalAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of a sheaf of graded algebras along a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of ringed spaces. The pullback of sheaves of modules along `f` is
strong monoidal for the tensor product of Tag 01CA
(`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`) and it is left adjoint to the
pushforward (`Stacks.RingedSpace.pullbackAdjunction`). Therefore the pushforward is **lax**
monoidal, and the transport of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality` applies to it: the
direct images `f_*(A_n)` of the homogeneous pieces of a sheaf of graded `𝒪_X`-algebras `A`
assemble into a sheaf of graded `𝒪_Y`-algebras `f_*A`.

The two transports are then adjoint, by
`SheafOfModules.GradedAlgebra.transportAdjunction`: homomorphisms of sheaves of graded algebras
`f^*B ⟶ A` correspond to homomorphisms `B ⟶ f_*A`, naturally in both arguments.

## Main definitions

* `Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal`: **the pushforward of sheaves
  of modules along a morphism of ringed spaces is lax monoidal**, as the right adjoint of a
  strong monoidal functor.
* `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra`: **the sheaf of graded algebras
  `f_*A`**, with homogeneous pieces the direct images `f_*(A_n)`.
* `Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction`: the adjunction
  between pullback and pushforward of sheaves of graded algebras.

## Main results

* `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_piece`: the pieces of `f_*A`.
* `Stacks.PushforwardGradedAlgebra.pullbackGradedAlgebra_eq_transport`: the pullback of a sheaf
  of graded algebras of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra` is
  the transport along the monoidal pullback functor.

## Implementation notes

**Why the lax monoidal structure on the pushforward is not stated at the presheaf level.**
`PresheafOfModules.pushforwardLaxMonoidal` already equips the presheaf-level pushforward with a
lax monoidal structure, for an arbitrary functor of sites. That structure is for the objectwise
tensor product of presheaves of modules, which is only isomorphic to the tensor product sheaf,
so it cannot be consumed by `SheafOfModules.GradedAlgebra.mulSheaf`. Reading it off the
adjunction instead keeps everything on the sheaf side of the localization, where the section
formulas of Tag 01CA live.

**The compatibility of the adjunction with the two monoidal structures is automatic.**
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal` is accompanied by an instance of
`CategoryTheory.Adjunction.IsMonoidal`, which is the hypothesis
`SheafOfModules.GradedAlgebra.transportAdjunction` takes; no compatibility has to be checked
here.

**No new `@[stacks]` attribute.** A morphism of ringed spaces is a particular morphism of
ringed topoi, so the statements here are instances of Tag 0FQX rather than the tag itself; the
tag is carried by `SheafOfModules.GradedAlgebra.transport`,
`SheafOfModules.GradedAlgebra.transportFunctor` and
`SheafOfModules.GradedAlgebra.transportAdjunction`, which state it for an arbitrary monoidal
adjunction between categories of sheaves of modules on sites.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096) — the adjunction
  between pullback and pushforward of sheaves of modules on ringed spaces.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open Stacks.PullbackGradedAlgebra SheafOfModules.GradedAlgebra

open scoped TensorProduct

universe u

namespace Stacks.PushforwardGradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal

/-- **The pushforward of sheaves of modules along a morphism of ringed spaces is a lax monoidal
functor for the monoidal structure of Tag 01CA.** It is the right adjoint of the strong monoidal
pullback functor, and `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` makes every right
adjoint of an oplax monoidal functor lax monoidal. -/
@[instance_reducible]
noncomputable def pushforwardFunctorLaxMonoidal : (pushforwardFunctor f).LaxMonoidal :=
  (pullbackAdjunction f).rightAdjointLaxMonoidal

attribute [local instance] pushforwardFunctorLaxMonoidal

/-- **The pushforward of a sheaf of graded algebras along a morphism of ringed spaces is a sheaf
of graded algebras**, with homogeneous pieces the direct images `f_*(A_n)`. -/
noncomputable def pushforwardGradedAlgebra
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y) :=
  transport (Osharp := X.sheaf) (Psharp := Y.sheaf) (pushforwardFunctor f) A
    (structureSheafRing X).property (structureSheafRing Y).property

/-- The homogeneous pieces of `f_*A` are the direct images of those of `A`. -/
theorem pushforwardGradedAlgebra_piece
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)) (n : ℤ) :
    (pushforwardGradedAlgebra f A).piece n = (pushforwardFunctor f).obj (A.piece n) :=
  rfl

/-- **The pullback of a sheaf of graded algebras along a morphism of ringed spaces is the
transport along the monoidal pullback functor.** -/
theorem pullbackGradedAlgebra_eq_transport
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) :
    pullbackGradedAlgebra f A (structureSheafRing Y).property =
      transport (Osharp := Y.sheaf) (Psharp := X.sheaf) (pullbackFunctor f) A
        (structureSheafRing Y).property (structureSheafRing X).property :=
  rfl

/-- **Pullback of sheaves of graded algebras is left adjoint to pushforward**, for a morphism of
ringed spaces. The right adjoint sends `A` to `f_*A`. -/
noncomputable def pullbackPushforwardGradedAlgebraAdjunction :
    transportFunctor (Osharp := Y.sheaf) (Psharp := X.sheaf) (pullbackFunctor f)
        (structureSheafRing Y).property (structureSheafRing X).property ⊣
      transportFunctor (Osharp := X.sheaf) (Psharp := Y.sheaf) (pushforwardFunctor f)
        (structureSheafRing X).property (structureSheafRing Y).property :=
  transportAdjunction (Osharp := X.sheaf) (Psharp := Y.sheaf) (pullbackAdjunction f)
    (structureSheafRing X).property (structureSheafRing Y).property

end Stacks.PushforwardGradedAlgebra

end
