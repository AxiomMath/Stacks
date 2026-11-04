module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.Homology.KFlat.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback is braided for the tensor product sheaf

Let `f : X ⟶ Y` be a morphism of ringed spaces.  `Mod(𝒪_Z)` carries the monoidal structure
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is the tensor product sheaf
`Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf` of [Stacks, Tag 01CA] definitionally, and it
is symmetric by `SheafOfModules.symmetricCategorySheafTensor`.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal` makes `f^*` a monoidal
functor for that structure, with the comparison `c_{A,B} : f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of
[Stacks, Tag 01CD] as its oplax tensorator.  This file adds the remaining compatibility: `c`
commutes with the symmetry constraint, so `f^*` is a *braided* monoidal functor for the tensor
product sheaf.  That is what makes `f^*` act on sheaves of algebras as a monoidal functor rather
than merely as a functor, the monoidal structure of `CategoryTheory.Mon` needing the braiding.

## Main definitions

* `Stacks.PullbackSheafTensor.laxBraided` and `braided`: **`f^*` is a braided monoidal functor**
  for the monoidal structure whose tensor product is the tensor product sheaf, seated on
  `Stacks.PullbackSheafTensor.monoidal`.
* `Stacks.PullbackSheafTensor.liftLaxBraided`: the same lax braided structure, with its type
  ascribed at the spelling of the functor and of the ring sheaf that the lift to complexes asks
  for.

## Main results

* `Stacks.PullbackSheafTensor.braiding_eq_strict`: **the two monoidal structures on `Mod(𝒪_Z)`
  whose tensor product is the tensor product sheaf have the same braiding**, with
  `braiding_hom_eq_strict` the same statement at the `β_` spelling.
* `Stacks.PullbackSheafTensor.sheafTensorComparison_braiding`: **the comparison of
  [Stacks, Tag 01CD] commutes with the braiding of the re-seated structure.**
* `Stacks.PullbackSheafTensor.monoidal_mu`: the lax tensorator of
  `Stacks.PullbackSheafTensor.monoidal` is the inverse of the comparison, by construction.

## Implementation notes

**Where the content is.**  The braiding compatibility itself is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, proved on local pure tensors
for `Stacks.PullbackGradedAlgebra.monoidalCategory`.  Nothing is recomputed here: the two
structures are shown to have the same braiding, and the compatibility is transported across.
This is the exact analogue of `Stacks.PullbackSheafTensor.sheafTensorComparison_associator`,
which transports the associativity coherence the same way.

**Why the braiding needs a transport and the associator does not.**  The two structures have the
same tensor product on objects, the same unit and the same associator by `rfl`
(`Stacks.RingedSpace.associator_eq_strict`), but *not* the same braiding by `rfl`: the braiding
of the re-seated structure is produced by `CategoryTheory.BraidedCategory.ofFullyFaithful` along
the identity functor, hence is a `CategoryTheory.Functor.preimage` and not the conjugate it is
equal to.  `CategoryTheory.MonoidalCategory.reseatSymmetric_braiding` identifies it with that
conjugate, and the conjugate is the braiding of the other structure
(`Stacks.SheafOfModules.Strict.braiding`) definitionally, so `braiding_eq_strict` is that lemma
with its instances named.

**The pinned restatements.**  `braiding_hom_eq_strict` is `braiding_eq_strict` written at exactly
the spelling a goal presents — the braiding of the local instance `symmetricSheafTensor`, printed
`β_` — and that is the form `rw` can fire; the general statement, whose braided structure is
named by `@`-application, matches no goal.  `monoidal_mu` does the same for the lax tensorator of
`Stacks.PullbackSheafTensor.monoidal`, mirroring
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal_mu`.

**Neither structure is left to instance synthesis.**  `Mod(𝒪_Z)` carries the re-seated structure
and `Stacks.PullbackGradedAlgebra.monoidalCategory` at once, and the latter is stated over
`Stacks.RingedSpace.structureRingSheaf`, which instance search cannot recover.  The re-seated one
is named by the local instances `monoidalSheafTensor` (of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal`) and
`symmetricSheafTensor`, so that `⊗` and `β_` refer to it, and every statement mentioning the
other one names it by `@`-application.  Like
`Stacks.PullbackTensorCoherence.pullbackComparisonBraided`, `braided` and `laxBraided` are
deliberately not global instances: there is a second `CategoryTheory.Functor.Monoidal` structure
on the same functor, at a second monoidal structure on `Mod(𝒪_Z)`, and registering both would
make instance search choose between them silently.

**Why `liftLaxBraided` exists.**  `laxBraided` is stated for
`Stacks.RingedSpace.pullbackFunctor` over `Stacks.RingedSpace.structureRingSheaf`, and the lift of
`f^*` to complexes asks for a structure on `StacksDraft.KFlat.modulePullback` over
`Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same functor between the same
categories and the passage is a conversion check, not a syntactic match, so the structure has to
be offered with its type ascribed at the second spelling — as
`Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal` already does for the monoidal structure.
The braiding at that spelling is
`Stacks.Cohomology.DerivedPullbackTensor.symmetricModules`, which is
`SheafOfModules.symmetricCategorySheafTensor Z.sheaf`, so only the spelling is converted and the
braiding is unchanged.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.RingedSpace

universe u

namespace Stacks.PullbackSheafTensor

attribute [local instance] monoidalSheafTensor

/-- The symmetry constraint of [Stacks, Tag 01CA] on `Mod(𝒪_Z)`, for the monoidal structure whose
tensor product is the tensor product sheaf, named so that the notation `β_` below refers to it and
not to the braiding of `Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
@[instance_reducible] local instance symmetricSheafTensor (Z : RingedSpace.{u, u}) :
    @SymmetricCategory (_root_.SheafOfModules.{u} (structureRingSheaf Z)) _
      (monoidalSheafTensor Z) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor Z.sheaf

/-! ### The two monoidal structures have the same braiding -/

/-- **The two monoidal structures on `Mod(𝒪_Z)` whose tensor product is the tensor product sheaf
of [Stacks, Tag 01CA] have the same braiding.**  The braiding of the re-seated structure is the
braiding of the localized structure conjugated by the re-seating isomorphism, by
`CategoryTheory.MonoidalCategory.reseatSymmetric_braiding`, and that conjugate is the braiding of
`Stacks.PullbackGradedAlgebra.monoidalCategory` definitionally. -/
theorem braiding_eq_strict (Z : RingedSpace.{u, u})
    (A B : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    (@BraidedCategory.braiding _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf)
        (_root_.SheafOfModules.symmetricCategorySheafTensor Z.sheaf).toBraidedCategory A B).hom =
      (@BraidedCategory.braiding _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory Z)
        (Stacks.PullbackTensorCoherence.braidedCategory Z) A B).hom :=
  @CategoryTheory.MonoidalCategory.reseatSymmetric_braiding
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) _
    (_root_.SheafOfModules.monoidalCategory Z.sheaf) _ _
    (_root_.SheafOfModules.symmetricCategory Z.sheaf)
    (_root_.SheafOfModules.sheafTensorNatIso Z.sheaf) (_root_.SheafOfModules.unitIso Z.sheaf) A B

/-- `braiding_eq_strict` restated at the `β_` spelling, i.e. with the braided structure left to
the local instance `symmetricSheafTensor` rather than named by `@`-application.  This is the form
`rw` can fire on a goal, the general statement matching no goal. -/
theorem braiding_hom_eq_strict (Z : RingedSpace.{u, u})
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Z)) :
    (β_ A B).hom =
      (@BraidedCategory.braiding _ _ (Stacks.PullbackGradedAlgebra.monoidalCategory Z)
        (Stacks.PullbackTensorCoherence.braidedCategory Z) A B).hom :=
  braiding_eq_strict Z A B

/-! ### The comparison of Tag 01CD commutes with the braiding -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of [Stacks, Tag 01CD] commutes with the braiding of the re-seated
structure.**  The two structures have the same braiding, so the same compatibility for
`Stacks.PullbackGradedAlgebra.monoidalCategory` —
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, where it is proved on local
pure tensors — becomes this one once the two braidings are moved across. -/
theorem sheafTensorComparison_braiding
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).map (β_ A B).hom ≫ sheafTensorComparison f B A =
      sheafTensorComparison f A B ≫
        (β_ ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)).hom := by
  rw [braiding_hom_eq_strict, braiding_hom_eq_strict]
  exact Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding f A B

/-! ### The pullback as a braided monoidal functor -/

/-- The lax tensorator of `Stacks.PullbackSheafTensor.monoidal` is the inverse of the comparison
of [Stacks, Tag 01CD], by construction. -/
theorem monoidal_mu (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    Functor.LaxMonoidal.μ (self := (monoidal f).toLaxMonoidal) (pullbackFunctor f) A B =
      inv (sheafTensorComparison f A B) :=
  rfl

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a lax braided
functor** for the monoidal structure whose tensor product is the tensor product sheaf, seated on
`Stacks.PullbackSheafTensor.monoidal`, whose lax tensorator is the inverse of the comparison of
[Stacks, Tag 01CD]. -/
@[instance_reducible]
noncomputable def laxBraided :
    letI := Stacks.PullbackSheafTensor.monoidal f
    (pullbackFunctor f).LaxBraided :=
  letI := Stacks.PullbackSheafTensor.monoidal f
  { toLaxMonoidal := (monoidal f).toLaxMonoidal
    braided := fun M N ↦ by
      rw [monoidal_mu, monoidal_mu, IsIso.eq_comp_inv, Category.assoc,
        sheafTensorComparison_braiding, IsIso.inv_hom_id_assoc] }

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a braided monoidal
functor** for the monoidal structure whose tensor product is the tensor product sheaf.
Deliberately **not** a global instance, for the reason recorded in the implementation notes. -/
@[instance_reducible, ega "0 4.3.4" "partial", ega "IV 10.2.8" "more general"]
noncomputable def braided : (pullbackFunctor f).Braided :=
  letI := Stacks.PullbackSheafTensor.monoidal f
  letI := laxBraided f
  { toMonoidal := monoidal f
    braided := Functor.LaxBraided.braided }

/-! ### The lax braided structure at the spelling the lift to complexes asks for -/

section Lift

/-- The monoidal structure whose tensor product is the tensor product sheaf, at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the ring sheaf: that is the spelling the lift
of `f^*` to complexes is stated at, and instance search does not pass between the two spellings on
its own. -/
@[instance_reducible] local instance monoidalTensorRingSheaf (Z : RingedSpace.{u, u}) :
    MonoidalCategory
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf

/-- The symmetry constraint at the same spelling; it is
`Stacks.Cohomology.DerivedPullbackTensor.symmetricModules`, the braiding the lift to complexes
uses. -/
@[instance_reducible] local instance symmetricTensorRingSheaf (Z : RingedSpace.{u, u}) :
    @SymmetricCategory
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) _
      (monoidalTensorRingSheaf Z) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor Z.sheaf

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-- **`laxBraided` with its type ascribed at the spelling of the functor and of the ring sheaf
that the lift of `f^*` to complexes asks for.**  The data are those of `laxBraided` and nothing
else; only the type is rewritten, exactly as
`Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal` rewrites the type of
`Stacks.PullbackSheafTensor.monoidal`. -/
@[instance_reducible]
noncomputable def liftLaxBraided :
    letI : (StacksDraft.KFlat.modulePullback f).Monoidal := Stacks.PullbackSheafTensor.monoidal f
    (StacksDraft.KFlat.modulePullback f).LaxBraided :=
  Stacks.PullbackSheafTensor.laxBraided f

end Lift

end Stacks.PullbackSheafTensor

end
