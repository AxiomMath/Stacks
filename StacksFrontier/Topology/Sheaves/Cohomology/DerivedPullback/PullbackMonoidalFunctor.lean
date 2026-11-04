module

public import StacksFrontier.CategoryTheory.Monoidal.CoreMonoidalOplaxUnitality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonAssociator
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorLeftUnitor

/-!
# Derived pullback is a monoidal functor, [Stacks, Tag 079U]

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces.  The comparison of
[Stacks, Tag 079U] and the unit comparison make the derived pullback `Lf^*` a
`CategoryTheory.Functor.CoreMonoidal` functor for the monoidal structure of [Stacks, Tag 0FPT],
and hence a `CategoryTheory.Functor.Monoidal` one.

Nothing is assumed about `f` beyond its being a morphism of ringed spaces: no flatness, no
finiteness, no quasi-coherence.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCoreMonoidal`: the
  `CategoryTheory.Functor.CoreMonoidal` structure.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal`: `Lf^*` is a monoidal
  functor for the derived tensor product of [Stacks, Tag 06YU].

## Implementation notes

*Why `CategoryTheory.Functor.CoreMonoidal.mk'` and not the structure itself.*  `mk'` states its
associativity clause on the **inverse** of the tensorator, which is the direction
[Stacks, Tag 079U] presents the comparison in, so
`derivedPullbackTensorIso_associator` is that clause verbatim up to the two spelling lemmas
`Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left` and `…_id_right`, which
identify the uncurried bifunctor on a morphism that is an identity in one factor with the
corresponding whiskering.  The structure's own `associativity` field is stated on the `hom` and
would have to be obtained by inverting a six-factor equation; `mk'` does exactly that
inversion internally.  The price is that `mk'` wants the two unitality clauses on the inverse
too, and that is `Stacks.CategoryTheory.Monoidal.oplax_left_unitality_of_hom` and
`…oplax_right_unitality_of_hom`.

*The instances are passed explicitly.*
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is a `def`, and introducing it
with `letI` does not make instance search find it at the
`DerivedCategory (SheafOfModules (structureSheafRing Z))` spelling that
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is stated at — the search
fails on `MonoidalCategoryStruct` even with the structure in the local context.  Every statement
below therefore applies `@Functor.CoreMonoidal` with both monoidal structures supplied
positionally.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

-- `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf` are in the list because the canonical tensor
-- product's ring sheaf is `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`, whose argument has
-- type `TopCat.Sheaf CommRingCat Z.carrier` while `Tensor.ringSheaf` asks for a
-- `CategoryTheory.Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat`.  Without them the
-- goals below are ill-typed at `implicit` transparency, and `dsimp` and `rw` report no progress on
-- a pattern the goal visibly contains.
-- `Tensor.ringSheaf` joins them for the same reason: the mismatch is inside its application, so
-- the two sides are recognised as the same type only once it too unfolds.  `structureSheafRing` is
-- *not* in the list: it is globally `@[instance_reducible]`, which already unfolds at `implicit`
-- transparency, and `[implicit_reducible]` is the strictly higher status, so naming it here would
-- move it off `instances` transparency and hide it from typeclass *search*.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit derivedPullbackUnitIso
  uncurry_map_id_left uncurry_map_id_right)

/-- **The comparison of [Stacks, Tag 079U] is natural in the first variable**, with the
whiskering of the monoidal structure of [Stacks, Tag 0FPT]. -/
theorem derivedPullbackTensorIso_hom_app_naturality_left
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (g : A ⟶ B)
    (A' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackTensorIso f).hom.app (A, A') ≫
        canonicalWhiskerRight X.sheaf ((derivedPullback f).map g) ((derivedPullback f).obj A') =
      (derivedPullback f).map (canonicalWhiskerRight Y.sheaf g A') ≫
        (derivedPullbackTensorIso f).hom.app (B, A') := by
  have h := (derivedPullbackTensorIso f).hom.naturality
    ((g ×ₘ 𝟙 A') : ((A, A') : _ × _) ⟶ (B, A'))
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rw [CategoryTheory.Functor.map_id, uncurry_map_id_right, uncurry_map_id_right] at h
  exact h.symm

/-- **The comparison of [Stacks, Tag 079U] is natural in the second variable**, with the
whiskering of the monoidal structure of [Stacks, Tag 0FPT]. -/
theorem derivedPullbackTensorIso_hom_app_naturality_right
    (A' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (g : A ⟶ B) :
    (derivedPullbackTensorIso f).hom.app (A', A) ≫
        canonicalWhiskerLeft X.sheaf ((derivedPullback f).obj A') ((derivedPullback f).map g) =
      (derivedPullback f).map (canonicalWhiskerLeft Y.sheaf A' g) ≫
        (derivedPullbackTensorIso f).hom.app (A', B) := by
  have h := (derivedPullbackTensorIso f).hom.naturality
    ((𝟙 A' ×ₘ g) : ((A', A) : _ × _) ⟶ (A', B))
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rw [CategoryTheory.Functor.map_id, uncurry_map_id_left, uncurry_map_id_left] at h
  exact h.symm

/-- **The associativity coherence of [Stacks, Tag 079U]**, with its two whiskerings written as
`Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerRight` and `…canonicalWhiskerLeft`, the
`▷` and `◁` of the monoidal structure of [Stacks, Tag 0FPT]. -/
theorem derivedPullbackTensorIso_associator_whiskered
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (derivedPullbackTensorIso f).hom.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj (A, B), C) ≫
        canonicalWhiskerRight X.sheaf ((derivedPullbackTensorIso f).hom.app (A, B))
            ((derivedPullback f).obj C) ≫
          canonicalAssociatorHom X.sheaf ((derivedPullback f).obj A)
            ((derivedPullback f).obj B) ((derivedPullback f).obj C) =
      (derivedPullback f).map (canonicalAssociatorHom Y.sheaf A B C) ≫
        (derivedPullbackTensorIso f).hom.app
            (A, (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj (B, C)) ≫
          canonicalWhiskerLeft X.sheaf ((derivedPullback f).obj A)
            ((derivedPullbackTensorIso f).hom.app (B, C)) := by
  have h := derivedPullbackTensorIso_associator f A B C
  rw [uncurry_map_id_right, uncurry_map_id_left] at h
  exact h

/-- **Derived pullback is a monoidal functor for the derived tensor product of
[Stacks, Tag 06YU]**, as a `CategoryTheory.Functor.CoreMonoidal` structure: the unit comparison
is `Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso` and the tensorator is the
comparison of [Stacks, Tag 079U], both inverted so as to point the way a lax monoidal structure
does. -/
def derivedPullbackCoreMonoidal :
    @Functor.CoreMonoidal _ _ (canonicalDerivedMonoidal Y.sheaf) _ _
      (canonicalDerivedMonoidal X.sheaf) (derivedPullback f) :=
  @Functor.CoreMonoidal.mk' _ _ (canonicalDerivedMonoidal Y.sheaf) _ _
    (canonicalDerivedMonoidal X.sheaf) (derivedPullback f)
    (derivedPullbackUnitIso f).symm
    (fun A B => ((derivedPullbackTensorIso f).app (A, B)).symm)
    (fun g A' => derivedPullbackTensorIso_hom_app_naturality_left f g A')
    (fun A' g => derivedPullbackTensorIso_hom_app_naturality_right f A' g)
    (fun A B C => derivedPullbackTensorIso_associator_whiskered f A B C)
    (fun A => @Stacks.CategoryTheory.Monoidal.oplax_left_unitality_of_hom
      _ _ (canonicalDerivedMonoidal Y.sheaf) _ _ (canonicalDerivedMonoidal X.sheaf)
      (derivedPullback f) (derivedPullbackUnitIso f).symm
      (fun P Q => ((derivedPullbackTensorIso f).app (P, Q)).symm) A
      (derivedPullbackTensorIso_leftUnitor f A))
    (fun A => @Stacks.CategoryTheory.Monoidal.oplax_right_unitality_of_hom
      _ _ (canonicalDerivedMonoidal Y.sheaf) _ _ (canonicalDerivedMonoidal X.sheaf)
      (derivedPullback f) (derivedPullbackUnitIso f).symm
      (fun P Q => ((derivedPullbackTensorIso f).app (P, Q)).symm) A
      (rightUnitorCoherence_canonical f A))

/-- **[Stacks, Tag 079U] as a monoidal functor structure**: `Lf^*` is monoidal for the derived
tensor product of [Stacks, Tag 06YU], with no hypothesis on `f` beyond its being a morphism of
ringed spaces.  This is `derivedPullbackCoreMonoidal` read through
`CategoryTheory.Functor.CoreMonoidal.toMonoidal`. -/
@[instance_reducible]
def derivedPullbackMonoidal :
    @Functor.Monoidal _ _ (canonicalDerivedMonoidal Y.sheaf) _ _
      (canonicalDerivedMonoidal X.sheaf) (derivedPullback f) :=
  @Functor.CoreMonoidal.toMonoidal _ _ (canonicalDerivedMonoidal Y.sheaf) _ _
    (canonicalDerivedMonoidal X.sheaf) (derivedPullback f) (derivedPullbackCoreMonoidal f)

end Stacks.Cohomology.DerivedPullbackTensor

end
