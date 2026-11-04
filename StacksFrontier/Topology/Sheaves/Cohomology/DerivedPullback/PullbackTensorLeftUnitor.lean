module

public import StacksFrontier.CategoryTheory.Monoidal.BraidedLeftUnitality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat

/-!
# The left-unit coherence of the comparison of [Stacks, Tag 079U]

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces. The comparison of
[Stacks, Tag 079U], `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, carries
the left unit constraint of the monoidal derived category of [Stacks, Tag 0FPT] on `D(O_Y)` to
the one on `D(O_X)`: this is the left-unitality clause of `CategoryTheory.Functor.CoreMonoidal`
for the derived pullback.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedTensorRightUnitorNatIso_hom_app_eq_canonical`:
  `Stacks.RingedSpace.derivedTensorRightUnitorNatIso` and
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom` are the same morphism at every
  object of `D(O_Z)`.
* `Stacks.Cohomology.DerivedPullbackTensor.rightUnitorCoherence_canonical`: the right-unit
  coherence of [Stacks, Tag 079U] restated at the monoidal structure of [Stacks, Tag 0FPT] and
  with the comparison inverted -- the right-unitality clause of
  `CategoryTheory.Functor.CoreMonoidal`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_leftUnitor`: **the left-unit
  coherence**, at every object of `D(O_Y)` and with no hypothesis on `f` beyond its being a
  morphism of ringed spaces.

## Implementation notes

`AlgebraicGeometry.SheafedSpace.sheaf` is `implicit_reducible` here -- the statements of the
imported files need it -- and under that transparency the unifier unfolds `Z.sheaf` to a term
`SheafOfModules.Tensor.ringSheaf` does not accept, so `rw`'s motive check fails on goals that
literally contain the pattern. Two steps are therefore written in term mode, where no motive is
abstracted.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
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

-- The list is the one of `PullbackTensorComparisonBraiding.lean`, for the same reasons: the
-- canonical tensor product's ring sheaf is `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`,
-- whose argument has type `TopCat.Sheaf CommRingCat Z.carrier` where `Tensor.ringSheaf` asks for
-- a `CategoryTheory.Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat`, so `TopCat.Sheaf`,
-- `TopCat.Presheaf.IsSheaf` and `Tensor.ringSheaf` itself have to unfold for the statements of
-- that file to be about the same objects.  `structureSheafRing` is *not* in the list: it is
-- globally `@[instance_reducible]`, which already unfolds at `implicit` transparency, and
-- `[implicit_reducible]` is the strictly higher status, so naming it here would move it off
-- `instances` transparency and hide it from typeclass *search* -- which is what makes the
-- category of `Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf` unfindable.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

section Bridge

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Naturality of the right unit constraint of Tag 0FPT**, at the pinned spelling
`Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom` and with the whiskering written
as the action of the derived tensor bifunctor. -/
theorem canonicalRightUnitorHom_naturality
    {G H : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (u : G ⟶ H) :
    canonicalWhiskerRight Z.sheaf u _ ≫ canonicalRightUnitorHom Z.sheaf H =
      canonicalRightUnitorHom Z.sheaf G ≫ u :=
  let := canonicalDerivedMonoidal Z.sheaf
  MonoidalCategory.rightUnitor_naturality u

/-- **The right unit constraint of Tag 0FPT is the right unit constraint of Tag 06YU, at the
image of a K-flat complex.** -/
theorem derivedTensorRightUnitorNatIso_hom_app_eq_canonical_q
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K) :
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app
        (DerivedCategory.Q.obj K) =
      canonicalRightUnitorHom Z.sheaf (DerivedCategory.Q.obj K) := by
  rw [canonicalComparison_rightUnitor Z.sheaf K hK,
    Stacks.Cohomology.DerivedProjectionFormula.derivedTensorRightUnitorNatIso_hom_app_q Z K,
    (canonicalDerivedTensorProduct Z.sheaf).comparisonRight_eq_comparison K
      (unitComplex (Stacks.RingedSpace.toRingedSite Z)) hK
      (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Z).O)]
  rfl

/-- **The two spellings of the right unit constraint of the derived tensor product agree, at
every object of `D(O_Z)`.**

`Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, built from the one-sided K-flat comparison
of [Stacks, Tag 06YU], and `Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom`, the
right unitor of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, are the same
morphism. -/
theorem derivedTensorRightUnitorNatIso_hom_app_eq_canonical
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app W =
      canonicalRightUnitorHom Z.sheaf W := by
  have hes := CochainComplex.KFlatBifunctor.kFlatQ_essSurj
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
  set G := CochainComplex.KFlatBifunctor.kFlatQ
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
  set M := G.objPreimage W
  have i : W ≅ DerivedCategory.Q.obj M.obj.as :=
    (G.objObjPreimageIso W).symm ≪≫ (DerivedCategory.quotientCompQhIso _).app _
  refine (cancel_mono i.hom).1
    (((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.naturality i.hom).symm.trans ?_)
  rw [derivedTensorRightUnitorNatIso_hom_app_eq_canonical_q Z M.obj.as M.property]
  exact canonicalRightUnitorHom_naturality Z i.hom

end Bridge

section LeftUnitor

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit derivedPullbackUnitIso)

/-- **The tensorator of Tag 079U carries the commutativity constraint of Tag 0FPT**, in the
direction the tensorator points: out of `Lf^*M (x) Lf^*N` and into `Lf^*(M (x) N)`. -/
theorem derivedPullbackTensorIso_inv_braiding
    (M N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    ((derivedPullbackTensorIso f).app (M, N)).inv ≫
        (derivedPullback f).map (canonicalBraidingHom Y.sheaf M N) =
      canonicalBraidingHom X.sheaf ((derivedPullback f).obj M)
          ((derivedPullback f).obj N) ≫
        ((derivedPullbackTensorIso f).app (N, M)).inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (derivedPullbackTensorIso_braiding f M N)).trans
      (Category.assoc _ _ _))

/-- **The right-unit coherence of the comparison of Tag 079U, at the monoidal structure of
Tag 0FPT**, with the comparison inverted so that it points the way a tensorator does: the
right-unitality clause of `CategoryTheory.Functor.CoreMonoidal`. -/
theorem rightUnitorCoherence_canonical
    (W : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    canonicalRightUnitorHom X.sheaf ((derivedPullback f).obj W) =
      canonicalWhiskerLeft X.sheaf ((derivedPullback f).obj W)
          (derivedPullbackUnitIso f).inv ≫
        ((derivedPullbackTensorIso f).app (W, singleUnit Y)).inv ≫
          (derivedPullback f).map (canonicalRightUnitorHom Y.sheaf W) := by
  have hX : ∀ V : DerivedCategory
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X),
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app V).hom =
        canonicalRightUnitorHom X.sheaf V :=
    derivedTensorRightUnitorNatIso_hom_app_eq_canonical X
  have hY : ∀ V : DerivedCategory
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y),
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app V).hom =
        canonicalRightUnitorHom Y.sheaf V :=
    derivedTensorRightUnitorNatIso_hom_app_eq_canonical Y
  have h := Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject f W
  rw [Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left, hX, hY] at h
  have h' : ((derivedPullbackTensorIso f).app (W, singleUnit Y)).hom ≫
      ((derivedTensorBifunctorOfSite X.sheaf).obj ((derivedPullback f).obj W)).map
          (derivedPullbackUnitIso f).hom ≫
        canonicalRightUnitorHom X.sheaf ((derivedPullback f).obj W) =
      (derivedPullback f).map (canonicalRightUnitorHom Y.sheaf W) := h
  simp only [canonicalWhiskerLeft]
  exact ((congrArg (fun g => ((derivedTensorBifunctorOfSite X.sheaf).obj
        ((derivedPullback f).obj W)).map (derivedPullbackUnitIso f).inv ≫ g)
      ((Iso.inv_comp_eq _).2 h'.symm)).trans
    (Iso.inv_hom_id_assoc
      (((derivedTensorBifunctorOfSite X.sheaf).obj ((derivedPullback f).obj W)).mapIso
        (derivedPullbackUnitIso f))
      (canonicalRightUnitorHom X.sheaf ((derivedPullback f).obj W)))).symm

/-- **The comparison of Tag 079U carries the left unit constraint of the monoidal derived
category of Tag 0FPT on `D(O_Y)` to the one on `D(O_X)`**, for arbitrary `M` in `D(O_Y)` and
with no finiteness, flatness or quasi-coherence hypothesis.  This is the left-unitality clause
of `CategoryTheory.Functor.CoreMonoidal` for the derived pullback. -/
theorem derivedPullbackTensorIso_leftUnitor
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    canonicalLeftUnitorHom X.sheaf ((derivedPullback f).obj M) =
      canonicalWhiskerRight X.sheaf (derivedPullbackUnitIso f).inv
          ((derivedPullback f).obj M) ≫
        ((derivedPullbackTensorIso f).app (singleUnit Y, M)).inv ≫
          (derivedPullback f).map (canonicalLeftUnitorHom Y.sheaf M) :=
  @Stacks.CategoryTheory.Monoidal.left_unitality_of_braided
    _ _ (canonicalDerivedMonoidal Y.sheaf)
    (canonicalDerivedSymmetric Y.sheaf).toBraidedCategory
    _ _ (canonicalDerivedMonoidal X.sheaf)
    (canonicalDerivedSymmetric X.sheaf).toBraidedCategory
    (derivedPullback f) (derivedPullbackUnitIso f).symm
    (fun A B => ((derivedPullbackTensorIso f).app (A, B)).symm)
    (derivedPullbackTensorIso_inv_braiding f) (rightUnitorCoherence_canonical f) M

end LeftUnitor

end Stacks.Cohomology.DerivedPullbackTensor

end
