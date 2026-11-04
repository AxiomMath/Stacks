module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula

/-!
# The derived projection-formula map on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)` and
`K ∈ D(𝒪_Y)`.  There is a canonical morphism

`Rf_*E ⊗^L_{𝒪_Y} K ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`,

the adjoint transpose of

`Lf^*(Rf_*E ⊗^L_{𝒪_Y} K) ≅ Lf^*Rf_*E ⊗^L_{𝒪_X} Lf^*K ⟶ E ⊗^L_{𝒪_X} Lf^*K`,

where the first map is the derived pullback-tensor comparison and the second is the counit of
`Lf^* ⊣ Rf_*` tensored with the identity of `Lf^*K`.

## Main definitions

* `Stacks.Cohomology.DerivedProjectionFormula.PullbackTensorComparison`: the type of the
  derived pullback-tensor comparison, a morphism of bifunctors
  `(- ⊗^L_{𝒪_Y} -) ⋙ Lf^* ⟶ (Lf^* × Lf^*) ⋙ (- ⊗^L_{𝒪_X} -)`, and
  `Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison`, the comparison of
  Stacks 079U read at that type.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap`: the derived
  projection-formula morphism.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq`: the morphism is the
  abstract adjunction-tensor morphism of
  `CategoryTheory.adjunctionTensorMap` for `Lf^* ⊣ Rf_*`.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left` and
  `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right`: the
  morphism is natural in `E` and in `K`, for arbitrary derived modules and with no
  finiteness or flatness hypothesis.

## Implementation notes

*The adjunction and the derived tensor products are the repository's own.*  The adjunction is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`, Stacks 079W for an
arbitrary morphism of ringed spaces, and the two derived tensor products are
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of Stacks 06YU at the ringed
sites of opens of `X` and of `Y`.  All of the formal content of the construction is the
abstract `CategoryTheory.adjunctionTensorMap`, which is stated for
an adjunction `L ⊣ R` with binary functors on the two categories and a morphism of bifunctors
`A ⋙ L ⟶ (L × L) ⋙ B`; the declarations below are its instance at `Lf^* ⊣ Rf_*`, so nothing
is reproved here.

*The pullback-tensor comparison is the repository's own.*  The comparison
`Lf^*(K ⊗^L L) ⟶ Lf^*K ⊗^L Lf^*L` of bifunctors on `D(𝒪_Y) × D(𝒪_Y)` is Stacks 079U, and it
is `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, the descent of the
value on K-flat representatives along the two K-flat localizations of `D(𝒪_Y)`.  It is the
bifunctorial statement and not merely a family of isomorphisms, which is what the
construction needs: it evaluates the comparison at the pair `(Rf_*E, K)`, whose left entry is
an arbitrary object of `D(𝒪_Y)`.

*The four sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for
`AddCommGrpCat.{u}` on the two sites of opens are the binders the derived tensor product of
Stacks 06YU is stated under.  Both are `Prop`s and both are inhabited for every ringed space,
by `Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so they are not a weakening.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

universe u

noncomputable section

namespace Stacks.Cohomology.DerivedProjectionFormula

section Curried

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] (T : A ⥤ B ⥤ C)

/-- The uncurried bifunctor on a morphism which is the identity in the second factor. -/
lemma uncurry_map_id_right {Z Z' : A} (u : Z ⟶ Z') (W : B) :
    (Functor.uncurry.obj T).map (u ×ₘ 𝟙 W) = (T.map u).app W := by
  simp

/-- The uncurried bifunctor on a morphism which is the identity in the first factor. -/
lemma uncurry_map_id_left (Z : A) {W W' : B} (v : W ⟶ W') :
    (Functor.uncurry.obj T).map (𝟙 Z ×ₘ v) = (T.obj Z).map v := by
  simp

variable {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
  (α : Functor.uncurry.obj TA ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TB)

/-- Naturality of the abstract adjunction-tensor morphism in the first argument, with both
bifunctors written in curried form. -/
private lemma adjunctionTensorMap_natural_left_curried {G G' : B} (g : G ⟶ G') (H : A) :
    (TA.map (R.map g)).app H ≫ CategoryTheory.adjunctionTensorMap
        adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α G' H =
      CategoryTheory.adjunctionTensorMap
          adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α G H ≫
        R.map ((TB.map g).app (L.obj H)) := by
  simpa [uncurry_map_id_right] using CategoryTheory.adjunctionTensorMap_natural
    adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α g (𝟙 H)

/-- Naturality of the abstract adjunction-tensor morphism in the second argument, with both
bifunctors written in curried form. -/
private lemma adjunctionTensorMap_natural_right_curried (G : B) {H H' : A} (k : H ⟶ H') :
    (TA.obj (R.obj G)).map k ≫ CategoryTheory.adjunctionTensorMap
        adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α G H' =
      CategoryTheory.adjunctionTensorMap
          adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α G H ≫
        R.map ((TB.obj G).map (L.map k)) := by
  simpa [uncurry_map_id_left] using CategoryTheory.adjunctionTensorMap_natural
    adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α (𝟙 G) k

end Curried

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived pullback-tensor comparison of Stacks 079U, as a morphism of bifunctors on
`D(𝒪_Y) × D(𝒪_Y)`: a map `Lf^*(K ⊗^L_{𝒪_Y} L) ⟶ Lf^*K ⊗^L_{𝒪_X} Lf^*L` natural in `K` and
in `L`. -/
abbrev PullbackTensorComparison :=
  Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf) ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
      Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)

/-- **The derived pullback-tensor comparison of Stacks 079U**, as a morphism of bifunctors on
`D(𝒪_Y) × D(𝒪_Y)`: the canonical isomorphism
`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`, read as a morphism. -/
abbrev pullbackTensorComparison : PullbackTensorComparison f :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom

/-- **The derived projection-formula morphism**
`Rf_*E ⊗^L_{𝒪_Y} K ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`: the adjoint transpose of the derived
pullback-tensor comparison of Stacks 079U followed by the counit of `Lf^* ⊣ Rf_*` in the left
tensor factor.  It is defined for arbitrary `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`. -/
@[stacks 0B53 "the map"]
def projectionFormulaMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj E)).obj K ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K)) :=
  CategoryTheory.adjunctionTensorMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) E K

/-- The derived projection-formula morphism is the abstract adjunction-tensor morphism for the
derived adjunction `Lf^* ⊣ Rf_*` and the two derived tensor products. -/
theorem projectionFormulaMap_eq
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    projectionFormulaMap f E K =
      CategoryTheory.adjunctionTensorMap
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
        (pullbackTensorComparison f) E K :=
  rfl

/-- The derived projection-formula morphism is natural in the derived module on the source. -/
@[stacks 0B53 "naturality in the source complex"]
theorem projectionFormulaMap_natural_left
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : E ⟶ E')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map e)).app K ≫
        projectionFormulaMap f E' K =
      projectionFormulaMap f E K ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map e).app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K)) :=
  adjunctionTensorMap_natural_left_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
    (pullbackTensorComparison f) e K

/-- The derived projection-formula morphism is natural in the derived module on the target. -/
@[stacks 0B53 "naturality in the target complex"]
theorem projectionFormulaMap_natural_right
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (k : K ⟶ K') :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj E)).map k ≫
        projectionFormulaMap f E K' =
      projectionFormulaMap f E K ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map k)) :=
  adjunctionTensorMap_natural_right_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
    (pullbackTensorComparison f) E k

end Stacks.Cohomology.DerivedProjectionFormula

end

end
