module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The derived projection-formula map with the pushforward on the right

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `K ∈ D(𝒪_Y)` and
`E ∈ D(𝒪_X)`.  The projection-formula map of [Stacks, Tag 0B53] puts the pushforward in the
*left* tensor factor, `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)`.  This file records the same
construction with the pushforward in the *right* tensor factor,

`K ⊗^L_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗^L_{𝒪_X} E)`,

the adjoint transpose of `Lf^*(K ⊗^L Rf_*E) ≅ Lf^*K ⊗^L Lf^*Rf_*E ⟶ Lf^*K ⊗^L E`, where the
first map is the comparison of [Stacks, Tag 079U] and the second is the counit of
`Lf^* ⊣ Rf_*` in the right tensor factor.

The source states the projection formula with the pushforward on the left only; the two forms
are interchanged by the commutativity constraint of the derived tensor product, but that
interchange needs the compatibility of [Stacks, Tag 079U] with the commutativity constraints,
which this library does not have.  The right-handed form is wanted on its own because the
tensor–internal-Hom bijection of [Stacks, Tag 08DI] tensors on the right,
`Hom(A, R𝓗om(B, C)) = Hom(A ⊗^L B, C)`, so a computation of `R𝓗om(Rf_*E, -)` through the
projection formula meets `Rf_*E` in the right factor.

## Main definitions

* `Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparisonSwap`: the comparison of
  [Stacks, Tag 079U] read on the bifunctors with their arguments interchanged.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight`: the right-handed
  projection-formula map.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight_eq`: the map is the
  abstract adjunction-tensor map `CategoryTheory.adjunctionTensorMap` at `Lf^* ⊣ Rf_*` and the
  interchanged bifunctors.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight_natural`: it is natural
  in both arguments.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

/-! ### The abstract construction with interchanged arguments -/

section Abstract

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- A comparison `A ⋙ L ⟶ (L × L) ⋙ B` of bifunctors, read on the bifunctors with their two
arguments interchanged: its component at `(a, b)` is the component of `α` at `(b, a)`. -/
def comparisonSwap :
    (CategoryTheory.Prod.swap C C ⋙ A) ⋙ L ⟶ L.prod L ⋙ (CategoryTheory.Prod.swap D D ⋙ B) where
  app p := α.app (p.2, p.1)
  naturality _ _ g := α.naturality (g.2 ×ₘ g.1)

/-- The component of `comparisonSwap A B α` at `p` is the component of `α` at `(p.2, p.1)`. -/
@[simp]
theorem comparisonSwap_app (p : C × C) :
    (comparisonSwap A B α).app p = α.app (p.2, p.1) :=
  rfl

end Abstract

/-! ### The right-handed projection-formula map of a morphism of ringed spaces -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of [Stacks, Tag 079U] with its arguments interchanged**: the map
`Lf^*(L ⊗^L K) ⟶ Lf^*L ⊗^L Lf^*K` read as a morphism of the bifunctors `(K, L) ↦ L ⊗^L K`. -/
abbrev pullbackTensorComparisonSwap :
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)) ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) :=
  comparisonSwap _ _ (pullbackTensorComparison f)

/-- **The right-handed derived projection-formula map**
`K ⊗^L_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗^L_{𝒪_X} E)`: the adjoint transpose of the comparison of
[Stacks, Tag 079U] followed by the counit of `Lf^* ⊣ Rf_*` in the right tensor factor.  It is
the map of [Stacks, Tag 0B53] with the two tensor factors interchanged on both sides, for
arbitrary `K ∈ D(𝒪_Y)` and `E ∈ D(𝒪_X)`. -/
def projectionFormulaMapRight
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj K).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj E) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K)).obj E) :=
  CategoryTheory.adjunctionTensorMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparisonSwap f) E K

/-- The right-handed projection-formula map is the abstract adjunction-tensor map for the
derived adjunction `Lf^* ⊣ Rf_*` and the two derived tensor products with their arguments
interchanged. -/
theorem projectionFormulaMapRight_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    projectionFormulaMapRight f K E =
      CategoryTheory.adjunctionTensorMap
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
        (pullbackTensorComparisonSwap f) E K :=
  rfl

/-- **The right-handed projection-formula map is natural in both arguments.** -/
theorem projectionFormulaMapRight_natural
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (k : K ⟶ K') (e : E ⟶ E') :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        (k ×ₘ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map e) ≫
        projectionFormulaMapRight f K' E' =
      projectionFormulaMapRight f K E ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map k ×ₘ e)) :=
  CategoryTheory.adjunctionTensorMap_natural
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparisonSwap f) e k

end Stacks.Cohomology.DerivedProjectionFormula

end
