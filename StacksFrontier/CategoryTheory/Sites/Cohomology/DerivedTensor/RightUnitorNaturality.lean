module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import Mathlib.Algebra.Homology.Monoidal
import StacksCore.Tactic.StacksAttribute

/-!
# The right unit constraint of the derived tensor product is natural

Let `(C, 𝒪)` be a ringed site and let `T` be a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. The structure sheaf in degree zero is a
right unit for `⊗^𝐋_𝒪`, and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` provides the isomorphism
`A ⊗^𝐋_𝒪 𝒪 ≅ A` one object at a time. This file upgrades that to a *natural* isomorphism of
functors on `D(𝒪)`:

`- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.tensorComplexRightUnitorNatIso`: the right unitor of the
  *total tensor complex*, `Tot(K ⊗_𝒪 𝒪[0]) ≅ K`, naturally in the complex `K`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorComparisonNatIso`: the
  right unitor on the images of complexes, `Q K ⊗^𝐋_𝒪 𝒪[0] ≅ Q K`, naturally in `K`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso`: the right unit
  constraint of `⊗^𝐋_𝒪` as a natural isomorphism `- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso_naturality` and
  `…_naturality_uncurry`: the naturality square of that isomorphism, written out at a morphism
  of `D(𝒪)`, in the two spellings of the tensor product of a morphism with an identity.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso_hom_app_q`: the value
  of that isomorphism at the image of a complex, which is where a computation with it starts.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonRight_unitObject_naturality`:
  the right K-flat comparison at the unit complex, natural in the left complex.

## Implementation notes

*Where the naturality comes from.* On complexes it is already available and costs nothing: the
total tensor complex is the tensor product of `HomologicalComplex.monoidalCategory`, Mathlib's
monoidal structure on complexes over a monoidal category, taken over the monoidal structure on
`Mod(𝒪)` whose tensor product is *definitionally* `Stacks.SheafOfModules.Tensor.sheafTensor`
(`SheafOfModules.monoidalCategorySheafTensor`). Its unit is the structure sheaf in degree zero
and its right unitor is therefore a natural isomorphism by the monoidal axioms, so
`tensorComplexRightUnitorNatIso` is `CategoryTheory.MonoidalCategory.rightUnitorNatIso` read at
that structure and no diagram is checked here. The two identifications that let it be read
there — `curriedTensor (Mod 𝒪) = ⊗_𝒪` and `𝟙_ (Mod 𝒪) = 𝒪` — are
`SheafOfModules.curriedTensor_sheafTensor` and `SheafOfModules.tensorUnit_sheafTensor`, and
both are `rfl`, so the crossing happens by definitional unfolding in term position.

*Why the monoidal structure is inferred here rather than imported.* It is the same structure
that `Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes` ([Stacks,
Tag 0FPQ]) records, whose fields `tensor_eq_total` and `unit_eq_structureSheaf` are `rfl` for
exactly this reason. That file is not imported because it also assembles the Koszul symmetry of
complexes, which is what makes it expensive; the monoidal structure alone is found by instance
search from the five local instances below, and nothing else in this file needs the braiding.

*How it is transported to the derived category.* `DerivedCategory.Q` is a localization functor
at the quasi-isomorphisms, so a natural transformation between functors on `D(𝒪)` is the same
thing as one between their composites with `Q`
(`CategoryTheory.Localization.liftNatIso`). The composite statement is
`rightUnitorComparisonNatIso`: the right K-flat comparison `comparisonRight`, which asks
flatness of the right factor only and is natural in the left complex, followed by `Q` of the
right unitor of complexes. The structure sheaf in degree zero is K-flat outright, by
`Stacks.SheafOfModules.isKFlat_single_unit`, so no resolution and no choice of representative
enters, and in particular `rightUnitorNatIso` is not built from
`AlgebraicGeometry.RingedSite.kFlatModel`.

*The ascribed whiskering.* `HomologicalComplex.mapBifunctor K L (⊗_𝒪) _` and
`((Tot(- ⊗_𝒪 -)).obj K).obj L` are equal by `rfl` and are not syntactically equal, and a term
mixing them is not type-correct at `implicit` transparency, so `rw` and `simp` refuse any goal
containing it. `tensorComplexWhiskerUnit` is `HomologicalComplex.mapBifunctorMap h (𝟙 𝒪[0])`
with its type **ascribed** at the total-tensor spelling, which is the spelling the fields of
`DerivedTensorProduct` produce; the crossing then happens once, inside a proof given by
`exact`.

*Why this is the one packaging of the constraint as an isomorphism of functors.*
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedUnitorCoherence` used to
carry a second one, `rightUnitNatIso`, of the same type: `NatIso.ofComponents` applied to the
pointwise `rightUnitIso`, with naturality obtained through a calculus-of-fractions argument on
`comparisonRight` against `𝒪[0]`. It had no consumer, and the two are not equal by `rfl` — the
lift here passes through no K-flat model, that one through the chosen model of each object — so
the duplication was not visible to a syntactic check. The one thing it had that this does not
is `rightUnitNatIso_app`, its components being `rightUnitIso` by `rfl`; that identification is
available instead from `…DerivedTensorProduct.rightUnitIso_hom_eq` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality`, which
identifies `rightUnitIso` with the components of the localization lift. Tag 0FPT itself is
registered on `symmetricMonoidalDerivedTensor`.

*What is not proved.* No identification of `rightUnitorNatIso` with the pointwise
`rightUnitIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean` is
established: that one passes through a chosen K-flat model of the left factor, and comparing
the two is a separate computation. The associativity constraint, the pentagon, the hexagon and
the unit triangles of [Stacks, Tag 0FPT] remain out of scope, so the symmetric monoidal
structure on `D(𝒪)` is still not assembled. [Stacks, Tag 0FPQ] is attributed on
`Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes`, and the pointwise
clauses of [Stacks, Tag 0FPT] on the statements of `DerivedSymmetryAndUnit.lean`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped CategoryTheory.Prod

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- Tensoring a morphism of complexes with the identity of the structure sheaf in degree zero,
with its type **ascribed** at the total-tensor-complex spelling
`((Tot(- ⊗_𝒪 -)).obj K).obj 𝒪[0]` rather than at `HomologicalComplex.mapBifunctor`. The two
are equal by `rfl`; the ascription is what makes the statements below rewritable. -/
def tensorComplexWhiskerUnit {K K' : CochainComplex (Modules X.O) ℤ} (h : K ⟶ K') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj (unitComplex X) ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').obj (unitComplex X) :=
  HomologicalComplex.mapBifunctorMap h (𝟙 (unitComplex X))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)

/-- **The right unitor of the total tensor complex, naturally in the complex**:
`Tot(K ⊗_𝒪 𝒪[0]) ≅ K`.

This is the right unitor of the monoidal structure of [Stacks, Tag 0FPQ] on complexes of
modules, whose tensor product is the total tensor complex and whose unit is the structure sheaf
in degree zero; naturality is one of the monoidal axioms. -/
def tensorComplexRightUnitorNatIso :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (unitComplex X) ≅
      𝟭 (CochainComplex (Modules X.O) ℤ) :=
  (MonoidalCategory.rightUnitorNatIso (CochainComplex (Modules X.O) ℤ) :)

/-- The naturality square of `tensorComplexRightUnitorNatIso`, written out. -/
theorem tensorComplexWhiskerUnit_comp_rightUnitor
    {K K' : CochainComplex (Modules X.O) ℤ} (h : K ⟶ K') :
    tensorComplexWhiskerUnit X h ≫ ((tensorComplexRightUnitorNatIso X).app K').hom =
      ((tensorComplexRightUnitorNatIso X).app K).hom ≫ h :=
  (tensorComplexRightUnitorNatIso X).hom.naturality h

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- **The right K-flat comparison at the unit complex is natural in the left complex.** This is
the field `comparisonRight_naturality` with the right morphism taken to be the identity of
`𝒪[0]`, restated at the unit object `𝒪[0]` of `D(𝒪)` and at the ascribed whiskering. -/
theorem comparisonRight_unitObject_naturality
    {K K' : CochainComplex (Modules X.O) ℤ} (h : K ⟶ K') :
    (T.tensor.map (DerivedCategory.Q.map h)).app (unitObject X) ≫
        (T.comparisonRight K' (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom =
      (T.comparisonRight K (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map (tensorComplexWhiskerUnit X h) := by
  have hc := T.comparisonRight_naturality h (𝟙 (unitComplex X))
    (Stacks.SheafOfModules.isKFlat_single_unit X.O)
    (Stacks.SheafOfModules.isKFlat_single_unit X.O)
  rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj K')).map_id,
    Category.id_comp] at hc
  exact hc

/-- **The right unit constraint on the image of a complex, naturally in that complex**:
`Q K ⊗^𝐋_𝒪 𝒪[0] ≅ Q K`.

The structure sheaf in degree zero is K-flat, so the right K-flat comparison computes the
derived tensor product with it as the total tensor complex, where the right unitor is the
natural one of [Stacks, Tag 0FPQ]. No K-flat model of `K` is chosen. -/
def rightUnitorComparisonNatIso :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (unitObject X) ≅
      DerivedCategory.Q (C := Modules X.O) :=
  NatIso.ofComponents
    (fun K => T.comparisonRight K (unitComplex X)
        (Stacks.SheafOfModules.isKFlat_single_unit X.O) ≪≫
      DerivedCategory.Q.mapIso ((tensorComplexRightUnitorNatIso X).app K))
    (fun {K K'} h => by
      dsimp only [Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, comparisonRight_unitObject_naturality X T h]
      simp only [Category.assoc, ← Functor.map_comp]
      rw [tensorComplexWhiskerUnit_comp_rightUnitor X h])

/-- **The right unit constraint of the derived tensor product, as a natural isomorphism**:
`- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.

`DerivedCategory.Q` is a localization functor at the quasi-isomorphisms, so the natural
isomorphism `rightUnitorComparisonNatIso` on the images of complexes extends uniquely to
`D(𝒪)`.

This is strictly more than the family of isomorphisms `DerivedSymmetryAndUnit.lean` supplies,
and strictly less than the monoidal structure: the associativity constraint, the pentagon, the
hexagon, the unit triangles and the involutivity of the braiding are still not proved, so
[Stacks, Tag 0FPT] is not discharged here. -/
def rightUnitorNatIso :
    T.tensor.flip.obj (unitObject X) ≅ 𝟭 (DerivedModules X.O) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules X.O))
    (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.tensor.flip.obj (unitObject X))
    (DerivedCategory.Q (C := Modules X.O))
    (T.tensor.flip.obj (unitObject X)) (𝟭 _)
    (rightUnitorComparisonNatIso X T)

/-- **The value of the right unit constraint at the image of a complex.** The lift adds nothing
to `rightUnitorComparisonNatIso` at an object of the form `Q K`: there it is the right K-flat
comparison followed by `Q` of the right unitor of complexes. This is the formula a computation
with `rightUnitorNatIso` has to start from, since every object of `D(𝒪)` is isomorphic to some
`Q K`. -/
theorem rightUnitorNatIso_hom_app_q (K : CochainComplex (Modules X.O) ℤ) :
    (T.rightUnitorNatIso X).hom.app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (unitComplex X)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map ((tensorComplexRightUnitorNatIso X).app K).hom := by
  dsimp only [rightUnitorNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, rightUnitorComparisonNatIso]

/-- **Naturality of the right unit constraint of `⊗^𝐋_𝒪`**, written out at a morphism `u` of
`D(𝒪)`: tensoring `u` with the identity of `𝒪[0]` and then cancelling the unit is cancelling
the unit and then `u`. -/
theorem rightUnitorNatIso_naturality {A B : DerivedModules X.O} (u : A ⟶ B) :
    (T.tensor.map u).app (unitObject X) ≫ (T.rightUnitorNatIso X).hom.app B =
      (T.rightUnitorNatIso X).hom.app A ≫ u :=
  (T.rightUnitorNatIso X).hom.naturality u

/-- **Naturality of the right unit constraint of `⊗^𝐋_𝒪`, with the tensor product read as a
functor on the product category.** This is `rightUnitorNatIso_naturality` with `u ⊗ 𝟙 𝒪[0]`
written as the image of `(u, 𝟙 𝒪[0])` under `CategoryTheory.Functor.uncurry` of the derived
tensor bifunctor, which is the shape in which the projection formula consumes it. -/
theorem rightUnitorNatIso_naturality_uncurry {A B : DerivedModules X.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map
          ((u ×ₘ 𝟙 (unitObject X)) :
            ((A, unitObject X) : _ × _) ⟶ (B, unitObject X)) ≫
        ((T.rightUnitorNatIso X).app B).hom =
      ((T.rightUnitorNatIso X).app A).hom ≫ u := by
  rw [Functor.uncurry_obj_map, (T.tensor.obj B).map_id, Category.comp_id]
  exact (T.rightUnitorNatIso X).hom.naturality u

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
