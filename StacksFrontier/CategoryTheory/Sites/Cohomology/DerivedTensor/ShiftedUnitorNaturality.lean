module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.Homology.KFlat.BifunctorShiftNaturality

/-!
# Tensoring with a translate of the structure sheaf is the translation

Let `(C, 𝒪)` be a ringed site and let `T` be a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` is the right unit
constraint `- ⊗^𝐋_𝒪 𝒪[0] ≅ 𝟭 D(𝒪)`.  **This file is its translate**: for every `n : ℤ`,

`- ⊗^𝐋_𝒪 𝒪[0]⟦n⟧ ≅ (-)⟦n⟧`,

a natural isomorphism of functors on `D(𝒪)`.

Nothing here uses the commutation of the derived tensor product with the translation in the
right variable — which is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_right`, the `commShiftObj` half
of the structure field `commShift₂`, which is constrained only by the axioms of a two-variable
shift datum and by exactness, so that no formula for it is available.  Instead the whole
construction happens at the level of complexes,
where the translate of the unit complex is K-flat and where the commutation of the total tensor
complex with the translation is Mathlib's `Functor.CommShift` instance on
`CategoryTheory.Functor.map₂CochainComplex` ([Stacks, Tag 0FNG]), and is then transported along
the localization `DerivedCategory.Q` exactly as `rightUnitorNatIso` is.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.shiftedUnitComplex`: the structure sheaf in degree zero,
  translated by `n`, as a complex.
* `Stacks.DerivedTensor.RingedSite.tensorComplexShiftedUnitorNatIso`:
  `Tot(K ⊗_𝒪 𝒪[0]⟦n⟧) ≅ K⟦n⟧`, naturally in the complex `K`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitObject`: the translate of the
  structure sheaf in degree zero, as an object of `D(𝒪)`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorComparisonNatIso`: the
  isomorphism on the images of complexes.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorNatIso`:
  `- ⊗^𝐋_𝒪 𝒪[0]⟦n⟧ ≅ (-)⟦n⟧` on all of `D(𝒪)`.

## Main results

* `Stacks.DerivedTensor.RingedSite.kFlat_shiftedUnitComplex`: the translate of the unit complex
  is K-flat, so no resolution and no choice of representative enters.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorNatIso_hom_app_q`: the value
  at the image of a complex, which is where a computation with it starts.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorNatIso_naturality_uncurry`:
  the naturality square, with the tensor product read on the product category, which is the
  shape the projection formula consumes.

## Implementation notes

*Why the component on complexes is `CochainComplex.mapBifunctorShift₂Iso` and not a
`commShiftIso`.*  The two are equal by `rfl`
(`CategoryTheory.Functor.commShiftIso_map₂CochainComplex_hom_app`), but
`Stacks.SheafOfModules.Tensor.tensorComplex` is spelled with
`CategoryTheory.Functor.map₂HomologicalComplex` while the `Functor.CommShift` instance is stated
at the `map₂CochainComplex` abbreviation, and instance search does not cross between them.
Naming the isomorphism directly avoids the crossing; its naturality in the complex `K` is
`CochainComplex.mapBifunctorMap_comp_mapBifunctorShift₂Iso`, which is that instance read at an
object.

*At `n = 0` this is not `rightUnitorNatIso`.*  The translate by zero of the unit complex is
isomorphic to it but not equal, and the two isomorphisms are not compared here; nothing below
needs that.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
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

/-- The structure sheaf of a ringed site in degree zero, translated by `n`: the complex `𝒪[-n]`,
written as the `n`-fold translate of the unit complex. -/
abbrev shiftedUnitComplex (n : ℤ) : CochainComplex (Modules X.O) ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n).obj (unitComplex X)

/-- **The translate of the unit complex is K-flat.**  The unit complex is K-flat
(`Stacks.SheafOfModules.isKFlat_single_unit`) and K-flatness is stable under the translation
(`CochainComplex.KFlatBifunctor.kFlat_shift`). -/
theorem kFlat_shiftedUnitComplex (n : ℤ) :
    Stacks.SheafOfModules.KFlat X.O (shiftedUnitComplex X n) :=
  CochainComplex.KFlatBifunctor.kFlat_shift _ (Stacks.SheafOfModules.isKFlat_single_unit X.O) n

/-- Tensoring a morphism of complexes with the identity of the translated unit complex, with its
type **ascribed** at the total-tensor-complex spelling, as
`Stacks.DerivedTensor.RingedSite.tensorComplexWhiskerUnit` is. -/
def tensorComplexWhiskerShiftedUnit (n : ℤ) {K K' : CochainComplex (Modules X.O) ℤ} (h : K ⟶ K') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj (shiftedUnitComplex X n) ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').obj (shiftedUnitComplex X n) :=
  HomologicalComplex.mapBifunctorMap h (𝟙 (shiftedUnitComplex X n))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)

/-- **Moving the translation out of the second tensor factor, as an isomorphism of functors of
the first**: `Tot(K ⊗_𝒪 𝒪[0]⟦n⟧) ≅ Tot(K ⊗_𝒪 𝒪[0])⟦n⟧`.  The components are
`CochainComplex.mapBifunctorShift₂Iso` and the naturality is
`CochainComplex.mapBifunctorMap_comp_mapBifunctorShift₂Iso`. -/
def tensorComplexShift₂NatIso (n : ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (shiftedUnitComplex X n) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (unitComplex X) ⋙
        CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n :=
  NatIso.ofComponents
    (fun K => CochainComplex.mapBifunctorShift₂Iso K (unitComplex X)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) n)
    (fun {_ _} h => CochainComplex.mapBifunctorMap_comp_mapBifunctorShift₂Iso
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) h (unitComplex X) n)

/-- **Tensoring a complex with the translated unit complex is the translation**:
`Tot(K ⊗_𝒪 𝒪[0]⟦n⟧) ≅ K⟦n⟧`, naturally in `K`.

The isomorphism is `tensorComplexShift₂NatIso`, which moves the translation out of the second
variable, followed by the translate of the right unitor of complexes. -/
def tensorComplexShiftedUnitorNatIso (n : ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (shiftedUnitComplex X n) ≅
      CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n :=
  tensorComplexShift₂NatIso X n ≪≫
    Functor.isoWhiskerRight (tensorComplexRightUnitorNatIso X)
      (CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n) ≪≫
    Functor.leftUnitor (CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n)

/-- The value of `tensorComplexShift₂NatIso` at a complex. -/
theorem tensorComplexShift₂NatIso_hom_app (n : ℤ) (K : CochainComplex (Modules X.O) ℤ) :
    (tensorComplexShift₂NatIso X n).hom.app K =
      (CochainComplex.mapBifunctorShift₂Iso K (unitComplex X)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) n).hom :=
  rfl

/-- The value of `tensorComplexShiftedUnitorNatIso` at a complex. -/
theorem tensorComplexShiftedUnitorNatIso_hom_app (n : ℤ)
    (K : CochainComplex (Modules X.O) ℤ) :
    (tensorComplexShiftedUnitorNatIso X n).hom.app K =
      (CochainComplex.mapBifunctorShift₂Iso K (unitComplex X)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) n).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) n).map
          ((tensorComplexRightUnitorNatIso X).hom.app K) :=
  congrArg (_ ≫ ·) (Category.comp_id _)

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- The structure sheaf in degree zero, translated by `n`, as an object of `D(𝒪)`. -/
abbrev shiftedUnitObject (n : ℤ) : DerivedModules X.O :=
  DerivedCategory.Q.obj (shiftedUnitComplex X n)

/-- **The right K-flat comparison at the translated unit complex is natural in the left
complex.**  This is the field `comparisonRight_naturality` with the right morphism taken to be
the identity. -/
theorem comparisonRight_shiftedUnitObject_naturality (n : ℤ)
    {K K' : CochainComplex (Modules X.O) ℤ} (h : K ⟶ K') :
    (T.tensor.map (DerivedCategory.Q.map h)).app (shiftedUnitObject X n) ≫
        (T.comparisonRight K' (shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n)).hom =
      (T.comparisonRight K (shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n)).hom ≫
        DerivedCategory.Q.map (tensorComplexWhiskerShiftedUnit X n h) := by
  have hc := T.comparisonRight_naturality h (𝟙 (shiftedUnitComplex X n))
    (kFlat_shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n)
  rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj K')).map_id,
    Category.id_comp] at hc
  exact hc

/-- **The right K-flat comparison at the translated unit complex, as an isomorphism of functors
of the left complex.**  Its components are the comparisons and its naturality is
`comparisonRight_shiftedUnitObject_naturality`. -/
def comparisonRightShiftedUnitNatIso (n : ℤ) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (shiftedUnitObject X n) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj (shiftedUnitComplex X n) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents
    (fun K => T.comparisonRight K (shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n))
    (fun {_ _} h => comparisonRight_shiftedUnitObject_naturality X T n h)

/-- The value of `comparisonRightShiftedUnitNatIso` at a complex. -/
theorem comparisonRightShiftedUnitNatIso_hom_app (n : ℤ)
    (K : CochainComplex (Modules X.O) ℤ) :
    (comparisonRightShiftedUnitNatIso X T n).hom.app K =
      (T.comparisonRight K (shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n)).hom :=
  rfl

/-- **Tensoring with the translated structure sheaf, on the images of complexes**:
`Q K ⊗^𝐋_𝒪 𝒪[0]⟦n⟧ ≅ (Q K)⟦n⟧`, naturally in `K`.

The translate of the unit complex is K-flat, so the right K-flat comparison computes the derived
tensor product with it as the total tensor complex, where
`tensorComplexShiftedUnitorNatIso` identifies it with the translate; `DerivedCategory.Q`
commutes with the translation. No K-flat model of `K` is chosen. -/
def shiftedUnitorComparisonNatIso (n : ℤ) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (shiftedUnitObject X n) ≅
      DerivedCategory.Q (C := Modules X.O) ⋙
        CategoryTheory.shiftFunctor (DerivedModules X.O) n :=
  comparisonRightShiftedUnitNatIso X T n ≪≫
    Functor.isoWhiskerRight (tensorComplexShiftedUnitorNatIso X n)
      (DerivedCategory.Q (C := Modules X.O)) ≪≫
    DerivedCategory.Q.commShiftIso n

/-- **Tensoring with the translated structure sheaf is the translation**:
`- ⊗^𝐋_𝒪 𝒪[0]⟦n⟧ ≅ (-)⟦n⟧` on `D(𝒪)`.

`DerivedCategory.Q` is a localization functor at the quasi-isomorphisms, so the natural
isomorphism `shiftedUnitorComparisonNatIso` on the images of complexes extends uniquely. -/
def shiftedUnitorNatIso (n : ℤ) :
    T.tensor.flip.obj (shiftedUnitObject X n) ≅
      CategoryTheory.shiftFunctor (DerivedModules X.O) n :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules X.O))
    (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.tensor.flip.obj (shiftedUnitObject X n))
    (DerivedCategory.Q (C := Modules X.O) ⋙
      CategoryTheory.shiftFunctor (DerivedModules X.O) n)
    (T.tensor.flip.obj (shiftedUnitObject X n))
    (CategoryTheory.shiftFunctor (DerivedModules X.O) n)
    (shiftedUnitorComparisonNatIso X T n)

/-- **The value at the image of a complex.**  The lift adds nothing to
`shiftedUnitorComparisonNatIso` at an object of the form `Q K`.  This is the formula a
computation with `shiftedUnitorNatIso` has to start from. -/
theorem shiftedUnitorNatIso_hom_app_q (n : ℤ) (K : CochainComplex (Modules X.O) ℤ) :
    (T.shiftedUnitorNatIso X n).hom.app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (shiftedUnitComplex X n) (kFlat_shiftedUnitComplex X n)).hom ≫
        DerivedCategory.Q.map ((tensorComplexShiftedUnitorNatIso X n).app K).hom ≫
          ((DerivedCategory.Q.commShiftIso n).app K).hom := by
  dsimp only [shiftedUnitorNatIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, shiftedUnitorComparisonNatIso,
    comparisonRightShiftedUnitNatIso_hom_app]

/-- **The isomorphism transported along an isomorphism of the tensor factor.**  For any object
`V` of `D(𝒪)` isomorphic to `𝒪[0]⟦n⟧` this gives `- ⊗^𝐋_𝒪 V ≅ (-)⟦n⟧`.  It exists so that a
consumer which spells the structure sheaf in degree `-n` differently — as a single-object
functor, say — gets the natural isomorphism and its naturality without having to transport the
latter itself. -/
def shiftedUnitorNatIsoOfIso (n : ℤ) {V : DerivedModules X.O}
    (e : shiftedUnitObject X n ≅ V) :
    T.tensor.flip.obj V ≅ CategoryTheory.shiftFunctor (DerivedModules X.O) n :=
  (T.tensor.flip.mapIso e).symm ≪≫ shiftedUnitorNatIso X T n

/-- Naturality of an isomorphism `- ⊗^𝐋_𝒪 V ≅ F`, with the tensor product read as a functor on the
product category. -/
private theorem uncurry_map_prod_id_comp_app_hom {V : DerivedModules X.O}
    {F : DerivedModules X.O ⥤ DerivedModules X.O} (α : T.tensor.flip.obj V ≅ F)
    {A B : DerivedModules X.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map ((u ×ₘ 𝟙 V) : ((A, V) : _ × _) ⟶ (B, V)) ≫ (α.app B).hom =
      (α.app A).hom ≫ F.map u := by
  rw [Functor.uncurry_obj_map, (T.tensor.obj B).map_id, Category.comp_id]
  exact α.hom.naturality u

/-- **Naturality of the transported isomorphism**, with the tensor product read as a functor on
the product category.  This is the shape in which the projection formula consumes it. -/
theorem shiftedUnitorNatIsoOfIso_naturality_uncurry (n : ℤ) {V : DerivedModules X.O}
    (e : shiftedUnitObject X n ≅ V) {A B : DerivedModules X.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map
          ((u ×ₘ 𝟙 V) : ((A, V) : _ × _) ⟶ (B, V)) ≫
        ((shiftedUnitorNatIsoOfIso X T n e).app B).hom =
      ((shiftedUnitorNatIsoOfIso X T n e).app A).hom ≫
        (CategoryTheory.shiftFunctor (DerivedModules X.O) n).map u :=
  uncurry_map_prod_id_comp_app_hom X T _ u

/-- **Naturality of the isomorphism, with the tensor product read as a functor on the product
category.**  This is the shape in which the projection formula consumes it. -/
theorem shiftedUnitorNatIso_naturality_uncurry (n : ℤ) {A B : DerivedModules X.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map
          ((u ×ₘ 𝟙 (shiftedUnitObject X n)) :
            ((A, shiftedUnitObject X n) : _ × _) ⟶ (B, shiftedUnitObject X n)) ≫
        ((T.shiftedUnitorNatIso X n).app B).hom =
      ((T.shiftedUnitorNatIso X n).app A).hom ≫
        (CategoryTheory.shiftFunctor (DerivedModules X.O) n).map u :=
  uncurry_map_prod_id_comp_app_hom X T _ u

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
