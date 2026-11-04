module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSingleUnitor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality

/-! # Tensoring with the structure sheaf placed in an arbitrary degree

Let `(C, 𝒪)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.  The structure sheaf placed in degree
zero is the unit of `⊗^𝐋_𝒪` and `- ⊗^𝐋_𝒪 𝒪[0] ≅ id` is its right unit constraint
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitTrans`).  In degree `q` the
structure sheaf is no longer the unit: this file constructs the natural isomorphism

`- ⊗^𝐋_𝒪 𝒪[q] ≅ (-)⟦-q⟧`

instead, which is what the dévissage of [Stacks, Tag 0944] needs at the structure sheaf placed in
each degree.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitObject`: `𝒪[q]` as an object of
  `D(𝒪)`, as `Q` of the complex.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso`: the natural isomorphism
  `- ⊗^𝐋_𝒪 𝒪[q] ≅ (-)⟦-q⟧`.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso_hom_app_q`: its value at
  the image of a complex — the right K-flat comparison of [Stacks, Tag 06YU] against the K-flat
  complex `𝒪[q]`, followed by `Q` of the unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` and by the
  commutation of `Q` with the shift.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.singleUnitorIso_uncurry_naturality`: its
  naturality with the tensor product read as a functor on the product category — the shape the
  projection formula consumes.

## Implementation notes

The construction is the one `rightUnitTrans` uses in degree zero: the functor `- ⊗^𝐋_𝒪 𝒪[q]`
descends `K ↦ Q(Tot(K ⊗_𝒪 𝒪[q]))` along the localization `Q`, because `𝒪[q]` is K-flat
(`Stacks.SheafOfModules.isKFlat_single_unit_deg`) and the right K-flat comparison asks no
flatness of the left factor; the shift `(-)⟦-q⟧` likewise descends `K ↦ Q(K⟦-q⟧)`, by the
commutation of `Q` with the shift; and the complex-level unit law
`Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso` is a natural isomorphism between the
two things descended.  `CategoryTheory.Localization.liftNatIso` then descends it.

No K-flat model of the left factor is chosen anywhere, so — unlike `rightUnitIso`, which is
built at a chosen model and proved natural afterwards — this isomorphism is natural by
construction.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
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
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- **The structure sheaf of a ringed site placed in the degree `q`, as an object of `D(𝒪)`.**
For `q = 0` this is `Stacks.DerivedTensor.RingedSite.unitObject`, the unit of `⊗^𝐋_𝒪`; for
`q ≠ 0` it is not a unit. -/
abbrev singleUnitObject (q : ℤ) : DerivedModules X.O :=
  DerivedCategory.Q.obj (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q)

/-- Tensoring a complex of `𝒪`-modules with the structure sheaf in degree `q` and passing to
`D(𝒪)`: the functor on complexes that `- ⊗^𝐋_𝒪 𝒪[q]` descends. -/
abbrev singleUnitTensorSource (q : ℤ) :
    CochainComplex (Modules X.O) ℤ ⥤ DerivedModules X.O :=
  (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj
      (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q) ⋙
    DerivedCategory.Q

/-- The shift by `-q` of a complex of `𝒪`-modules, passed to `D(𝒪)`: the functor on complexes
that `(-)⟦-q⟧` descends. -/
abbrev singleUnitShiftSource (q : ℤ) :
    CochainComplex (Modules X.O) ℤ ⥤ DerivedModules X.O :=
  CategoryTheory.shiftFunctor (CochainComplex (Modules X.O) ℤ) (-q) ⋙ DerivedCategory.Q

/-- **`- ⊗^𝐋_𝒪 𝒪[q]` descends `K ↦ Q(Tot(K ⊗_𝒪 𝒪[q]))`.**  The lifting isomorphism is the
right K-flat comparison, which asks no flatness of the left factor, at the structure sheaf in
degree `q`, which is K-flat by `Stacks.SheafOfModules.isKFlat_single_unit_deg`; its naturality
is the comparison's own naturality field with an identity in the second variable. -/
@[instance_reducible]
def singleUnitTensorLifting (q : ℤ) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
      (singleUnitTensorSource X q) (T.tensor.flip.obj (singleUnitObject X q)) where
  iso := NatIso.ofComponents
    (fun K ↦ T.comparisonRight K (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q)
      (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q))
    (fun {_ _} f ↦ by
      have h := T.comparisonRight_naturality f
        (𝟙 (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q))
        (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)
        (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)
      rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
      exact h)

/-- **`(-)⟦-q⟧` descends `K ↦ Q(K⟦-q⟧)`.**  The lifting isomorphism is the commutation of `Q`
with the shift. -/
@[instance_reducible]
def singleUnitShiftLifting (q : ℤ) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
      (singleUnitShiftSource X q)
      (CategoryTheory.shiftFunctor (DerivedModules X.O) (-q)) where
  iso := (DerivedCategory.Q.commShiftIso (-q)).symm

attribute [local instance] singleUnitTensorLifting singleUnitShiftLifting

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` of the total tensor product, read in `D(𝒪)`.** -/
def singleUnitTensorNatIso (q : ℤ) :
    singleUnitTensorSource X q ≅ singleUnitShiftSource X q :=
  NatIso.ofComponents
    (fun K ↦ DerivedCategory.Q.mapIso
      (Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso X.O K q))
    (fun {_ _} f ↦
      ((DerivedCategory.Q.map_comp _ _).symm.trans
          (congrArg DerivedCategory.Q.map
            (Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso_naturality X.O f q))).trans
        (DerivedCategory.Q.map_comp _ _))

/-- **Tensoring with the structure sheaf placed in the degree `q` is the shift by `-q`:**
`- ⊗^𝐋_𝒪 𝒪[q] ≅ (-)⟦-q⟧`, naturally.

This is the descent along the localization `Q` of the complex-level unit law
`Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso`.  For `q = 0` it is the right unit
constraint of [Stacks, Tag 0FPT] up to the identification of the shift by zero with the
identity. -/
def singleUnitorIso (q : ℤ) :
    T.tensor.flip.obj (singleUnitObject X q) ≅
      CategoryTheory.shiftFunctor (DerivedModules X.O) (-q) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
    (singleUnitTensorSource X q) (singleUnitShiftSource X q)
    (T.tensor.flip.obj (singleUnitObject X q))
    (CategoryTheory.shiftFunctor (DerivedModules X.O) (-q))
    (singleUnitTensorNatIso X q)

/-- **The value of `- ⊗^𝐋_𝒪 𝒪[q] ≅ (-)⟦-q⟧` at the image of a complex**: the right K-flat
comparison of [Stacks, Tag 06YU] against `𝒪[q]`, followed by `Q` of the unit law
`Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` and by the commutation of `Q` with the shift.  No K-flat model of
`K` is chosen, because the right factor is already K-flat. -/
theorem singleUnitorIso_hom_app_q (q : ℤ) (K : CochainComplex (Modules X.O) ℤ) :
    (singleUnitorIso X T q).hom.app (DerivedCategory.Q.obj K) =
      (T.comparisonRight K (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q)
          (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)).hom ≫
        DerivedCategory.Q.map
            (Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso X.O K q).hom ≫
          (DerivedCategory.Q.commShiftIso (-q)).hom.app K := by
  have hiso : (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
        (singleUnitTensorSource X q) (T.tensor.flip.obj (singleUnitObject X q))).hom.app K =
      (T.comparisonRight K (Stacks.Sheaves.DerivedPullback.singleUnitComplex X.O q)
        (Stacks.SheafOfModules.isKFlat_single_unit_deg X.O q)).hom := rfl
  have hiso' : (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
        (singleUnitShiftSource X q)
        (CategoryTheory.shiftFunctor (DerivedModules X.O) (-q))).inv.app K =
      (DerivedCategory.Q.commShiftIso (-q)).hom.app K := rfl
  rw [singleUnitorIso, Localization.liftNatIso, Localization.liftNatTrans_app, hiso, hiso']
  rfl

/-- **The naturality of `- ⊗^𝐋_𝒪 𝒪[q] ≅ (-)⟦-q⟧`, with the tensor product read as a functor on
the product category** — the shape the projection formula and the shifted-unitor coherence
consume.  This is the naturality of `singleUnitorIso` with `u ⊗ 𝟙 𝒪[q]` written as the image of
`(u, 𝟙 𝒪[q])` under `CategoryTheory.Functor.uncurry` of the derived tensor bifunctor. -/
theorem singleUnitorIso_uncurry_naturality (q : ℤ) {A B : DerivedModules X.O} (u : A ⟶ B) :
    (Functor.uncurry.obj T.tensor).map
          ((u ×ₘ 𝟙 (singleUnitObject X q)) :
            ((A, singleUnitObject X q) : _ × _) ⟶ (B, singleUnitObject X q)) ≫
        (singleUnitorIso X T q).hom.app B =
      (singleUnitorIso X T q).hom.app A ≫
        (CategoryTheory.shiftFunctor (DerivedModules X.O) (-q)).map u := by
  rw [Functor.uncurry_obj_map, (T.tensor.obj B).map_id, Category.comp_id]
  exact (singleUnitorIso X T q).hom.naturality u

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
