module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedRightUnitorCoherenceReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect

/-!
# The projection formula on ringed topoi at the shifts of the structure sheaf

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites. For `E ∈ D(𝒪_C)` and `K ∈ D(𝒪_D)` the projection-formula map of
[Stacks, Tag 0B56] is

  `Rf_*E ⊗^L_{𝒪_D} K ⟶ Rf_*(E ⊗^L_{𝒪_C} Lf^*K)`.

This file proves that it is an isomorphism whenever `K` is isomorphic to a shift `𝒪_D[n]` of the
structure sheaf — the base case of [Stacks, Tag 0944], of [Stacks, Tag 08EU] and of
[Stacks, Tag 08IN] — and, through the dévissage of
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage`, at every shift of every strictly perfect
complex of `𝒪_D`-modules.

## Main results

* `isEquivalence_tensor_of_iso_shift_unit`:
  on a ringed site, `- ⊗^L K` is an equivalence when `K ≅ 𝒪[n]`.
* `isIso_projectionFormulaMap_of_iso_shift_unit`:
  the projection-formula map is an isomorphism at every `K ≅ 𝒪_D[n]`.
* `isIso_projectionFormulaMap_singleUnit_shift`:
  the same at the structure sheaf placed in every degree and shifted by every amount.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect'`:
  the projection-formula map is an isomorphism at every shift of every strictly perfect complex.

## Implementation notes

No coherence of the comparison of [Stacks, Tag 07A4] with the unit constraints is used. The map
is the mate of the square `Lf^*(- ⊗^L K) ≅ Lf^*(-) ⊗^L Lf^*K`, and both `- ⊗^L K` and
`- ⊗^L Lf^*K` are isomorphic to shift functors: by the two-variable shift structure of the derived
tensor product (`CommShift₂Int`, whose naturality in the first variable is part of the data) and
the right unitor `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso`, and on
the source side `Lf^*𝒪_D[n] ≅ 𝒪_C[n]` by [Stacks, Tag 06YY] and
`Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso`. The abstract statement
`CategoryTheory.isIso_adjunctionTensorMap_of_isEquivalence` then applies.

## References

* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaUnitInvertible

universe u

attribute [local instance] HasDerivedCategory.standard

section Site

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct X.O)

/-- `- ⊗^L K⟦n⟧ ≅ (- ⊗^L K)⟦n⟧`, naturally in the first variable: the commutation with the shift
in the second variable carried by the two-variable shift structure. -/
def tensorFlipShiftIso (K : DerivedModules X.O) (n : ℤ) :
    T.tensor.flip.obj (K⟦n⟧) ≅ T.tensor.flip.obj K ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun Z => ((T.tensor.obj Z).commShiftIso n).app K) (fun {Z Z'} g => by
    let := T.commShift₂.commShiftObj Z
    let := T.commShift₂.commShiftObj Z'
    have : NatTrans.CommShift (T.tensor.map g) ℤ := T.commShift₂.commShift_map g
    simpa using (NatTrans.shift_app_comm (T.tensor.map g) n K).symm)

/-- **Tensoring with a shift of the structure sheaf is an equivalence**: `- ⊗^L K` is isomorphic
to the shift functor `⟦n⟧` as soon as `K ≅ 𝒪[n]`. -/
theorem isEquivalence_tensor_of_iso_shift_unit {K : DerivedModules X.O} (n : ℤ)
    (e : K ≅ (unitObject X)⟦n⟧) : (T.tensor.flip.obj K).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (T.rightUnitorNatIso X).symm _ ≪≫
      (tensorFlipShiftIso X T (unitObject X) n).symm ≪≫ T.tensor.flip.mapIso e.symm)

/-- `curry (uncurry F)` with its second argument fixed is `F` with its second argument fixed. -/
def curryUncurryFlipObjIso {𝒞 : Type*} [Category* 𝒞] (F : 𝒞 ⥤ 𝒞 ⥤ 𝒞) (K : 𝒞) :
    (Functor.curry.obj (Functor.uncurry.obj F)).flip.obj K ≅ F.flip.obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {Z Z'} g => by simp)

/-- Currying the uncurried derived tensor product and fixing the second argument `K ≅ 𝒪[n]`
gives an equivalence. -/
private theorem isEquivalence_curry_uncurry_flip_obj_of_iso_shift_unit {K : DerivedModules X.O}
    (n : ℤ) (e : K ≅ (unitObject X)⟦n⟧) :
    ((Functor.curry.obj (Functor.uncurry.obj (derivedTensorProductFunctor X.O))).flip.obj
      K).IsEquivalence :=
  have := isEquivalence_tensor_of_iso_shift_unit X (canonicalDerivedTensorProduct X.O) n e
  Functor.isEquivalence_of_iso (curryUncurryFlipObjIso _ K).symm

end Site

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The projection formula at a shift of the structure sheaf.** For a morphism of ringed topoi
presented by a morphism of sites, every `E ∈ D(𝒪_C)` and every `K ∈ D(𝒪_D)` isomorphic to
`𝒪_D[n]`, the map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` of [Stacks, Tag 0B56] is an isomorphism. -/
theorem isIso_projectionFormulaMap_of_iso_shift_unit
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (n : ℤ) (e : K ≅ (unitObject ⟨Y.C, Y.J, Y.O⟩)⟦n⟧) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K) := by
  let := DerivedPullbackOnRingedTopoi.derivedPullbackCommShift f hmos
  let e' : (derivedPullback f).obj K ≅ (unitObject ⟨X.C, X.J, X.O⟩)⟦n⟧ :=
    (derivedPullback f).mapIso e ≪≫ ((derivedPullback f).commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso (Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso f hmos)
  have := isEquivalence_curry_uncurry_flip_obj_of_iso_shift_unit ⟨Y.C, Y.J, Y.O⟩ n e
  have := isEquivalence_curry_uncurry_flip_obj_of_iso_shift_unit ⟨X.C, X.J, X.O⟩ n e'
  exact isIso_adjunctionTensorMap_of_isEquivalence
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom E K

/-- The structure sheaf placed in degree `i` and shifted by `n` is the structure sheaf in degree
zero shifted by `n - i`. -/
def singleUnitShiftUnitIso (i n : ℤ) :
    (ProjectionFormulaPerfectDevissage.singleUnit Y.O i)⟦n⟧ ≅
      (unitObject ⟨Y.C, Y.J, Y.O⟩)⟦n - i⟧ :=
  ProjectionFormulaPerfectDevissage.singleUnitShiftIso Y.O i n ≪≫
    eqToIso (by congr 1; omega) ≪≫
      (ProjectionFormulaPerfectDevissage.singleUnitShiftIso Y.O 0 (n - i)).symm

/-- **The projection formula at the structure sheaf placed in every degree and shifted by every
amount**, for a morphism of ringed topoi presented by a morphism of sites and arbitrary
`E ∈ D(𝒪_C)`. -/
theorem isIso_projectionFormulaMap_singleUnit_shift
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (i n : ℤ) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      ((ProjectionFormulaPerfectDevissage.singleUnit Y.O i)⟦n⟧)) :=
  isIso_projectionFormulaMap_of_iso_shift_unit f hmos E (n - i) (singleUnitShiftUnitIso i n)

/-- **The projection formula at a strictly perfect complex**: for a morphism of ringed topoi
presented by a morphism of sites, every `E ∈ D(𝒪_C)` and every strictly perfect complex `P` of
`𝒪_D`-modules, the map `Rf_*E ⊗^L P⟦n⟧ ⟶ Rf_*(E ⊗^L Lf^*(P⟦n⟧))` is an isomorphism. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect'
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (n : ℤ) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      ((DerivedCategory.Q.obj P)⟦n⟧)) :=
  ProjectionFormulaPerfectDevissage.isIso_projectionFormulaMap_of_isStrictlyPerfect f hmos E
    (isIso_projectionFormulaMap_singleUnit_shift f hmos E) P hP n

end Stacks.Cohomology.ProjectionFormulaUnitInvertible

end
