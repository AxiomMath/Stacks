module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The mate of the slice tensor comparison is an isomorphism, and invertibility is local

Let `(C, O)` be a ringed site and `U` an object of `C` which is subterminal, so that extension by
zero `j_!` from the slice site `C/U` is fully faithful (`j^*j_! = id`); every open of a
topological space is such an object. For objects `L`, `M` of `D(O)` the canonical map

`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

of [Stacks, Tag 08I3] — the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose`, whose transpose is
the restriction of the evaluation morphism — is an isomorphism. This is [Stacks, Tag 08DL] through
the canonical map. The proof is the formal statement
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective`, fed the adjunction `j_! ⊣ j^*`
on derived categories, the slice tensor comparison
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso` with its naturality, and the
projection formula [Stacks, Tag 0GL1]; no chain-level computation and no 2-cell identity is used.

## Main results

* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose`: the mate is
  an isomorphism, for all `L` and `M`.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedSheafHomCounit_iff`: the restriction of
  the evaluation morphism `R𝓗om_O(L, M) ⊗^𝐋_O L ⟶ M` is an isomorphism exactly when the evaluation
  morphism formed over `C/U` at `L|_U`, `M|_U` is one.
* `Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`:
  **invertibility in `D(O)` is local** on a covering by subterminal objects.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction extension)

universe u

namespace Stacks.Cohomology.SliceDerivedSheafHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over U).O)
      (ComplexShape.up ℤ)]

/-- Extension by zero `j_!` from the slice site `C/U`, on unbounded derived categories: the left
adjoint of `Stacks.Cohomology.SliceDerivedSheafHom.restrictD`, written at the spelling of the
categories that the derived internal hom is stated at. -/
abbrev extensionD :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (extension X U).mapDerivedCategory

/-- **The projection formula** [Stacks, Tag 0GL1], `j_!Z ⊗^𝐋_O L ≅ j_!(Z ⊗^𝐋_{O|_U} L|_U)`, read
at the derived tensor products of [Stacks, Tag 08J8] on both sides.

The two derived tensor products of [Stacks, Tag 08J8] and of the projection formula are
compared by `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`, over `C` and
over `C/U`. That comparison is the instance at the canonical derived tensor product of
`Stacks.SheafOfModules.DerivedMonoidal.interfaceDerivedBifunctorTensorIso`, which identifies the
bifunctor of an *arbitrary* `Stacks.SheafOfModules.DerivedTensorProduct` with the K-flat descent;
the canonical one is forced here on both sides, by the tensor–internal-hom bijection of
[Stacks, Tag 08J8] on the left and by [Stacks, Tag 0GL1] on the right. -/
def projectionIso
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj ((extensionD X U).obj Z)).obj L ≅
      (extensionD X U).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj Z).obj
          ((restrictD X U).obj L)) :=
  ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app
      ((extensionD X U).obj Z)).app L ≪≫
    Stacks.DerivedTensor.ExtensionByZero.derivedTensorExtensionIso X U Z L ≪≫
    (extensionD X U).mapIso
      (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso (X.over U)).app Z).app
        ((restrictD X U).obj L)).symm

/-- The slice tensor comparison `(A ⊗^𝐋_O B)|_U ≅ A|_U ⊗^𝐋_{O|_U} B|_U` as an isomorphism of
bifunctors, at the derived tensor products of [Stacks, Tag 08J8]: the natural isomorphism
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionNatIso` conjugated by the two
comparisons of derived tensor products. -/
def sliceTensorRestrictionNatIso :
    Stacks.SheafOfModules.derivedTensorProductFunctor X ⋙
        (Functor.whiskeringRight _ _ _).obj (restrictD X U) ≅
      restrictD X U ⋙ Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U) ⋙
        (Functor.whiskeringLeft _ _ _).obj (restrictD X U) :=
  Functor.isoWhiskerRight (kFlatTensorBridge X).symm
      ((Functor.whiskeringRight _ _ _).obj (restrictD X U)) ≪≫
    Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionNatIso X U ≪≫
    Functor.isoWhiskerLeft (restrictD X U)
      (Functor.isoWhiskerRight (kFlatTensorBridge (X.over U))
        ((Functor.whiskeringLeft _ _ _).obj (restrictD X U)))

/-- At a pair of objects, `sliceTensorRestrictionNatIso` is
`Stacks.Cohomology.SliceDerivedSheafHom.sliceTensorRestrictionObjIso`. -/
theorem sliceTensorRestrictionNatIso_hom_app_app
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((sliceTensorRestrictionNatIso X U).hom.app A).app B =
      (sliceTensorRestrictionObjIso X U A B).hom :=
  rfl

/-- **The slice tensor comparison is natural in its first variable.** -/
theorem sliceTensorRestrictionObjIso_naturality
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ A')
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (restrictD X U).map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app B) ≫
        (sliceTensorRestrictionObjIso X U A' B).hom =
      (sliceTensorRestrictionObjIso X U A B).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
          ((restrictD X U).map f)).app ((restrictD X U).obj B) := by
  rw [← sliceTensorRestrictionNatIso_hom_app_app, ← sliceTensorRestrictionNatIso_hom_app_app]
  exact NatTrans.congr_app ((sliceTensorRestrictionNatIso X U).hom.naturality f) B

omit [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over U).O)
      (ComplexShape.up ℤ)] in
/-- **The evaluation morphism exhibits the derived internal hom as an internal hom**: morphisms
`Z ⟶ R𝓗om_O(L, M)` correspond to morphisms `Z ⊗^𝐋_O L ⟶ M` under `g ↦ (g ⊗ 1) ≫ e`. This is
the bijection of [Stacks, Tag 08J8] with its formula
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply` substituted. -/
theorem bijective_derivedSheafHomCounit
    (Z L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Function.Bijective (fun g : Z ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M =>
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app L ≫
        RingedSite.derivedSheafHomCounit X L M) := by
  have h : (fun g : Z ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M =>
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app L ≫
        RingedSite.derivedSheafHomCounit X L M) = RingedSite.derivedCurryHomEquiv X Z L M :=
    funext fun g => (RingedSite.derivedCurryHomEquiv_apply X Z L M g).symm
  rw [h]
  exact (RingedSite.derivedCurryHomEquiv X Z L M).bijective

variable [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit]

/-- **The mate of the slice tensor comparison is an isomorphism.** For a ringed site `(C, O)`, an
object `U` of `C` which is subterminal (so that `j^*j_! = id`, as for every open of a topological
space) and objects `L`, `M` of `D(O)`, the canonical map

`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)`

of [Stacks, Tag 08I3] at the localization morphism — the transpose of the restricted evaluation
morphism — is an isomorphism. This is [Stacks, Tag 08DL] through that canonical map; the proof
is `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective` fed the adjunction
`j_! ⊣ j^*`, the slice tensor comparison and the projection formula [Stacks, Tag 0GL1]. -/
theorem isIso_derivedSheafHomRestrictionTranspose
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (derivedSheafHomRestrictionTranspose X U L M) := by
  have := Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit X U
  have currying_eq : sliceCurryEquiv X U L M =
      RingedSite.derivedCurryHomEquiv (X.over U)
        ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
        ((restrictD X U).obj L) ((restrictD X U).obj M) := rfl
  have transpose_image := congrArg (fun morphism => sliceCurryEquiv X U L M morphism)
    (derivedSheafHomRestrictionTranspose_eq_symm_apply X U L M)
  have ht := (transpose_image.trans
    ((sliceCurryEquiv X U L M).apply_symm_apply (derivedSheafHomRestrictionDatum X U L M))).symm
  rw [currying_eq, RingedSite.derivedCurryHomEquiv_apply] at ht
  exact CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective
    (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U))
    (Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction X U)
    (sliceTensorRestrictionObjIso X U)
    (fun f B => sliceTensorRestrictionObjIso_naturality X U f B)
    (projectionIso X U)
    (RingedSite.derivedSheafHomCounit X L M)
    (fun Z => bijective_derivedSheafHomCounit X Z L M)
    (RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L) ((restrictD X U).obj M))
    (fun Z => bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (derivedSheafHomRestrictionTranspose X U L M) ht.symm


/-- **The comparison of [Stacks, Tag 08DL] through the canonical map**, as an isomorphism
`R𝓗om_O(L, M)|_U ≅ R𝓗om_{O|_U}(L|_U, M|_U)`. -/
def derivedSheafHomRestrictionTransposeIso
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M) ≅
      ((RingedSite.derivedSheafHomBifunctor (X.over U)).obj
          (op ((restrictD X U).obj L))).obj ((restrictD X U).obj M) :=
  haveI := isIso_derivedSheafHomRestrictionTranspose X U L M
  asIso (derivedSheafHomRestrictionTranspose X U L M)

/-- **Restriction to a subterminal object carries the evaluation morphism to an isomorphism exactly
when the evaluation morphism of the restrictions is one.** -/
theorem isIso_map_derivedSheafHomCounit_iff
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso ((restrictD X U).map (RingedSite.derivedSheafHomCounit X L M)) ↔
      IsIso (RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L)
        ((restrictD X U).obj M)) := by
  have := Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit X U
  have currying_eq : sliceCurryEquiv X U L M =
      RingedSite.derivedCurryHomEquiv (X.over U)
        ((restrictD X U).obj (((RingedSite.derivedSheafHomBifunctor X).obj (op L)).obj M))
        ((restrictD X U).obj L) ((restrictD X U).obj M) := rfl
  have transpose_image := congrArg (fun morphism => sliceCurryEquiv X U L M morphism)
    (derivedSheafHomRestrictionTranspose_eq_symm_apply X U L M)
  have ht := (transpose_image.trans
    ((sliceCurryEquiv X U L M).apply_symm_apply (derivedSheafHomRestrictionDatum X U L M))).symm
  rw [currying_eq, RingedSite.derivedCurryHomEquiv_apply] at ht
  exact CategoryTheory.InternalHomTransfer.isIso_map_iff_of_tensorHomBijective
    (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U))
    (Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction X U)
    (sliceTensorRestrictionObjIso X U)
    (fun f B => sliceTensorRestrictionObjIso_naturality X U f B)
    (projectionIso X U)
    (RingedSite.derivedSheafHomCounit X L M)
    (fun Z => bijective_derivedSheafHomCounit X Z L M)
    (RingedSite.derivedSheafHomCounit (X.over U) ((restrictD X U).obj L) ((restrictD X U).obj M))
    (fun Z => bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (derivedSheafHomRestrictionTranspose X U L M) ht.symm

end Slice

/-! ### Invertibility is local -/

section Glueing

variable (X : RingedSite.{u, u, u}) [HasBinaryProducts X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **Invertibility in `D(O)` is local.** Let `Y` be a family of subterminal objects covering a
ringed site — for instance a family of opens covering a topological space. An object of `D(O)`
whose restriction to each `C/Y i` is an invertible object of `D(O|_{Y i})` is an invertible object
of `D(O)`. -/
theorem isInvertible_of_isInvertible_restriction
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    [∀ i, IsIso (Over.forgetAdjStar (Y i)).unit]
    [∀ i, HasSheafify (X.J.over (Y i)) AddCommGrpCat.{u}]
    [∀ i, (X.J.over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (Y i)).Additive]
    [∀ i, (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).Additive]
    [∀ i, ∀ M, ((sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).obj M).Additive]
    [∀ i, ∀ (K L : CochainComplex (Modules (X.over (Y i)).O) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O)
        (ComplexShape.up ℤ)]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : ∀ i, letI := RingedSite.derivedTensorMonoidal (X.over (Y i))
      MonoidalCategory.IsInvertible ((restrictD X (Y i)).obj L)) :
    letI := RingedSite.derivedTensorMonoidal X
    MonoidalCategory.IsInvertible L :=
  isInvertible_of_isIso_transpose_of_isInvertible_restriction X hY L
    (fun i => isIso_derivedSheafHomRestrictionTranspose X (Y i) L _) hL

end Glueing

end Stacks.Cohomology.SliceDerivedSheafHom

end
