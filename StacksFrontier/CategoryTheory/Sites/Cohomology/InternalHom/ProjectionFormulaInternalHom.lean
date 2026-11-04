module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom and derived direct image

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `L`, `M` be objects
of `D(O_C)`.  There is a canonical map

`Rf_*RHom_{O_C}(L, M) ⟶ RHom_{O_D}(Rf_*L, Rf_*M)`

of [Stacks, Tag 0B6D].  Under the tensor–internal-Hom bijection on `D(O_D)`
([Stacks, Tag 08J8]) it corresponds to

`Rf_*RHom_{O_C}(L, M) ⊗^L_{O_D} Rf_*L ⟶ Rf_*(RHom_{O_C}(L, M) ⊗^L_{O_C} L) ⟶ Rf_*M`,

the relative cup product of [Stacks, Tag 0B6C] followed by `Rf_*` of the evaluation morphism
`RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`.

## Main definitions

All in the namespace `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi`.

* `derivedPushforwardSheafHomMap` — the canonical map of [Stacks, Tag 0B6D], when `f` comes
  from a morphism of sites, for the development's own derived internal Hom
  `derivedSheafHomBifunctor` and its tensor–internal-Hom bijection `derivedCurryHomEquiv` of
  [Stacks, Tag 08J8].
* `derivedTensorHomBijection` — that bijection, read at the derived tensor product the relative
  cup product is stated over, as `TensorHomBijection` data.
* `TensorHomBijection` — the tensor–internal-Hom bijection `(A ⟶ RHom(B, M)) ≃ (A ⊗ B ⟶ M)` of
  [Stacks, Tag 08J8] for an abstract pair of a tensor and an internal Hom bifunctor, and
  `TensorHomAdjunction` — the same together with its naturality in the three objects.
* `TensorHomBijection.evaluation` — the evaluation morphism `RHom(L, M) ⊗ L ⟶ M`, the image of
  the identity of `RHom(L, M)` under that bijection.
* `projectionFormulaInternalHomMap` — the construction of the canonical map at an abstract
  bijection, of which the map of [Stacks, Tag 0B6D] is the instance at the development's own
  data.

## Main results

* `derivedPushforwardSheafHomMap_homEquiv` — the defining property of the canonical map of
  [Stacks, Tag 0B6D]: its adjunct under the bijection of [Stacks, Tag 08J8] on `D(O_D)` is the
  relative cup product followed by direct image of evaluation.
* `derivedPushforwardSheafHomMap_eq` — the canonical map is that construction at the
  development's own data, so a consumer never unfolds the definition.
* `derivedTensorCurryHomEquiv_apply` and `derivedTensorHomBijection_homEquiv` — the bijection is
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` followed by the comparison of the two
  derived tensor products.
* `derivedTensorHomBijection_evaluation` — the evaluation morphism of that bijection is the
  counit `AlgebraicGeometry.RingedSite.derivedSheafHomCounit` of [Stacks, Tag 08J8], read across
  the comparison of the two derived tensor products.
* `projectionFormulaInternalHomMap_homEquiv`, and
  `projectionFormulaInternalHomMap_naturality_source`,
  `projectionFormulaInternalHomMap_naturality_target` — the same defining property, and
  contravariance in `L` and covariance in `M`, at an abstract bijection; the naturality clauses
  need the naturality of the bijection and so are stated for `TensorHomAdjunction`.

## Implementation notes

*The evaluation morphism.*  Remark [Stacks, Tag 0B6D] obtains `RHom(L, M) ⊗^L L ⟶ M` from the
composition morphism of [Stacks, Tag 0A98] "with `O` in one of the spots", that is by composing
it with the identification `RHom(O, M) ≅ M`, which is
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`.  The evaluation morphism is
instead taken here to be the image of the identity of `RHom(L, M)` under the
tensor–internal-Hom bijection of [Stacks, Tag 08J8], which is the development's own
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit` and is the deliberately equivalent
description: in a closed monoidal setting the two agree, and the second is a pinned canonical
morphism rather than a choice.  The identification of the two routes is not formed here, and is
what this file still owes the source.

*What the canonical map is built from.*  The relative cup product here is the site-presented
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct`, which asks the functor
underlying `f` to be a morphism of sites (`hmos`).  The canonical map of [Stacks, Tag 0B6D] for an
arbitrary morphism of ringed topoi, built from the relative cup product
`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct` with no such hypothesis, is
`Stacks.Cohomology.PushforwardInternalHomOfToposHom.derivedPushforwardSheafHomMap`, the full
form of the tag; the map here is registered as its site-presented variant.  The internal Hom
bifunctor is
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` and the bijection is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, the bijection of [Stacks, Tag 08J8].

*Which derived tensor product the bijection is read at.*  There are two constructions of the
derived tensor product of [Stacks, Tag 06YU] in this development, with distinct canonical
choices: `Stacks.SheafOfModules.derivedTensorProductFunctor`, indexed by a ringed *site*, which
is the one the derived internal Hom development uses — in particular the one [Stacks, Tag 08J8]
is stated at — and `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, indexed by the
sheaf of rings, which is the one derived pullback uses, so the one the compatibility
`Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of [Stacks, Tag 07A4] and hence the relative cup product are
stated at.  The two are isomorphic by
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`, both being computed by the
total tensor complex on K-flat representatives, and `derivedTensorHomBijection` reads the
bijection of [Stacks, Tag 08J8] across that isomorphism, at the second tensor product, which is
the one the relative cup product lands in and so the only one at which the adjunct below can be
formed.

*Why the bijection and not an adjunction of functors.*  `TensorHomBijection` is a family of
bijections of morphism groups indexed by all three objects rather than a family of
`CategoryTheory.Adjunction`s indexed by the middle object, because that is the shape in which
[Stacks, Tag 08J8] is stated and in which the repository provides it: `D(O)` carries no
`CategoryTheory.MonoidalClosed` structure, and the derived internal Hom is not constructed as a
right adjoint.

*What the abstract layer is for, and what is not asserted of the canonical map.*  Remark
[Stacks, Tag 0B6D] asserts the canonical map and nothing more, and that is what
`derivedPushforwardSheafHomMap` and its defining property carry the tag for.  A consumer may
also want the map to be contravariant in `L` and covariant in `M`.  Those two clauses need the
naturality of the bijection of [Stacks, Tag 08J8] in its three objects, which is a **recorded
gap** of this development — see the "What this file does not contain" section of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying`, which reduces it to
the naturality of [Stacks, Tag 0A94] in both variables — so they are proved here only at the
abstract `TensorHomAdjunction`, where the naturality is part of the data, and are **not**
asserted of `derivedPushforwardSheafHomMap`.  That abstract layer is also what
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.PushforwardTrace`
([Stacks, Tag 0E57]) is stated over.

## References

* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u

/-! ### The tensor–internal-Hom bijection -/

section TensorHom

variable {C : Type*} [Category C]

/-- **The tensor–internal-Hom bijection of [Stacks, Tag 08J8]** between a tensor bifunctor `T`
and an internal Hom bifunctor `H` on a category: the bijection
`(A ⟶ H(B, M)) ≃ (T(A, B) ⟶ M)`. -/
structure TensorHomBijection (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) where
  /-- The bijection `(A ⟶ H(B, M)) ≃ (T(A, B) ⟶ M)`. -/
  homEquiv (A B M : C) : (A ⟶ (H.obj (op B)).obj M) ≃ ((T.obj A).obj B ⟶ M)

/-- **The tensor–internal-Hom adjunction of [Stacks, Tag 08J8]**: the bijection
`(A ⟶ H(B, M)) ≃ (T(A, B) ⟶ M)` together with its naturality in the source `A`, in the object
`B` and in the target `M`. -/
structure TensorHomAdjunction (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) extends
    TensorHomBijection T H where
  /-- Naturality in the source `A`: precomposing with `u : A' ⟶ A` corresponds to precomposing
  with `u ⊗ 1`. -/
  homEquiv_naturality_source {A A' B M : C} (u : A' ⟶ A) (h : A ⟶ (H.obj (op B)).obj M) :
    homEquiv A' B M (u ≫ h) = (T.map u).app B ≫ homEquiv A B M h
  /-- Naturality in the object `B`: postcomposing with the contravariant action of `g : B' ⟶ B`
  on the internal Hom corresponds to precomposing with `1 ⊗ g`. -/
  homEquiv_naturality_middle {A B B' M : C} (g : B' ⟶ B) (h : A ⟶ (H.obj (op B)).obj M) :
    homEquiv A B' M (h ≫ (H.map g.op).app M) = (T.obj A).map g ≫ homEquiv A B M h
  /-- Naturality in the target `M`: postcomposing with the covariant action of `m : M ⟶ M'` on
  the internal Hom corresponds to postcomposing with `m`. -/
  homEquiv_naturality_target {A B M M' : C} (h : A ⟶ (H.obj (op B)).obj M) (m : M ⟶ M') :
    homEquiv A B M' (h ≫ (H.obj (op B)).map m) = homEquiv A B M h ≫ m

namespace TensorHomBijection

variable {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (D : TensorHomBijection T H)

/-- **The evaluation morphism** `H(L, M) ⊗ L ⟶ M`: the image of the identity of `H(L, M)` under
the tensor–internal-Hom bijection. -/
def evaluation (L M : C) : (T.obj ((H.obj (op L)).obj M)).obj L ⟶ M :=
  D.homEquiv ((H.obj (op L)).obj M) L M (𝟙 ((H.obj (op L)).obj M))

end TensorHomBijection

namespace TensorHomAdjunction

variable {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (D : TensorHomAdjunction T H)

/-- **The evaluation morphism is covariant in the target of the internal Hom.** -/
theorem evaluation_naturality_target (L : C) {M M' : C} (m : M ⟶ M') :
    (T.map ((H.obj (op L)).map m)).app L ≫ D.toTensorHomBijection.evaluation L M' =
      D.toTensorHomBijection.evaluation L M ≫ m := by
  have h₁ := D.homEquiv_naturality_source ((H.obj (op L)).map m) (𝟙 ((H.obj (op L)).obj M'))
  have h₂ := D.homEquiv_naturality_target (𝟙 ((H.obj (op L)).obj M)) m
  rw [Category.comp_id] at h₁
  rw [Category.id_comp] at h₂
  exact h₁.symm.trans h₂

/-- **The evaluation morphism is contravariant in the source of the internal Hom.** -/
theorem evaluation_naturality_source {L L' : C} (g : L' ⟶ L) (M : C) :
    (T.map ((H.map g.op).app M)).app L' ≫ D.toTensorHomBijection.evaluation L' M =
      (T.obj ((H.obj (op L)).obj M)).map g ≫ D.toTensorHomBijection.evaluation L M := by
  have h₁ := D.homEquiv_naturality_source ((H.map g.op).app M) (𝟙 ((H.obj (op L')).obj M))
  have h₂ := D.homEquiv_naturality_middle g (𝟙 ((H.obj (op L)).obj M))
  rw [Category.comp_id] at h₁
  rw [Category.id_comp] at h₂
  exact h₁.symm.trans h₂

end TensorHomAdjunction

end TensorHom

attribute [local instance] HasDerivedCategory.standard

/-! ### The bijection of Tag 08J8 at the derived tensor product of the relative cup product -/

section Site

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- **The tensor–internal-Hom bijection of [Stacks, Tag 08J8] at the derived tensor product the
relative cup product is stated over.**  It is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, whose tensor product is the site-indexed
one, read across the comparison
`AlgebraicGeometry.RingedSite.derivedTensorObjIso` of the two derived tensor products of
[Stacks, Tag 06YU]. -/
def derivedTensorCurryHomEquiv
    (A B M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (A ⟶ ((RingedSite.derivedSheafHomBifunctor Z).obj (op B)).obj M) ≃
      (((derivedTensorProductFunctor Z.O).obj A).obj B ⟶ M) where
  toFun h :=
    (RingedSite.derivedTensorObjIso Z A B).inv ≫ RingedSite.derivedCurryHomEquiv Z A B M h
  invFun g :=
    (RingedSite.derivedCurryHomEquiv Z A B M).symm ((RingedSite.derivedTensorObjIso Z A B).hom ≫ g)
  left_inv h := by simp
  right_inv g := by simp

/-- What `derivedTensorCurryHomEquiv` does to a morphism: the comparison of the two derived
tensor products, then the bijection of [Stacks, Tag 08J8]. -/
theorem derivedTensorCurryHomEquiv_apply
    (A B M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (h : A ⟶ ((RingedSite.derivedSheafHomBifunctor Z).obj (op B)).obj M) :
    derivedTensorCurryHomEquiv Z A B M h =
      (RingedSite.derivedTensorObjIso Z A B).inv ≫ RingedSite.derivedCurryHomEquiv Z A B M h :=
  rfl

/-- The bijection of [Stacks, Tag 08J8] between the development's derived tensor product and its
derived internal Hom, as `TensorHomBijection` data. -/
def derivedTensorHomBijection :
    TensorHomBijection (derivedTensorProductFunctor Z.O) (RingedSite.derivedSheafHomBifunctor Z)
    where
  homEquiv := derivedTensorCurryHomEquiv Z

/-- The bijection of that `TensorHomBijection` is `derivedTensorCurryHomEquiv`, so a consumer
never unfolds the structure. -/
theorem derivedTensorHomBijection_homEquiv :
    (derivedTensorHomBijection Z).homEquiv = derivedTensorCurryHomEquiv Z :=
  rfl

/-- **The evaluation morphism of that bijection is the counit
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit` of [Stacks, Tag 08J8]**, read across the
comparison of the two derived tensor products. -/
theorem derivedTensorHomBijection_evaluation
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedTensorHomBijection Z).evaluation L M =
      (RingedSite.derivedTensorObjIso Z
          (((RingedSite.derivedSheafHomBifunctor Z).obj (op L)).obj M) L).inv ≫
        RingedSite.derivedSheafHomCounit Z L M := by
  simp only [TensorHomBijection.evaluation, derivedTensorHomBijection,
    RingedSite.derivedSheafHomCounit, derivedTensorCurryHomEquiv, Equiv.coe_fn_mk]

end Site

/-! ### The canonical map of Tag 0B6D -/

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (HX : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (HY : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

section Bijection

variable (DX : TensorHomBijection (derivedTensorProductFunctor X.O) HX)
  (DY : TensorHomBijection (derivedTensorProductFunctor Y.O) HY)

/-- The construction of the canonical map of [Stacks, Tag 0B6D] at an abstract
tensor–internal-Hom bijection on each of `D(O_C)` and `D(O_D)`: the morphism which the
bijection on `D(O_D)` sends to the relative cup product of [Stacks, Tag 0B6C] followed by
`Rf_*` of the evaluation morphism.  Its instance at the development's own derived internal Hom
is `derivedPushforwardSheafHomMap`. -/
def projectionFormulaInternalHomMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj ((HX.obj (op L)).obj M) ⟶
      (HY.obj (op ((derivedPushforward f).obj L))).obj ((derivedPushforward f).obj M) :=
  (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
      ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)).symm
    (relativeCupProduct f hmos ((HX.obj (op L)).obj M) L ≫
      (derivedPushforward f).map (DX.evaluation L M))

/-- **The defining property of the canonical map**: its adjunct under the tensor–internal-Hom
bijection on `D(O_D)` is the relative cup product followed by `Rf_*` of the evaluation
morphism. -/
theorem projectionFormulaInternalHomMap_homEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
        ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)
        (projectionFormulaInternalHomMap f hmos HX HY DX DY L M) =
      relativeCupProduct f hmos ((HX.obj (op L)).obj M) L ≫
        (derivedPushforward f).map (DX.evaluation L M) := by
  dsimp only [projectionFormulaInternalHomMap]
  exact (DY.homEquiv _ _ _).apply_symm_apply _

end Bijection

section Adjunction

variable (DX : TensorHomAdjunction (derivedTensorProductFunctor X.O) HX)
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.O) HY)

/-- **The canonical map at an abstract adjunction is covariant in the target `M`.** -/
theorem projectionFormulaInternalHomMap_naturality_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    (derivedPushforward f).map ((HX.obj (op L)).map m) ≫
        projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
          DY.toTensorHomBijection L M' =
      projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
          DY.toTensorHomBijection L M ≫
        (HY.obj (op ((derivedPushforward f).obj L))).map ((derivedPushforward f).map m) := by
  apply (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
    ((derivedPushforward f).obj L) ((derivedPushforward f).obj M')).injective
  have hev := DX.evaluation_naturality_target L m
  have hcup := relativeCupProduct_naturality_left f hmos ((HX.obj (op L)).map m) L
  dsimp only [projectionFormulaInternalHomMap]
  rw [DY.homEquiv_naturality_source, DY.homEquiv_naturality_target,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, reassoc_of% hcup, ← Functor.map_comp, hev,
    Functor.map_comp, Category.assoc]

/-- **The canonical map at an abstract adjunction is contravariant in the source `L`.** -/
theorem projectionFormulaInternalHomMap_naturality_source
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L' ⟶ L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).map ((HX.map g.op).app M) ≫
        projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
          DY.toTensorHomBijection L' M =
      projectionFormulaInternalHomMap f hmos HX HY DX.toTensorHomBijection
          DY.toTensorHomBijection L M ≫
        (HY.map ((derivedPushforward f).map g).op).app ((derivedPushforward f).obj M) := by
  apply (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
    ((derivedPushforward f).obj L') ((derivedPushforward f).obj M)).injective
  have hev := DX.evaluation_naturality_source g M
  have hcupL := relativeCupProduct_naturality_left f hmos ((HX.map g.op).app M) L'
  have hcupR := relativeCupProduct_naturality_right f hmos ((HX.obj (op L)).obj M) g
  dsimp only [projectionFormulaInternalHomMap]
  rw [DY.homEquiv_naturality_source, DY.homEquiv_naturality_middle,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, reassoc_of% hcupL, ← Functor.map_comp, hev,
    Functor.map_comp, ← reassoc_of% hcupR]

end Adjunction

/-- The canonical map of [Stacks, Tag 0B6D] when the morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` comes from a morphism of sites: for objects `L`, `M` of
`D(O_C)`, the map

`Rf_*RHom_{O_C}(L, M) ⟶ RHom_{O_D}(Rf_*L, Rf_*M)`.

It is the morphism which the tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(O_D)`
sends to the relative cup product of [Stacks, Tag 0B6C] followed by `Rf_*` of the evaluation
morphism `RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`. -/
@[stacks 0B6D "the canonical map, variant: the special case of a morphism of ringed topoi
presented by a morphism of sites; the tag for an arbitrary morphism of ringed topoi is
Stacks.Cohomology.PushforwardInternalHomOfToposHom.derivedPushforwardSheafHomMap"]
def derivedPushforwardSheafHomMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj
        (op ((derivedPushforward f).obj L))).obj ((derivedPushforward f).obj M) :=
  projectionFormulaInternalHomMap f hmos
    (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X))
    (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
    (derivedTensorHomBijection (RingedTopos.toRingedSite X))
    (derivedTensorHomBijection (RingedTopos.toRingedSite Y)) L M

/-- The canonical map of [Stacks, Tag 0B6D] is the construction `projectionFormulaInternalHomMap`
at the development's own derived internal Hom and its bijection of [Stacks, Tag 08J8], so a
consumer never unfolds the definition. -/
theorem derivedPushforwardSheafHomMap_eq
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedPushforwardSheafHomMap f hmos L M =
      projectionFormulaInternalHomMap f hmos
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X))
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
        (derivedTensorHomBijection (RingedTopos.toRingedSite X))
        (derivedTensorHomBijection (RingedTopos.toRingedSite Y)) L M :=
  rfl

/-- **The defining property of the canonical map of [Stacks, Tag 0B6D]**: its adjunct under the
tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(O_D)` is the relative cup product of
[Stacks, Tag 0B6C] followed by `Rf_*` of the evaluation morphism
`RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`. -/
@[stacks 0B6D "the defining adjunction property, variant: the special case of a morphism of
ringed topoi presented by a morphism of sites; the tag for an arbitrary morphism of ringed topoi
is Stacks.Cohomology.PushforwardInternalHomOfToposHom.derivedPushforwardSheafHomMap_homEquiv"]
theorem derivedPushforwardSheafHomMap_homEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorHomBijection (RingedTopos.toRingedSite Y)).homEquiv
        ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite X)).obj (op L)).obj M))
        ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)
        (derivedPushforwardSheafHomMap f hmos L M) =
      relativeCupProduct f hmos
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite X)).obj (op L)).obj M) L ≫
        (derivedPushforward f).map
          ((derivedTensorHomBijection (RingedTopos.toRingedSite X)).evaluation L M) := by
  rw [derivedPushforwardSheafHomMap_eq, projectionFormulaInternalHomMap_homEquiv]

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

end
