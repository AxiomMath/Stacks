module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# The restriction comparison of the total tensor complex is natural in both variables

Let `X` be a ringed site, `U` an object of its underlying category and `A`, `B` complexes of
`O`-modules. The comparison `AlgebraicGeometry.RingedSite.tensorComplexOverIso` identifies the
restriction of `Tot(A ⊗_O B)` to the site over `U` with the total tensor complex
`Tot(A|_U ⊗_{O|_U} B|_U)` formed there. This file records that the identification is natural in
`A` and in `B`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorComplexOverIso_inv_naturality_left` and
  `AlgebraicGeometry.RingedSite.tensorComplexOverIso_inv_naturality_right`: the two naturality
  squares, for the inverse of the comparison.
* `AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_left` and
  `AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_right`: the same two
  squares read through the comparison rather than its inverse.
* `AlgebraicGeometry.RingedSite.ι_tensorComplexOverIso_inv_naturality_left` and
  `AlgebraicGeometry.RingedSite.ι_tensorComplexOverIso_inv_naturality_right`: each square on the
  summand of one bidegree, which is what the two squares are checked on.
* `AlgebraicGeometry.RingedSite.sheafTensorOverIso_inv_naturality_left` and
  `AlgebraicGeometry.RingedSite.sheafTensorOverIso_inv_naturality_right`: the naturality of the
  objectwise comparison, read through its inverse.
* `AlgebraicGeometry.RingedSite.ι_mapBifunctorMap_id_right` and
  `AlgebraicGeometry.RingedSite.ι_mapBifunctorMap_id_left`: for an arbitrary bifunctor, the
  inclusion of one summand through the map of total complexes induced by a morphism in one
  variable and the identity in the other, with that identity collapsed.

## Implementation notes

The squares are proved for the **inverse** of the comparison, because it is the inverse that
the library computes: `AlgebraicGeometry.RingedSite.ι_tensorComplexOverIso_inv` evaluates it on
the summand of a fixed bidegree of the bicomplex over `U`, and that evaluation together with
`AlgebraicGeometry.RingedSite.ι_mapBifunctorMap_id_right` reduces each square to the naturality
of the objectwise comparison `AlgebraicGeometry.RingedSite.sheafTensorOverIso` at a single
bidegree. A morphism out of a total complex is determined by its restrictions to those summands
(`HomologicalComplex₂.total.hom_ext`), so nothing else is needed. The `hom` forms are the `inv`
forms conjugated, with no further computation.

**Everything below is in term mode, and has to be.** The slice's ring sheaf has two spellings,
`(Tensor.ringSheaf X.O).over U` and `Tensor.ringSheaf (X.O.over U)`; they denote the same object
but are not reducibly equal. Consequently a composite that mentions both — which every square
here does, the restriction functor landing in the first spelling and the tensor product formed
over `U` in the second — is not type-correct at the `implicit` transparency level at which
`rewrite` checks the motive it builds, and at which `simp` keys its discrimination tree. So
`rw [← Category.assoc]` reports that it cannot find `?f ≫ ?g ≫ ?h` in a goal that visibly is
one, and `simp` handed the relevant equation as a rewrite rule reports no progress. `Eq.trans`,
`congrArg` and the `Iso` lemmas applied as terms check their arguments up to definitional
unfolding instead, and go through; the associativity and functoriality steps of each square are
therefore spelled out one `.trans` at a time rather than normalised by a tactic.

Two further consequences of the same ambiguity. Both halves of each square are written with the
factor formed *over* `U` first, which is the seating
`AlgebraicGeometry.RingedSite.ι_tensorComplexOverIso_inv` is stated in; writing them the other
way round makes `HomologicalComplex₂.total.hom_ext` itself cross the two spellings, which
exhausts the heartbeat budget of the declaration outright. And the summand lemma for the induced
map of total complexes is stated for an arbitrary bifunctor, in Mathlib's own
`HomologicalComplex.mapBifunctor` vocabulary, rather than for `sheafTensor` in the vocabulary of
`AlgebraicGeometry.RingedSite.sheafTensorBicomplex`: the two vocabularies are definitionally the
same complex, but `simp` cannot prove the statement in the second, where it can in the first.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor Stacks.SheafOfModules.UliftTensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

section Generic

variable {C₁ : Type*} {C₂ : Type*} {D : Type*} [Category C₁] [Category C₂] [Category D]
  [Limits.HasZeroMorphisms C₁] [Limits.HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [hFZero : F.PreservesZeroMorphisms]
  [hFObjZero : ∀ Y, (F.obj Y).PreservesZeroMorphisms]

/-- **The inclusion of one summand through a map of total complexes induced in the first
variable.** The second-variable identity collapses, so what is left is the bifunctor applied to
the component of the morphism in the first degree, followed by the inclusion of the
corresponding summand of the target. -/
lemma ι_mapBifunctorMap_id_right {A A' : CochainComplex C₁ ℤ} (f : A ⟶ A')
    (B : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor A B F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor A' B F (ComplexShape.up ℤ)] (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c) :
    HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) t r c h ≫
        (HomologicalComplex.mapBifunctorMap f (𝟙 B) F (ComplexShape.up ℤ)).f c =
      (F.map (f.f t)).app (B.X r) ≫
        HomologicalComplex.ιMapBifunctor A' B F (ComplexShape.up ℤ) t r c h := by
  simp

/-- **The inclusion of one summand through a map of total complexes induced in the second
variable.** -/
lemma ι_mapBifunctorMap_id_left (A : CochainComplex C₁ ℤ)
    {B B' : CochainComplex C₂ ℤ} (g : B ⟶ B')
    [HomologicalComplex.HasMapBifunctor A B F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor A B' F (ComplexShape.up ℤ)] (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c) :
    HomologicalComplex.ιMapBifunctor A B F (ComplexShape.up ℤ) t r c h ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 A) g F (ComplexShape.up ℤ)).f c =
      (F.obj (A.X t)).map (g.f r) ≫
        HomologicalComplex.ιMapBifunctor A B' F (ComplexShape.up ℤ) t r c h := by
  simp

end Generic

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

section Objectwise

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

/-- **The objectwise restriction comparison is natural in the first variable**, read through the
inverse of the comparison. -/
lemma sheafTensorOverIso_inv_naturality_left
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : M ⟶ M')
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafTensorOverIso X U M N).inv ≫ (((sheafTensor.{u, u, u, u, u} X.O).map f).app N).over U =
      ((sheafTensor.{u, u, u, u, u} (X.O.over U)).map (f.over U)).app (N.over U) ≫
        (sheafTensorOverIso X U M' N).inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (sheafTensorOverIso_naturality_left X U f N)).trans
      (Category.assoc _ _ _))

/-- **The objectwise restriction comparison is natural in the second variable**, read through
the inverse of the comparison. -/
lemma sheafTensorOverIso_inv_naturality_right
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : N ⟶ N') :
    (sheafTensorOverIso X U M N).inv ≫ (((sheafTensor.{u, u, u, u, u} X.O).obj M).map g).over U =
      ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj (M.over U)).map (g.over U) ≫
        (sheafTensorOverIso X U M N').inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (sheafTensorOverIso_naturality_right X U M g)).trans
      (Category.assoc _ _ _))

end Objectwise

section Left

variable {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (f : A ⟶ A')
  (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The restriction comparison is natural in the first variable, on a summand.** -/
lemma ι_tensorComplexOverIso_inv_naturality_left (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c) :
    (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫
        (((tensorComplex (X.O.over U)).map (restrictComplexMap X U f)).app
          (restrictComplex X B U) ≫ (tensorComplexOverIso X U A' B).inv).f c =
      (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫
        ((tensorComplexOverIso X U A B).inv ≫
          restrictComplexMap X U (((tensorComplex X.O).map f).app B)).f c := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (tensorComplexOverIso X U A' B).inv.f c)
    (ι_mapBifunctorMap_id_right (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (hFZero := Functor.preservesZeroMorphisms_of_additive
        (sheafTensor.{u, u, u, u, u} (X.O.over U)))
      (hFObjZero := fun M => Functor.preservesZeroMorphisms_of_additive
        ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M))
      (restrictComplexMap X U f) (restrictComplex X B U) t r c h)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z) (ι_tensorComplexOverIso_inv X U A' B t r c h)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ _)
    (sheafTensorOverIso_inv_naturality_left X U (f.f t) (B.X r)).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_comp
      _ _).symm).trans ?_
  refine (congrArg (fun z => _ ≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map z)
    (ι_mapBifunctorMap_id_right (sheafTensor.{u, u, u, u, u} X.O)
      (hFZero := Functor.preservesZeroMorphisms_of_additive (sheafTensor.{u, u, u, u, u} X.O))
      (hFObjZero := fun M => Functor.preservesZeroMorphisms_of_additive
        ((sheafTensor.{u, u, u, u, u} X.O).obj M)) f B t r c h).symm).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_comp
      _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ _)
    (ι_tensorComplexOverIso_inv X U A B t r c h).symm).trans ?_
  exact Category.assoc _ _ _

/-- **The restriction comparison of the total tensor complex is natural in the first
variable.** For a morphism `f : A ⟶ A'` of complexes of `O`-modules, the square relating the
inverse comparisons at `(A, B)` and at `(A', B)` to `Tot(f|_U ⊗ 1)` and to the restriction of
`Tot(f ⊗ 1)` commutes. -/
lemma tensorComplexOverIso_inv_naturality_left :
    ((tensorComplex (X.O.over U)).map (restrictComplexMap X U f)).app
          (restrictComplex X B U) ≫ (tensorComplexOverIso X U A' B).inv =
      (tensorComplexOverIso X U A B).inv ≫
        restrictComplexMap X U (((tensorComplex X.O).map f).app B) := by
  refine HomologicalComplex.hom_ext _ _ fun c => ?_
  refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) fun t r h => ?_
  exact ι_tensorComplexOverIso_inv_naturality_left X U f B t r c h

/-- **The restriction comparison of the total tensor complex is natural in the first
variable**, read through the comparison rather than its inverse. -/
lemma tensorComplexOverIso_hom_naturality_left :
    restrictComplexMap X U (((tensorComplex X.O).map f).app B) ≫
        (tensorComplexOverIso X U A' B).hom =
      (tensorComplexOverIso X U A B).hom ≫
        ((tensorComplex (X.O.over U)).map (restrictComplexMap X U f)).app
          (restrictComplex X B U) :=
  ((Iso.eq_inv_comp _).1
    (((Iso.comp_inv_eq _).1 (tensorComplexOverIso_inv_naturality_left X U f B)).trans
      (Category.assoc _ _ _))).symm

end Left

section Right

variable (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (g : B ⟶ B')

/-- **The restriction comparison is natural in the second variable, on a summand.** -/
lemma ι_tensorComplexOverIso_inv_naturality_right (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c) :
    (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫
        (((tensorComplex (X.O.over U)).obj (restrictComplex X A U)).map
          (restrictComplexMap X U g) ≫ (tensorComplexOverIso X U A B').inv).f c =
      (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫
        ((tensorComplexOverIso X U A B).inv ≫
          restrictComplexMap X U (((tensorComplex X.O).obj A).map g)).f c := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (tensorComplexOverIso X U A B').inv.f c)
    (ι_mapBifunctorMap_id_left (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (hFZero := Functor.preservesZeroMorphisms_of_additive
        (sheafTensor.{u, u, u, u, u} (X.O.over U)))
      (hFObjZero := fun M => Functor.preservesZeroMorphisms_of_additive
        ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M))
      (restrictComplex X A U) (restrictComplexMap X U g) t r c h)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z) (ι_tensorComplexOverIso_inv X U A B' t r c h)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ _)
    (sheafTensorOverIso_inv_naturality_right X U (A.X t) (g.f r)).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_comp
      _ _).symm).trans ?_
  refine (congrArg (fun z => _ ≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map z)
    (ι_mapBifunctorMap_id_left (sheafTensor.{u, u, u, u, u} X.O)
      (hFZero := Functor.preservesZeroMorphisms_of_additive (sheafTensor.{u, u, u, u, u} X.O))
      (hFObjZero := fun M => Functor.preservesZeroMorphisms_of_additive
        ((sheafTensor.{u, u, u, u, u} X.O).obj M)) A g t r c h).symm).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_comp
      _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ _)
    (ι_tensorComplexOverIso_inv X U A B t r c h).symm).trans ?_
  exact Category.assoc _ _ _

/-- **The restriction comparison of the total tensor complex is natural in the second
variable.** -/
lemma tensorComplexOverIso_inv_naturality_right :
    ((tensorComplex (X.O.over U)).obj (restrictComplex X A U)).map
          (restrictComplexMap X U g) ≫ (tensorComplexOverIso X U A B').inv =
      (tensorComplexOverIso X U A B).inv ≫
        restrictComplexMap X U (((tensorComplex X.O).obj A).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun c => ?_
  refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) fun t r h => ?_
  exact ι_tensorComplexOverIso_inv_naturality_right X U A g t r c h

/-- **The restriction comparison of the total tensor complex is natural in the second
variable**, read through the comparison rather than its inverse. -/
lemma tensorComplexOverIso_hom_naturality_right :
    restrictComplexMap X U (((tensorComplex X.O).obj A).map g) ≫
        (tensorComplexOverIso X U A B').hom =
      (tensorComplexOverIso X U A B).hom ≫
        ((tensorComplex (X.O.over U)).obj (restrictComplex X A U)).map
          (restrictComplexMap X U g) :=
  ((Iso.eq_inv_comp _).1
    (((Iso.comp_inv_eq _).1 (tensorComplexOverIso_inv_naturality_right X U A g)).trans
      (Category.assoc _ _ _))).symm

end Right

end AlgebraicGeometry.RingedSite

end
