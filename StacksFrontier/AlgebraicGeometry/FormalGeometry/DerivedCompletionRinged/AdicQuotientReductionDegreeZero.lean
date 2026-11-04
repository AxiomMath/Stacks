module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientReduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientTriangles
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealPowerTensorQuotient
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.UnitLawNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Uniqueness

/-!
# `H⁰` of the derived reduction `ℱ ⟶ ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ` is the projection `ℱ ⟶ ℱ/ℐⁿℱ`

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊆ 𝒪` a sheaf of ideals and `ℱ` an arbitrary sheaf of
`𝒪`-modules. The derived reduction `AlgebraicGeometry.RingedSite.adicQuotientReduction` of
[Stacks, Tag 0CQH] is a map `ℱ[0] ⟶ ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ` in `D(𝒪)`, and the derived tensor product
lies in `D^{≤ 0}`, so it is determined by what it does in degree zero. This file writes down the
truncation

`τₙ : ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ ⟶ (ℱ/ℐⁿℱ)[0]`

onto degree zero and proves that the reduction followed by it is the projection `ℱ ⟶ ℱ/ℐⁿℱ`
placed in degree zero. Together with the invertibility of `τₙ` on `H⁰` this says that
`H⁰(ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ)` is `ℱ/ℐⁿℱ` and that `H⁰` of the derived reduction is the projection. No
flatness, finiteness, coherence, Noetherian or compactness hypothesis is used.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorRowSingleIso`: the termwise tensor complex of `ℱ[0]` with
  a module `𝒢` is `(ℱ ⊗_𝒪 𝒢)[0]`.
* `AlgebraicGeometry.RingedSite.adicQuotientTruncation`: **the truncation
  `τₙ : ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ ⟶ (ℱ/ℐⁿℱ)[0]`.**

## Main results

* `AlgebraicGeometry.RingedSite.adicQuotientReduction_comp_adicQuotientTruncation`: **the
  derived reduction followed by the truncation is the projection `ℱ ⟶ ℱ/ℐⁿℱ`.**
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_adicQuotientTruncation`: **the truncation is
  invertible on `H⁰`**, so `H⁰(ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ) = ℱ/ℐⁿℱ`.
* `AlgebraicGeometry.RingedSite.isLE_derivedTensor_adicQuotientObj`: the derived tensor
  product lies in `D^{≤ 0}`.
* `AlgebraicGeometry.RingedSite.epi_homologyMap_adicQuotientReduction` and
  `AlgebraicGeometry.RingedSite.hom_ext_of_adicQuotientReduction_comp`: `H⁰` of the derived
  reduction is an epimorphism, so a map out of `ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ` into a module placed in degree
  zero is determined by its composite with the reduction; hence
  `AlgebraicGeometry.RingedSite.eq_adicQuotientTruncation`: `τₙ` is the **unique** map whose
  composite with the reduction is the projection.
* `AlgebraicGeometry.RingedSite.adicQuotientTruncation_naturality`: the truncations are
  compatible with the transition maps of the two towers.

## Implementation notes

**Where `τₙ` comes from.** It is the canonical map of [Stacks, Tag 06YU] from the derived to the
ordinary total tensor product, `Stacks.SheafOfModules.DerivedTensorProduct.toTensor`, followed by
two identifications of complexes: the total tensor complex of a second factor concentrated in
degree zero is the termwise one
(`CochainComplex.KFlatBifunctor.totalSingleIso`), the termwise complex of `ℱ[0]` is
`(ℱ ⊗_𝒪 𝒢)[0]` (`tensorRowSingleIso`, a component of
`HomologicalComplex.singleMapHomologicalComplex`), and finally the identification
`ℱ ⊗_𝒪 𝒪/ℐⁿ ≅ ℱ/ℐⁿℱ` of `Stacks.Sites.tensorAdicQuotientModuleIso`. So no choice is made: `τₙ`
is `toTensor` read through the identifications of its target.

**Where the content of the main identity is.** The derived reduction is built from the unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso` of the derived tensor product, and `τₙ`
from `toTensor`; the identity therefore needs the value of that unit law at the image of a
complex, which is
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso_inv_comp_toTensor`. Once that is available
the derived-category part is the naturality of `toTensor` in the second variable, and everything
else happens in complexes concentrated in degree zero, where it reduces by
`HomologicalComplex.from_single_hom_ext` to one equation in `Mod(𝒪)`: the naturality of
`Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections` together with the naturality of
`ℱ ⊗_𝒪 -` in its first variable.

**Why `tensorSingleCochainIso` is not `HomologicalComplex.mapBifunctorSingleIso`.** The two have
the same type, at the bifunctor `⊗_𝒪`. They are not interchangeable here, because the identity
this file proves needs the identification to be *compatible with a map in the second variable*,
and `mapBifunctorSingleIso` carries no naturality statement at all — a fact its own consumers
record. The composite used here is built from
`CochainComplex.KFlatBifunctor.totalSingleIso`, whose naturality in both variables is proved
(`totalSingleIso_hom_naturality`, `totalSingleIso_hom_naturality_right`), and from a component
of `HomologicalComplex.singleMapHomologicalComplex`; and it is the one the unit law
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections` is itself built from, so the two meet
without a further comparison. No identification of the two is proved, and none is needed.

**What this does and does not give for [Stacks, Tag 0A0K] part (3).** It identifies the degree-0
part of the reduction tower `n ↦ ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ` with the adic filtration quotient tower
`n ↦ ℱ/ℐⁿℱ`, compatibly with the canonical maps out of `ℱ` and with the transition maps. It does
*not* produce `ℱ^∧ = lim ℱ/ℐⁿℱ`: that needs the reduction tower to compute the derived
completion, which is false in unrestricted form
(`AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_of_periodic`), and the
passage from `R lim` to `lim`.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
  CategoryTheory.Functor.flip_obj_additive

variable (X : RingedSite.{u, u, u})

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### The identifications at the level of complexes -/

section Complexes

variable (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The termwise tensor complex of `ℱ[0]` with a module `𝒢` is `(ℱ ⊗_𝒪 𝒢)[0]`.** This is the
component at `ℱ` of `HomologicalComplex.singleMapHomologicalComplex` for the functor
`- ⊗_𝒪 𝒢`. -/
def tensorRowSingleIso (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    CochainComplex.KFlatBifunctor.rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        ((HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) 0).obj F) G ≅
      (HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) :=
  (HomologicalComplex.singleMapHomologicalComplex
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj G) (ComplexShape.up ℤ) 0).app F

omit [∀ (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The termwise unit law and the termwise identification agree with the ordinary map
`ℱ ⟶ ℱ ⊗_𝒪 𝒢` induced by a map `𝒪 ⟶ 𝒢`.** Both sides are maps out of a complex concentrated in
degree zero, so the statement reduces to one equation in `Mod(𝒪)`, which is the naturality of
the unit law `ℱ ⊗_𝒪 𝒪 ≅ ℱ` together with the naturality of `- ⊗_𝒪 𝒢` in the first variable. -/
theorem rowComplexMapRight_comp_tensorRowSingleIso_hom
    {G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ G) :
    CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F) g ≫
        (tensorRowSingleIso X F G).hom =
      (Stacks.SheafOfModules.rowComplexUnitIsoFreeSections X.O
            ((HomologicalComplex.single
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ) 0).obj F)).hom ≫
        (HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).map
          ((Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  by_cases hp : p = 0
  swap
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) p hp).eq_of_tgt _ _
  subst hp
  have hnat1 := ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom).naturality g
  have hnat2 := Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections_naturality X.O
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  rw [Functor.flip_obj_map] at hnat2
  have h3 : (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O
          (((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F).X 0)).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom).app
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
        (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat2, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have key : (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O
          (((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F).X 0)).inv ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (((HomologicalComplex.single
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
                (ComplexShape.up ℤ) 0).obj F).X 0)).map g ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom).app G) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
        ((Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g) := by
    rw [hnat1, ← Category.assoc _ _ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g),
      h3, Category.assoc]
  have key2 : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (((HomologicalComplex.single
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ) 0).obj F).X 0)).map g ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom).app G =
      (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O
            (((HomologicalComplex.single
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ) 0).obj F).X 0)).hom ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
          ((Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g)) := by
    rw [← key, Iso.hom_inv_id_assoc]
  have hrow : ∀ (L : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) (q : ℤ),
      ((Stacks.SheafOfModules.rowComplexUnitIsoFreeSections X.O L).hom).f q =
        (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O (L.X q)).hom ≫ 𝟙 _ :=
    fun _ _ => rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self, tensorRowSingleIso, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, hrow, Category.comp_id]
  dsimp only [CochainComplex.KFlatBifunctor.rowComplexMapRight, Functor.flip_obj_map,
    Functor.flip_obj_obj]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G)).inv) key2)).trans
    (Category.assoc _ _ _)

/-- **The identification `Tot(ℱ[0] ⊗_𝒪 𝒢[0]) ≅ (ℱ ⊗_𝒪 𝒢)[0]`**: the total tensor complex of a
second factor concentrated in degree zero is the termwise complex, which for a first factor
concentrated in degree zero is the single complex of the tensor product. -/
def tensorSingleCochainIso (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F)).obj
        ((HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) 0).obj G) ≅
      (HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) :=
  CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      ((HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj F) G ≪≫
    tensorRowSingleIso X F G

/-- **At the level of complexes, tensoring `ℱ[0]` with a map `𝒪[0] ⟶ 𝒢[0]` and reading the
target through `tensorSingleCochainIso` is the unit law followed by the ordinary map
`ℱ ⟶ ℱ ⊗_𝒪 𝒢`.** The first factor is the naturality of the termwise identification of the total
complex in the second variable; the second is
`rowComplexMapRight_comp_tensorRowSingleIso_hom`. -/
theorem mapBifunctorMap_comp_tensorSingleCochainIso_hom
    {G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ G) :
    HomologicalComplex.mapBifunctorMap
          (𝟙 ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F))
          ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).map g)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        (tensorSingleCochainIso X F G).hom =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
            ((HomologicalComplex.single
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ) 0).obj F)).hom ≫
        (HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).map
          ((Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g) := by
  erw [tensorSingleCochainIso, Iso.trans_hom, ← Category.assoc,
    CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right, Category.assoc,
    rowComplexMapRight_comp_tensorRowSingleIso_hom X F g, Category.assoc]

end Complexes

/-! ### The truncation of the derived reduction onto degree zero -/

section Truncation

variable (I : _root_.SheafOfModules.Submodule
    (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The identification `Tot(ℱ[0] ⊗_𝒪 (𝒪/ℐⁿ)[0]) ≅ (ℱ/ℐⁿℱ)[0]`: the identification of the total
tensor complex with `(ℱ ⊗_𝒪 𝒪/ℐⁿ)[0]`, followed by `Stacks.Sites.tensorAdicQuotientModuleIso`
placed in degree zero. -/
def adicQuotientCochainIso (n : ℕ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F)).obj
        ((HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) 0).obj
          (Stacks.Sites.adicQuotientModule (X := X) I n)) ≅
      (HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj
        (Stacks.Sites.idealSmulQuotient F (Stacks.Sites.idealPow (O := X.O) I n)) :=
  tensorSingleCochainIso X F (Stacks.Sites.adicQuotientModule (X := X) I n) ≪≫
    (HomologicalComplex.single (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).mapIso
      (Stacks.Sites.tensorAdicQuotientModuleIso F I n)

/-- **The truncation `τₙ : ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ ⟶ (ℱ/ℐⁿℱ)[0]` onto degree zero**: the canonical map
of [Stacks, Tag 06YU] to the ordinary total tensor complex, followed by the identification of
that complex with `(ℱ/ℐⁿℱ)[0]`. -/
def adicQuotientTruncation (n : ℕ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)).obj
        (adicQuotientObj X I n) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
        (Stacks.Sites.idealSmulQuotient F (Stacks.Sites.idealPow (O := X.O) I n)) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
      ((HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj F)
      ((HomologicalComplex.single
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ) 0).obj
        (Stacks.Sites.adicQuotientModule (X := X) I n)) ≫
    DerivedCategory.Q.map (adicQuotientCochainIso X I F n).hom

/-- **`H⁰` of the derived reduction `ℱ ⟶ ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ` is the projection `ℱ ⟶ ℱ/ℐⁿℱ`:** the
reduction followed by the truncation onto degree zero is the projection, placed in degree zero.

No flatness, finiteness, coherence, Noetherian or compactness hypothesis is used: the derived
reduction is built from the unit law of the derived tensor product, whose value at `ℱ[0]` is the
ordinary unit law, and the canonical map to the ordinary total tensor complex is natural. -/
theorem adicQuotientReduction_comp_adicQuotientTruncation (n : ℕ) :
    adicQuotientReduction X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n ≫
        adicQuotientTruncation X I F n =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.idealSmulQuotientπ F (Stacks.Sites.idealPow (O := X.O) I n)) := by
  have hnat := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality
    (𝟙 ((HomologicalComplex.single
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ) 0).obj F))
    ((HomologicalComplex.single
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ) 0).map
      (Stacks.Sites.adicQuotientModuleπ (X := X) I n))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hnat
  have hu := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso_inv_comp_toTensor X
    ((HomologicalComplex.single (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ) 0).obj F)
  have hL := mapBifunctorMap_comp_tensorSingleCochainIso_hom X F
    (Stacks.Sites.adicQuotientModuleπ (X := X) I n)
  have hleg := Stacks.Sites.adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom F I n
  have hW : HomologicalComplex.mapBifunctorMap
          (𝟙 ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).obj F))
          ((HomologicalComplex.single
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).map (Stacks.Sites.adicQuotientModuleπ (X := X) I n))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        (adicQuotientCochainIso X I F n).hom =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O
            ((HomologicalComplex.single
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ) 0).obj F)).hom ≫
        (HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) 0).map
          (Stacks.Sites.idealSmulQuotientπ F (Stacks.Sites.idealPow (O := X.O) I n)) := by
    erw [adicQuotientCochainIso, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, hL,
      Category.assoc, ← Functor.map_comp, hleg]
    rfl
  have hW' := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map hW).trans (DerivedCategory.Q.map_comp _ _))
  rw [adicQuotientReduction, adicQuotientTruncation, Category.assoc]
  erw [reassoc_of% hnat]
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hW'))).trans ?_
  erw [reassoc_of% hu, ← Functor.map_comp_assoc, Iso.inv_hom_id, DerivedCategory.Q.map_id,
    Category.id_comp]
  rfl

/-- **The derived tensor product `ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ` lies in `D^{≤ 0}`**, by right t-exactness of
the derived tensor product. -/
theorem isLE_derivedTensor_adicQuotientObj (n : ℕ) :
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)).obj
      (adicQuotientObj X I n)).IsLE 0 :=
  Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_single
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) F
    (Stacks.Sites.adicQuotientModule (X := X) I n)

/-- **The truncation `τₙ` is invertible on `H⁰`**, so `H⁰(ℱ ⊗^𝐋_𝒪 𝒪/ℐⁿ)` is `ℱ/ℐⁿℱ`. The
canonical map to the ordinary total tensor complex is invertible on `H⁰` at two modules placed
in degree zero — this is right exactness of the tensor product, with no flatness hypothesis —
and the rest of `τₙ` is an isomorphism of complexes. -/
theorem isIso_homologyMap_adicQuotientTruncation (n : ℕ) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      (adicQuotientTruncation X I F n)) := by
  have hbridge := derivedTensorObjIso_hom_comp_toTensor X
    ((HomologicalComplex.single (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ) 0).obj F)
    ((HomologicalComplex.single
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (ComplexShape.up ℤ) 0).obj
      (Stacks.Sites.adicQuotientModule (X := X) I n))
  have h2 := Stacks.DerivedTensor.RingedSite.isIso_homologyMap_toTensor_single X.O
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O) F
    (Stacks.Sites.adicQuotientModule (X := X) I n)
  have h1 : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
        ((HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) 0).obj F)
        ((HomologicalComplex.single
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) 0).obj (Stacks.Sites.adicQuotientModule (X := X) I n)))) := by
    rw [← hbridge, Functor.map_comp]
    exact IsIso.comp_isIso' inferInstance h2
  rw [adicQuotientTruncation, Functor.map_comp]
  exact IsIso.comp_isIso' h1 inferInstance

/-- **`H⁰` of the derived reduction is an epimorphism.** In the distinguished triangle attached
to `0 → ℐⁿ → 𝒪 → 𝒪/ℐⁿ → 0` the reduction is the second morphism, and the first vertex
`ℱ[0] ⊗^𝐋_𝒪 ℐⁿ` lies in `D^{≤ 0}`, so `H¹` of it vanishes and the homology sequence of the
triangle makes the second morphism an epimorphism on `H⁰`. -/
theorem epi_homologyMap_adicQuotientReduction (n : ℕ) :
    Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      (adicQuotientReduction X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n)) := by
  have hS : (ShortComplex.mk (Stacks.Sites.idealPow (O := X.O) I n).ι
      (Stacks.Sites.adicQuotientModuleπ (X := X) I n)
      (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := X) I n)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) inferInstance
      (Stacks.Sites.epi_adicQuotientModuleπ (X := X) I n)
  have hdist := tensorShortExact_distinguished X
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) hS
  have := Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_single
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) F
    (Stacks.Sites.idealPow (O := X.O) I n).toSheafOfModules
  refine (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hdist 0 1 rfl).2 ?_
  exact (DerivedCategory.isZero_of_isLE
    (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj F)).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj
        (Stacks.Sites.idealPow (O := X.O) I n).toSheafOfModules)) 0 1
    (by norm_num)).eq_of_tgt _ _

/-- **A map out of `ℱ[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ` into a module placed in degree zero is determined by its
composite with the derived reduction.** The source lies in `D^{≤ 0}`, so such a map is
determined by `H⁰`, and `H⁰` of the reduction is an epimorphism. -/
theorem hom_ext_of_adicQuotientReduction_comp
    {G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (n : ℕ)
    (a b : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)).obj
        (adicQuotientObj X I n) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj G)
    (hab : adicQuotientReduction X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n ≫ a =
        adicQuotientReduction X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n ≫ b) :
    a = b := by
  refine Stacks.DerivedCategory.homologyMap_injective_of_isLE
    (isLE_derivedTensor_adicQuotientObj X I F n) a b ?_
  have := epi_homologyMap_adicQuotientReduction X I F n
  rw [← cancel_epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      (adicQuotientReduction X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n)),
    ← Functor.map_comp, ← Functor.map_comp, hab]

/-- **`τₙ` is the unique map whose composite with the derived reduction is the projection
`ℱ ⟶ ℱ/ℐⁿℱ`.** -/
theorem eq_adicQuotientTruncation (n : ℕ)
    (t : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)).obj
        (adicQuotientObj X I n) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
        (Stacks.Sites.idealSmulQuotient F (Stacks.Sites.idealPow (O := X.O) I n)))
    (ht : adicQuotientReduction X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F) n ≫ t =
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
          (Stacks.Sites.idealSmulQuotientπ F (Stacks.Sites.idealPow (O := X.O) I n))) :
    t = adicQuotientTruncation X I F n :=
  hom_ext_of_adicQuotientReduction_comp X I F n t _
    (ht.trans (adicQuotientReduction_comp_adicQuotientTruncation X I F n).symm)

/-- **The truncations are compatible with the transition maps of the two towers**: tensoring the
transition map `𝒪/ℐⁿ ⟶ 𝒪/ℐᵐ` with `ℱ[0]` and truncating is truncating and then the transition
map `ℱ/ℐⁿℱ ⟶ ℱ/ℐᵐℱ`. Both sides agree after precomposition with the derived reduction, which
determines a map out of the derived tensor product into a module placed in degree zero. -/
theorem adicQuotientTruncation_naturality {m n : ℕ} (h : m ≤ n) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj F)).map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            (Stacks.Sites.adicQuotientModuleMap (X := X) I h)) ≫
        adicQuotientTruncation X I F m =
      adicQuotientTruncation X I F n ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
          (Stacks.Sites.idealSmulQuotientMap F
            (Stacks.Sites.idealPow_antitone (O := X.O) I h)) := by
  refine hom_ext_of_adicQuotientReduction_comp X I F n _ _ ?_
  rw [← Category.assoc, ← Category.assoc, adicQuotientReduction_comp_map X I _ h,
    adicQuotientReduction_comp_adicQuotientTruncation,
    adicQuotientReduction_comp_adicQuotientTruncation, ← Functor.map_comp,
    Stacks.Sites.idealSmulQuotientπ_comp_idealSmulQuotientMap]

end Truncation

end AlgebraicGeometry.RingedSite

end
