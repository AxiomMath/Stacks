module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedCounitForget
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# Naturality of the Čech comparison in a morphism of abelian sheaves

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions whose common zero locus is
contained in a closed subset `T`, and let `ℱ`, `𝒢` be quasi-coherent `𝒪_X`-modules.  The
comparison of [Stacks, Tag 0G7L] is the map

`𝓕^• ⟶ i_* R𝓗_T(ℱ)`

of `Stacks.Perfect.SupportedFraction.cechToDerivedSupport`, in the derived category of
`𝒪_X`-modules.  For a morphism `ψ` of the underlying abelian sheaves of `ℱ` and `𝒢` this file
states its naturality after forgetting the module structure.  Write `Φ` for the forgetful functor
`D(𝒪_X) ⥤ D(Ab(X))` on derived categories, `i_* R𝓗_T` for
`Stacks.Perfect.SupportedFraction.supportPush` and `i_* R𝓗_T^{ab}` for its abelian counterpart
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward`.  The square is

`Φ(𝓕^•) ⟶ Φ(i_* R𝓗_T(ℱ)) ⟶ i_* R𝓗_T^{ab}(Φ(ℱ[0]))`

over

`Φ(𝓖^•) ⟶ Φ(i_* R𝓗_T(𝒢)) ⟶ i_* R𝓗_T^{ab}(Φ(𝒢[0]))`,

whose left vertical is the abelian Čech chain map of `Stacks.Perfect.AbelianFraction.cplxAb`, read
in the derived category of abelian sheaves, and whose right vertical is `i_* R𝓗_T^{ab}` applied to
`ψ` placed in degree `0`.  The horizontal maps are the comparison of [Stacks, Tag 0G7L],
forgotten, followed by the comparison of [Stacks, Tag 0G74] part (2) with `i_*` folded in.

## Main definitions

* `derivedCechAb`: the abelian Čech chain map in the derived category — the map
  `Φ(𝓕^•) ⟶ Φ(𝓖^•)` induced by a morphism of the underlying abelian sheaves of the coefficient
  modules, obtained from `Stacks.Perfect.AbelianFraction.cplxAb` by extending the grading from `ℕ`
  to `ℤ` and localizing.
* `derivedSingleAb`: `ψ` placed in degree `0`, as a map `Φ(ℱ[0]) ⟶ Φ(𝒢[0])` of the derived
  category of abelian sheaves.
* `forgetComparison` and `forgetComparisonIso`: the comparison of [Stacks, Tag 0G74] part (2) with
  `i_*` folded in, at the canonical derived functors, and its value at an object as an
  isomorphism.

## Main results

* `abelianCechDerivedSquare`: the square commutes, in the form with no inverse — the two
  composites `Φ(𝓕^•) ⟶ i_* R𝓗_T^{ab}(Φ(𝒢[0]))` agree.
* `abelianCechDerivedSquare_conj`: the same square with the right-hand comparison inverted, so
  that the right vertical is a map `Φ(i_* R𝓗_T(ℱ)) ⟶ Φ(i_* R𝓗_T(𝒢))`.
* `augmentationSquare`: the derived abelian augmentation square
  `Φ(aug_ℱ) ≫ ψ[0] = (abelian Čech derived map) ≫ Φ(aug_𝒢)` in `D(Ab(X))`.
* `forget_supportPushCounit_app`: the compatibility of the counit of [Stacks, Tag 0G72] with the
  forgetful functor, at the canonical derived functors.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.AbelianSupportedCounitForget
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.Perfect.AbelianFraction
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianCechDerivedSquare

-- The standard model of the derived category takes priority over the global instances.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} {m : ℕ} (e : Fin m → Γ(X, ⊤))

/-! ### The chain-level square -/

section Complexes

variable {F G : X.Modules}

/-- The degree-`0` term of the extended alternating Čech complex is the coefficient module. -/
private def augZero (F : X.Modules) : (cplx e F).X 0 ≅ F := Iso.refl _

/-- Projection of the extended alternating Čech complex
`Stacks.Perfect.ExtendedAlternatingCech.cplx` onto its degree-`0` term. -/
private def augCplx (F : X.Modules) :
    cplx e F ⟶ (HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj F :=
  ((cplx e F).toSingle₀Equiv F).symm (augZero e F).hom

/-- In degree `0` the projection onto the degree-`0` Čech term is the canonical identification of
the degree-`0` term with the coefficient module. -/
private lemma augCplx_f_zero (F : X.Modules) :
    (augCplx e F).f 0 =
      (augZero e F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := by
  simp [augCplx, CochainComplex.toSingle₀Equiv_symm_apply_f_zero]

/-- The chain-level map underlying the augmentation of [Stacks, Tag 0G7L]: the projection onto the
degree-`0` term, extended from the `ℕ`-grading to the `ℤ`-grading and identified with the single
complex there. -/
private def augExt (F : X.Modules) :
    (cplx e F).extend ComplexShape.embeddingUpNat ⟶
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F :=
  HomologicalComplex.extendMap (augCplx e F) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom

/-- The augmentation of [Stacks, Tag 0G7L] is the localization of `augExt`. -/
private lemma augmentation_eq (F : X.Modules) :
    augmentation e F = DerivedCategory.Q.map (augExt e F) := rfl

/-- In degree `0` the chain-level augmentation is the composite of the two canonical degree
identifications. -/
private lemma augExt_f_zero (F : X.Modules) :
    (augExt e F).f 0 =
      (HomologicalComplex.extendXIso (cplx e F) ComplexShape.embeddingUpNat
          ComplexShape.embeddingUpNat_f_zero).hom ≫
        (augZero e F).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [augExt, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f (augCplx e F) ComplexShape.embeddingUpNat
      ComplexShape.embeddingUpNat_f_zero,
    HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat F 0 0
      ComplexShape.embeddingUpNat_f_zero,
    augCplx_f_zero]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

/-- In degree `0` the comparison between extending a complex and forgetting the module structure
degreewise is the identity, read through the two canonical degree identifications. -/
private lemma extendIso_hom_f_zero (F : X.Modules) :
    (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx e F)
          ComplexShape.embeddingUpNat).hom.f 0 =
      (HomologicalComplex.extendXIso
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx e F))
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom ≫
        (abelianSheaf X).map (HomologicalComplex.extendXIso (cplx e F)
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).inv :=
  HomologicalComplex.mapHomologicalComplexExtendIso_hom_f (abelianSheaf X) (cplx e F)
    ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero

/-- In degree `0` the extension of the abelian Čech chain map is the degree-`0` component of that
chain map, read through the two canonical degree identifications. -/
private lemma extendMap_cplxAb_f_zero
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (HomologicalComplex.extendMap (cplxAb e ψ) ComplexShape.embeddingUpNat).f 0 =
      (HomologicalComplex.extendXIso
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx e F))
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom ≫
        (cplxAb e ψ).f 0 ≫
        (HomologicalComplex.extendXIso
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx e G))
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).inv :=
  HomologicalComplex.extendMap_f (cplxAb e ψ) ComplexShape.embeddingUpNat
    ComplexShape.embeddingUpNat_f_zero

/-- In degree `0` the abelian Čech chain map is `ψ`, read through the identification of the
degree-`0` Čech term with the coefficient module. -/
private lemma key_zero (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).map (augZero e F).hom ≫ abHom ψ =
      (cplxAb e ψ).f 0 ≫ (abelianSheaf X).map (augZero e G).hom := by
  simp only [augZero]
  rfl

/-- `key_zero` with a further morphism appended on the right. -/
private lemma key_zero_assoc (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    {Z : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}}
    (h : (abelianSheaf X).obj G ⟶ Z) :
    (abelianSheaf X).map (augZero e F).hom ≫ abHom ψ ≫ h =
      (cplxAb e ψ).f 0 ≫ (abelianSheaf X).map (augZero e G).hom ≫ h :=
  by rw [← Category.assoc, key_zero, Category.assoc]

/-- `ψ` placed in degree `0`, at the level of cochain complexes of abelian sheaves: the
morphism of single complexes induced by `ψ`, conjugated by the canonical identification of the
forgetful image of a single complex with the single complex of the forgetful image. -/
public def singleCplxAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F) ⟶
      ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj G) :=
  (HomologicalComplex.singleMapHomologicalComplex (abelianSheaf X)
        (ComplexShape.up ℤ) 0).hom.app F ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (abHom ψ) ≫
    (HomologicalComplex.singleMapHomologicalComplex (abelianSheaf X)
      (ComplexShape.up ℤ) 0).inv.app G

/-- In degree `0` the chain-level degree-`0` map is `ψ`, read through the two canonical degree
identifications of the single complexes. -/
private lemma singleCplxAb_f_zero (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (singleCplxAb ψ).f 0 =
      (abelianSheaf X).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
        abHom ψ ≫
        (abelianSheaf X).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv := by
  rw [singleCplxAb, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp

/-- The chain-level augmentation square: applying the forgetful functor degreewise to the
augmentation of [Stacks, Tag 0G7L] and then `ψ` in degree `0` is the abelian Čech chain map
followed by the forgetful image of the augmentation, both read through the comparison between
extending a complex and forgetting degreewise. -/
private lemma augmentationSquareComplex
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx e F)
          ComplexShape.embeddingUpNat).hom ≫
        ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map (augExt e F) ≫
        singleCplxAb ψ =
      HomologicalComplex.extendMap (cplxAb e ψ) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx e G)
            ComplexShape.embeddingUpNat).hom ≫
          ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map (augExt e G) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f]
    rw [extendIso_hom_f_zero, extendIso_hom_f_zero, extendMap_cplxAb_f_zero, augExt_f_zero,
      augExt_f_zero, singleCplxAb_f_zero]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      CategoryTheory.Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    rw [key_zero_assoc]
  · exact (CategoryTheory.Functor.map_isZero (abelianSheaf X)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn)).eq_of_tgt _ _

/-- The abelian Čech chain map on the `ℤ`-graded extensions, conjugated into the forgetful image
of the extended complex. -/
public def cplxAbExtend (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((cplx e F).extend ComplexShape.embeddingUpNat) ⟶
      ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((cplx e G).extend ComplexShape.embeddingUpNat) :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx e F)
        ComplexShape.embeddingUpNat).inv ≫
    HomologicalComplex.extendMap (cplxAb e ψ) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx e G)
      ComplexShape.embeddingUpNat).hom

/-- The chain-level augmentation square, with the comparison of extensions absorbed into the
abelian Čech chain map. -/
private lemma augmentationSquareComplex'
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map (augExt e F) ≫
        singleCplxAb ψ =
      cplxAbExtend e ψ ≫
        ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map (augExt e G) := by
  rw [cplxAbExtend]
  simp only [Category.assoc]
  rw [← augmentationSquareComplex, Iso.inv_hom_id_assoc]

end Complexes

/-! ### The derived augmentation square -/

section Derived

variable {F G : X.Modules}

/-- The naturality of the comparison identifying the forgetful functor on derived categories with
the forgetful functor applied degreewise, in the spelling with the functors applied one at a
time. -/
private lemma factors_hom_naturality {A B : CochainComplex X.Modules ℤ} (g : A ⟶ B) :
    (abelianSheaf X).mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
        (abelianSheaf X).mapDerivedCategoryFactors.hom.app B =
      (abelianSheaf X).mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  (abelianSheaf X).mapDerivedCategoryFactors.hom.naturality g

/-- The naturality of the inverse comparison, in the spelling with the functors applied one at a
time. -/
private lemma factors_inv_naturality {A B : CochainComplex X.Modules ℤ} (g : A ⟶ B) :
    (abelianSheaf X).mapDerivedCategoryFactors.inv.app A ≫
        (abelianSheaf X).mapDerivedCategory.map (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        (abelianSheaf X).mapDerivedCategoryFactors.inv.app B :=
  ((abelianSheaf X).mapDerivedCategoryFactors.inv.naturality g).symm

/-- The abelian Čech chain map in the derived category of abelian sheaves: the map
`Φ(𝓕^•) ⟶ Φ(𝓖^•)` induced by a morphism of the underlying abelian sheaves of the coefficient
modules: `Stacks.Perfect.AbelianFraction.cplxAb`, extended from the `ℕ`-grading to the `ℤ`-grading
and localized, read through the comparison identifying the forgetful functor on derived categories
with the forgetful functor applied degreewise. -/
public def derivedCechAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) ⟶
      (abelianSheaf X).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((cplx e G).extend ComplexShape.embeddingUpNat)) :=
  (abelianSheaf X).mapDerivedCategoryFactors.hom.app
      ((cplx e F).extend ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (cplxAbExtend e ψ) ≫
    (abelianSheaf X).mapDerivedCategoryFactors.inv.app
      ((cplx e G).extend ComplexShape.embeddingUpNat)

/-- `ψ` placed in degree `0`, as a map `Φ(ℱ[0]) ⟶ Φ(𝒢[0])` in the derived category of abelian
sheaves on `X`. -/
public def derivedSingleAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)) ⟶
      (abelianSheaf X).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj G)) :=
  (abelianSheaf X).mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F) ≫
    DerivedCategory.Q.map (singleCplxAb ψ) ≫
    (abelianSheaf X).mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj G)

/-- The derived abelian augmentation square, with the augmentation written as the localization of
its chain-level model. -/
private lemma augmentationSquare_aux
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.map (DerivedCategory.Q.map (augExt e F)) ≫
        derivedSingleAb ψ =
      derivedCechAb e ψ ≫
        (abelianSheaf X).mapDerivedCategory.map (DerivedCategory.Q.map (augExt e G)) := by
  have key := congrArg DerivedCategory.Q.map (augmentationSquareComplex' e ψ)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at key
  rw [derivedSingleAb, derivedCechAb]
  simp only [Category.assoc]
  rw [reassoc_of% (factors_hom_naturality (augExt e F)), factors_inv_naturality,
    reassoc_of% key]

/-- The derived abelian augmentation square: in the derived category of abelian sheaves, the
forgetful image of the augmentation of [Stacks, Tag 0G7L] followed by `ψ` in degree `0` is the
abelian Čech derived map followed by the forgetful image of the augmentation. -/
public theorem augmentationSquare (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.map (augmentation e F) ≫ derivedSingleAb ψ =
      derivedCechAb e ψ ≫ (abelianSheaf X).mapDerivedCategory.map (augmentation e G) :=
  augmentationSquare_aux e ψ

end Derived

/-! ### Cancelling a counit, formally -/

section Formal

variable {C D : Type*} [Category* C] [Category* D] (Phi : C ⥤ D) (RH : C ⥤ C) (RHab : D ⥤ D)
  (eps : RH ⟶ Functor.id C) (cmp : RH ⋙ Phi ⟶ Phi ⋙ RHab) (epsab : RHab ⟶ Functor.id D)
  (hcounit : ∀ Z : C, Phi.map (eps.app Z) = cmp.app Z ≫ epsab.app (Phi.obj Z))
  (hcmpiso : ∀ Z : C, IsIso (cmp.app Z))

/-- The naturality of the comparison, in the spelling with the functors applied one at a time. -/
private lemma cmp_naturality {A B : C} (g : A ⟶ B) :
    Phi.map (RH.map g) ≫ cmp.app B = cmp.app A ≫ RHab.map (Phi.map g) :=
  cmp.naturality g

/-- The naturality of the counit `RHab ⟶ id`, with the identity functor removed. -/
private lemma epsab_naturality {A B : D} (w : A ⟶ B) :
    epsab.app A ≫ w = RHab.map w ≫ epsab.app B :=
  (epsab.naturality w).symm

include hcounit hcmpiso in
/-- Given a map `cts : L ⟶ RH(S)` whose composite with the counit `eps` of `RH` is `RH` applied
to a map `aug : L ⟶ S`, the counit `epsab` of `RHab` followed by the image of `cts` and the
comparison is `RHab` applied to the image of `aug`. -/
private lemma counit_comp_formal {L S : C} (cts : L ⟶ RH.obj S) (aug : L ⟶ S)
    (hL : eps.app L ≫ cts = RH.map aug) :
    epsab.app (Phi.obj L) ≫ Phi.map cts ≫ cmp.app S = RHab.map (Phi.map aug) := by
  refine ((@asIso _ _ _ _ _ (hcmpiso L)).cancel_iso_hom_left _ _).mp ?_
  rw [show (@asIso _ _ _ _ _ (hcmpiso L)).hom = cmp.app L from rfl,
    ← Category.assoc, ← hcounit L, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hL]
  exact cmp_naturality Phi RH RHab cmp aug

include hcounit hcmpiso in
/-- Let `eps : RH ⟶ id` and `epsab : RHab ⟶ id` be counits compatible
along an invertible comparison `cmp : RH ⋙ Phi ⟶ Phi ⋙ RHab`.  Given two maps
`ctsK : K ⟶ RH(S)` and `ctsL : L ⟶ RH(S')` each characterised, after the counit, by an
augmentation (`hK` and `hL`), the counit being invertible at `K` (`hKiso`), and a commuting
augmentation square after applying `Phi` (`hsq`), the images of the two maps commute with the two
given maps past the comparison. -/
private lemma square_formal {K L S S' : C}
    (ctsK : K ⟶ RH.obj S) (ctsL : L ⟶ RH.obj S') (augK : K ⟶ S) (augL : L ⟶ S')
    (u : Phi.obj K ⟶ Phi.obj L) (v : Phi.obj S ⟶ Phi.obj S')
    (hK : eps.app K ≫ ctsK = RH.map augK) (hL : eps.app L ≫ ctsL = RH.map augL)
    (hKiso : IsIso (eps.app K)) (hsq : Phi.map augK ≫ v = u ≫ Phi.map augL) :
    Phi.map ctsK ≫ cmp.app S ≫ RHab.map v = u ≫ Phi.map ctsL ≫ cmp.app S' := by
  have hPhi : IsIso (Phi.map (eps.app K)) := CategoryTheory.Functor.map_isIso _ _
  refine ((@asIso _ _ _ _ _ hPhi).cancel_iso_hom_left _ _).mp ?_
  rw [show (@asIso _ _ _ _ _ hPhi).hom = Phi.map (eps.app K) from rfl,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, hK,
    reassoc_of% (cmp_naturality Phi RH RHab cmp augK), ← CategoryTheory.Functor.map_comp, hsq,
    CategoryTheory.Functor.map_comp, hcounit K, Category.assoc,
    reassoc_of% (epsab_naturality RHab epsab u),
    counit_comp_formal Phi RH RHab eps cmp epsab hcounit hcmpiso ctsL augL hL]

end Formal

/-! ### The counit of the supported pushforward and the forgetful functor -/

section Counit

variable {T : Set X} (hT : IsClosed T)

/-- The comparison of [Stacks, Tag 0G74] part (2) with `i_*` folded in, at the canonical
derived functors `i_* R𝓗_T` of
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward` and `i_* R𝓗_T^{ab}` of
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward`. -/
public def forgetComparison :
    supportPush hT ⋙ underlyingDerivedSheaf (structureSheafRing X.toRingedSpace) ⟶
      underlyingDerivedSheaf (structureSheafRing X.toRingedSpace) ⋙
        derivedAbelianSupportedPushforward X.toRingedSpace T hT :=
  abelianSupportedEndoForgetComparison X.toRingedSpace T
    (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
    (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT)
    (supportPush hT) (derivedSupportedPushforwardUnit X.toRingedSpace T hT)

/-- For closed `T`, the comparison of [Stacks, Tag 0G74] part (2) is invertible at every
object. -/
public lemma isIso_forgetComparison_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((forgetComparison hT).app K) :=
  have h : IsIso (forgetComparison hT) :=
    isIso_abelianSupportedEndoForgetComparison X.toRingedSpace T
      (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
      (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT)
      (supportPush hT) (derivedSupportedPushforwardUnit X.toRingedSpace T hT) hT
  @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (forgetComparison hT) h K

include hT in
/-- The comparison of [Stacks, Tag 0G74] part (2) at an object, as an isomorphism. -/
public def forgetComparisonIso
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  @asIso _ _ _ _ ((forgetComparison hT).app K) (isIso_forgetComparison_app hT K)

/-- Forgetting the module structure carries the counit of [Stacks, Tag 0G72] to the abelian
counit past `forgetComparison`, at the canonical derived functors. -/
public theorem forget_supportPushCounit_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).map
        ((supportPushCounit hT).app K) =
      (forgetComparison hT).app K ≫
        (abelianSupportPushCounit X.toRingedSpace T hT).app
          ((underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).obj K) := by
  have h := whiskerRight_derivedSupportedSectionsToId X.toRingedSpace T
    (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
    (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT)
    (supportPush hT) (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
  exact congr_app h K

end Counit

/-! ### The square -/

section Square

variable {T : Set X} (hT : IsClosed T) {F G : X.Modules}

/-- For a closed `T` containing the common zero locus of `e` and a morphism `ψ` of the underlying
abelian sheaves of two quasi-coherent coefficient modules, the comparison of [Stacks, Tag 0G7L],
forgotten and followed by the comparison of [Stacks, Tag 0G74] part (2), carries the abelian Čech
derived map to `i_* R𝓗_T^{ab}` applied to `ψ` in degree `0`, as maps
`Φ(𝓕^•) ⟶ i_* R𝓗_T^{ab}(Φ(𝒢[0]))`. -/
public theorem abelianCechDerivedSquare [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hTe : equationsClosedSet e ⊆ T)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).map
          (cechToDerivedSupport e F hT hTe) ≫
        (forgetComparison hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map (derivedSingleAb ψ) =
      derivedCechAb e ψ ≫
        (underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).map
          (cechToDerivedSupport e G hT hTe) ≫
        (forgetComparison hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  square_formal (underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)) (supportPush hT)
    (derivedAbelianSupportedPushforward X.toRingedSpace T hT) (supportPushCounit hT)
    (forgetComparison hT) (abelianSupportPushCounit X.toRingedSpace T hT)
    (forget_supportPushCounit_app hT) (isIso_forgetComparison_app hT)
    (cechToDerivedSupport e F hT hTe) (cechToDerivedSupport e G hT hTe)
    (augmentation e F) (augmentation e G) (derivedCechAb e ψ) (derivedSingleAb ψ)
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport e F hT hTe)
    (derivedSupportedSectionsToId_comp_cechToDerivedSupport e G hT hTe)
    (isIso_derivedSupportedSectionsToId_cech e F hT hTe)
    (augmentationSquare e ψ)

/-- Cancelling an isomorphism from the right of an equality of composites. -/
private lemma comp_inv_of_eq {C₀ : Type*} [Category* C₀] {A B B' : C₀} (p : A ⟶ B) (q : A ⟶ B')
    (α : B' ≅ B) (h : p = q ≫ α.hom) : p ≫ α.inv = q := by
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `abelianCechDerivedSquare` in conjugated form: the right vertical is the comparison of
[Stacks, Tag 0G74] part (2), then `i_* R𝓗_T^{ab}` applied to `ψ` in degree `0`, then the inverse
of that comparison; with that reading the square is a commuting square of maps
`Φ(𝓕^•) ⟶ Φ(i_* R𝓗_T(𝒢))`. -/
public theorem abelianCechDerivedSquare_conj [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hTe : equationsClosedSet e ⊆ T)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    ((underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).map
            (cechToDerivedSupport e F hT hTe) ≫
          (forgetComparison hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
          (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map (derivedSingleAb ψ)) ≫
        (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj G)).inv =
      derivedCechAb e ψ ≫
        (underlyingDerivedSheaf (structureSheafRing X.toRingedSpace)).map
          (cechToDerivedSupport e G hT hTe) :=
  comp_inv_of_eq _ _ _
    ((abelianCechDerivedSquare e hT hTe ψ).trans (Category.assoc _ _ _).symm)

end Square

end Stacks.Perfect.AbelianCechDerivedSquare

end
