module

public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.Algebra.Homology.DoubleMappingCone
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes

/-!
# The derived pullback of a two-term complex

Let `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces and `d : 𝒞 ⟶ ℬ` a morphism of
`𝒪_X`-modules, so that `K = (𝒞 ⟶ ℬ)` (in degrees `-1` and `0`) is a two-term complex. This file
compares `Lg^*K` with the degreewise pullback `g^*K = (g^*𝒞 ⟶ g^*ℬ)` through the comparison
`Lg^*K ⟶ g^*K` of **Stacks 06YJ**.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.mapDoubleIso`: the identification of the degreewise
  pullback of `HomologicalComplex.double d` with `HomologicalComplex.double (g^*d)`, which is
  `HomologicalComplex.doubleMapFunctorIso` read backwards; `mapDoubleIso_hom_eq` describes it
  through the identifications of both complexes with mapping cones.
* `AlgebraicGeometry.RingedSpaceThickening.kSingle`: the comparison `Lg^*(M[0]) ⟶ (g^*M)[0]`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackComparisonOnComplex_naturality'`: the
  comparison `Lg^*(QK) ⟶ Q(g^*K)` is natural in the complex.
* `AlgebraicGeometry.RingedSpaceThickening.pullbackExtClass_conormalExtClass`: the image under
  `Lg^*`, pushed along a coefficient map `c : g^*ℱ ⟶ 𝒢`, of the class in `Ext¹(K, ℱ)` of a
  homomorphism `δ : 𝒞 ⟶ ℱ` is the comparison followed by the class in `Ext¹(g^*K, 𝒢)` of
  `c ∘ g^*δ`.
* `AlgebraicGeometry.RingedSpaceThickening.eq_zero_of_comp_eq_zero_of_triangle`: the diagram
  chase in a pretriangulated category behind the injectivity below.
* `AlgebraicGeometry.RingedSpaceThickening.eq_zero_of_derivedPullbackComparisonOnComplex_comp`:
  if `ℬ` is flat, a class in `Ext¹(g^*K, 𝒢)` which vanishes after precomposition with the
  comparison `Lg^*K ⟶ g^*K` vanishes.

## Implementation notes

The comparison at a complex is
`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex`. Here it is assembled as
a natural transformation `Q ⋙ Lg^* ⟶ g^* ⋙ Q` out of pieces which commute with the shift, so that
its compatibility with the shift comes from the instances.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X Y : RingedSpace.{u, u}} (g : Y ⟶ X)

/-- The comparison `Lg^*(QK) ⟶ Q(g^*K)`, as a natural transformation assembled from pieces each
of which commutes with the shift. -/
def derivedPullbackComparisonNat :
    DerivedCategory.Q ⋙ derivedPullback g ⟶
      (modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).inv
      (derivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ))
      (derivedPullbackComparison g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).hom

/-- The component of `derivedPullbackComparisonNat g` at a complex `K` is
`derivedPullbackComparisonOnComplex g K`. -/
theorem derivedPullbackComparisonNat_app (K : CochainComplex (ModuleSheaves X) ℤ) :
    (derivedPullbackComparisonNat g).app K = derivedPullbackComparisonOnComplex g K := by
  simp [derivedPullbackComparisonNat, derivedPullbackComparisonOnComplex]

/-- The comparison `derivedPullbackComparisonNat g` commutes with the shift by `ℤ`. -/
instance : NatTrans.CommShift (derivedPullbackComparisonNat g) ℤ := by
  unfold derivedPullbackComparisonNat
  infer_instance

/-- **Naturality of the comparison** `Lg^*(QK) ⟶ Q(g^*K)` in the complex `K`. -/
@[reassoc]
theorem derivedPullbackComparisonOnComplex_naturality' {K L : CochainComplex (ModuleSheaves X) ℤ}
    (φ : K ⟶ L) :
    (derivedPullback g).map (DerivedCategory.Q.map φ) ≫ derivedPullbackComparisonOnComplex g L =
      derivedPullbackComparisonOnComplex g K ≫
        DerivedCategory.Q.map
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  rw [← derivedPullbackComparisonNat_app, ← derivedPullbackComparisonNat_app]
  exact (derivedPullbackComparisonNat g).naturality φ

/-- **The comparison commutes with the shift.** -/
@[reassoc]
theorem derivedPullbackComparisonOnComplex_commShift (K : CochainComplex (ModuleSheaves X) ℤ) :
    (derivedPullback g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedPullbackComparisonOnComplex g K)⟦(1 : ℤ)⟧' =
      derivedPullbackComparisonOnComplex g (K⟦(1 : ℤ)⟧) ≫
        DerivedCategory.Q.map ((((modulePullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _ := by
  have h := NatTrans.shift_app_comm (derivedPullbackComparisonNat g) (1 : ℤ) K
  simp only [Functor.commShiftIso_comp_hom_app, derivedPullbackComparisonNat_app,
    Category.assoc] at h
  exact h

/-! ### The degreewise pullback of a two-term complex -/

section Double

open HomologicalComplex CochainComplex

variable {C B : ModuleSheaves X} (d : C ⟶ B)

/-- The identification of the pullback of a single complex with the single complex of the
pullback. -/
abbrev singlePullbackIso (M : ModuleSheaves X) :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj M) ≅
      (single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj M) :=
  (singleMapHomologicalComplex (modulePullback g) (ComplexShape.up ℤ) 0).app M

/-- Naturality of `singlePullbackIso` in the module. -/
theorem singlePullbackIso_naturality {M N : ModuleSheaves X} (a : M ⟶ N) :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map a) ≫ (singlePullbackIso g N).hom =
      (singlePullbackIso g M).hom ≫
        (single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map ((modulePullback g).map a) :=
  (singleMapHomologicalComplex (modulePullback g) (ComplexShape.up ℤ) 0).hom.naturality a

/-- Naturality of the inverse of `singlePullbackIso` in the module. -/
theorem singlePullbackIso_inv_naturality {M N : ModuleSheaves X} (a : M ⟶ N) :
    (single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map ((modulePullback g).map a) ≫
        (singlePullbackIso g N).inv =
      (singlePullbackIso g M).inv ≫ ((modulePullback g).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map a) :=
  (singleMapHomologicalComplex (modulePullback g) (ComplexShape.up ℤ) 0).inv.naturality a

private theorem mappingCone_map_eq_id {A : Type*} [Category* A] [Preadditive A]
    [HasBinaryBiproducts A] {K L : CochainComplex A ℤ} (φ : K ⟶ L) (a : K ⟶ K) (b : L ⟶ L)
    (ha : a = 𝟙 _) (hb : b = 𝟙 _) (comm : φ ≫ b = a ≫ φ) :
    mappingCone.map φ φ a b comm = 𝟙 _ := by
  subst ha hb
  exact mappingCone.map_id φ

/-- In degree `0`, `singlePullbackIso` is inverse to the pullback of the identification of the
single complex with its degree `0` term, followed by the one for `g^*M`. -/
private theorem map_singleObjXSelf_inv_comp_singlePullbackIso_hom_f (M : ModuleSheaves X) :
    (modulePullback g).map (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
      (singlePullbackIso g M).hom.f 0 =
    (singleObjXSelf (ComplexShape.up ℤ) 0 ((modulePullback g).obj M)).inv := by
  rw [singlePullbackIso, Iso.app_hom, singleMapHomologicalComplex_hom_app_self,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The identification of the mapping cone of the pullback of `single d` with the mapping cone of
`single (g^*d)`. -/
def mappingConePullbackIso :
    mappingCone (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≅
      mappingCone ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
        ((modulePullback g).map d)) where
  hom := mappingCone.map _ _ (singlePullbackIso g C).hom (singlePullbackIso g B).hom
    (singlePullbackIso_naturality g d)
  inv := mappingCone.map _ _ (singlePullbackIso g C).inv (singlePullbackIso g B).inv
    (singlePullbackIso_inv_naturality g d)
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    exact mappingCone_map_eq_id _ _ _ (Iso.hom_inv_id _) (Iso.hom_inv_id _) _
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    exact mappingCone_map_eq_id _ _ _ (Iso.inv_hom_id _) (Iso.inv_hom_id _) _

/-- **The degreewise pullback of the two-term complex `double d` is `double (g^*d)`**: the
identification `HomologicalComplex.doubleMapFunctorIso`, read in this direction. -/
abbrev mapDoubleIso :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (double d ComplexShape.upIntRelNegOneZero) ≅
      double ((modulePullback g).map d) ComplexShape.upIntRelNegOneZero :=
  (doubleMapFunctorIso (modulePullback g) d ComplexShape.upIntRelNegOneZero (by decide)).symm

/-- `mapDoubleIso` read through the identifications of the two two-term complexes with mapping
cones. -/
theorem mapDoubleIso_hom_eq : (mapDoubleIso g d).hom =
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
    (mappingCone.mapHomologicalComplexIso _ (modulePullback g)).hom ≫
    (mappingConePullbackIso g d).hom ≫
    (doubleIsoMappingCone ((modulePullback g).map d) ComplexShape.upIntRelNegOneZero).inv := by
  rw [← cancel_mono (doubleIsoMappingCone ((modulePullback g).map d)
    ComplexShape.upIntRelNegOneZero).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  apply from_double_hom_ext
  · simp only [doubleIsoMappingCone, doubleToMappingCone, asIso_hom, doubleMapFunctorIso,
      doubleMapFunctorHom, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mkHomFromDouble_f₀, mappingCone.mapHomologicalComplexIso, Hom.isoOfComponents_hom_f,
      mappingCone.mapHomologicalComplexXIso_eq _ _ (-1) 0 (by norm_num),
      mappingCone.mapHomologicalComplexXIso'_hom, mappingConePullbackIso, mappingCone.map,
      Category.assoc]
    congr 1
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      ← Functor.map_comp_assoc, mappingCone.inl_v_fst_v, mappingCone.inl_v_snd_v,
      Category.comp_id, comp_zero, Functor.map_zero, zero_comp, add_zero,
      mappingCone.inl_v_desc_f]
    rw [HomComplex.Cochain.comp_v _ _ (zero_add _) 0 0 (-1) (by norm_num) (by norm_num),
      HomComplex.Cochain.ofHom_v, Iso.inv_hom_id_assoc, ← Category.assoc,
      map_singleObjXSelf_inv_comp_singlePullbackIso_hom_f]
  · simp only [doubleIsoMappingCone, doubleToMappingCone, asIso_hom, doubleMapFunctorIso,
      doubleMapFunctorHom, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mkHomFromDouble_f₁, mappingCone.mapHomologicalComplexIso, Hom.isoOfComponents_hom_f,
      mappingCone.mapHomologicalComplexXIso_eq _ _ 0 1 (by norm_num),
      mappingCone.mapHomologicalComplexXIso'_hom, mappingConePullbackIso, mappingCone.map,
      Category.assoc]
    congr 1
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      ← Functor.map_comp_assoc, mappingCone.inr_f_fst_v, mappingCone.inr_f_snd_v,
      Category.comp_id, comp_zero, Functor.map_zero, zero_comp, zero_add,
      mappingCone.inr_f_desc_f]
    rw [HomologicalComplex.comp_f, Iso.inv_hom_id_assoc, ← Category.assoc,
      map_singleObjXSelf_inv_comp_singlePullbackIso_hom_f]

/-- Under `mapDoubleIso`, the pullback of the inclusion of the degree `0` term `ℬ` into
`double d` is the inclusion of `g^*ℬ` into `double (g^*d)`. -/
theorem map_doubleInclh_comp_mapDoubleIso_hom :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (mappingCone.inr ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d) ≫
          (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).inv) ≫
        (mapDoubleIso g d).hom =
      (singlePullbackIso g B).hom ≫
        mappingCone.inr ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
          ((modulePullback g).map d)) ≫
        (doubleIsoMappingCone ((modulePullback g).map d) ComplexShape.upIntRelNegOneZero).inv := by
  have h₂ : mappingCone.inr (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
      mappingCone.map _ _ (singlePullbackIso g C).hom (singlePullbackIso g B).hom
        (singlePullbackIso_naturality g d) =
      (singlePullbackIso g B).hom ≫ mappingCone.inr ((single (ModuleSheaves Y)
        (ComplexShape.up ℤ) 0).map ((modulePullback g).map d)) :=
    (mappingCone.triangleMap _ _ _ _ (singlePullbackIso_naturality g d)).comm₂
  rw [mapDoubleIso_hom_eq]
  simp only [mappingConePullbackIso, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ))
    (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Category.assoc _ (mappingCone.mapHomologicalComplexIso _ _).hom,
    mappingCone.map_inr, reassoc_of% h₂]

/-- The third morphism of the triangle of a mapping cone, with its source written as the mapping
cone itself. -/
abbrev coneδ {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) : mappingCone φ ⟶ K⟦(1 : ℤ)⟧ :=
  (mappingCone.triangle φ).mor₃

/-- The pullback of the third morphism of the mapping cone triangle of `single d`, followed by the
identifications with the shift and `singlePullbackIso`, is the third morphism of the mapping cone
triangle of `single (g^*d)`, read through `mappingConePullbackIso`. -/
theorem map_coneδ_comp_singlePullbackIso :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C) ≫
        (singlePullbackIso g C).hom⟦(1 : ℤ)⟧' =
      (mappingCone.mapHomologicalComplexIso _ (modulePullback g)).hom ≫
        (mappingConePullbackIso g d).hom ≫
        coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
          ((modulePullback g).map d)) := by
  have h₃ : mappingCone.map _ _ (singlePullbackIso g C).hom (singlePullbackIso g B).hom
        (singlePullbackIso_naturality g d) ≫
      coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map ((modulePullback g).map d)) =
      coneδ (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (singlePullbackIso g C).hom⟦(1 : ℤ)⟧' :=
    (mappingCone.triangleMap _ _ _ _ (singlePullbackIso_naturality g d)).comm₃.symm
  have hδ : ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C) =
      (mappingCone.mapHomologicalComplexIso _ (modulePullback g)).hom ≫
        coneδ (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) :=
    mappingCone.map_δ _ _
  rw [reassoc_of% hδ]
  exact congrArg (_ ≫ ·) h₃.symm

/-- Under `mapDoubleIso`, the pullback of the projection of `double d` onto `C[1]` is the
projection of `double (g^*d)` onto `(g^*C)[1]`. -/
theorem map_doubleProj_comp :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C) ≫
        (singlePullbackIso g C).hom⟦(1 : ℤ)⟧' =
      (mapDoubleIso g d).hom ≫
        (doubleIsoMappingCone ((modulePullback g).map d) ComplexShape.upIntRelNegOneZero).hom ≫
        coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
          ((modulePullback g).map d)) := by
  rw [Functor.map_comp, Category.assoc, map_coneδ_comp_singlePullbackIso, mapDoubleIso_hom_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Double

/-! ### The comparison on the triangle of a two-term complex -/

section Triangle

open HomologicalComplex CochainComplex NaiveCotangentTwoTerm

/-- The comparison `Lg^*(M[0]) ⟶ (g^*M)[0]` of a module placed in degree `0`. -/
abbrev kSingle (M : ModuleSheaves X) :
    (derivedPullback g).obj (DerivedCategory.Q.obj
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj M)) ⟶
      DerivedCategory.Q.obj ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj
        ((modulePullback g).obj M)) :=
  derivedPullbackComparisonOnComplex g ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map (singlePullbackIso g M).hom

/-- Naturality of `kSingle` in the module. -/
@[reassoc]
theorem kSingle_naturality {M N : ModuleSheaves X} (a : M ⟶ N) :
    (derivedPullback g).map (DerivedCategory.Q.map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map a)) ≫ kSingle g N =
      kSingle g M ≫ DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
        ((modulePullback g).map a)) := by
  simp only [kSingle]
  rw [derivedPullbackComparisonOnComplex_naturality'_assoc, Category.assoc,
    ← Functor.map_comp DerivedCategory.Q, ← Functor.map_comp DerivedCategory.Q,
    singlePullbackIso_naturality]

/-- Naturality of the shift of `kSingle` by `1` in the module. -/
@[reassoc]
theorem kSingle_naturality_shift {M N : ModuleSheaves X} (a : M ⟶ N) :
    ((derivedPullback g).map (DerivedCategory.Q.map
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map a)))⟦(1 : ℤ)⟧' ≫
        (kSingle g N)⟦(1 : ℤ)⟧' =
      (kSingle g M)⟦(1 : ℤ)⟧' ≫ (DerivedCategory.Q.map ((single (ModuleSheaves Y)
        (ComplexShape.up ℤ) 0).map ((modulePullback g).map a)))⟦(1 : ℤ)⟧' := by
  rw [← Functor.map_comp, ← Functor.map_comp, kSingle_naturality]

variable {C B : ModuleSheaves X} (d : C ⟶ B)

/-- **The comparison on the inclusion of the degree `0` term.** -/
@[reassoc]
theorem map_incl_comp_derivedPullbackComparisonOnComplex :
    (derivedPullback g).map (DerivedCategory.Q.map
        (mappingCone.inr ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
          DerivedCategory.Q.map (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).inv) ≫
        derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map (mapDoubleIso g d).hom =
      kSingle g B ≫ DerivedCategory.Q.map (mappingCone.inr ((single (ModuleSheaves Y)
          (ComplexShape.up ℤ) 0).map ((modulePullback g).map d))) ≫
        DerivedCategory.Q.map (doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).inv := by
  rw [← Functor.map_comp DerivedCategory.Q (mappingCone.inr _),
    derivedPullbackComparisonOnComplex_naturality'_assoc,
    ← Functor.map_comp DerivedCategory.Q (((modulePullback g).mapHomologicalComplex _).map _)
      (mapDoubleIso g d).hom, map_doubleInclh_comp_mapDoubleIso_hom]
  simp only [kSingle, Functor.map_comp, Category.assoc]

/-- The image under `DerivedCategory.Q` of `map_doubleProj_comp`, with the shift commuted past
`DerivedCategory.Q`. -/
theorem Q_map_proj_aux :
    DerivedCategory.Q.map (((modulePullback g).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d))) ≫
      DerivedCategory.Q.map ((((modulePullback g).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
      (DerivedCategory.Q.map (singlePullbackIso g C).hom)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
        DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
            ((modulePullback g).map d))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C)) := by
  rw [← Functor.commShiftIso_hom_naturality DerivedCategory.Q, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  exact congrArg (fun t ↦ DerivedCategory.Q.map t ≫ _) (map_doubleProj_comp g d)

/-- **The comparison on the projection onto the shifted degree `-1` term.** -/
@[reassoc]
theorem map_proj_comp_kSingle :
    (derivedPullback g).map (DerivedCategory.Q.map
        ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d))) ≫
        (derivedPullback g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        (derivedPullbackComparisonOnComplex g
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C))⟦(1 : ℤ)⟧' ≫
        (DerivedCategory.Q.map (singlePullbackIso g C).hom)⟦(1 : ℤ)⟧' =
      derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
        DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
            ((modulePullback g).map d))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C)) := by
  rw [derivedPullbackComparisonOnComplex_commShift_assoc,
    derivedPullbackComparisonOnComplex_naturality'_assoc]
  refine congrArg (derivedPullbackComparisonOnComplex g _ ≫ ·) ?_
  exact Q_map_proj_aux g d

/-- `map_proj_comp_kSingle`, with the comparison on `C[0]` written as `kSingle g C`. -/
@[reassoc]
theorem map_proj_comp_kSingle' :
    (derivedPullback g).map (DerivedCategory.Q.map
        ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d))) ≫
        (derivedPullback g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        (kSingle g C)⟦(1 : ℤ)⟧' =
      derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
        DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
            ((modulePullback g).map d))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C)) := by
  rw [kSingle, Functor.map_comp (CategoryTheory.shiftFunctor (DerivedCategory (ModuleSheaves Y))
    (1 : ℤ))]
  exact map_proj_comp_kSingle g d

/-- The third morphism of `ofDoubleNegOne d` is the image under `DerivedCategory.Q` of the
projection of `double d` onto `C[1]`, followed by the commutation of `DerivedCategory.Q` with the
shift. -/
theorem ofDoubleNegOne_proj_eq :
    (ofDoubleNegOne d).proj =
      DerivedCategory.Q.map ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C) := by
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- `kSingle g F` written through `DerivedCategory.quotientCompQhIso` and
`derivedPullbackComparison g`. -/
theorem kSingle_eq (F : ModuleSheaves X) :
    kSingle g F = (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      (derivedPullbackComparison g).app ((HomotopyCategory.quotient _ _).obj
        ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      DerivedCategory.Q.map (singlePullbackIso g F).hom := by
  have hf : ((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F) = 𝟙 _ := rfl
  have h2 : DerivedCategory.Qh.map (((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      (DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).hom.app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) =
      (DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).hom.app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) := by
    rw [hf]
    exact (congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)
  rw [kSingle, derivedPullbackComparisonOnComplex]
  simp only [Category.assoc]
  rw [reassoc_of% h2]

/-- The comparison `derivedPullbackSingleObj g F` is `kSingle g F`. -/
theorem derivedPullbackSingleObj_eq (F : ModuleSheaves X) :
    derivedPullbackSingleObj g F = kSingle g F := by
  rw [kSingle_eq, derivedPullbackSingleObj, Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
  rfl

/-- The image under `Lg^*` of the projection of `double d` onto `C[1]` followed by `δ[1]`, then
`kSingle g F` shifted and `c`, is the comparison followed by `mapDoubleIso`, the projection of
`double (g^*d)` onto `(g^*C)[1]` and `(c ∘ g^*δ)[1]`. -/
theorem map_conormalExtClass_aux {F : ModuleSheaves X} {G : ModuleSheaves Y} (δ : C ⟶ F)
    (c : (modulePullback g).obj F ⟶ G) :
    (derivedPullback g).map (DerivedCategory.Q.map
        ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d))) ≫
      (derivedPullback g).map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
      (derivedPullback g).map ((DerivedCategory.Q.map
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map δ))⟦(1 : ℤ)⟧') ≫
      ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      (kSingle g F)⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map c))⟦(1 : ℤ)⟧' =
    derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
      DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
      DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom ≫
        coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map ((modulePullback g).map d))) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C)) ≫
      (DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
        ((modulePullback g).map δ ≫ c)))⟦(1 : ℤ)⟧' := by
  have hcL := Functor.commShiftIso_hom_naturality (derivedPullback g)
    (DerivedCategory.Q.map ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map δ)) (1 : ℤ)
  rw [reassoc_of% hcL]
  rw [kSingle_naturality_shift_assoc, map_proj_comp_kSingle'_assoc]
  simp only [Functor.map_comp, Category.assoc]

/-- `map_conormalExtClass_aux`, with `kSingle g F` written as `derivedPullbackSingleObj g F` and
the composites grouped as in `pullbackExtClass_conormalExtClass`. -/
theorem map_conormalExtClass_aux' {F : ModuleSheaves X} {G : ModuleSheaves Y} (δ : C ⟶ F)
    (c : (modulePullback g).obj F ⟶ G) :
    (derivedPullback g).map ((DerivedCategory.Q.map
        (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
        DerivedCategory.Q.map (coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        (DerivedCategory.Q.map
          ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map δ))⟦(1 : ℤ)⟧') ≫
      ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj F)) ≫
      (derivedPullbackSingleObj g F ≫
        DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map c))⟦(1 : ℤ)⟧' =
    derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
      DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
      (DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom) ≫
        DerivedCategory.Q.map (coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
          ((modulePullback g).map d))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C))) ≫
      (DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
        ((modulePullback g).map δ ≫ c)))⟦(1 : ℤ)⟧' := by
  rw [derivedPullbackSingleObj_eq]
  simpa only [Functor.map_comp, Category.assoc] using map_conormalExtClass_aux g d δ c

/-- **The image of a conormal class under `Lg^*`.** For a two-term complex `K = (𝒞 ⟶ ℬ)`, a
homomorphism `δ : 𝒞 ⟶ ℱ` and a coefficient map `c : g^*ℱ ⟶ 𝒢`, the image of the class of `δ` in
`Ext¹(K, ℱ)` under `Lg^*`, commuted past the shift and pushed along `c`, is the comparison
`Lg^*K ⟶ g^*K = (g^*𝒞 ⟶ g^*ℬ)` followed by the class of `c ∘ g^*δ` in `Ext¹(g^*K, 𝒢)`. -/
theorem pullbackExtClass_conormalExtClass {F : ModuleSheaves X} {G : ModuleSheaves Y}
    (δ : C ⟶ F) (c : (modulePullback g).obj F ⟶ G) :
    (derivedPullback g).map ((ofDoubleNegOne d).conormalExtClass F δ) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        (coefficientExtMap g c)⟦(1 : ℤ)⟧' =
      derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
        (ofDoubleNegOne ((modulePullback g).map d)).conormalExtClass G
          ((modulePullback g).map δ ≫ c) :=
  map_conormalExtClass_aux' g d δ c

end Triangle

/-! ### Injectivity on `Ext¹` when the degree `0` term is flat -/

section Injectivity

open HomologicalComplex CochainComplex NaiveCotangentTwoTerm

/-- **On a flat module the comparison is invertible**: a flat module in degree `0` is K-flat. -/
theorem isIso_kSingle {M : ModuleSheaves X}
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    IsIso (kSingle g M) := by
  have hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X
      ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj M) :=
    Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.sheaf M hM 0
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    g _ hK
  have : IsIso (derivedPullbackComparisonOnComplex g
      ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj M)) := by
    unfold derivedPullbackComparisonOnComplex
    infer_instance
  infer_instance

/-- **Precomposition with the comparison is injective on homomorphisms out of a module in degree
`0`**: a homomorphism `g^*M ⟶ 𝒢` which vanishes on `Lg^*(M[0])` vanishes. The module `M` is
covered by a flat module, on which the comparison is invertible, and `g^*` preserves
epimorphisms. -/
theorem eq_zero_of_kSingle_comp {M : ModuleSheaves X} {G : ModuleSheaves Y}
    (z : (modulePullback g).obj M ⟶ G)
    (hz : kSingle g M ≫ DerivedCategory.Q.map
      ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map z) = 0) : z = 0 := by
  obtain ⟨P, π, hP, hπ⟩ := Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat X.sheaf M
  have := isIso_kSingle g hP
  have he : Epi ((modulePullback g).map π) :=
    @Functor.PreservesEpimorphisms.preserves _ _ _ _ _
      (Functor.preservesEpimorphisms_of_adjunction (modulePullbackPushforwardAdjunction g)) _ _ π hπ
  have h1 : kSingle g P ≫ DerivedCategory.Q.map
      ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
      ((modulePullback g).map π ≫ z)) = 0 := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← kSingle_naturality g π,
      Category.assoc, hz, comp_zero]
  have h2 : DerivedCategory.Q.map ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
      ((modulePullback g).map π ≫ z)) = 0 := by
    rw [← cancel_epi (kSingle g P), h1, comp_zero]
  have h3 : (modulePullback g).map π ≫ z = 0 := by
    apply (DerivedCategory.singleFunctor (ModuleSheaves Y) 0).map_injective
    rwa [Functor.map_zero]
  rw [← cancel_epi ((modulePullback g).map π), h3, comp_zero]

variable {C B : ModuleSheaves X} (d : C ⟶ B)

/-- The second morphism of `ofDoubleNegOne d` is the image under `DerivedCategory.Q` of the
inclusion of `B[0]` into the mapping cone, followed by the identification of the mapping cone with
`double d`. -/
theorem ofDoubleNegOne_incl_eq :
    (ofDoubleNegOne d).incl =
      DerivedCategory.Q.map
          (mappingCone.inr ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        DerivedCategory.Q.map (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).inv :=
  rfl

end Injectivity

/-! ### An abstract diagram chase -/

section Chase

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A diagram chase in a pretriangulated category.** Let `T` and `T'` be distinguished
triangles and `k₁, k₂, k₃` maps between their objects commuting with the first two morphisms and,
through `m` and `m'`, with the third ones. If `k₂` is invertible and precomposition with
`k₁⟦1⟧` is injective on morphisms to `Z`, then so is precomposition with `k₃` on morphisms
`T'.obj₃ ⟶ Z`. -/
theorem eq_zero_of_comp_eq_zero_of_triangle {T T' : Triangle D} (hT : T ∈ distTriang D)
    (hT' : T' ∈ distTriang D) (k₁ : T.obj₁ ⟶ T'.obj₁) (k₂ : T.obj₂ ⟶ T'.obj₂)
    (k₃ : T.obj₃ ⟶ T'.obj₃) [IsIso k₂] (hc₁ : T.mor₁ ≫ k₂ = k₁ ≫ T'.mor₁)
    (hc₂ : T.mor₂ ≫ k₃ = k₂ ≫ T'.mor₂) {m : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧}
    {m' : T'.obj₃ ⟶ T'.obj₁⟦(1 : ℤ)⟧} (hm : T.mor₃ = m) (hm' : T'.mor₃ = m')
    (hc₃ : m ≫ k₁⟦(1 : ℤ)⟧' = k₃ ≫ m') {Z : D}
    (hinj : ∀ w : T'.obj₁⟦(1 : ℤ)⟧ ⟶ Z, k₁⟦(1 : ℤ)⟧' ≫ w = 0 → w = 0)
    (x : T'.obj₃ ⟶ Z) (hx : k₃ ≫ x = 0) : x = 0 := by
  subst hm hm'
  have h1 : T'.mor₂ ≫ x = 0 := by
    rw [← cancel_epi k₂, ← Category.assoc, ← hc₂, Category.assoc, hx, comp_zero, comp_zero]
  obtain ⟨v, rfl⟩ := Triangle.yoneda_exact₃ _ hT' x h1
  have h2 : T.mor₃ ≫ k₁⟦(1 : ℤ)⟧' ≫ v = 0 := by
    rw [← Category.assoc, hc₃, Category.assoc, hx]
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) _ h2
  obtain ⟨u', hu'⟩ : ∃ u' : T.obj₂⟦(1 : ℤ)⟧ ⟶ Z,
      k₁⟦(1 : ℤ)⟧' ≫ v = -(T.mor₁⟦(1 : ℤ)⟧' ≫ u') :=
    ⟨u, by rw [hu]; exact Preadditive.neg_comp _ _⟩
  have h3 : k₁⟦(1 : ℤ)⟧' ≫ (v + T'.mor₁⟦(1 : ℤ)⟧' ≫ inv k₂⟦(1 : ℤ)⟧' ≫ u') = 0 := by
    have e : k₁⟦(1 : ℤ)⟧' ≫ T'.mor₁⟦(1 : ℤ)⟧' ≫ inv k₂⟦(1 : ℤ)⟧' = T.mor₁⟦(1 : ℤ)⟧' := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, ← hc₁, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [Preadditive.comp_add, hu', reassoc_of% e, neg_add_cancel]
  have h4 := hinj _ h3
  rw [show v = -(T'.mor₁⟦(1 : ℤ)⟧' ≫ inv k₂⟦(1 : ℤ)⟧' ≫ u') from eq_neg_of_add_eq_zero_left h4,
    Preadditive.comp_neg, ← Category.assoc, comp_distTriang_mor_zero₃₁ _ hT', zero_comp, neg_zero]

end Chase


/-! ### Injectivity on `Ext¹` -/

section InjectivityExt

open HomologicalComplex CochainComplex NaiveCotangentTwoTerm

variable {C B : ModuleSheaves X} (d : C ⟶ B)

/-- The triangle of the two-term complex `double d`, with its morphisms written out. -/
theorem double_triangle_distinguished {Z : RingedSpace.{u, u}} {C' B' : ModuleSheaves Z}
    (d' : C' ⟶ B') :
    Triangle.mk ((DerivedCategory.singleFunctor (ModuleSheaves Z) 0).map d')
      (DerivedCategory.Q.map
          (mappingCone.inr ((single (ModuleSheaves Z) (ComplexShape.up ℤ) 0).map d')) ≫
        DerivedCategory.Q.map (doubleIsoMappingCone d' ComplexShape.upIntRelNegOneZero).inv)
      (DerivedCategory.Q.map ((doubleIsoMappingCone d' ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves Z) (ComplexShape.up ℤ) 0).map d')) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Z) (ComplexShape.up ℤ) 0).obj C')) ∈ distTriang _ := by
  have h := (ofDoubleNegOne d').distinguished
  rwa [ofDoubleNegOne_proj_eq] at h

/-- The derived pullback of the triangle of `double d`, with its morphisms written out. -/
theorem derivedPullback_double_triangle_distinguished :
    Triangle.mk ((derivedPullback g).map
        ((DerivedCategory.singleFunctor (ModuleSheaves X) 0).map d))
      ((derivedPullback g).map (DerivedCategory.Q.map
          (mappingCone.inr ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
        DerivedCategory.Q.map (doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).inv))
      ((derivedPullback g).map (DerivedCategory.Q.map
          ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
            coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C))) ∈
      distTriang _ :=
  (derivedPullback g).map_distinguished _ (double_triangle_distinguished d)

/-- `map_proj_comp_kSingle'`, with the composites grouped as the third morphisms of the triangles
`derivedPullback_double_triangle_distinguished` and `double_triangle_distinguished`. -/
theorem map_proj_comp_kSingle_unsplit :
    ((derivedPullback g).map (DerivedCategory.Q.map
          ((doubleIsoMappingCone d ComplexShape.upIntRelNegOneZero).hom ≫
            coneδ ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map d)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C)) ≫
        ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((single (ModuleSheaves X) (ComplexShape.up ℤ) 0).obj C))) ≫
        (kSingle g C)⟦(1 : ℤ)⟧' =
      (derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map (mapDoubleIso g d).hom) ≫
        (DerivedCategory.Q.map ((doubleIsoMappingCone ((modulePullback g).map d)
          ComplexShape.upIntRelNegOneZero).hom ≫
          coneδ ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map
            ((modulePullback g).map d))) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj C))) := by
  rw [Functor.map_comp (derivedPullback g)]
  simpa only [Category.assoc] using map_proj_comp_kSingle' g d

/-- **Injectivity of precomposition with the comparison `Lg^*K ⟶ g^*K` on `Ext¹(g^*K, 𝒢)`**, for
a two-term complex `K = (𝒞 ⟶ ℬ)` in degrees `-1` and `0` whose degree `0` term `ℬ` is flat: a
class in `Ext¹(g^*K, 𝒢)` which vanishes on `Lg^*K` vanishes. -/
theorem eq_zero_of_derivedPullbackComparisonOnComplex_comp
    (hB : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) B)
    {G : ModuleSheaves Y}
    (x : DerivedCategory.Q.obj (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (double d ComplexShape.upIntRelNegOneZero)) ⟶
      ((DerivedCategory.singleFunctor (ModuleSheaves Y) 0).obj G)⟦(1 : ℤ)⟧)
    (hx : derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫ x = 0) :
    x = 0 := by
  have := isIso_kSingle g hB
  have hcancel : DerivedCategory.Q.map (mapDoubleIso g d).hom ≫
      DerivedCategory.Q.map (mapDoubleIso g d).inv ≫ x = x := by
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hinj : ∀ w : ((DerivedCategory.singleFunctor (ModuleSheaves Y) 0).obj
      ((modulePullback g).obj C))⟦(1 : ℤ)⟧ ⟶
        ((DerivedCategory.singleFunctor (ModuleSheaves Y) 0).obj G)⟦(1 : ℤ)⟧,
      (kSingle g C)⟦(1 : ℤ)⟧' ≫ w = 0 → w = 0 := by
    intro w hw
    obtain ⟨z, rfl⟩ := exists_eq_shift_map (DerivedCategory.singleFunctor (ModuleSheaves Y) 0) w
    have hz : kSingle g C ≫ DerivedCategory.Q.map
        ((single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map z) = 0 := by
      apply (CategoryTheory.shiftFunctor (DerivedCategory (ModuleSheaves Y)) (1 : ℤ)).map_injective
      rwa [Functor.map_comp, Functor.map_zero]
    rw [eq_zero_of_kSingle_comp g z hz, Functor.map_zero, Functor.map_zero]
  have hx' : (derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
      DerivedCategory.Q.map (mapDoubleIso g d).hom) ≫
        (DerivedCategory.Q.map (mapDoubleIso g d).inv ≫ x) = 0 := by
    rw [Category.assoc, hcancel, hx]
  have key := eq_zero_of_comp_eq_zero_of_triangle
    (derivedPullback_double_triangle_distinguished g d)
    (double_triangle_distinguished ((modulePullback g).map d))
    (kSingle g C) (kSingle g B)
    (derivedPullbackComparisonOnComplex g (double d ComplexShape.upIntRelNegOneZero) ≫
      DerivedCategory.Q.map (mapDoubleIso g d).hom)
    (kSingle_naturality g d) (map_incl_comp_derivedPullbackComparisonOnComplex g d)
    rfl rfl (map_proj_comp_kSingle_unsplit g d) hinj _ hx'
  rw [← hcancel, key, comp_zero]

end InjectivityExt

end AlgebraicGeometry.RingedSpaceThickening

end
