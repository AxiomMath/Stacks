module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFlatteningIdealOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRingLevelZeroLocusOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing loci along an affine chart are closed subspaces

Over an affine object `V` of the big fppf category over `S`, along a chart `g` whose source is the
algebraic space of an affine object `W` and along which the sections of `g^*𝒢` are projective
over `Γ(V, ⊤)`, the vanishing locus of the chart's map is a closed subspace of `V`.

The closed subspace is cut out by an ideal of `Γ(V, ⊤)`: the extension of scalars of the sections
of `g^*u` over `Γ(W, 𝒪_W)` to `Γ(W, 𝒪_W) ⊗_{Γ(V, ⊤)} Γ(T, ⊤)` vanishes exactly when the ideal
dies in `Γ(T, ⊤)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_affine_cover_le_ker_appTop_iff`: every object `U` of the
  category has an affine cover inside the category along which containment of an ideal of
  `Γ(V, ⊤)` in the kernel of `Γ(V, ⊤) ⟶ Γ(U, ⊤)` is detected.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_projective`: the
  vanishing subfunctor of the base is a closed subspace for a situation presented through an
  affine chart through which every morphism from a representable presheaf factors.
* `AlgebraicGeometry.Space.ModuleMapSituation.affineChartZeroLocusClosed`:
  `AlgebraicGeometry.Space.ModuleMapSituation.AffineChartZeroLocusClosed` holds for every big fppf
  site.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every object `U` of the big fppf category over `S` has an affine cover inside that category
along which containment of an ideal in the kernel on global functions is detected: for a morphism
`k : U ⟶ V` of the category and an ideal `I` of `Γ(V, ⊤)`, the containment
`I ≤ \ker(Γ(V, ⊤) ⟶ Γ(U, ⊤))` holds exactly when it holds for each member of the cover. -/
theorem BigFppfOver.exists_affine_cover_le_ker_appTop_iff (U : BigFppfOver B S hS) :
    ∃ (ι : Type u) (A : ι → BigFppfOver B S hS) (g : ∀ i, A i ⟶ U),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (A i))) ∧
      ∀ (V : BigFppfOver B S hS) (k : U ⟶ V)
        (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
        (I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom ↔
          ∀ i, I ≤ RingHom.ker
            ((BigFppfOver.toScheme B S hS).map (g i ≫ k)).appTop.hom) := by
  classical
  let 𝒰 : Scheme.OpenCover.{u, u} ((BigFppfOver.toScheme B S hS).obj U) :=
    ((BigFppfOver.toScheme B S hS).obj U).affineCover
  have hc : ∀ i, B.Contains (𝒰.X i) := fun i =>
    B.contains_of_isOpenImmersion (𝒰.f i) U.left.2
  refine ⟨𝒰.I₀, fun i => BigFppfOver.mk B S hS (hc i) (𝒰.f i ≫ B.inclusion.map U.hom),
    fun i => Over.homMk (ObjectProperty.homMk (X := B.obj (hc i)) (Y := U.left) (𝒰.f i))
      (by apply ObjectProperty.hom_ext; rfl),
    fun i => show IsAffine (𝒰.X i) from inferInstance, fun V k I => ?_⟩
  have hcomp : ∀ i, ∀ a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      ((BigFppfOver.toScheme B S hS).map
          ((Over.homMk (ObjectProperty.homMk (X := B.obj (hc i)) (Y := U.left) (𝒰.f i))
            (by apply ObjectProperty.hom_ext; rfl) :
              BigFppfOver.mk B S hS (hc i) (𝒰.f i ≫ B.inclusion.map U.hom) ⟶ U) ≫
            k)).appTop.hom a =
        (𝒰.f i).appTop.hom (((BigFppfOver.toScheme B S hS).map k).appTop.hom a) := by
    intro i a
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  refine ⟨fun h i a ha => ?_, fun h a ha => ?_⟩
  · rw [RingHom.mem_ker, hcomp i a, RingHom.mem_ker.mp (h ha), map_zero]
    rfl
  · refine RingHom.mem_ker.mpr (Scheme.zero_of_zero_cover _ 𝒰 fun i => ?_)
    exact (hcomp i a).symm.trans (RingHom.mem_ker.mp (h i ha))

namespace Space

/-- Factoring through the range of `yoneda` of a monomorphism of the category is factoring through
the monomorphism itself. -/
theorem exists_comp_range_yoneda_map_iff {P Y₀ : BigFppfOver B S hS} (j : P ⟶ Y₀)
    [Mono (yoneda.map j)] (U : BigFppfOver B S hS) (h : yoneda.obj U ⟶ yoneda.obj Y₀) :
    (∃ k : yoneda.obj U ⟶ (Subfunctor.range (yoneda.map j)).toFunctor,
        k ≫ (Subfunctor.range (yoneda.map j)).ι = h) ↔
      ∃ χ : U ⟶ P, yoneda.map χ ≫ yoneda.map j = h := by
  have hinv : inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map j =
      (Subfunctor.range (yoneda.map j)).ι :=
    (congrArg (fun m => inv (Subfunctor.toRange (yoneda.map j)) ≫ m)
      (Subfunctor.toRange_ι (yoneda.map j)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨yoneda.preimage (k ≫ inv (Subfunctor.toRange (yoneda.map j))), ?_⟩
    rwa [Functor.map_preimage, Category.assoc, hinv]
  · rintro ⟨χ, hχ⟩
    refine ⟨yoneda.map χ ≫ Subfunctor.toRange (yoneda.map j), ?_⟩
    rwa [Category.assoc, Subfunctor.toRange_ι]

namespace ModuleMapSituation

/-- Let `D` be a situation of Stacks 083F whose target is the algebraic space of an affine object
`Y₀` of the category, let `V₀` be an affine chart of its source space through which every
morphism from a representable factors, and suppose the sections of `𝒢` over `V₀` are projective
over `Γ(Y₀, ⊤)`.  Then there is an ideal `I` of `Γ(Y₀, ⊤)` such that, at every affine test
scheme, the base change of `u` vanishes exactly when `I` dies in the functions on the test
scheme. -/
theorem exists_ideal_isZeroAt_iff_le_ker_of_isAffine
    (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀)
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom)
    (hproj :
      letI : CommRing
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
      letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartSiteAlgebra B S hS D.X V₀ α
      letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
            (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
        Module.compHom _ (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))))
      Module.Projective (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u)) :
    ∃ I : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u),
      ∀ T : D.SchemesOver, IsAffine (D.testScheme.obj T) →
        (D.IsZeroAt (modulePullbackSystem B S hS) T ↔
          I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map
            (testSiteHom B S hS D hDY T)).appTop.hom) := by
  let : CommRing
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
  let : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
    chartSiteAlgebra B S hS D.X V₀ α
  let : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
        (isEtale_chartToSpace B S hS D.X V₀)).obj D.F).val.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
    Module.compHom _ (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))))
  let : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
        (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
    Module.compHom _ (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))))
  have : IsScalarTower (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
      ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
        (isEtale_chartToSpace B S hS D.X V₀)).obj D.F).val.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
    ⟨fun r c m => mul_smul (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) r) c m⟩
  have : IsScalarTower (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))
      ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
        (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
    ⟨fun r c n => mul_smul (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) r) c n⟩
  obtain ⟨I, hI⟩ := Stacks.Flattening.exists_ideal_lTensor_tensorProduct_eq_zero_iff
    ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
      (isEtale_chartToSpace B S hS D.X V₀)).map D.u).val.app
      (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))).hom) hproj
  refine ⟨I, fun T hT => ?_⟩
  let := siteMorphismAlgebra B S hS (testSiteHom B S hS D hDY T)
  refine (isZeroAt_iff_baseChange_val_app B S hS D hDY hY₀ V₀ α hα hV₀ hV₀term T hT).trans ?_
  refine (Stacks.Flattening.baseChange_eq_zero_iff_lTensor _ _).trans ?_
  exact hI (Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) : Type u)
    ((BigFppfOver.toScheme B S hS).map (testSiteHom B S hS D hDY T)).appTop.hom

/-! ### From the affine test schemes to all of them -/

/-- An object of the category equipped with a morphism to `Y₀`, read as a test scheme of a
situation whose target is the algebraic space of `Y₀`.  The transport along the identification of
the target is composed in, so that the structure morphism is the Yoneda image of the given
morphism of the category. -/
def siteTest (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) {U : BigFppfOver B S hS} (k : U ⟶ Y₀) : D.SchemesOver :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map k ≫ eqToHom hDY.symm)

/-- The object of `AlgebraicGeometry.Space.ModuleMapSituation.siteTest` is the given object. -/
@[simp]
theorem siteTest_left (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) {U : BigFppfOver B S hS} (k : U ⟶ Y₀) :
    (siteTest B S hS D hDY k).left = U := rfl

/-- The image under `schemeSpaceFunctor` of the morphism of the category attached to a test scheme,
composed with the transport along `hDY`, is the structure morphism of the test scheme. -/
theorem schemeSpaceMap_testSiteHom_comp_eqToHom (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver) :
    (schemeSpaceFunctor B S hS).map (testSiteHom B S hS D hDY T) ≫ eqToHom hDY.symm = T.hom := by
  have hid : eqToHom hDY ≫ eqToHom hDY.symm = CategoryStruct.id D.Y :=
    (eqToHom_trans hDY hDY.symm).trans (eqToHom_refl _ _)
  refine ObjectProperty.hom_ext _ ?_
  change yoneda.map (testSiteHom B S hS D hDY T) ≫ (eqToHom hDY.symm).hom = T.hom.hom
  rw [yoneda_map_testSiteHom B S hS D hDY T]
  exact (congrArg (fun m : D.Y ⟶ D.Y => T.hom.hom ≫ m.hom) hid).trans (Category.comp_id _)

/-- The morphism of the category attached to
`AlgebraicGeometry.Space.ModuleMapSituation.siteTest` is the morphism one started with. -/
theorem testSiteHom_siteTest (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) {U : BigFppfOver B S hS}
    (k : U ⟶ Y₀) : testSiteHom B S hS D hDY (siteTest B S hS D hDY k) = k := by
  have hid : eqToHom hDY.symm ≫ eqToHom hDY = CategoryStruct.id (schemeSpace Y₀) :=
    (eqToHom_trans hDY.symm hDY).trans (eqToHom_refl _ _)
  refine yoneda.map_injective ?_
  refine (yoneda_map_testSiteHom B S hS D hDY (siteTest B S hS D hDY k)).trans ?_
  exact (congrArg (fun m : schemeSpace Y₀ ⟶ schemeSpace Y₀ => yoneda.map k ≫ m.hom) hid).trans
    (Category.comp_id _)

/-- A morphism of the category over `Y₀` into the object of a test scheme, read as a morphism of
test schemes. -/
def siteTestHomMk (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver) {U : BigFppfOver B S hS} (a : U ⟶ T.left) :
    siteTest B S hS D hDY (a ≫ testSiteHom B S hS D hDY T) ⟶ T :=
  CostructuredArrow.homMk a (by
    change (schemeSpaceFunctor B S hS).map a ≫ T.hom =
      (schemeSpaceFunctor B S hS).map (a ≫ testSiteHom B S hS D hDY T) ≫ eqToHom hDY.symm
    rw [Functor.map_comp, Category.assoc,
      schemeSpaceMap_testSiteHom_comp_eqToHom B S hS D hDY T])

/-- A factorisation of the structure morphism of a test scheme through a morphism to `Y₀`, read
as a morphism of test schemes. -/
def siteTestHomMkOfFactor (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver) {U : BigFppfOver B S hS} (k : U ⟶ Y₀)
    (a : T.left ⟶ U) (ha : a ≫ k = testSiteHom B S hS D hDY T) :
    T ⟶ siteTest B S hS D hDY k :=
  CostructuredArrow.homMk a (by
    change (schemeSpaceFunctor B S hS).map a ≫
      ((schemeSpaceFunctor B S hS).map k ≫ eqToHom hDY.symm) = T.hom
    rw [← Category.assoc, ← Functor.map_comp, ha,
      schemeSpaceMap_testSiteHom_comp_eqToHom B S hS D hDY T])

/-- `AlgebraicGeometry.Space.ModuleMapSituation.exists_ideal_isZeroAt_iff_le_ker_of_isAffine` with
the affineness of the test scheme removed: there is an ideal `I` of `Γ(Y₀, ⊤)` such that, at every
test scheme, the base change of `u` vanishes exactly when `I` dies in the functions on the test
scheme. -/
theorem exists_ideal_isZeroAt_iff_le_ker
    (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀)
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom)
    (hproj :
      letI : CommRing
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
      letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartSiteAlgebra B S hS D.X V₀ α
      letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
            (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
        Module.compHom _ (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))))
      Module.Projective (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u)) :
    ∃ I : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u),
      ∀ T : D.SchemesOver,
        (D.IsZeroAt (modulePullbackSystem B S hS) T ↔
          I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map
            (testSiteHom B S hS D hDY T)).appTop.hom) := by
  have := hY₀
  obtain ⟨I, hI⟩ := exists_ideal_isZeroAt_iff_le_ker_of_isAffine B S hS D hDY hY₀ V₀ α hα hV₀
    hV₀term hproj
  have hI' : ∀ {U : BigFppfOver B S hS} (k : U ⟶ Y₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      (D.IsZeroAt (modulePullbackSystem B S hS) (siteTest B S hS D hDY k) ↔
        I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom) := fun k hk =>
    (hI (siteTest B S hS D hDY k) hk).trans (by rw [testSiteHom_siteTest]; exact Iff.rfl)
  refine ⟨I, fun T => ⟨fun hz => ?_, fun hle => ?_⟩⟩
  · obtain ⟨ι, A, gcov, hAaff, hcov⟩ :=
      BigFppfOver.exists_affine_cover_le_ker_appTop_iff B S hS T.left
    exact (hcov Y₀ (testSiteHom B S hS D hDY T) I).mpr fun i =>
      (hI' _ (hAaff i)).mp (D.isZeroAt_of_hom (modulePullbackSystem B S hS)
        (siteTestHomMk B S hS D hDY T (gcov i)) hz)
  · obtain ⟨ψ, hψ⟩ := exists_comp_eq_specQuotientSiteHom B S hS Y₀ I
      (testSiteHom B S hS D hDY T) hle
    have hzZ := (hI' (specQuotientSiteHom B S hS Y₀ I)
      (inferInstanceAs
        (IsAffine (Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) ⧸ I)))))).mpr
      (ker_appTop_specQuotientSiteHom B S hS Y₀ I).ge
    exact D.isZeroAt_of_hom (modulePullbackSystem B S hS)
      (siteTestHomMkOfFactor B S hS D hDY T (specQuotientSiteHom B S hS Y₀ I) ψ hψ) hzZ

/-! ### The vanishing locus is a closed subspace -/

/-- If a closed subspace `Z` of the base represents the vanishing condition at every test scheme,
then the vanishing subfunctor of the base is a closed subspace. -/
theorem isClosedSubspace_zeroSubfunctor_of_forall_isZeroAt_iff
    (D : ModuleMapSituation.{u, u} B S hS) (Z : Subfunctor D.Y.1)
    (h : ∀ T : D.SchemesOver, D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      ∃ k : yoneda.obj T.left ⟶ Z.toFunctor, k ≫ Z.ι = T.hom.hom)
    (hZ : IsClosedSubspace B S hS Z) :
    IsClosedSubspace B S hS D.zeroSubfunctor := by
  rwa [zeroSubfunctor_eq_of_forall_isZeroAt_iff D Z h]

/-- Let `D` be a situation of Stacks 083F whose target is the algebraic space of an affine object
`Y₀` of the big fppf category over `S`, let `V₀` be an affine chart of its source space through
which every morphism from a representable presheaf factors, and suppose the sections of `𝒢` over
`V₀` are projective over `Γ(Y₀, ⊤)`.  Then the vanishing subfunctor of the base is a closed
subspace. -/
@[sga "3 VIII 6.4" "special case"]
theorem isClosedSubspace_zeroSubfunctor_of_projective
    (D : ModuleMapSituation.{u, u} B S hS) {Y₀ : BigFppfOver B S hS}
    (hDY : D.Y = schemeSpace Y₀)
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (V₀ : SmallEtale B S hS D.X.1) (α : V₀.1.left ⟶ Y₀)
    (hα : (V₀.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀.1.left))
    (hV₀term : ∀ (c : BigFppfOver B S hS) (i : yoneda.obj c ⟶ D.X.1),
      ∃ h : c ⟶ V₀.1.left, i = yoneda.map h ≫ V₀.1.hom)
    (hproj :
      letI : CommRing
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartRing_commRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
          (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))
      letI : Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))) :=
        chartSiteAlgebra B S hS D.X V₀ α
      letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
            (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
            (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u) :=
        Module.compHom _ (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartRing B S hS (chartSpace B S hS D.X V₀).1 (chartSpace B S hS D.X V₀).2
            (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀))))
      Module.Projective (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        ((((etaleModulePullback B S hS (chartToSpace B S hS D.X V₀)
          (isEtale_chartToSpace B S hS D.X V₀)).obj D.G).val.obj
          (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS D.X.1).obj V₀)))) : Type u)) :
    IsClosedSubspace B S hS D.zeroSubfunctor := by
  have := hY₀
  obtain ⟨I, hI⟩ := exists_ideal_isZeroAt_iff_le_ker B S hS D hDY hY₀ V₀ α hα hV₀ hV₀term hproj
  clear hproj hV₀term hα hV₀ α V₀
  revert hDY
  obtain ⟨X, Y, f, F, G, qF, qG, u⟩ := D
  dsimp only
  rintro rfl hI
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (specQuotientSiteHom B S hS Y₀ I)) :=
    inferInstance
  have : Mono (specQuotientSiteHom B S hS Y₀ I) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono
  have : Mono (yoneda.map (specQuotientSiteHom B S hS Y₀ I)) := inferInstance
  have hforall : ∀ T : (ModuleMapSituation.mk X (schemeSpace Y₀) f F G qF qG u).SchemesOver,
      (ModuleMapSituation.mk X (schemeSpace Y₀) f F G qF qG u).IsZeroAt
          (modulePullbackSystem B S hS) T ↔
        ∃ k : yoneda.obj T.left ⟶
          (Subfunctor.range (yoneda.map (specQuotientSiteHom B S hS Y₀ I))).toFunctor,
          k ≫ (Subfunctor.range (yoneda.map (specQuotientSiteHom B S hS Y₀ I))).ι =
            T.hom.hom := by
    intro T
    have hts : yoneda.map (testSiteHom B S hS _ rfl T) = T.hom.hom :=
      (yoneda_map_testSiteHom B S hS _ rfl T).trans (Category.comp_id _)
    refine (hI T).trans (Iff.trans ?_
      (exists_comp_range_yoneda_map_iff B S hS (specQuotientSiteHom B S hS Y₀ I)
        T.left T.hom.hom).symm)
    refine ⟨fun hle => ?_, fun hex => ?_⟩
    · obtain ⟨χ, hχ⟩ := exists_comp_eq_specQuotientSiteHom B S hS Y₀ I
        (testSiteHom B S hS _ rfl T) hle
      exact ⟨χ, by rw [← Functor.map_comp, hχ, hts]⟩
    · obtain ⟨χ, hχ⟩ := hex
      refine le_ker_appTop_of_comp_eq_specQuotientSiteHom B S hS Y₀ I
        (testSiteHom B S hS _ rfl T) χ (yoneda.map_injective ?_)
      rwa [Functor.map_comp, hts]
  exact isClosedSubspace_zeroSubfunctor_of_forall_isZeroAt_iff B S hS _ _ hforall
    (isClosedSubspace_range_yoneda_map B S hS (specQuotientSiteHom B S hS Y₀ I) inferInstance)

/-! ### The affine chart predicate -/

/-- `AlgebraicGeometry.Space.ModuleMapSituation.AffineChartZeroLocusClosed` holds for every big
fppf site. -/
theorem affineChartZeroLocusClosed : AffineChartZeroLocusClosed B S hS := by
  intro D V W hV hW hDY g hF hG α _hgflat _hGft _hGflat hcomm hproj
  refine isClosedSubspace_zeroSubfunctor_of_projective B S hS
    (D.pullbackSituation g hF hG) hDY hV (idEtaleChart B S hS W) α ?_ hW ?_ ?_
  · have h : g.hom ≫ D.f.hom ≫ (eqToHom hDY).hom = yoneda.map α :=
      congrArg (fun m : schemeSpace W ⟶ schemeSpace V => m.hom) hcomm
    simp only [Category.assoc]
    exact h
  · intro c i
    exact ⟨yoneda.preimage (show yoneda.obj c ⟶ yoneda.obj W from i),
      (Functor.map_preimage yoneda (show yoneda.obj c ⟶ yoneda.obj W from i)).symm.trans
        (Category.comp_id _).symm⟩
  · exact projective_sections_of_projective_restrictToChartScheme B S hS
      (D.pullbackSituation g hF hG).X (D.pullbackSituation g hF hG).G
      (idEtaleChart B S hS W) V α hproj

end ModuleMapSituation

end Space

end AlgebraicGeometry

end
