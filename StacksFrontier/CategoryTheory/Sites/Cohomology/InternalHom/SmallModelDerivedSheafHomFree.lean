module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SmallModelDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Derived internal Hom out of a free module, in degree zero

Let `X` be a ringed site whose underlying category is essentially small, with morphisms and
structure rings in `Type u`. For a type `ι` in `Type u`, the zeroth cohomology sheaf of
`R𝓗om_{𝒪_X}(𝒪_X^{⊕ ι}, 𝒪_X)` is the product `∏_{ι} 𝒪_X` of sheaves of modules:

`H⁰(R𝓗om_{𝒪_X}(𝒪_X^{⊕ ι}[0], 𝒪_X[0])) ≅ ∏_{ι} 𝒪_X`.

Here `R𝓗om` is `AlgebraicGeometry.RingedSite.smallModelDerivedSheafHom`.

## Main results

* `Stacks.Homology.homologyZeroPiIso` — for cochain complexes `K_k` vanishing in degree `-1`, the
  zeroth cohomology of the product `∏_k K_k` is the product of the zeroth cohomologies: in degree
  zero cohomology is a kernel, and kernels commute with products.
* `AlgebraicGeometry.RingedSite.smallModelDerivedSheafHomFreeHomologyIso` — the identification
  above.

## Implementation notes

On the small model the derived internal Hom into an injective resolution `𝒪 → J` placed in
degrees `≥ 0` is the internal Hom complex `𝓗om^•(𝒪^{⊕ ι}[0], J) = ∏_{ι} J`
(`AlgebraicGeometry.RingedSite.isLimitFanHomFree`), and only the degree-zero cohomology of
`∏_{ι} J` is computed: it is `∏_{ι} H⁰(J) = ∏_{ι} 𝒪`, which needs no exactness of products. The
whole cohomology of `∏_{ι} J` is not used and is in general not concentrated in degree zero.

## References

* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u d

namespace Stacks.Homology

section ProductHomology

variable {A : Type*} [Category A] [Abelian A] {ι : Type*} [HasProductsOfShape ι A]

/-- The degree-`n` term of a product of cochain complexes is the product of the degree-`n`
terms, the projections being the degree-`n` components of the projections. -/
def isLimitFanPiX (K : ι → CochainComplex A ℤ) (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ K).X n) fun k => (Pi.π K k).f n) :=
  (Fan.isLimitMapConeEquiv (HomologicalComplex.eval A (ComplexShape.up ℤ) n) _ _)
    (isLimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n) (productIsProduct K))

/-- The cycles in degree zero of a product of cochain complexes are the product of the cycles,
the projections being the maps induced by the projections. -/
def isLimitFanPiCycles (K : ι → CochainComplex A ℤ) :
    IsLimit (Fan.mk ((∏ᶜ K).cycles 0)
      fun k => HomologicalComplex.cyclesMap (Pi.π K k) 0) := by
  have hX0 := isLimitFanPiX K 0
  have hX1 := isLimitFanPiX K 1
  refine Fan.IsLimit.mk _ (fun s => (∏ᶜ K).liftCycles
      (Fan.IsLimit.lift hX0 fun k => s.proj k ≫ (K k).iCycles 0) 1 (by simp) ?_)
    (fun s k => ?_) (fun s m hm => ?_)
  · refine Fan.IsLimit.hom_ext hX1 _ _ fun k => ?_
    have h1 : (Fan.IsLimit.lift hX0 fun k => s.proj k ≫ (K k).iCycles 0) ≫ (Pi.π K k).f 0 =
        s.proj k ≫ (K k).iCycles 0 :=
      Fan.IsLimit.fac hX0 (fun k => s.proj k ≫ (K k).iCycles 0) k
    change (_ ≫ (∏ᶜ K).d 0 1) ≫ (Pi.π K k).f 1 = (0 : s.pt ⟶ (∏ᶜ K).X 1) ≫ (Pi.π K k).f 1
    rw [zero_comp, Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc, h1,
      Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  · change _ ≫ HomologicalComplex.cyclesMap (Pi.π K k) 0 = s.proj k
    rw [← cancel_mono ((K k).iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.liftCycles_i]
    exact Fan.IsLimit.fac hX0 (fun k => s.proj k ≫ (K k).iCycles 0) k
  · rw [← cancel_mono ((∏ᶜ K).iCycles 0), HomologicalComplex.liftCycles_i]
    refine Fan.IsLimit.hom_ext hX0 _ _ fun k => ?_
    have h1 : (Fan.IsLimit.lift hX0 fun k => s.proj k ≫ (K k).iCycles 0) ≫ (Pi.π K k).f 0 =
        s.proj k ≫ (K k).iCycles 0 :=
      Fan.IsLimit.fac hX0 (fun k => s.proj k ≫ (K k).iCycles 0) k
    have hmk : m ≫ HomologicalComplex.cyclesMap (Pi.π K k) 0 = s.proj k := hm k
    change (m ≫ (∏ᶜ K).iCycles 0) ≫ (Pi.π K k).f 0 = _ ≫ (Pi.π K k).f 0
    rw [h1, Category.assoc, ← HomologicalComplex.cyclesMap_i, ← Category.assoc, hmk]

/-- **Cohomology in degree zero commutes with products, for complexes vanishing in degree
`-1`.** In degree zero the cohomology of such a complex is the kernel of its first differential,
and kernels commute with products. -/
def homologyZeroPiIso (K : ι → CochainComplex A ℤ) (hK : ∀ k, IsZero ((K k).X (-1))) :
    (∏ᶜ K).homology 0 ≅ ∏ᶜ fun k => (K k).homology 0 :=
  have hP : IsZero ((∏ᶜ K).X (-1)) := by
    rw [IsZero.iff_id_eq_zero]
    exact Fan.IsLimit.hom_ext (isLimitFanPiX K (-1)) _ _ fun k => (hK k).eq_of_tgt _ _
  ((∏ᶜ K).isoHomologyπ (-1) 0 (by simp) (hP.eq_of_src _ _)).symm ≪≫
    IsLimit.conePointUniqueUpToIso (isLimitFanPiCycles K) (productIsProduct _) ≪≫
    Pi.mapIso fun k => (K k).isoHomologyπ (-1) 0 (by simp) ((hK k).eq_of_src _ _)

end ProductHomology

end Stacks.Homology

namespace AlgebraicGeometry.RingedSite

section Model

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- An injective resolution of the structure sheaf, as a cochain complex in degrees `≥ 0`. -/
abbrev structureSheafInjectiveComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  (injectiveResolution
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).cochainComplex

/-- The internal Hom complex from `𝒪^{⊕ ι}[0]` is the product of `ι` copies of the target. -/
def sheafHomComplexFreeIsoPi (ι : Type u)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (sheafHomComplex Y (freeComplex Y ι) I).obj ≅ ∏ᶜ fun _ : ι => I :=
  IsLimit.conePointUniqueUpToIso
    (isLimitFanCompIso (isLimitFanHomFree Y ι I) fun _ : ι => structureSheafHomIso Y I)
    (productIsProduct fun _ : ι => I)

/-- The zeroth cohomology of an injective resolution of the structure sheaf is the structure
sheaf. -/
def structureSheafInjectiveComplexHomologyIso :
    (structureSheafInjectiveComplex Y).homology 0 ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (asIso (HomologicalComplex.homologyMap
      (injectiveResolution
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).ι' 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

/-- **`H⁰(R𝓗om(𝒪^{⊕ ι}[0], 𝒪[0])) ≅ ∏_{ι} 𝒪`** on a ringed site all of whose universes agree. -/
def derivedSheafHomFreeHomologyIso (ι : Type u) :
    (DerivedCategory.homologyFunctor _ 0).obj (((derivedSheafHomBifunctor Y).obj
        (op (DerivedCategory.Q.obj (freeComplex Y ι)))).obj (derivedStructureSheaf Y)) ≅
      ∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  have : (structureSheafInjectiveComplex Y).IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  have : IsIso (DerivedCategory.Q.map (injectiveResolution
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  (DerivedCategory.homologyFunctor _ 0).mapIso
      (((derivedSheafHomBifunctor Y).obj (op (DerivedCategory.Q.obj (freeComplex Y ι)))).mapIso
          (asIso (DerivedCategory.Q.map (injectiveResolution
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).ι')) ≪≫
        derivedSheafHomComparison Y (freeComplex Y ι) (structureSheafInjectiveComplex Y)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (sheafHomComplexFreeIsoPi Y ι (structureSheafInjectiveComplex Y)) ≪≫
    Stacks.Homology.homologyZeroPiIso (fun _ : ι => structureSheafInjectiveComplex Y)
      (fun _ => CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by decide)) ≪≫
    Pi.mapIso fun _ => structureSheafInjectiveComplexHomologyIso Y

end Model

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] smallModelHasDerivedCategory

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The Comparison Lemma carries the free module `𝒪_X^{⊕ ι}` to the free module of the model. -/
def smallModelModulesEquivFreeIso (ι : Type u) :
    (smallModelModulesEquiv X).functor.obj
        (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ι) ≅
      SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O) ι :=
  PreservesCoproduct.iso (smallModelModulesEquiv X).functor _ ≪≫
    Sigma.mapIso fun _ => smallModelModulesEquivUnitIso X

/-- The functor to the model carries `𝒪_X^{⊕ ι}[0]` to `𝒪_model^{⊕ ι}[0]`. -/
def toSmallModelDerivedFreeIso (ι : Type u) :
    (toSmallModelDerived X).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ι)) ≅
      DerivedCategory.Q.obj (freeComplex (smallModel X) ι) :=
  ((smallModelModulesEquiv X).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (smallModelModulesEquivFreeIso X ι) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

/-- **`H⁰(R𝓗om_{𝒪_X}(𝒪_X^{⊕ ι}[0], 𝒪_X[0])) ≅ ∏_{ι} 𝒪_X`.** -/
def smallModelDerivedSheafHomFreeHomologyIso (ι : Type u) :
    (DerivedCategory.homologyFunctor _ 0).obj (((smallModelDerivedSheafHom X).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ι)))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ≅
      ∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  smallModelDerivedSheafHomHomologyIso X 0 _ _ ≪≫
    (smallModelModulesEquiv X).inverse.mapIso
      ((DerivedCategory.homologyFunctor _ 0).mapIso
          ((((derivedSheafHomBifunctor (smallModel X)).mapIso
              (toSmallModelDerivedFreeIso X ι).op).app _).symm ≪≫
            ((derivedSheafHomBifunctor (smallModel X)).obj _).mapIso
              (toSmallModelDerivedStructureSheafIso X)) ≪≫
        derivedSheafHomFreeHomologyIso (smallModel X) ι) ≪≫
    PreservesProduct.iso (smallModelModulesEquiv X).inverse _ ≪≫
    Pi.mapIso fun _ => ((smallModelModulesEquiv X).unitIso.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm

end AlgebraicGeometry.RingedSite

end
