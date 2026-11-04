module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULiftSelfIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonSurjective
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.TwistSumExt
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexKInjectiveRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.Topology.Sheaves.Modules.FiniteLocallyFreePresentation

/-!
# Beilinson's equivalence for projective space

Let `A` be a ring, `X = P^n_A = Proj A[T₀, …, Tₙ]`, `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` and
`R = Hom_{Comp^dg(𝒪_X)}(P, P)` the endomorphism differential graded algebra of `P` placed in
degree zero. The derived tensor product `- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` is an equivalence of
triangulated categories sending `R` to `P`.

The derived tensor product is valued in the standard model of the derived category of
`RingedSite.TensorModO (site A n)`; it is compared with the default model of `D(X.Modules)`
through `modelEquivalence`.

## Main definitions

* `Stacks.AlgebraicGeometry.Beilinson.site`: `X` as the ringed site of its opens.
* `Stacks.AlgebraicGeometry.Beilinson.generator`: `P` placed in degree zero.
* `Stacks.AlgebraicGeometry.Beilinson.endAlgebra`: the differential graded algebra `R`.
* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGenerator`: the functor
  `- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)`.
* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGeneratorEquivalence`: an equivalence
  `D(R) ≌ D_QCoh(𝒪_X)` whose functor is `- ⊗_R^𝐋 P`.
* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGeneratorObjRegularIso`: `- ⊗_R^𝐋 P` sends `R` to
  `P`.

## Main results

* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGenerator_bijective_map_regular`: the derived
  tensor product with `P` is bijective on `Hom_{D(R)}(R, R[m])` for every `m`.
* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGenerator_isTriangulated`: `- ⊗_R^𝐋 P` is exact.
* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGenerator_isEquivalence`: `- ⊗_R^𝐋 P` is an
  equivalence of categories.

## References

* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Stacks.AlgebraicGeometry.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `X = P^n_A` as the ringed site of its opens. -/
abbrev site : RingedSite.{u, u, u} :=
  Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite
    (AlgebraicGeometry.Proj (polyGrading A n))

/-- The twist sum `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`, placed in degree zero. -/
def generator : CochainComplex (RingedSite.ModO.{u, u, u, u} (site A n)) ℤ :=
  (CochainComplex.singleFunctor (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) 0).obj
    (twistSumModule A n)

/-- In the homotopy category, the lift `RingedSite.liftComplex` of `P` is `P` in degree zero. -/
def liftGeneratorIso :
    (HomotopyCategory.quotient (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
        (ComplexShape.up ℤ)).obj
          (RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n)) ≅
      (HomotopyCategory.singleFunctor (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) 0).obj
        (twistSumModule A n) :=
  (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    (RingedSite.liftComplexSelfIso (site A n) (generator A n))

/-- `Hom_{D(𝒪_X)}(P[k], P) = 0` for `k ≠ 0`, in any model of the derived category of
`RingedSite.TensorModO (site A n)`. -/
theorem subsingleton_hom_generator_shift
    (h : HasDerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n)))
    (k : ℤ) (hk : k ≠ 0) :
    Subsingleton
      (((DerivedCategory.singleFunctor (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) 0).obj
        (twistSumModule A n))⟦k⟧ ⟶
      (DerivedCategory.singleFunctor (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) 0).obj
        (twistSumModule A n)) :=
  @Stacks.AlgebraicGeometry.ExampleGenerator.subsingleton_hom_single_twistSumModule_shift
    A _ n h k hk

/-- The derived tensor product with `P` is bijective on `Hom_{D(R)}(R, R[m])` for every `m`. -/
theorem tensorWithGenerator_bijective_map_regular (m : ℤ) :
    Function.Bijective
      (fun f : RingedSite.repRegularDerived.{u, u, u, u, u} (site A n) (generator A n) ⟶
          (RingedSite.repRegularDerived.{u, u, u, u, u} (site A n) (generator A n))⟦m⟧ =>
        (RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ
          (generator A n)).map f) := by
  refine RingedSite.tensorWithComplexDerived_bijective_map_regular_of_bijective.{u, u, u, u, u}
    (site A n) (generator A n) (fun k => ?_) m
  have h1 := subsingleton_hom_generator_shift A n (HasDerivedCategory.standard _) k
  have h2 := @DerivedCategory.bijective_Qh_map_singleFunctor_shift
    (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) _ _ (HasDerivedCategory.standard _)
    (twistSumModule A n) k h1
  exact Functor.bijective_map_of_iso _
    ((CategoryTheory.shiftFunctor _ k).mapIso (liftGeneratorIso A n)).symm
    (liftGeneratorIso A n).symm h2

/-! ### `D_QCoh(𝒪_X)` in the standard model -/

/-- `D_QCoh(𝒪_X)` inside the standard model of the derived category of
`RingedSite.TensorModO (site A n)`. -/
abbrev qcoh : ObjectProperty (@DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    _ _ (HasDerivedCategory.standard _)) :=
  RingedSite.tensorModOQuasicoherentDerived.{u, u, u, u, u} (site A n)

/-- The quasi-coherent `𝒪_X`-modules form a weak Serre subcategory of the ambient category of
`𝒪_X`-modules. -/
theorem isWeakSerre_tensorModOQuasicoherent :
    WeakSerre.IsWeakSerre (RingedSite.tensorModOQuasicoherent.{u, u, u, u, u} (site A n)) :=
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms. -/
theorem qcoh_isClosedUnderIsomorphisms :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (qcoh A n).IsClosedUnderIsomorphisms :=
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_tensorModOQuasicoherent A n)

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory. -/
theorem qcoh_isTriangulated :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (qcoh A n).IsTriangulated :=
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_tensorModOQuasicoherent A n)

/-- `D_QCoh(𝒪_X)` is closed under direct sums. -/
theorem qcoh_prop_of_isColimit :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    ∀ {ι : Type u} (Z : ι → DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n)))
      (c : Cofan Z), IsColimit c → (∀ i, qcoh A n (Z i)) → qcoh A n c.pt := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  intro ι Z c hc hZ
  let : IsGrothendieckAbelian.{u} (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, u, u, u} (site A n).J
      (Stacks.SheafOfModules.Tensor.ringSheaf (site A n).O)
  let := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) ι
  have := qcoh_isClosedUnderIsomorphisms A n
  have hsum : ∀ (Mf : ι → RingedSite.TensorModO.{u, u, u, u, u} (site A n)),
      (∀ i, RingedSite.tensorModOQuasicoherent.{u, u, u, u, u} (site A n) (Mf i)) →
      RingedSite.tensorModOQuasicoherent.{u, u, u, u, u} (site A n) (∐ Mf) := fun Mf hMf =>
    RingedSite.tensorModOQuasicoherent_schemeRingedSite_colimit _ Mf _ (coproductIsCoproduct Mf) hMf
  exact (qcoh A n).prop_of_iso (hc.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    (Stacks.Duality.derivedCategoryB_prop_coproduct
      (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
      (RingedSite.tensorModOQuasicoherent.{u, u, u, u, u} (site A n))
      (isWeakSerre_tensorModOQuasicoherent A n) hsum Z hZ)

/-! ### Comparison with `D_QCoh(𝒪_X)` in its default model -/

/-- The identity of the category of `𝒪_X`-modules, from `RingedSite.TensorModO (site A n)` to
`X.Modules`. -/
def toModules : RingedSite.TensorModO.{u, u, u, u, u} (site A n) ⥤
    (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  𝟭 _

/-- The identity of the category of `𝒪_X`-modules, as an equivalence between the two spellings. -/
def modulesEquivalence : RingedSite.TensorModO.{u, u, u, u, u} (site A n) ≌
    (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  CategoryTheory.Equivalence.refl

/-- The functor of `modulesEquivalence` is additive. -/
instance : (modulesEquivalence A n).functor.Additive := ⟨by intros; rfl⟩

/-- The inverse of `modulesEquivalence` is additive. -/
instance : (modulesEquivalence A n).inverse.Additive := ⟨by intros; rfl⟩

/-- The comparison of the two models of `D(𝒪_X)`: from the standard model of the derived
category of `RingedSite.TensorModO (site A n)` to the default model of `D(X.Modules)`. -/
def modelEquivalence :
    @DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) _ _
        (HasDerivedCategory.standard _) ≌
      DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (modulesEquivalence A n)

/-- The comparison of the two models of `D(𝒪_X)` does not change the cohomology sheaves. -/
def modelEquivalenceHomologyIso (q : ℤ) (K : @DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u}
    (site A n)) _ _ (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (DerivedCategory.homologyFunctor (AlgebraicGeometry.Proj (polyGrading A n)).Modules q).obj
        ((modelEquivalence A n).functor.obj K) ≅
      (DerivedCategory.homologyFunctor (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) q).obj
        K :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  ((modulesEquivalence A n).functor.mapDerivedCategoryHomologyIso q).app K

/-- An object of `D(𝒪_X)` in the standard model lies in `D_QCoh(𝒪_X)` exactly when its
comparison to the default model does. -/
theorem qcoh_iff (K : @DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) _ _
    (HasDerivedCategory.standard _)) :
    DerivedCategoryB.derivedCategoryB (A := (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
        (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)
        ((modelEquivalence A n).functor.obj K) ↔ qcoh A n K := by
  refine forall_congr' fun q => ?_
  rw [← RingedSite.tensorModOQuasicoherent_schemeRingedSite_eq]
  exact (RingedSite.tensorModOQuasicoherent.{u, u, u, u, u} (site A n)).prop_iff_of_iso
    (modelEquivalenceHomologyIso A n q K)

/-- The comparison of the two models of `D(𝒪_X)` restricts to an equivalence of `D_QCoh(𝒪_X)` in
the standard model with `Stacks.Duality.quasiCoherentDerivedCategory`. -/
def qcohModelEquivalence :
    (qcoh A n).FullSubcategory ≌
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  haveI := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (A := (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
    (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)
    (@WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ _ _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass _))
  (modelEquivalence A n).congrFullSubcategory (funext fun K => propext (qcoh_iff A n K))

/-- The comparison of the two models of `D(𝒪_X)` commutes with the shift. -/
instance : (modelEquivalence A n).functor.CommShift ℤ :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  (inferInstance : (modulesEquivalence A n).functor.mapDerivedCategory.CommShift ℤ)

/-- The comparison of the two models of `D(𝒪_X)` is additive. -/
instance : (modelEquivalence A n).functor.Additive :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  (inferInstance : (modulesEquivalence A n).functor.mapDerivedCategory.Additive)

/-! ### The generator in the two models -/

/-- The comparison of the two models carries the lift of `P` in degree zero to
`Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh`. -/
def modelEquivalenceGeneratorIso :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (modelEquivalence A n).functor.obj (DerivedCategory.Q.obj
        (RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n))) ≅
      (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n).obj :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  (modelEquivalence A n).functor.mapIso
      (DerivedCategory.Q.mapIso (RingedSite.liftComplexSelfIso (site A n) (generator A n)) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ
          (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) 0).app (twistSumModule A n)).symm) ≪≫
    ((modulesEquivalence A n).functor.mapDerivedCategorySingleFunctor 0).app (twistSumModule A n) ≪≫
    Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModuleSingleIso A n

/-- The shifts of `P` in the two models. -/
def modelEquivalenceGeneratorShiftIso (m : ℤ) :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (modelEquivalence A n).functor.obj ((DerivedCategory.Q.obj
        (RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n)))⟦m⟧) ≅
      ((Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n).obj)⟦m⟧ :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  ((modelEquivalence A n).functor.commShiftIso m).app _ ≪≫
    (CategoryTheory.shiftFunctor _ m).mapIso (modelEquivalenceGeneratorIso A n)

/-- `D_QCoh(𝒪_X)`, in its default model, is closed under isomorphisms. -/
theorem qcohDefault_isClosedUnderIsomorphisms :
    (DerivedCategoryB.derivedCategoryB (A := (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
      (SheafOfModules.isQuasicoherent
        (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (@WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ _ _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass _))

/-- `P` lies in `D_QCoh(𝒪_X)`. -/
theorem qcoh_generator :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    qcoh A n (DerivedCategory.Q.obj
      (RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n))) := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  have := qcohDefault_isClosedUnderIsomorphisms A n
  exact (qcoh_iff A n _).1 (ObjectProperty.prop_of_iso _ (modelEquivalenceGeneratorIso A n).symm
    (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n).property)

/-- `P` generates `D_QCoh(𝒪_X)` in the standard model: an object of `D_QCoh(𝒪_X)` receiving no
nonzero map from any shift of `P` is zero. -/
theorem isZero_of_qcoh_of_hom_generator_eq_zero :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    ∀ L : DerivedCategory (RingedSite.TensorModO.{u, u, u, u, u} (site A n)), qcoh A n L →
      (∀ (m : ℤ) (f : (DerivedCategory.Q.obj
        (RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n)))⟦m⟧ ⟶ L), f = 0) →
      IsZero L := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  intro L hL h
  let Ψ := modelEquivalence A n
  let L' : Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
    ⟨Ψ.functor.obj L, (qcoh_iff A n L).2 hL⟩
  have hz : IsZero L' := by
    refine Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSumQCoh A n L'
      ?_
    rintro Z g ⟨E, m, e, hE⟩
    rw [ObjectProperty.singleton_iff] at hE
    subst hE
    rw [← cancel_epi e.inv, comp_zero]
    apply (ObjectProperty.fullyFaithfulι _).map_injective
    rw [Functor.map_zero]
    let k := ((ObjectProperty.ι _).commShiftIso m).app
      (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n)
    let eS := modelEquivalenceGeneratorShiftIso A n m
    let g' := (ObjectProperty.ι _).map (e.inv ≫ g)
    have h0 := h m (Ψ.fullyFaithfulFunctor.preimage (eS.hom ≫ k.inv ≫ g'))
    have h1 : eS.hom ≫ k.inv ≫ g' = 0 := by
      rw [← Ψ.fullyFaithfulFunctor.map_preimage (eS.hom ≫ k.inv ≫ g'), h0, Functor.map_zero]
    show g' = 0
    have h2 : g' = (k.hom ≫ eS.inv) ≫ (eS.hom ≫ k.inv ≫ g') := by simp
    rw [h2, h1, comp_zero]
  have hz' : IsZero (Ψ.functor.obj L) := (ObjectProperty.ι _).map_isZero hz
  exact (Ψ.inverse.map_isZero hz').of_iso (Ψ.unitIso.app L)

/-! ### `P` is compact in `D_QCoh(𝒪_X)` -/

/-- `P` is perfect. -/
theorem isPerfect_twistSumQCoh :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (AlgebraicGeometry.Proj (polyGrading A n)).toRingedSpace)
      (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n).obj := by
  let P : ObjectProperty (DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules) :=
    fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (AlgebraicGeometry.Proj (polyGrading A n)).toRingedSpace) K
  let hT : P.IsTriangulated :=
    @Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect _ inferInstance
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e h⟩
  have : HasFiniteBiproducts
      (DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteBiproducts
      (DerivedCategory (Stacks.AlgebraicGeometry.ExampleGenerator.Mods A n)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hC : P.IsClosedUnderFiniteCoproducts :=
    ⟨fun _ _ ↦ ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _ _⟩
  have hi : ∀ i : Fin (n + 1), P (Stacks.AlgebraicGeometry.ExampleGenerator.twist A n (-(i : ℤ))) :=
    fun i => by
      have := Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_twistingSheaf A n
        (-(i : ℤ))
      exact isPerfect_singleFunctor_of_isFiniteLocallyFree
        (AlgebraicGeometry.Proj (polyGrading A n))
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-(i : ℤ)))
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree.{u, u, u} _
          (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-(i : ℤ))) 1))
  exact P.prop_of_iso (biproduct.isoCoproduct
    (fun i : Fin (n + 1) => Stacks.AlgebraicGeometry.ExampleGenerator.twist A n (-(i : ℤ)))).symm
    (P.prop_coproduct hi)

/-- `P` is a compact object of `D_QCoh(𝒪_X)`. -/
theorem isCompactObject_twistSumQCoh :
    IsCompactObject.{u} (Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n) :=
  Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect _ _ (isPerfect_twistSumQCoh A n)

/-- The shifts of `P` are compact relative to `D_QCoh(𝒪_X)`, in the standard model. -/
theorem isRelativelyCompactShifts_generator :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    RingedSite.IsRelativelyCompactShifts.{u, u, u, u, u} (site A n) (generator A n) (qcoh A n) := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  intro A' hA' ι _ Z hZ T j hj
  obtain ⟨A₀, m, e, hA₀⟩ := hA'
  rw [ObjectProperty.singleton_iff] at hA₀
  subst hA₀
  let Ψ := modelEquivalence A n
  have := qcoh_isClosedUnderIsomorphisms A n
  have := qcoh_isTriangulated A n
  have hqA : qcoh A n A' :=
    (qcoh A n).prop_of_iso e.symm ((qcoh A n).le_shift m _ (qcoh_generator A n))
  let C' : Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
    ⟨Ψ.functor.obj A', (qcoh_iff A n A').2 hqA⟩
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (AlgebraicGeometry.Proj (polyGrading A n)).toRingedSpace) C'.obj :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (Ψ.functor.mapIso e ≪≫ modelEquivalenceGeneratorShiftIso A n m).symm
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift (isPerfect_twistSumQCoh A n) m)
  have hC := Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect _ C' hperf
  let Z' : ι →
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
    fun i => ⟨Ψ.functor.obj (Z i), (qcoh_iff A n _).2 (hZ i)⟩
  let T' : Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
    ⟨Ψ.functor.obj T, (qcoh_iff A n _).2 (qcoh_prop_of_isColimit A n Z (Cofan.mk T j) hj hZ)⟩
  let j' : ∀ i, Z' i ⟶ T' := fun i => ObjectProperty.homMk (Ψ.functor.map (j i))
  have hamb : IsColimit (Cofan.mk (Ψ.functor.obj T) fun i => Ψ.functor.map (j i)) :=
    (isColimitMapCoconeCofanMkEquiv Ψ.functor Z j) (isColimitOfPreserves Ψ.functor hj)
  have hc' : IsColimit (Cofan.mk T' j') :=
    isColimitOfReflects (ObjectProperty.ι _)
      ((isColimitMapCoconeCofanMkEquiv (ObjectProperty.ι _) Z' j').symm hamb)
  have := Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory
    (AlgebraicGeometry.Proj (polyGrading A n))
  have h1 := (AlgebraicGeometry.Space.bijective_cofanMap_map_iff_of_fullyFaithful
    (ObjectProperty.ι _) C' j').2 (bijective_cofanMap C' hC j' hc')
  exact (AlgebraicGeometry.Space.bijective_cofanMap_map_iff_of_fullyFaithful Ψ.functor A' j).1 h1

/-! ### Beilinson's equivalence -/

/-- The (noncommutative) differential graded algebra `R = Hom^dg(P, P)`, the endomorphism
differential graded algebra of `P` placed in degree zero. -/
abbrev endAlgebra : DifferentialGradedAlgebra.{0, u} ℤ :=
  (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra

/-- `D(R)`, the derived category of differential graded `R`-modules. -/
abbrev derivedCategoryR : Type _ :=
  DifferentialGradedModule.derivedCategory.{0, u, u} (endAlgebra A n)

/-- The regular module `R`, as an object of `D(R)`. -/
abbrev regular : derivedCategoryR A n :=
  RingedSite.repRegularDerived.{u, u, u, u, u} (site A n) (generator A n)

/-- `- ⊗_R^𝐋 P` takes values in `D_QCoh(𝒪_X)`, read in the default model. -/
theorem tensorWithGenerator_obj_mem (M : derivedCategoryR A n) :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    DerivedCategoryB.derivedCategoryB (A := (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
      (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)
      ((modelEquivalence A n).functor.obj
        ((CategoryTheory.signTwist _).obj
          ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ
            (generator A n)).obj M))) := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  have := qcoh_isClosedUnderIsomorphisms A n
  have := qcoh_isTriangulated A n
  exact (qcoh_iff A n _).2 (RingedSite.prop_tensorWithComplexDerived_obj.{u, u, u, u, u} (site A n)
    (generator A n) (qcoh A n) (qcoh_prop_of_isColimit A n) (qcoh_generator A n) M)

/-- The derived tensor product `- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` for `X = P^n_A`,
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` and `R = Hom^dg(P, P)`, valued in
`Stacks.Duality.quasiCoherentDerivedCategory`. Its commutation with the shift is that of
`- ⊗_R^𝐋 P` twisted by the sign `CategoryTheory.signTwist`. -/
def tensorWithGenerator :
    derivedCategoryR A n ⥤
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  ObjectProperty.lift _
    ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n) ⋙
      CategoryTheory.signTwist _) ⋙ (modelEquivalence A n).functor)
    (tensorWithGenerator_obj_mem A n)

/-- `- ⊗_R^𝐋 P` commutes with the shift. -/
instance : (tensorWithGenerator A n).CommShift ℤ :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  (inferInstance : (ObjectProperty.lift _
    ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n) ⋙
      CategoryTheory.signTwist _) ⋙ (modelEquivalence A n).functor)
    (tensorWithGenerator_obj_mem A n)).CommShift ℤ)

/-- `- ⊗_R^𝐋 P` is exact. -/
theorem tensorWithGenerator_isTriangulated : (tensorWithGenerator A n).IsTriangulated := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  have := RingedSite.tensorWithComplexDerived_signTwist_isTriangulated.{u, u, u, u, u}
    (site A n) (generator A n)
  have : (modelEquivalence A n).functor.IsTriangulated :=
    (inferInstance : (modulesEquivalence A n).functor.mapDerivedCategory.IsTriangulated)
  exact ObjectProperty.isTriangulated_lift _ _ (tensorWithGenerator_obj_mem A n)

/-- An equivalence `D(R) ≌ D_QCoh(𝒪_X)`. -/
def tensorWithGeneratorEquivalence :
    derivedCategoryR A n ≌
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  haveI := qcoh_isClosedUnderIsomorphisms A n
  haveI := qcoh_isTriangulated A n
  (RingedSite.tensorWithComplexDerivedEquivalenceOfExt.{u, u, u, u, u} (site A n) (generator A n)
    (qcoh A n) (qcoh_prop_of_isColimit A n) (qcoh_generator A n)
    (isRelativelyCompactShifts_generator A n) (tensorWithGenerator_bijective_map_regular A n)
    (isZero_of_qcoh_of_hom_generator_eq_zero A n)).trans (qcohModelEquivalence A n)

/-- The functor of that equivalence is `- ⊗_R^𝐋 P`. -/
def tensorWithGeneratorEquivalenceFunctorIso :
    (tensorWithGeneratorEquivalence A n).functor ≅ tensorWithGenerator A n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (Category.comp_id _).trans (Eq.trans (by
    apply ObjectProperty.hom_ext
    exact congrArg (modelEquivalence A n).functor.map
      (CategoryTheory.signTwist_map (C := @DerivedCategory
        (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) _ _ (HasDerivedCategory.standard _))
        ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ
          (generator A n)).map f)).symm) (Category.id_comp _).symm))

/-- `- ⊗_R^𝐋 P` is an equivalence of categories. -/
theorem tensorWithGenerator_isEquivalence : (tensorWithGenerator A n).IsEquivalence :=
  Functor.isEquivalence_of_iso (tensorWithGeneratorEquivalenceFunctorIso A n)

/-- `- ⊗_R^𝐋 P` sends `R` to `P`. -/
def tensorWithGeneratorObjRegularIso :
    (tensorWithGenerator A n).obj (regular A n) ≅
      Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh A n :=
  letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  ObjectProperty.isoMk _ ((modelEquivalence A n).functor.mapIso
    ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).mapIso
      ((DifferentialGradedModule.quasiIsomorphisms
          (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra).Q.mapIso
        ((DifferentialGradedModule.toHomotopyCategory
          (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra).mapIso
            DGCategory.representableSelfIsoRegular)).symm ≪≫
      RingedSite.tensorWithComplexDerivedObjRegularIso.{u, u, u, u, u} (site A n)
        (generator A n)) ≪≫
    modelEquivalenceGeneratorIso A n)

end Stacks.AlgebraicGeometry.Beilinson

end
