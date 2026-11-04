module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffineBaseChangeModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveTruncationTower
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOnOpenDerived

/-!
# Derived global sections of the base-change complex on the big affine fppf site

Let `S = Spec A` be an affine scheme and let `M^•` be a complex of `A`-modules. The complex
`F^•` of sheaves of `𝒪`-modules on `(Aff/S)_fppf` with `F^n(U) = M^n ⊗_A Γ(U, 𝒪_U)` carries a
canonical map `M^• ⟶ Γ((Aff/S)_fppf, F^•)`, `m ↦ 1 ⊗ m`; composing it with the universal unit
of a total right derived functor of global sections gives `M^• ⟶ RΓ((Aff/S)_fppf, F^•)`, and
that map is a quasi-isomorphism.

## Main definitions

* `AlgebraicGeometry.BigAffineFppf.baseObject` is the final object `Spec A` of the site and
  `AlgebraicGeometry.BigAffineFppf.globalSections` is evaluation there, with scalars in `A`.
* `AlgebraicGeometry.BigAffineFppf.globalSectionsUnit` is the canonical map
  `M ⟶ Γ((Aff/S)_fppf, F)`, `m ↦ 1 ⊗ m`, and
  `AlgebraicGeometry.BigAffineFppf.globalSectionsUnitComplex` its version on complexes.
* `AlgebraicGeometry.BigAffineFppf.derivedComparison` is the canonical map
  `M^• ⟶ RΓ((Aff/S)_fppf, F^•)` in the derived category of `A`-modules, formed from an
  arbitrary total right derived functor of global sections together with its universal unit.

## Main results

* `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison`: the canonical map
  `M^• ⟶ RΓ((Aff/S)_fppf, F^•)` is a quasi-isomorphism.
* `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison_of_rightAcyclic`: the same
  conclusion for any complex whose terms are acyclic for the forgetful functor to presheaves
  of modules.

## Implementation notes

Derived global sections are not fixed by a choice: the comparison is stated for an arbitrary
total right derived functor `RΓ` of global sections together with its universal unit, which
determines `RΓ` up to unique isomorphism. The underived comparison `M^• ⟶ Γ((Aff/S)_fppf, F^•)`
is an isomorphism because the base object has coordinate ring `A`
(`AlgebraicGeometry.BigAffineFppf.isIso_globalSectionsUnitComplex`), so everything is carried
by the unit, and `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison_iff` records that.

The proof of the acyclicity hypothesis has two halves. On the big fppf site over `Spec A` the
higher cohomology of the associated sheaf of a quasi-coherent module vanishes on an object with
affine total space (`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`); the affine
objects form a dense subsite, so restriction of abelian sheaves along the inclusion is an
equivalence and does not change cohomology over an object. Vanishing cohomology over every
object in turn makes the sheaf acyclic for the forgetful functor, because the right derived
functors of that functor are computed sectionwise and over an object they are controlled by
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`, the comparison of Tag
03FD. The cohomology of the source is read in the morphism universe of the site and that of the
target in the morphism universe of the sheaf category, one universe higher;
`CategoryTheory.Abelian.Ext.chgUniv` carries the vanishing between them.

Sheaves of `𝒪`-modules on this site have their sections one universe below its objects, which
is why the ambient-universe Grothendieck-abelianness statements of the library do not apply and
the essential smallness of the site is used instead.

## References

* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.TruncationTower

-- The sheaves of modules here have their sections in a universe *below* the objects of the
-- site, which the ambient-universe instances of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean` cannot
-- describe; left in place they leave the universe of every statement about them unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace AlgebraicGeometry.BigAffineFppf

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (A : CommRingCat.{u})
  (hS : B.Contains (Spec A))

/-! ### Global sections -/

/-- The base object `Spec A` of `(Aff/Spec A)_fppf`. -/
public def baseObject : BigAffineFppf B (Spec A) hS :=
  ⟨Over.mk (𝟙 (B.obj hS)), inferInstanceAs (IsAffine (Spec A))⟩

/-- The base object is the final object of `(Aff/Spec A)_fppf`, so that sections over it are
the global sections of the site. -/
public def isTerminal_baseObject : IsTerminal (baseObject B A hS) := by
  refine IsTerminal.ofUniqueHom (fun Y => ?_) (fun Y m => ?_)
  · exact InducedCategory.homMk ((Over.mkIdTerminal (X := B.obj hS)).from Y.obj)
  · exact InducedCategory.hom_ext ((Over.mkIdTerminal (X := B.obj hS)).hom_ext m.hom _)

/-- Global sections on `(Aff/Spec A)_fppf`, with scalars in `A`: sections over the final object
`Spec A` of the site, with scalars restricted along `A ≅ Γ(Spec A, 𝒪)`. -/
public def globalSections : SheafOfModules.{u} (structureSheaf B A hS) ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation (structureSheaf B A hS) (op (baseObject B A hS)) ⋙
    ModuleCat.restrictScalars (structureAlgebraMap B A hS (op (baseObject B A hS))).hom

/-- Global sections are additive, so they extend termwise to complexes. -/
public instance globalSections_additive : (globalSections B A hS).Additive where
  map_add := rfl

/-- The canonical map `M ⟶ Γ((Aff/S)_fppf, F)`, which sends `m` to `1 ⊗ m` in
`M ⊗_A Γ(Spec A, 𝒪)`. -/
public def globalSectionsUnitLinear (M : ModuleCat.{u} A) :
    M →ₗ[A] (globalSections B A hS).obj ((baseChangeSheafFunctor B A hS).obj M) where
  toFun m := (1 : (coordinateAlgebra B A hS).obj (op (baseObject B A hS))) ⊗ₜ[A] m
  map_add' m n := TensorProduct.tmul_add _ m n
  map_smul' a m := by
    change (1 : (coordinateAlgebra B A hS).obj (op (baseObject B A hS))) ⊗ₜ[A] (a • m) =
      algebraMap A ((coordinateAlgebra B A hS).obj (op (baseObject B A hS))) a •
        ((1 : (coordinateAlgebra B A hS).obj (op (baseObject B A hS))) ⊗ₜ[A] m)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    exact TensorProduct.tmul_eq_smul_one_tmul _ m

/-- The canonical map `M ⟶ Γ((Aff/S)_fppf, F)` as a map of `A`-modules. -/
public def globalSectionsUnit (M : ModuleCat.{u} A) :
    M ⟶ (globalSections B A hS).obj ((baseChangeSheafFunctor B A hS).obj M) :=
  ConcreteCategory.ofHom (C := ModuleCat.{u} A) (globalSectionsUnitLinear B A hS M)

/-- The canonical map of complexes `M^• ⟶ Γ((Aff/S)_fppf, F^•)`. -/
public def globalSectionsUnitComplex (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    M ⟶ ((globalSections B A hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((baseChangeComplex B A hS).obj M) where
  f n := globalSectionsUnit B A hS (M.X n)
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

private lemma isIso_structureAlgebraMap_baseObject :
    IsIso (structureAlgebraMap B A hS (op (baseObject B A hS))) := by
  show IsIso ((Scheme.ΓSpecIso A).inv ≫ Scheme.Hom.appTop (𝟙 (Spec A)))
  rw [Scheme.Hom.id_appTop, Category.comp_id]
  infer_instance

private lemma bijective_tensor_unit {R S M : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (h : Function.Bijective (algebraMap R S)) :
    Function.Bijective (fun m : M => (1 : S) ⊗ₜ[R] m) := by
  let e : R ≃ₗ[R] S := (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv
  let t := (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr e (LinearEquiv.refl R M))
  convert t.bijective using 1
  ext m
  simp [t, e]

/-- The canonical map `M ⟶ Γ((Aff/S)_fppf, F)` is an isomorphism: the base object has
coordinate ring `A`, so `M ⊗_A Γ(Spec A, 𝒪) = M`. -/
public lemma isIso_globalSectionsUnit (M : ModuleCat.{u} A) :
    IsIso (globalSectionsUnit B A hS M) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  apply bijective_tensor_unit
  have := isIso_structureAlgebraMap_baseObject B A hS
  exact ConcreteCategory.bijective_of_isIso
    (structureAlgebraMap B A hS (op (baseObject B A hS)))

/-- The canonical map of complexes `M^• ⟶ Γ((Aff/S)_fppf, F^•)` is an isomorphism. -/
public lemma isIso_globalSectionsUnitComplex (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (globalSectionsUnitComplex B A hS M) := by
  have (n : ℤ) : IsIso ((globalSectionsUnitComplex B A hS M).f n) :=
    isIso_globalSectionsUnit B A hS (M.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical map of complexes is natural in the complex of `A`-modules. -/
public lemma globalSectionsUnitComplex_naturality
    {M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ N) :
    f ≫ globalSectionsUnitComplex B A hS N =
      globalSectionsUnitComplex B A hS M ≫
        ((globalSections B A hS).mapHomologicalComplex (.up ℤ)).map
          ((baseChangeComplex B A hS).map f) := by
  ext n x
  rfl

universe uC vC uD vD wC wD

/-! ### The categories of sheaves on the big affine fppf site -/

/-- `(Aff/Spec A)_fppf` is essentially small: it is a full subcategory of the schemes over
`Spec A` inside the partial universe of the big site, which is essentially small. -/
public instance affineFppf_essentiallySmall :
    EssentiallySmall.{u} (BigAffineFppf B (Spec A) hS) := by
  have : EssentiallySmall.{u} B.Schemes := essentiallySmall_schemeBelow B.cutoff
  have : EssentiallySmall.{u} (Over (B.obj hS)) :=
    essentiallySmall_of_fully_faithful
      (Over.post (equivSmallModel.{u} B.Schemes).functor)
  exact essentiallySmall_of_fully_faithful
    (AlgebraicGeometry.BigAffineFppf.inclusion B (Spec A) hS)

/-- Abelian sheaves on `(Aff/Spec A)_fppf` admit sheafification, the site being essentially
small. -/
public instance hasSheafify_affineTopology :
    HasSheafify (affineTopology B A hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- Sheafification of abelian sheaves on `(Aff/Spec A)_fppf` inverts exactly the locally
bijective maps, the site being essentially small. -/
public instance wEqualsLocallyBijective_affineTopology :
    (affineTopology B A hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheaves of modules over a sheaf of rings on an essentially small site form a Grothendieck
abelian category: the free modules on the representables of a small model separate, and the
three conditions transfer from presheaves of modules along the sheafification adjunction. -/
private lemma moduleSheaves_grothendieck_of_essentiallySmall
    {C : Type uC} [Category.{u} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  let e := equivSmallModel.{u} C
  let generators := e.inverse ⋙ yoneda ⋙ PresheafOfModules.free R.obj
  have hgenerators : (ObjectProperty.ofObj generators.obj).IsSeparating := by
    intro M N f g h
    apply PresheafOfModules.freeYoneda.isSeparating R.obj f g
    rintro _ ⟨X⟩ φ
    let comparison := (yoneda ⋙ PresheafOfModules.free R.obj).mapIso (e.unitIso.app X)
    have equality := h _ (ObjectProperty.ofObj_apply generators.obj (e.functor.obj X))
      (comparison.inv ≫ φ)
    simpa only [Category.assoc, Iso.cancel_iso_inv_left] using equality
  let _ : HasSeparator (PresheafOfModules.{u} R.obj) :=
    ⟨_, hgenerators.isSeparator_coproduct⟩
  let _ : LocallySmall.{u} (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (locallySmall_congr (Equivalence.congrLeft (equivSmallModel.{u} Cᵒᵖ))).mpr inferInstance
  let _ : LocallySmall.{u} (PresheafOfModules.{u} R.obj) :=
    locallySmall_of_faithful (PresheafOfModules.toPresheaf R.obj)
  let _ : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R.obj) := {
    hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
    ab5OfSize := ⟨fun D _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
      have : PreservesLimit F (colim (J := D) ⋙ PresheafOfModules.toPresheaf R.obj) :=
        preservesLimit_of_natIso _
          (preservesColimitNatIso (PresheafOfModules.toPresheaf R.obj)).symm
      preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R.obj)⟩⟩⟩⟩ }
  exact {
    locallySmall := locallySmall_of_faithful (SheafOfModules.forget R)
    hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
    ab5OfSize := ⟨fun K _ _ ↦
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
    hasSeparator := .of_adjunction
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) }

/-- Sheaves of `𝒪`-modules on `(Aff/Spec A)_fppf` form a Grothendieck abelian category. -/
public lemma affineFppf_modules_grothendieck :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheaf B A hS)) :=
  moduleSheaves_grothendieck_of_essentiallySmall _

/-- Abelian sheaves on `(Aff/Spec A)_fppf` form a Grothendieck abelian category. -/
public lemma affineFppf_abelianSheaves_grothendieck :
    IsGrothendieckAbelian.{u} (Sheaf (affineTopology B A hS) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall (affineTopology B A hS) AddCommGrpCat.{u}

/-! ### The comparison with derived global sections -/

attribute [local instance] HasDerivedCategory.standard

/-- On sections over an object the base change `U ↦ M ⊗_A Γ(U, 𝒪_U)` is extension of scalars
along `A ⟶ Γ(U, 𝒪_U)`. -/
private def baseChangeModuleEvaluationIso (X : (BigAffineFppf B (Spec A) hS)ᵒᵖ) :
    baseChangeModuleFunctor B A hS ⋙
        PresheafOfModules.evaluation
          (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) X ≅
      ModuleCat.extendScalars (R := A) (S := (coordinateRing B A hS).obj X)
        (structureAlgebraMap B A hS X).hom := by
  refine NatIso.ofComponents (fun M ↦ Iso.refl _) fun f ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul r m => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

private lemma baseChangeModuleFunctor_preservesColimitsOfShape
    (J : Type u) [SmallCategory J] :
    PreservesColimitsOfShape J (baseChangeModuleFunctor B A hS) := by
  refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  have := preservesColimitsOfShape_of_natIso (J := J)
    (baseChangeModuleEvaluationIso B A hS X).symm
  exact isColimitOfPreserves (baseChangeModuleFunctor B A hS ⋙
    PresheafOfModules.evaluation
      (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) X) hc

private lemma baseChangeSheafFunctor_preservesColimitsOfShape
    (J : Type u) [SmallCategory J] :
    PreservesColimitsOfShape J (baseChangeSheafFunctor B A hS) := by
  have : PreservesColimitsOfShape J
      (baseChangeSheafFunctor B A hS ⋙ SheafOfModules.forget (structureSheaf B A hS)) :=
    baseChangeModuleFunctor_preservesColimitsOfShape B A hS J
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (baseChangeSheafFunctor B A hS) (SheafOfModules.forget (structureSheaf B A hS))

/-- Global sections on the homotopy category of complexes of `𝒪`-modules, followed by
localization: the functor whose total right derived functor is `RΓ((Aff/S)_fppf, -)`. -/
public abbrev homotopyGlobalSections :
    HomotopyCategory (SheafOfModules.{u} (structureSheaf B A hS)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (globalSections B A hS).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The canonical map `M^• ⟶ RΓ((Aff/S)_fppf, F^•)` in the derived category of `A`-modules:
the base-change unit `M^• ⟶ Γ((Aff/S)_fppf, F^•)` followed by the universal unit of a total
right derived functor of global sections. -/
public def derivedComparison
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q.obj M ⟶ RGamma.obj
      (DerivedCategory.Q.obj ((baseChangeComplex B A hS).obj M)) :=
  DerivedCategory.Q.map (globalSectionsUnitComplex B A hS M) ≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app _ ≫
    DerivedCategory.Qh.map
      (((globalSections B A hS).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((baseChangeComplex B A hS).obj M)) ≫
    unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((baseChangeComplex B A hS).obj M)) ≫
    RGamma.map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheaf B A hS))).hom.app
        ((baseChangeComplex B A hS).obj M))

/-- The canonical map to derived global sections is natural in the complex of `A`-modules. -/
public lemma derivedComparison_naturality
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma)
    {M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ N) :
    DerivedCategory.Q.map f ≫ derivedComparison B A hS RGamma unit N =
      derivedComparison B A hS RGamma unit M ≫
        RGamma.map (DerivedCategory.Q.map ((baseChangeComplex B A hS).map f)) := by
  let L := baseChangeComplex B A hS
  let G := (globalSections B A hS).mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient (SheafOfModules.{u} (structureSheaf B A hS)) (.up ℤ)
  have h₁ := congrArg DerivedCategory.Q.map (globalSectionsUnitComplex_naturality B A hS f)
  simp only [CategoryTheory.Functor.map_comp] at h₁
  have h₂ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.naturality
    (G.map (L.map f))
  have h₃ := congrArg DerivedCategory.Qh.map
    (((globalSections B A hS).mapHomotopyCategoryFactors (.up ℤ)).inv.naturality (L.map f))
  simp only [CategoryTheory.Functor.map_comp] at h₃
  have h₄ := unit.naturality (q.map (L.map f))
  have h₅ := congrArg RGamma.map
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheaf B A hS))).hom.naturality (L.map f))
  simp only [CategoryTheory.Functor.map_comp] at h₅
  dsimp only [CategoryTheory.Functor.comp_map] at h₂ h₃ h₄ h₅
  unfold derivedComparison
  simp only [← Category.assoc]
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]

/-- The canonical map to derived global sections is invertible exactly when the universal unit
of the total right derived functor is invertible at the base-change complex: the underived
comparison `M^• ⟶ Γ((Aff/S)_fppf, F^•)` is already an isomorphism. -/
public lemma isIso_derivedComparison_iff
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (derivedComparison B A hS RGamma unit M) ↔
      IsIso (unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((baseChangeComplex B A hS).obj M))) := by
  have := isIso_globalSectionsUnitComplex B A hS M
  simp only [derivedComparison, isIso_comp_left_iff, isIso_comp_right_iff]

/-- Sections over the base object of a presheaf of `𝒪`-modules, with scalars in `A`; global
sections factor through it along the forgetful functor. -/
private abbrev baseSections : PresheafOfModules.{u}
    (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS)) ⥤ ModuleCat.{u} A :=
  PresheafOfModules.evaluation (Stacks.Sites.structurePresheaf (Spec A) (toOver B A hS))
      (op (baseObject B A hS)) ⋙
    ModuleCat.restrictScalars (structureAlgebraMap B A hS (op (baseObject B A hS))).hom

private instance baseSections_preservesFiniteLimits :
    PreservesFiniteLimits (baseSections B A hS) := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
      (structureAlgebraMap B A hS (op (baseObject B A hS))).hom) :=
    Stacks.Cohomology.ModuleComparison.restrictScalars_preservesFiniteLimits _
  exact comp_preservesFiniteLimits _ _

private instance baseSections_preservesFiniteColimits :
    PreservesFiniteColimits (baseSections B A hS) := by
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u}
      (structureAlgebraMap B A hS (op (baseObject B A hS))).hom) :=
    Stacks.Cohomology.ModuleComparison.restrictScalars_preservesFiniteColimits _
  exact comp_preservesFiniteColimits _ _

private instance baseSections_additive : (baseSections B A hS).Additive :=
  Functor.additive_of_preserves_binary_products _

private instance baseSections_preservesHomology :
    (baseSections B A hS).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-! ### Cohomology over an object under restriction along a continuous functor -/

section Restriction

/-- Maps from the free abelian presheaf on a representable are the sections at that object:
a map is determined by the image of the identity. -/
private def freeEvaluationHomAddEquiv {C : Type uC} [Category.{u} C] (U : C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toFun map := map.app (op U) (FreeAbelianGroup.of (𝟙 U))
  invFun element :=
    { app point := AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift (fun arrow : (point.unop ⟶ U) => F.map arrow.op element))
      naturality source target arrow := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro generator
        change FreeAbelianGroup.lift _
          (FreeAbelianGroup.map _ (FreeAbelianGroup.of generator)) =
            F.map arrow (FreeAbelianGroup.lift _ (FreeAbelianGroup.of generator))
        simp }
  left_inv map := by
    apply NatTrans.ext
    funext point
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro generator
    change (point.unop ⟶ U) at generator
    change FreeAbelianGroup.lift (fun arrow : (point.unop ⟶ U) =>
      F.map arrow.op (map.app (op U) (FreeAbelianGroup.of (𝟙 U))))
      (FreeAbelianGroup.of generator) = map.app point (FreeAbelianGroup.of generator)
    rw [FreeAbelianGroup.lift_apply_of]
    have naturality := (ConcreteCategory.congr_hom (map.naturality generator.op)
      (FreeAbelianGroup.of (𝟙 U))).symm
    change F.map generator.op (map.app (op U) (FreeAbelianGroup.of (𝟙 U))) =
      map.app point (FreeAbelianGroup.map (fun arrow => generator ≫ arrow)
        (FreeAbelianGroup.of (𝟙 U))) at naturality
    simpa [uliftFunctor] using naturality
  right_inv element := by
    change FreeAbelianGroup.lift (fun arrow : (U ⟶ U) => F.map arrow.op element)
      (FreeAbelianGroup.of (𝟙 U)) = element
    simp
  map_add' first second := rfl

variable {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- Maps from the free abelian sheaf on a representable are the sections at that object. -/
private def abelianSectionsEquiv (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃+
      F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ F).trans
    (freeEvaluationHomAddEquiv U F.obj)

private lemma abelianSectionsEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{u}}
    (f : F ⟶ G) (g : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    abelianSectionsEquiv J U G (g ≫ f) =
      f.hom.app (op U) (abelianSectionsEquiv J U F g) := by
  show freeEvaluationHomAddEquiv U G.obj
    (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ G) (g ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- **Cohomology over an object is unchanged by restriction along a continuous functor** whose
restriction functor on abelian sheaves is exact and preserves injective objects: the free
abelian sheaf on the representable at `U` corresponds, under the adjunction, to the free
abelian sheaf on the representable at `f U`. -/
private def cohomologyRestrictionIso
    {D : Type uC} [Category.{u} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{u}] (f : C ⥤ D) [f.IsContinuous J K]
    [(f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsRightAdjoint]
    [PreservesFiniteColimits (f.sheafPushforwardContinuous AddCommGrpCat.{u} J K)]
    [(f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).PreservesInjectiveObjects]
    [HasExt.{max uC u} (Sheaf J AddCommGrpCat.{u})]
    [HasExt.{max uC u} (Sheaf K AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{u})]
    (U : C) (n : ℕ) (F : Sheaf K AddCommGrpCat.{u}) :
    Sheaf.H' F n (f.obj U) ≅
      Sheaf.H' ((f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj F) n U := by
  let R := f.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  let α : R ⋙ preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      preadditiveCoyoneda.obj (op ((presheafToSheaf K AddCommGrpCat.{u}).obj
        (yoneda.obj (f.obj U) ⋙ AddCommGrpCat.free))) :=
    NatIso.ofComponents (fun F ↦ ((abelianSectionsEquiv J U (R.obj F)).trans
      (abelianSectionsEquiv K (f.obj U) F).symm).toAddCommGrpIso) (by
      intro F G g
      ext x
      change ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ R.obj F) at x
      apply (abelianSectionsEquiv K (f.obj U) G).injective
      change abelianSectionsEquiv K (f.obj U) G
        ((abelianSectionsEquiv K (f.obj U) G).symm
          (abelianSectionsEquiv J U (R.obj G) (x ≫ R.map g))) =
        abelianSectionsEquiv K (f.obj U) G
          ((abelianSectionsEquiv K (f.obj U) F).symm
            (abelianSectionsEquiv J U (R.obj F) x) ≫ g)
      have h1 : abelianSectionsEquiv J U (R.obj G) (x ≫ R.map g) =
          (R.map g).hom.app (op U) (abelianSectionsEquiv J U (R.obj F) x) :=
        abelianSectionsEquiv_naturality J U (R.map g) x
      have h2 : abelianSectionsEquiv K (f.obj U) G
          ((abelianSectionsEquiv K (f.obj U) F).symm
            (abelianSectionsEquiv J U (R.obj F) x) ≫ g) =
          g.hom.app (op (f.obj U)) (abelianSectionsEquiv J U (R.obj F) x) :=
        (abelianSectionsEquiv_naturality K (f.obj U) g _).trans
          (congrArg _ ((abelianSectionsEquiv K (f.obj U) F).apply_symm_apply _))
      exact ((abelianSectionsEquiv K (f.obj U) G).apply_symm_apply _).trans
        (h1.trans h2.symm))
  exact (Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp R α n).app F

end Restriction

/-! ### Vanishing of the higher cohomology of the base-change sheaf -/

section Vanishing

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite

/-- An abelian category with enough injectives has `Ext`-groups in its own universe of
morphisms, being locally small in that universe. -/
private lemma hasExt_morphismUniverse (E : Type uC) [Category.{vC} E] [Abelian E]
    [EnoughInjectives E] : HasExt.{vC} E :=
  have : LocallySmall.{vC} E := CategoryTheory.locallySmall_self E
  hasExt_of_enoughInjectives E

/-- Moving a vanishing statement for cohomology over an object from the morphism universe of
the site into the morphism universe of the sheaf category, by `Abelian.Ext.chgUniv`. -/
private lemma isZero_cohomology_chgUniv {E : Type uC} [Category.{u} E]
    (K : GrothendieckTopology E) [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    [HasExt.{max uC u} (Sheaf K AddCommGrpCat.{u})]
    (G : Sheaf K AddCommGrpCat.{u}) (n : ℕ) (V : E)
    (h : IsZero (Sheaf.H'.{u, u, uC} G n V)) :
    IsZero (Sheaf.H'.{max uC u, u, uC} G n V) := by
  let X := (presheafToSheaf K AddCommGrpCat.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free)
  have hsmall : Subsingleton (Abelian.Ext.{u} X G n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (h : IsZero ((Abelian.extFunctorObj.{u} X n).obj G))
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ?_
  show Subsingleton (Abelian.Ext.{max uC u} X G n)
  exact ⟨fun x y ↦ (Abelian.Ext.chgUniv.{max uC u, u} (X := X) (Y := G) (n := n)).symm.injective
    (hsmall.elim _ _)⟩

/-- The topology of the big fppf site localized at `Spec A`, in the spelling of the Čech
machinery for a localized big site. -/
private abbrev bigOverTopology : GrothendieckTopology (BigFppfOver B (Spec A) hS) :=
  BigFppfOver.topology B (Spec A) hS

/-- The big fppf site localized at `Spec A` is essentially small. -/
private instance bigFppfOver_essentiallySmall :
    EssentiallySmall.{u} (BigFppfOver B (Spec A) hS) := by
  have : EssentiallySmall.{u} B.Schemes := essentiallySmall_schemeBelow B.cutoff
  exact essentiallySmall_of_fully_faithful
    (Over.post (equivSmallModel.{u} B.Schemes).functor)

/-- Abelian sheaves on the big fppf site localized at `Spec A` admit sheafification. -/
private instance hasSheafify_bigOverTopology :
    HasSheafify (bigOverTopology B A hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ AddCommGrpCat.{u}

/-- Sheafification of abelian sheaves on the big fppf site localized at `Spec A` inverts
exactly the locally bijective maps. -/
private instance wEqualsLocallyBijective_bigOverTopology :
    (bigOverTopology B A hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Abelian sheaves on the big fppf site localized at `Spec A` have enough injectives. -/
private instance enoughInjectives_bigOverTopology :
    EnoughInjectives (Sheaf (bigOverTopology B A hS) AddCommGrpCat.{u}) :=
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite _

/-- `Ext`-groups of abelian sheaves on the big fppf site localized at `Spec A`, in the morphism
universe of the site. -/
private lemma hasExtLow_bigOverTopology :
    HasExt.{u} (Sheaf (bigOverTopology B A hS) AddCommGrpCat.{u}) :=
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite _

/-- Abelian sheaves on `(Aff/Spec A)_fppf` have enough injectives. -/
private instance enoughInjectives_affineTopology :
    EnoughInjectives (Sheaf (affineTopology B A hS) AddCommGrpCat.{u}) :=
  have := affineFppf_abelianSheaves_grothendieck B A hS
  IsGrothendieckAbelian.enoughInjectives

/-- Restriction to the affine objects does not change cohomology over an affine object: the
inclusion is a dense subsite, so restriction of abelian sheaves is an equivalence. -/
private lemma isZero_cohomology_restriction
    [HasExt.{u + 1} (Sheaf (affineTopology B A hS) AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf (bigOverTopology B A hS) AddCommGrpCat.{u})]
    (G : Sheaf (bigOverTopology B A hS) AddCommGrpCat.{u})
    (U : BigAffineFppf B (Spec A) hS) (n : ℕ)
    (h : IsZero (Sheaf.H'.{u + 1} G n
      ((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec A) hS).obj U))) :
    IsZero (Sheaf.H'.{u + 1}
      (((AlgebraicGeometry.BigAffineFppf.inclusion B (Spec A) hS).sheafPushforwardContinuous
        AddCommGrpCat.{u} (affineTopology B A hS) (bigOverTopology B A hS)).obj G) n U) := by
  let i := AlgebraicGeometry.BigAffineFppf.inclusion B (Spec A) hS
  have : ∀ V, HasLimitsOfShape (StructuredArrow V i.op) AddCommGrpCat.{u} := fun _ ↦
    hasLimitsOfShape_of_essentiallySmall _ _
  let R := i.sheafPushforwardContinuous AddCommGrpCat.{u} (affineTopology B A hS)
    (bigOverTopology B A hS)
  have : R.IsEquivalence := inferInstance
  have : PreservesFiniteColimits R := ⟨fun _ _ _ ↦ inferInstance⟩
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      R.asEquivalence.symm.toAdjunction
  exact IsZero.of_iso h
    (cohomologyRestrictionIso (affineTopology B A hS) (bigOverTopology B A hS) i U n G).symm

/-- **The higher cohomology of the base-change sheaf vanishes on every object of
`(Aff/Spec A)_fppf`.** On the big fppf site over `Spec A` this is the affine acyclicity of the
associated sheaf of a quasi-coherent module, and the affine objects form a dense subsite, along
which cohomology over an object does not change. -/
private lemma isZero_baseChangeSheaf_cohomology
    [HasExt.{u + 1} (Sheaf (affineTopology B A hS) AddCommGrpCat.{u})]
    (N : ModuleCat.{u} A) (U : BigAffineFppf B (Spec A) hS) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf (structureSheaf B A hS)).obj
      ((baseChangeSheafFunctor B A hS).obj N)) n U) := by
  let i := AlgebraicGeometry.BigAffineFppf.inclusion B (Spec A) hS
  have hcont : (Over.post B.inclusion : BigFppfOver B (Spec A) hS ⥤ Over (Spec A)).IsContinuous
      (bigOverTopology B A hS) (Scheme.fpqcTopology.{u}.over (Spec A)) :=
    AlgebraicGeometry.isContinuous_overToSlice_fpqc CoveringTopology.fppf B (Spec A) hS
  let G := ((Over.post B.inclusion : BigFppfOver B (Spec A) hS ⥤ Over (Spec A)
      ).sheafPushforwardContinuous AddCommGrpCat.{u} (bigOverTopology B A hS)
      (Scheme.fpqcTopology.{u}.over (Spec A))).obj
    (AlgebraicGeometry.fpqcOverAssociatedSheaf (Spec A) (tilde N))
  have hU : i.obj U ∈ AlgebraicGeometry.overAffineObjects CoveringTopology.fppf B
      (Spec A) hS := U.property
  have hlow := hasExtLow_bigOverTopology B A hS
  have hzu : IsZero (Sheaf.H'.{u, u, u + 1} G n (i.obj U)) :=
    AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine (Spec A) (tilde N)
      CoveringTopology.fppf B hS (i.obj U) hU n hn
  have hhigh := hasExt_morphismUniverse (Sheaf (bigOverTopology B A hS) AddCommGrpCat.{u})
  have hz : IsZero (Sheaf.H'.{u + 1, u, u + 1} G n (i.obj U)) :=
    isZero_cohomology_chgUniv (bigOverTopology B A hS) G n (i.obj U) hzu
  have hz' := isZero_cohomology_restriction B A hS G U n hz
  have e : (SheafOfModules.toSheaf (structureSheaf B A hS)).obj
      ((baseChangeSheafFunctor B A hS).obj N) ≅
      (i.sheafPushforwardContinuous AddCommGrpCat.{u} (affineTopology B A hS)
        (bigOverTopology B A hS)).obj G :=
    (fullyFaithfulSheafToPresheaf (affineTopology B A hS) AddCommGrpCat.{u}).preimageIso
      (baseChangePresheafIso B A hS N)
  exact IsZero.of_iso hz'
    (((Sheaf.cohomologyPresheafFunctor (affineTopology B A hS) n).mapIso e).app (op U))

end Vanishing

/-! ### Acyclicity of the forgetful functor -/

section ForgetAcyclic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Vanishing cohomology over every object makes a sheaf of modules acyclic for the
forgetful functor.** The right derived functors of the forgetful functor are computed
sectionwise, because evaluation of presheaves of modules is exact, and over an object they are
controlled by the cohomology of the underlying abelian sheaf (the comparison of Tag 03FD). -/
private lemma rightAcyclic_forget_of_isZero_cohomology
    {C : Type uC} [Category.{u} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{max uC u} (Sheaf J AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max uC u} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{max uC u} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{max uC u} (PresheafOfModules.{u} R.obj)]
    (F : SheafOfModules.{u} R)
    (hF : ∀ (U : C) (n : ℕ),
      IsZero (Sheaf.H'.{max uC u} ((SheafOfModules.toSheaf R).obj F) (n + 1) U)) :
    (SheafOfModules.forget R).rightAcyclic F := by
  rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n + 1 := ⟨p - 1, by omega⟩
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.forget R) (PresheafOfModules.evaluation R.obj U) (n + 1) F
  have hsub : Subsingleton
      (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U).rightDerived
        (n + 1)).obj F) :=
    Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation J R F U.unop n
      (hF U.unop n)
  have hsub' : Subsingleton
      ((((SheafOfModules.forget R).rightDerived (n + 1)).obj F).obj U) :=
    ⟨fun _ _ ↦ (ConcreteCategory.bijective_of_isIso e.hom).injective (Subsingleton.elim _ _)⟩
  ext x
  exact Subsingleton.elim _ _

end ForgetAcyclic

section Acyclic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The category of sheaves of modules over the structure sheaf `structureSheaf B A hS` is a
Grothendieck abelian category. -/
local instance : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheaf B A hS)) :=
  affineFppf_modules_grothendieck B A hS

/-- **The canonical map to derived global sections is a quasi-isomorphism, given termwise
acyclicity.** If each `N ⊗_A Γ(-, 𝒪)` has no higher cohomology for the forgetful functor, then
`M^• ⟶ RΓ((Aff/S)_fppf, F^•)` is invertible: the truncations of `F^•` have acyclic terms, so the
tower of their injective resolutions is carried to a quasi-isomorphism and its limit is a
K-injective resolution of `F^•` on which the universal unit is invertible. -/
public lemma isIso_derivedComparison_of_rightAcyclic
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS)) (.up ℤ)))
    (hacyclic : ∀ N : ModuleCat.{u} A,
      (SheafOfModules.forget (structureSheaf B A hS)).rightAcyclic
        ((baseChangeSheafFunctor B A hS).obj N))
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (derivedComparison B A hS RGamma unit M) := by
  have : HasExactLimitsOfShape (Discrete ℕ)
      (PresheafOfModules.{u} (structureSheaf B A hS).obj) :=
    presheafModules_hasExactCountableProducts (structureSheaf B A hS).obj
  let G := SheafOfModules.forget.{u} (structureSheaf B A hS)
  let L := baseChangeSheafFunctor B A hS
  have : PreservesColimitsOfSize.{u, u} L :=
    ⟨fun {J} _ ↦ baseChangeSheafFunctor_preservesColimitsOfShape B A hS J⟩
  have : PreservesColimitsOfSize.{0, 0} L := preservesColimitsOfSize_shrink L
  have : PreservesLimitsOfSize.{0, 0} G := ⟨fun {_} _ ↦ inferInstance⟩
  have : G.rightAcyclic.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (NatTrans.isIso_app_iff_of_iso
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _))
      ((HomotopyCategory.Plus.singleFunctor _ 0).mapIso e)).1 h⟩
  obtain ⟨I, f, hI, hf, hGf⟩ := exists_quasiIso_isKInjective_map_quasiIso G
    (fun f hf ↦ quasiIso_of_forget_map_quasiIso (structureSheaf B A hS) f hf)
    ((baseChangeComplex B A hS).obj M)
    (property_truncGE_map L G.rightAcyclic hacyclic M)
  have : QuasiIso (((globalSections B A hS).mapHomologicalComplex (.up ℤ)).map f) := by
    show QuasiIso (((baseSections B A hS).mapHomologicalComplex (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map f))
    exact @HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _
      ((G.mapHomologicalComplex (.up ℤ)).map f) (baseSections B A hS)
      (baseSections_additive B A hS) (baseSections_preservesHomology B A hS) _ _ _ _ hGf
  rw [isIso_derivedComparison_iff]
  exact isIso_derivedUnit_of_quasiIso_map (globalSections B A hS)
    (fun K ↦ ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance,
      inferInstance⟩)
    RGamma unit f hI

end Acyclic

/-! ### The comparison is a quasi-isomorphism -/

section Main

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks 0H0U.** For a complex `M^•` of `A`-modules the canonical map
`M^• ⟶ RΓ((Aff/S)_fppf, F^•)` is a quasi-isomorphism, where `F^•` is the complex of sheaves of
`𝒪`-modules `U ↦ M^• ⊗_A Γ(U, 𝒪_U)` on the big affine fppf site of `S = Spec A`. -/
@[stacks 0H0U "the canonical map to derived global sections is a quasi-isomorphism"]
public theorem isIso_derivedComparison
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
        (ComplexShape.up ℤ)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (derivedComparison B A hS RGamma unit M) := by
  have := affineFppf_modules_grothendieck B A hS
  have := affineFppf_abelianSheaves_grothendieck B A hS
  have hJ := hasExt_morphismUniverse (Sheaf (affineTopology B A hS) AddCommGrpCat.{u})
  have hM : HasExt.{u + 1} (SheafOfModules.{u} (structureSheaf B A hS)) :=
    hasExt_morphismUniverse (SheafOfModules.{u} (structureSheaf B A hS))
  exact isIso_derivedComparison_of_rightAcyclic B A hS RGamma unit hRGamma
    (fun N ↦ rightAcyclic_forget_of_isZero_cohomology (affineTopology B A hS)
      (structureSheaf B A hS) ((baseChangeSheafFunctor B A hS).obj N)
      (fun U n ↦ isZero_baseChangeSheaf_cohomology B A hS N U (n + 1) (Nat.succ_pos n))) M

end Main

end AlgebraicGeometry.BigAffineFppf

end
