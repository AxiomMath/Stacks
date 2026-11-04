module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Monoidal.ExternalAdjunctionMate
public import StacksFrontier.CategoryTheory.Monoidal.ExternalAdjunctionMateNaturality
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExternalTensorProductComparison
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExternalTensorProductAdditive
public import StacksFrontier.Homology.ConstMapDerivedCategoryMonoidal
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Homology.MapHomologicalComplexBraided
public import StacksFrontier.Homology.RestrictionMapHomologicalComplexKFlat
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Homology.Devissage.CompactGenerationOfDiagramsAnyModel
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitPreservesColimits
public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorTensorCommShift
public import StacksFrontier.Homology.ConstMapDerivedCategoryLaxMonoidalCommShift
public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorCoproducts
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.RegularModuleIsSeparating
public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorTriangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical comparison of the derived product formula on a product of chaotic sites

Let `C₁` and `C₂` be small categories with the chaotic topology, `R` a commutative ring, and
`g_i` the inverse images along the two projections of `C₁ × C₂`, so that `g_i^{-1}` is
restriction of diagrams of `R`-modules and is exact.  Derived lower shriek on each of the three
sites is `Stacks.CategoryHomology.totalDerivedColimit`, the total left derived functor of the
colimit (Stacks 08PF, 08Q6), left adjoint to the derived constant diagram
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction`).  This file builds the canonical
morphism

`L(π₁ × π₂)_!(g₁^{-1}K₁ ⊗^L_{R̲} g₂^{-1}K₂) ⟶ Lπ_{1,!}K₁ ⊗^L_R Lπ_{2,!}K₂`

of Stacks 08QB, as the two-variable mate
`CategoryTheory.Adjunction.externalMate` of the two identifications `g_i^{-1} ∘ π_i^{-1} =
π^{-1}` of the inverse images of the point, taken for the three derived adjunctions and for the
monoidal structure `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` of the derived
constant diagram.  It is the derived counterpart of
`Stacks.CategoryHomology.colimExternalTensorComparison`, which is the same mate for the
underived adjunction between the colimit and the constant diagram.

## Main definitions

* `Stacks.CategoryHomology.derivedConstCompProjFstIso` and
  `Stacks.CategoryHomology.derivedConstCompProjSndIso`: the derived form of the identifications
  `g_i^{-1} ∘ π_i^{-1} = π^{-1}`, which hold on the nose at the level of diagrams
  (`Stacks.CategoryHomology.const_comp_projFstInverseImage`).
* `Stacks.CategoryHomology.derivedExternalTensorComparison`: the canonical morphism of
  Stacks 08QB.
* `Stacks.CategoryHomology.derivedExternalTensorComparisonNatTrans`: the same morphism as a
  morphism of bifunctors on the product of the two derived categories, natural in both
  complexes.
* `Stacks.CategoryHomology.totalDerivedColimitSingleFreeYonedaIso`: derived lower shriek of a
  free diagram with projective coefficients, placed in degree zero, is the coefficient module
  placed in degree zero.
* `Stacks.CategoryHomology.derivedExternalTensorSingleFreeYonedaIso`: the derived external
  tensor product of two generators is the free diagram on the pair of objects with the tensor
  product of the coefficients.
* `Stacks.CategoryHomology.derivedExternalTensorComparisonSourceIso` and
  `Stacks.CategoryHomology.derivedExternalTensorComparisonTargetIso`: at a pair of generators
  both the source and the target of the comparison are `P ⊗_R Q` placed in degree zero, and
  `Stacks.CategoryHomology.derivedExternalTensorGeneratorIso` is the resulting isomorphism
  between them.

## Main results

* `CategoryTheory.Adjunction.externalMate_naturality`, proved in
  `StacksFrontier/CategoryTheory/Monoidal/ExternalAdjunctionMateNaturality.lean`, is what makes the
  comparison natural in both variables.
* `Stacks.CategoryHomology.commShift_derivedConstCompProjFstIso` and
  `Stacks.CategoryHomology.commShift_derivedConstCompProjSndIso`: **the two derived
  identifications are compatible with the shift**, which is what a dévissage of the comparison
  along the compact generators asks of them.
* `Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q` and
  `Stacks.CategoryHomology.derivedConstCompProjSndIso_hom_app_Q`: **the two derived
  identifications, at the image of a cochain complex, are the canonical factorizations of the
  three descents involved** -- which is what a chase through the comparison below the
  localization functor meets.
* `Stacks.CategoryHomology.kFlat_single_freeYoneda`: **a free diagram with flat coefficients,
  placed in degree zero, is a K-flat complex of diagrams** -- so at the generators of the
  dévissage the derived tensor product of diagrams is computed by the ordinary one.
* `Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateFstSource` and
  `Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateFstTarget`: **the two
  functors the dévissage of the comparison in the first variable compares preserve direct
  sums**, which with their shift compatibility and exactness is the whole of what
  `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` asks of them.  The
  factors are the restriction functors, which are exact and preserve direct sums pointwise, the
  two derived lower shrieks, which are left adjoints, and `- ⊗^L L` on each of the two derived
  categories, which is
  `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorRight`.
* `Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateSndSource` and
  `Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateSndTarget`: **the same
  for the dévissage in the second variable**, where the fixed factor sits on the left and
  `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft`
  replaces its mirror.
* `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_snd`: **the inner
  dévissage**, at a fixed first complex, from the generators of the second variable to every
  second complex.
* `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_fst`: **the outer
  dévissage**, with the second complex arbitrary, from the generators of the first variable to
  every first complex.
* `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators` and
  `Stacks.CategoryHomology.isIso_derivedExternalTensorComparisonNatTrans_of_generators`: **the two
  dévissages chained**, reducing Stacks 08QB -- as a morphism and as a morphism of bifunctors --
  to the invertibility of the comparison at a pair of free diagrams with projective coefficients
  placed in degree zero.  That generator case is a hypothesis of both statements here; it is
  `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_freeYoneda`.

## Implementation notes

The three derived tensor products are
`CochainComplex.KFlatMonoidal.derivedMonoidal`.  Over the coefficient ring the hypothesis it
needs is discharged by Stacks 06Y4
(`CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso`); over the three diagram
category of the product site it is the statement `hres` that every cochain complex of diagrams
receives a quasi-isomorphism from a K-flat one, which is Stacks 06YS for the chaotic site and
is the same input that `StacksFrontier.Homology.ConstMapDerivedCategoryMonoidal` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/EilenbergZilber.lean` take; without it
the derived tensor product of diagrams does not exist and the comparison cannot be written.

Tag 08QB asserts that `Stacks.CategoryHomology.derivedExternalTensorComparison` is
*invertible*.  This file reduces that to a pair of generators; the generator case, and with it
the tag (`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison`), is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedExternalTensorProductFormula`,
where `hres` is discharged by `Stacks.CategoryHomology.exists_kFlat_quasiIso_diagrams`.

`HasDerivedCategory.standard` is made a local instance at a raised priority, because
`Stacks.CategoryHomology.totalDerivedColimit` and its adjunction are stated at that model and
`StacksFrontier.Homology.DerivedCategory.LocallySmall` supplies a competing instance for
`ModuleCat.{u} R` one universe lower, which instance search otherwise prefers.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

namespace Stacks.CategoryHomology

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CochainComplex.symmetricCategory

universe u

/-! ### K-flatness of the generators -/

section Generators

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

/-- **The sections of a free diagram with flat coefficients are flat.**  The value of
`CategoryTheory.Presheaf.freeYoneda X P` at `W` is a coproduct of copies of `P`, hence a direct
sum of copies of it, and a direct sum of flat modules is flat. -/
instance flat_freeYoneda_obj (X : C) (P : ModuleCat.{u} R) [Module.Flat R P] (W : Cᵒᵖ) :
    Module.Flat R ((Presheaf.freeYoneda X P).obj W) := by
  classical
  exact Module.Flat.of_linearEquiv
    (ModuleCat.coprodIsoDirectSum (fun _ : (yoneda.obj X).obj W => P)).toLinearEquiv

/-- **A free diagram with flat coefficients, placed in degree zero, is a K-flat complex of
diagrams.**

K-flatness of a complex of diagrams is a pointwise condition
(`CochainComplex.KFlatBifunctor.kFlat_of_forall_evaluation`), the evaluation of a complex
concentrated in one degree is concentrated in that degree
(`HomologicalComplex.singleMapHomologicalComplex`), and a flat module placed in degree zero is
K-flat (`CochainComplex.DerivedTensor.kFlat_single_of_flat`).  The sections of a free diagram on
flat coefficients are flat by `Stacks.CategoryHomology.flat_freeYoneda_obj`.

This is what makes the derived tensor product of two generators of the dévissage of Stacks 08QB
computed by their ordinary tensor product. -/
theorem kFlat_single_freeYoneda (X : C) (P : ModuleCat.{u} R) [Module.Flat R P] :
    KFlat (curriedTensor (Cᵒᵖ ⥤ ModuleCat.{u} R))
      ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (Presheaf.freeYoneda X P)) :=
  CochainComplex.KFlatBifunctor.kFlat_of_forall_evaluation _ fun W =>
    CochainComplex.KFlatBifunctor.KFlat.of_iso _
      (CochainComplex.DerivedTensor.kFlat_single_of_flat ((Presheaf.freeYoneda X P).obj W))
      ((HomologicalComplex.singleMapHomologicalComplex
        ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj W) (ComplexShape.up ℤ) 0).app
        (Presheaf.freeYoneda X P)).symm

/-- **A projective module is flat**, read across `ModuleCat`'s carrier.  This is what makes the
flatness the derived tensor product asks of the generators of the dévissage free: the dévissage
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` supplies *projective*
coefficients, and at module coefficients projective implies flat. -/
@[ega "0 6.1.2"]
theorem flat_of_projective (P : ModuleCat.{u} R) [Projective P] : Module.Flat R P :=
  have : Module.Projective R P := ModuleCat.projective_of_module_projective P
  Module.Flat.of_projective

/-- **The tensor product of two projective modules is projective**, across the carrier of the
monoidal structure of `ModuleCat`: the underlying module of `P ⊗ Q` is `TensorProduct R P Q`, for
which `Module.Projective.tensorProduct` is Mathlib's statement.  This is what makes the free
diagram on `(U, V)` with coefficients `P ⊗_R Q` -- the value of the external tensor product of
two generators -- projective again, so that derived lower shriek has no higher terms there. -/
theorem projective_tensorObj (P Q : ModuleCat.{u} R) [Projective P] [Projective Q] :
    Projective (P ⊗ Q : ModuleCat.{u} R) :=
  have : Module.Projective R P := ModuleCat.projective_of_module_projective P
  have : Module.Projective R Q := ModuleCat.projective_of_module_projective Q
  have : Module.Projective R (TensorProduct R P Q) := Module.Projective.tensorProduct
  ModuleCat.projective_of_categoryTheory_projective (P ⊗ Q)

/-- **Derived lower shriek of a generator is its coefficient module, placed in degree zero.**
A free diagram on projective coefficients is projective
(`Stacks.CategoryHomology.freeYonedaProjective`), so derived lower shriek has no higher terms
there (`Stacks.CategoryHomology.totalDerivedColimitObjSingleIso`), and the colimit of a free
diagram on a representable is its coefficient module
(`Stacks.CategoryHomology.colimFreeYonedaIso`). -/
def totalDerivedColimitSingleFreeYonedaIso (U : C) (P : ModuleCat.{u} R) [Projective P] :
    (totalDerivedColimit C (ModuleCat.{u} R)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            (Presheaf.freeYoneda U P))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj P) :=
  haveI := freeYonedaProjective U P
  totalDerivedColimitObjSingleIso C (ModuleCat.{u} R) (Presheaf.freeYoneda U P) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).mapIso
        (colimFreeYonedaIso U P))

end Generators

section Statement

variable (C₁ : Type u) [SmallCategory C₁] (C₂ : Type u) [SmallCategory C₂]
  (R : Type u) [CommRing R]

/-- Restriction along the first projection preserves finite limits, being computed pointwise. -/
@[sga "4 I 5.0" "special case"]
instance projFstInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (projFstInverseImage C₁ C₂ R) :=
  inferInstanceAs (PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C₁ C₂).op))

/-- Restriction along the first projection preserves finite colimits. -/
instance projFstInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (projFstInverseImage C₁ C₂ R) :=
  inferInstanceAs (PreservesFiniteColimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C₁ C₂).op))

/-- Restriction along the second projection preserves finite limits. -/
@[sga "4 I 5.0" "special case"]
instance projSndInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (projSndInverseImage C₁ C₂ R) :=
  inferInstanceAs (PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C₁ C₂).op))

/-- Restriction along the second projection preserves finite colimits. -/
instance projSndInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (projSndInverseImage C₁ C₂ R) :=
  inferInstanceAs (PreservesFiniteColimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C₁ C₂).op))

/-- **The derived identification `g₁^{-1} ∘ π_1^{-1} = π^{-1}`.** -/
def derivedConstCompProjFstIso :
    (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory ⋙
        (projFstInverseImage C₁ C₂ R).mapDerivedCategory ≅
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _) (projFstInverseImage C₁ C₂ R)).symm

/-- **The derived identification along the first projection is compatible with the shift.** -/
instance commShift_derivedConstCompProjFstIso :
    NatTrans.CommShift (derivedConstCompProjFstIso C₁ C₂ R).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _) (projFstInverseImage C₁ C₂ R)).inv ℤ)

/-- **The derived identification along the first projection, at the image of a cochain complex.**
At the class of `K` it is the derived restriction of the canonical factorization for the constant
diagram on `C₁`, then the factorization for the restriction, then the factorization for the
constant diagram on the product site read backwards.  It is
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q`, the composite of the
constant diagram on `C₁` with the restriction being the constant diagram on the product site by
`rfl` (`Stacks.CategoryHomology.const_comp_projFstInverseImage`). -/
@[reassoc]
theorem derivedConstCompProjFstIso_hom_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedConstCompProjFstIso C₁ C₂ R).hom.app (DerivedCategory.Q.obj K) =
      (projFstInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app K) ≫
        (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
            (((Functor.const C₁ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ :
            ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.inv.app K :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q _ _ K

/-- **The derived identification `g₂^{-1} ∘ π_2^{-1} = π^{-1}`.** -/
def derivedConstCompProjSndIso :
    (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory ⋙
        (projSndInverseImage C₁ C₂ R).mapDerivedCategory ≅
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _) (projSndInverseImage C₁ C₂ R)).symm

/-- **The derived identification along the second projection is compatible with the shift.** -/
instance commShift_derivedConstCompProjSndIso :
    NatTrans.CommShift (derivedConstCompProjSndIso C₁ C₂ R).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _) (projSndInverseImage C₁ C₂ R)).inv ℤ)

/-- **The derived identification along the second projection, at the image of a cochain complex.**
The companion of `Stacks.CategoryHomology.derivedConstCompProjFstIso_hom_app_Q`: at the class of
`K` it is `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q`, the composite
of the constant diagram on `C₂` with the restriction being the constant diagram on the product
site by `rfl` (`Stacks.CategoryHomology.const_comp_projSndInverseImage`). -/
@[reassoc]
theorem derivedConstCompProjSndIso_hom_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedConstCompProjSndIso C₁ C₂ R).hom.app (DerivedCategory.Q.obj K) =
      (projSndInverseImage C₁ C₂ R).mapDerivedCategory.map
          ((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.hom.app K) ≫
        (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.hom.app
            (((Functor.const C₂ᵒᵖ : ModuleCat.{u} R ⥤ _).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          (Functor.const (C₁ × C₂)ᵒᵖ :
            ModuleCat.{u} R ⥤ _).mapDerivedCategoryFactors.inv.app K :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q _ _ K

variable
    (hres : ∀ G : CochainComplex ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ,
      ∃ (P : CochainComplex ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (f : P ⟶ G),
        KFlat (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) P ∧ QuasiIso f)

/-- The canonical comparison of the derived product formula. -/
def derivedExternalTensorComparison
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).obj
        (MonoidalCategoryStruct.tensorObj
          ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj K₁)
          ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj K₂)) ⟶
      MonoidalCategoryStruct.tensorObj
        ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj K₁)
        ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj K₂) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  letI := Functor.constMapDerivedCategoryMonoidal
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).externalMate
    (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R))
    (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R))
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory
    (derivedConstCompProjFstIso C₁ C₂ R).hom
    (derivedConstCompProjSndIso C₁ C₂ R).hom K₁ K₂

/-- **The comparison of the derived product formula is natural in both variables.**  The
morphisms `Stacks.CategoryHomology.derivedExternalTensorComparison` assemble into a morphism of
bifunctors on `DerivedCategory (C₁ᵒᵖ ⥤ R-Mod) × DerivedCategory (C₂ᵒᵖ ⥤ R-Mod)`, from
`(K₁, K₂) ↦ L(π₁ × π₂)_!(g₁^{-1}K₁ ⊗^L g₂^{-1}K₂)` to `(K₁, K₂) ↦ Lπ_{1,!}K₁ ⊗^L Lπ_{2,!}K₂`.
Naturality is `CategoryTheory.Adjunction.externalMate_naturality`. -/
def derivedExternalTensorComparisonNatTrans :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.prod
          (projSndInverseImage C₁ C₂ R).mapDerivedCategory) ⋙
        Functor.uncurry.obj
          (curriedTensor (DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))) ⋙
        totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R) ⟶
      ((totalDerivedColimit C₁ (ModuleCat.{u} R)).prod
            (totalDerivedColimit C₂ (ModuleCat.{u} R))) ⋙
        Functor.uncurry.obj (curriedTensor (DerivedCategory (ModuleCat.{u} R))) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  letI := Functor.constMapDerivedCategoryMonoidal
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  { app := fun K => derivedExternalTensorComparison C₁ C₂ R hres K.1 K.2
    naturality := fun K K' f => by
      dsimp only [derivedExternalTensorComparison, Functor.comp_map, Functor.prod_map,
        Functor.uncurry_obj_map, curriedTensor_obj_map, curriedTensor_map_app]
      rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def]
      exact Adjunction.externalMate_naturality _ _ _ _ _ _ _ f.1 f.2 }

/-- **The comparison of the derived product formula, read in the first variable at a fixed second
complex, is compatible with the shift.**

The shift compatibility of a morphism of exact direct-sum-preserving functors out of
`D(C₁ᵒᵖ ⥤ R-Mod)` is what `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel`
asks of it beyond those two properties, so this is the statement that opens the dévissage of
Stacks 08QB along the free diagrams.  Everything else it consumes is available:

* the two derived identifications `g_i^{-1} ∘ π_i^{-1} = π^{-1}` are shift-compatible, by
  `Stacks.CategoryHomology.commShift_derivedConstCompProjFstIso`;
* the three adjunctions are shift-compatible, by
  `CategoryTheory.Adjunction.commShift_of_rightAdjoint`, their right adjoints being degreewise;
* each `K ⊗ -` and `- ⊗ L` on the two derived categories commutes with the shift, by
  `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift` and
  `derivedMonoidal_tensorRight_commShift`, and the action of the tensor product on morphisms is
  compatible with those commutations, by
  `CochainComplex.KFlatMonoidal.derivedMonoidal_tensorCommShift`.

The remaining input, that the tensorator

`π^{-1}K ⊗^L π^{-1}L ⟶ π^{-1}(K ⊗^L L)`

of `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` commutes with the shift in each
variable, is a condition on that monoidal structure and not a consequence of it; it is
`CategoryTheory.constMapDerivedCategoryLaxMonoidalCommShift`. -/
theorem commShift_externalMateNatTransFst_derivedExternalTensor
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    letI := Functor.constMapDerivedCategoryMonoidal
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
    letI := fun K : DerivedCategory (ModuleCat.{u} R) =>
      derivedMonoidal_tensorLeft_commShift (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) K
    letI := fun L : DerivedCategory (ModuleCat.{u} R) =>
      derivedMonoidal_tensorRight_commShift (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) L
    letI := fun K : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
      derivedMonoidal_tensorLeft_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres K
    letI := fun L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
      derivedMonoidal_tensorRight_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres L
    NatTrans.CommShift
      ((totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).externalMateNatTransFst
        (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R))
        (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R))
        (projFstInverseImage C₁ C₂ R).mapDerivedCategory
        (projSndInverseImage C₁ C₂ R).mapDerivedCategory
        (derivedConstCompProjFstIso C₁ C₂ R).hom
        (derivedConstCompProjSndIso C₁ C₂ R).hom K₂) ℤ := by
  let := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := Functor.constMapDerivedCategoryMonoidal
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  let := fun K : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) K
  let := fun L : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) L
  let := fun K : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres K
  let := fun L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres L
  let := derivedMonoidal_tensorCommShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).commShift_of_rightAdjoint ℤ
  let := (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R)).commShift_of_rightAdjoint ℤ
  let := CategoryTheory.constMapDerivedCategoryLaxMonoidalCommShift
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  exact Adjunction.commShift_externalMateNatTransFst' _ _ _ _ _ _ _ ℤ K₂

/-! ### Direct sums -/

/-- Restriction along the first projection preserves direct sums of diagrams, both sides being
computed pointwise. -/
instance projFstInverseImage_preservesColimitsOfShape_discrete (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (projFstInverseImage C₁ C₂ R) :=
  preservesColimitsOfShape_of_evaluation _ _ fun Z => preservesColimitsOfShape_of_natIso
    (Iso.refl ((evaluation C₁ᵒᵖ (ModuleCat.{u} R)).obj (op Z.unop.1)))

/-- Restriction along the second projection preserves direct sums of diagrams. -/
instance projSndInverseImage_preservesColimitsOfShape_discrete (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (projSndInverseImage C₁ C₂ R) :=
  preservesColimitsOfShape_of_evaluation _ _ fun Z => preservesColimitsOfShape_of_natIso
    (Iso.refl ((evaluation C₂ᵒᵖ (ModuleCat.{u} R)).obj (op Z.unop.2)))

/-- **Restriction along the first projection preserves direct sums on the derived categories.**
It is exact and preserves them at the level of diagrams, being computed pointwise, so
`Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory` applies. -/
theorem preservesColimitsOfShape_discrete_projFstInverseImage_mapDerivedCategory (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (projFstInverseImage C₁ C₂ R).mapDerivedCategory :=
  Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J

/-- **Restriction along the second projection preserves direct sums on the derived categories.**
-/
theorem preservesColimitsOfShape_discrete_projSndInverseImage_mapDerivedCategory (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (projSndInverseImage C₁ C₂ R).mapDerivedCategory :=
  Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J

/-- **`- ⊗^L_R L` on `D(R-Mod)` preserves direct sums.**  This is
`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorRight` at
the coefficient ring; the hypotheses it asks of the coefficients are that direct sums exist and
that tensoring preserves them, both of which hold in a module category. -/
theorem preservesColimitsOfShape_discrete_tensorRight_moduleCat (J : Type u)
    (L : DerivedCategory (ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    PreservesColimitsOfShape (Discrete J) (MonoidalCategory.tensorRight L) :=
  preservesColimitsOfShape_discrete_derivedMonoidal_tensorRight (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) J L

/-- **`- ⊗^L L` on the derived category of diagrams on the product site preserves direct
sums.**  The companion of
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_tensorRight_moduleCat`, at the
coefficients the comparison's source lives at.  Tensoring a diagram of modules preserves direct
sums because both are computed pointwise. -/
theorem preservesColimitsOfShape_discrete_tensorRight_diagrams (J : Type u)
    (L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    PreservesColimitsOfShape (Discrete J) (MonoidalCategory.tensorRight L) :=
  preservesColimitsOfShape_discrete_derivedMonoidal_tensorRight _ hres J L

/-- **The source of the first-variable dévissage of Stacks 08QB preserves direct sums.**  It is
`g₁^{-1}`, followed by `- ⊗^L g₂^{-1}K₂` on the product site, followed by `L(π₁ × π₂)_!`; the
first factor is
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_projFstInverseImage_mapDerivedCategory`,
the second is
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_tensorRight_diagrams`, and the third
is a left adjoint. -/
theorem preservesColimitsOfShape_discrete_externalMateFstSource (J : Type u)
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    PreservesColimitsOfShape (Discrete J)
      (((projFstInverseImage C₁ C₂ R).mapDerivedCategory ⋙
          MonoidalCategory.tensorRight ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj K₂)) ⋙
        totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)) := by
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := preservesColimitsOfShape_discrete_projFstInverseImage_mapDerivedCategory C₁ C₂ R J
  let := preservesColimitsOfShape_discrete_tensorRight_diagrams C₁ C₂ R hres J
    ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj K₂)
  infer_instance

/-- **The target of the first-variable dévissage of Stacks 08QB preserves direct sums.**  It is
`Lπ_{1,!}` followed by `- ⊗^L_R Lπ_{2,!}K₂`; the first factor is a left adjoint and the second is
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_tensorRight_moduleCat`. -/
theorem preservesColimitsOfShape_discrete_externalMateFstTarget (J : Type u)
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    PreservesColimitsOfShape (Discrete J)
      (totalDerivedColimit C₁ (ModuleCat.{u} R) ⋙
        MonoidalCategory.tensorRight ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj K₂)) := by
  let := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := preservesColimitsOfShape_discrete_tensorRight_moduleCat R J
    ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj K₂)
  infer_instance

/-- **The source of the second-variable dévissage of Stacks 08QB preserves direct sums.**  It is
`g₂^{-1}`, followed by `g₁^{-1}K₁ ⊗^L -` on the product site, followed by `L(π₁ × π₂)_!`; the
first factor is
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_projSndInverseImage_mapDerivedCategory`,
the second is
`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft`, and
the third is a left adjoint.  The mirror of
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateFstSource`: there the
second complex is arbitrary and the fixed factor sits on the right, here the first complex is
fixed and the factor sits on the left. -/
theorem preservesColimitsOfShape_discrete_externalMateSndSource (J : Type u)
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    PreservesColimitsOfShape (Discrete J)
      (((projSndInverseImage C₁ C₂ R).mapDerivedCategory ⋙
          tensorLeft ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj K₁)) ⋙
        totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)) := by
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := preservesColimitsOfShape_discrete_projSndInverseImage_mapDerivedCategory C₁ C₂ R J
  let := preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft
    ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres J
    ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj K₁)
  infer_instance

/-- **The target of the second-variable dévissage of Stacks 08QB preserves direct sums.**  It is
`Lπ_{2,!}` followed by `Lπ_{1,!}K₁ ⊗^L_R -`; the first factor is a left adjoint and the second is
`CochainComplex.KFlatMonoidal.preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft` at the
coefficient ring.  The mirror of
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateFstTarget`. -/
theorem preservesColimitsOfShape_discrete_externalMateSndTarget (J : Type u)
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R)) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    PreservesColimitsOfShape (Discrete J)
      (totalDerivedColimit C₂ (ModuleCat.{u} R) ⋙
        tensorLeft ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj K₁)) := by
  let := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := preservesColimitsOfShape_discrete_derivedMonoidal_tensorLeft (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) J
    ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj K₁)
  infer_instance

/-! ### The comparison at a pair of generators -/

/-- **The restriction along the first projection of a free diagram with projective coefficients,
placed in degree zero, is a K-flat complex of diagrams on the product site.**  Restriction along
the first projection is `(whiskeringLeft _ _ _).obj π₁ᵒᵖ`, which carries K-flatness by
`CochainComplex.KFlatBifunctor.kFlat_whiskeringLeftMapHomologicalComplex`, and
`HomologicalComplex.singleMapHomologicalComplex` moves the restriction inside the `single`; the
complex it is applied to is K-flat by `Stacks.CategoryHomology.kFlat_single_freeYoneda`, the
coefficients being flat by `Stacks.CategoryHomology.flat_of_projective`. -/
theorem kFlat_single_projFst_freeYoneda (U : C₁) (P : ModuleCat.{u} R) [Projective P] :
    KFlat (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
      ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))) :=
  let := flat_of_projective P
  KFlat.of_iso _
    (kFlat_whiskeringLeftMapHomologicalComplex (CategoryTheory.Prod.fst C₁ C₂).op _
      (kFlat_single_freeYoneda U P))
    ((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
      (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda U P))

/-- **The restriction along the second projection of a free diagram with projective coefficients,
placed in degree zero, is a K-flat complex of diagrams on the product site.**  The companion of
`Stacks.CategoryHomology.kFlat_single_projFst_freeYoneda`. -/
theorem kFlat_single_projSnd_freeYoneda (V : C₂) (Q : ModuleCat.{u} R) [Projective Q] :
    KFlat (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
      ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q))) :=
  let := flat_of_projective Q
  KFlat.of_iso _
    (kFlat_whiskeringLeftMapHomologicalComplex (CategoryTheory.Prod.snd C₁ C₂).op _
      (kFlat_single_freeYoneda V Q))
    ((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
      (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda V Q))

/-- Restriction along the first projection of a diagram placed in degree zero, read on the
derived categories: the derived functor of the restriction factors through the degreewise
restriction (`CategoryTheory.Functor.mapDerivedCategoryFactors`), and the degreewise restriction
of a complex concentrated in one degree is concentrated in that degree
(`HomologicalComplex.singleMapHomologicalComplex`). -/
def projFstDerivedSingleIso (F : C₁ᵒᵖ ⥤ ModuleCat.{u} R) :
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          ((projFstInverseImage C₁ C₂ R).obj F)) :=
  (projFstInverseImage C₁ C₂ R).mapDerivedCategoryFactors.app
      ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj F) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (projFstInverseImage C₁ C₂ R)
        (ComplexShape.up ℤ) 0).app F)

/-- Restriction along the second projection of a diagram placed in degree zero, read on the
derived categories.  The companion of
`Stacks.CategoryHomology.projFstDerivedSingleIso`. -/
def projSndDerivedSingleIso (G : C₂ᵒᵖ ⥤ ModuleCat.{u} R) :
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj G)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          ((projSndInverseImage C₁ C₂ R).obj G)) :=
  (projSndInverseImage C₁ C₂ R).mapDerivedCategoryFactors.app
      ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj G) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (projSndInverseImage C₁ C₂ R)
        (ComplexShape.up ℤ) 0).app G)

/-- **The derived external tensor product of two generators is the free diagram on the pair.**
On the K-flat complexes `g_i^{-1}j_{U!}P` the derived tensor product is the total tensor product
of complexes (`CochainComplex.KFlatMonoidal.derivedTensorIso`), the total complex of two
complexes concentrated in degree zero is concentrated in degree zero
(`HomologicalComplex.mapBifunctorSingleIso`), and there it is the external tensor product of the
two free diagrams, which is the free diagram on `(U, V)` with coefficients `P ⊗_R Q`
(`Stacks.CategoryHomology.externalTensorFreeYonedaIso`).  This is the computation the proof of
Stacks 08QB makes on the generators, read for the derived tensor product. -/
def derivedExternalTensorSingleFreeYonedaIso (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R)
    [Projective P] [Projective Q] :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    MonoidalCategoryStruct.tensorObj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (Presheaf.freeYoneda ((U, V) : C₁ × C₂) (P ⊗ Q))) :=
  letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  derivedTensorIso ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
      (kFlat_single_projFst_freeYoneda C₁ C₂ R U P)
      (kFlat_single_projSnd_freeYoneda C₁ C₂ R V Q) ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapBifunctorSingleIso (curriedTensor ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R))
          ((projFstInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda U P))
          ((projSndInverseImage C₁ C₂ R).obj (Presheaf.freeYoneda V Q)) ≪≫
        (HomologicalComplex.single ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).mapIso
          (externalTensorFreeYonedaIso U V P Q))

/-- **The source of the comparison of Stacks 08QB at a pair of generators is `P ⊗_R Q` placed in
degree zero.**  The two restrictions are computed by
`Stacks.CategoryHomology.projFstDerivedSingleIso` and its companion, their derived tensor product
by `Stacks.CategoryHomology.derivedExternalTensorSingleFreeYonedaIso`, and derived lower shriek
of the resulting free diagram by
`Stacks.CategoryHomology.totalDerivedColimitSingleFreeYonedaIso`, the coefficients `P ⊗_R Q`
being projective by `Stacks.CategoryHomology.projective_tensorObj`. -/
def derivedExternalTensorComparisonSourceIso (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R)
    [Projective P] [Projective Q] :
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).obj
        (MonoidalCategoryStruct.tensorObj
          ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P))))
          ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q))))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (P ⊗ Q)) :=
  letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  haveI := projective_tensorObj P Q
  (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).mapIso
      (tensorIso (projFstDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda U P))
          (projSndDerivedSingleIso C₁ C₂ R (Presheaf.freeYoneda V Q)) ≪≫
        derivedExternalTensorSingleFreeYonedaIso C₁ C₂ R hres U V P Q) ≪≫
    totalDerivedColimitSingleFreeYonedaIso ((U, V) : C₁ × C₂) (P ⊗ Q)

/-- **The target of the comparison of Stacks 08QB at a pair of generators is `P ⊗_R Q` placed in
degree zero.**  Each derived lower shriek is computed by
`Stacks.CategoryHomology.totalDerivedColimitSingleFreeYonedaIso`, and the derived tensor product
of the two results by `CochainComplex.KFlatMonoidal.derivedTensorIso` together with
`HomologicalComplex.mapBifunctorSingleIso`, the two coefficient modules being K-flat in degree
zero by `CochainComplex.DerivedTensor.kFlat_single_of_flat`. -/
def derivedExternalTensorComparisonTargetIso (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R)
    [Projective P] [Projective Q] :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    MonoidalCategoryStruct.tensorObj
        ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda U P))))
        ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q)))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (P ⊗ Q)) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  letI := flat_of_projective P
  letI := flat_of_projective Q
  tensorIso (totalDerivedColimitSingleFreeYonedaIso U P)
      (totalDerivedColimitSingleFreeYonedaIso V Q) ≪≫
    derivedTensorIso (ModuleCat.{u} R)
        (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
        (CochainComplex.DerivedTensor.kFlat_single_of_flat P)
        (CochainComplex.DerivedTensor.kFlat_single_of_flat Q) ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.mapBifunctorSingleIso (curriedTensor (ModuleCat.{u} R)) P Q)

/-- **At a pair of generators the source and the target of the comparison of Stacks 08QB are
isomorphic**, both being `P ⊗_R Q` placed in degree zero: this is
`Stacks.CategoryHomology.derivedExternalTensorComparisonSourceIso` followed by the inverse of
`Stacks.CategoryHomology.derivedExternalTensorComparisonTargetIso`.

This is **not** yet the statement that the comparison
`Stacks.CategoryHomology.derivedExternalTensorComparison` is invertible there.  What is still
owed is the transposition identity of
`CategoryTheory.Adjunction.isIso_externalMate_of_unit_comp_map`, which says that this
isomorphism has the defining property of the two-variable mate; by
`CategoryTheory.Adjunction.eq_externalMate_of_unit_comp_map` that identity is exactly what
would identify the two. -/
def derivedExternalTensorGeneratorIso (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R)
    [Projective P] [Projective Q] :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
    (totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)).obj
        (MonoidalCategoryStruct.tensorObj
          ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda U P))))
          ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
                (Presheaf.freeYoneda V Q))))) ≅
      MonoidalCategoryStruct.tensorObj
        ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda U P))))
        ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q)))) :=
  derivedExternalTensorComparisonSourceIso C₁ C₂ R hres U V P Q ≪≫
    (derivedExternalTensorComparisonTargetIso C₁ C₂ R U V P Q).symm

/-! ### The two dévissages -/

/-- A morphism of exact direct-sum-preserving functors out of `D(Cᵒᵖ ⥤ R-Mod)` is invertible as
soon as it is invertible on the free diagrams with projective coefficients placed in degree zero. -/
private theorem isIso_of_isIso_app_single_freeYoneda {C : Type u} [SmallCategory C]
    {R : Type u} [CommRing R]
    {F G : DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hgen : ∀ (X : C) (P : ModuleCat.{u} R) [Projective P],
      IsIso (τ.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (Presheaf.freeYoneda X P))))) :
    IsIso τ :=
  StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel
    (fun _ : PUnit.{u + 1} ↦ ModuleCat.of R R)
    (fun _ ↦ StacksDraft.Perfect.isCompactObject_regularModule)
    Stacks.ChaoticSite.isSeparating_ofObj_regularModule τ fun X _ =>
      (Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms τ).of_iso
        ((DerivedCategory.singleFunctorIsoCompQ (Cᵒᵖ ⥤ ModuleCat.{u} R) 0).app
          (Presheaf.freeYoneda X (ModuleCat.of R R))).symm
        (hgen X (ModuleCat.of R R))

/-- **The inner dévissage of Stacks 08QB: at a fixed first complex, the comparison is invertible
at every second complex as soon as it is invertible at the generators of the second variable.**

**The generator case is an input here, not a result: it is the binder `_hgen`, and nothing below
proves it.**  What is proved is the reduction.  The comparison, read at the fixed `K₁` as a
morphism of functors of the second variable, is
`CategoryTheory.Adjunction.externalMateNatTransSnd`, and
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` applies to it: its two
functors are exact (`Stacks.CategoryHomology.totalDerivedColimit_isTriangulated`,
`CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_isTriangulated` and the exactness of the
derived restriction functors) and preserve direct sums
(`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateSndSource` and
`…SndTarget`), and the morphism is compatible with the shift by
`CategoryTheory.Adjunction.commShift_externalMateNatTransSnd'`.  The generating family is the
regular module, as in `Stacks.ChaoticSite.isIso_derivedColimitForgetComparison`.

The dévissage tests the morphism at `CategoryTheory.DerivedCategory.singleFunctor`, while `_hgen`
is stated at `DerivedCategory.Q` of `HomologicalComplex.single`; the two are identified by
`CategoryTheory.DerivedCategory.singleFunctorIsoCompQ`, along which the invertibility locus
transports because it is closed under isomorphisms
(`Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms`). -/
theorem isIso_derivedExternalTensorComparison_of_generators_snd
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    ∀ (_hgen : ∀ (V : C₂) (Q : ModuleCat.{u} R) [Projective Q],
        IsIso (derivedExternalTensorComparison C₁ C₂ R hres K₁
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q))))),
      IsIso (derivedExternalTensorComparison C₁ C₂ R hres K₁ K₂) := by
  let := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := Functor.constMapDerivedCategoryMonoidal
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  let := fun K : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) K
  let := fun L : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) L
  let := fun K : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres K
  let := fun L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres L
  let := derivedMonoidal_tensorCommShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).commShift_of_rightAdjoint ℤ
  let := (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R)).commShift_of_rightAdjoint ℤ
  let := CategoryTheory.constMapDerivedCategoryLaxMonoidalCommShift
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  let := fun K : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_isTriangulated ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres K
  let := fun K : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_isTriangulated (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) K
  intro hgen
  let τ := (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).externalMateNatTransSnd
    (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R))
    (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R))
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory
    (derivedConstCompProjFstIso C₁ C₂ R).hom
    (derivedConstCompProjSndIso C₁ C₂ R).hom K₁
  have : NatTrans.CommShift τ ℤ :=
    Adjunction.commShift_externalMateNatTransSnd' _ _ _ _ _ _ _ ℤ K₁
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (((projSndInverseImage C₁ C₂ R).mapDerivedCategory ⋙
          tensorLeft ((projFstInverseImage C₁ C₂ R).mapDerivedCategory.obj K₁)) ⋙
        totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)) := fun J =>
    preservesColimitsOfShape_discrete_externalMateSndSource C₁ C₂ R hres J K₁
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (totalDerivedColimit C₂ (ModuleCat.{u} R) ⋙
        tensorLeft ((totalDerivedColimit C₁ (ModuleCat.{u} R)).obj K₁)) := fun J =>
    preservesColimitsOfShape_discrete_externalMateSndTarget C₁ C₂ R J K₁
  have : IsIso τ := isIso_of_isIso_app_single_freeYoneda τ hgen
  exact NatIso.isIso_app_of_isIso τ K₂

/-- **The outer dévissage of Stacks 08QB: with the second complex arbitrary, the comparison is
invertible at every first complex as soon as it is invertible at the generators of the first
variable.**

**The generator case is an input here, not a result: it is the binder `_hgen`, and nothing below
proves it.**  What is proved is the reduction.  This is the mirror of
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_snd`, run on
`CategoryTheory.Adjunction.externalMateNatTransFst` instead: the shift compatibility is
`Stacks.CategoryHomology.commShift_externalMateNatTransFst_derivedExternalTensor` and the
direct-sum preservation is
`Stacks.CategoryHomology.preservesColimitsOfShape_discrete_externalMateFstSource` and
`…FstTarget`, so that `- ⊗^L L` appears where the inner dévissage has `K ⊗^L -`. -/
theorem isIso_derivedExternalTensorComparison_of_generators_fst
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    ∀ (_hgen : ∀ (U : C₁) (P : ModuleCat.{u} R) [Projective P]
        (M₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)),
        IsIso (derivedExternalTensorComparison C₁ C₂ R hres
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda U P))) M₂)),
      IsIso (derivedExternalTensorComparison C₁ C₂ R hres K₁ K₂) := by
  let := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  let := derivedMonoidal ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres
  let := Functor.constMapDerivedCategoryMonoidal
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) hres
  let := fun K : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) K
  let := fun L : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) L
  let := fun K : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorLeft_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres K
  let := fun L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_commShift ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres L
  let := fun L : DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_isTriangulated ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{u} R) hres L
  let := fun L : DerivedCategory (ModuleCat.{u} R) =>
    derivedMonoidal_tensorRight_isTriangulated (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R) L
  intro hgen
  let τ := (totalDerivedColimitAdjunction (C₁ × C₂) (ModuleCat.{u} R)).externalMateNatTransFst
    (totalDerivedColimitAdjunction C₁ (ModuleCat.{u} R))
    (totalDerivedColimitAdjunction C₂ (ModuleCat.{u} R))
    (projFstInverseImage C₁ C₂ R).mapDerivedCategory
    (projSndInverseImage C₁ C₂ R).mapDerivedCategory
    (derivedConstCompProjFstIso C₁ C₂ R).hom
    (derivedConstCompProjSndIso C₁ C₂ R).hom K₂
  have : NatTrans.CommShift τ ℤ :=
    commShift_externalMateNatTransFst_derivedExternalTensor C₁ C₂ R hres K₂
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (((projFstInverseImage C₁ C₂ R).mapDerivedCategory ⋙
          MonoidalCategory.tensorRight ((projSndInverseImage C₁ C₂ R).mapDerivedCategory.obj K₂)) ⋙
        totalDerivedColimit (C₁ × C₂) (ModuleCat.{u} R)) := fun J =>
    preservesColimitsOfShape_discrete_externalMateFstSource C₁ C₂ R hres J K₂
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (totalDerivedColimit C₁ (ModuleCat.{u} R) ⋙
        MonoidalCategory.tensorRight ((totalDerivedColimit C₂ (ModuleCat.{u} R)).obj K₂)) :=
    fun J => preservesColimitsOfShape_discrete_externalMateFstTarget C₁ C₂ R J K₂
  have : IsIso τ := isIso_of_isIso_app_single_freeYoneda τ fun U P _ => hgen U P K₂
  exact NatIso.isIso_app_of_isIso τ K₁

/-- **The two dévissages of Stacks 08QB chained: the comparison is invertible everywhere as soon
as it is invertible at a pair of generators.**

**The generator case is an input here, not a result: it is the binder `_hgen`, which asks for the
invertibility of the comparison at a pair of free diagrams with projective coefficients placed in
degree zero, and nothing below proves it.**  What is proved is that it suffices.  The inner
dévissage `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_snd`
removes the restriction on the second complex at a fixed first generator, and the outer dévissage
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators_fst` then removes it
on the first.

The generator case is `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_freeYoneda`,
and the two together are `Stacks.CategoryHomology.isIso_derivedExternalTensorComparison`. -/
theorem isIso_derivedExternalTensorComparison_of_generators
    (K₁ : DerivedCategory (C₁ᵒᵖ ⥤ ModuleCat.{u} R))
    (K₂ : DerivedCategory (C₂ᵒᵖ ⥤ ModuleCat.{u} R)) :
    ∀ (_hgen : ∀ (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R) [Projective P] [Projective Q],
        IsIso (derivedExternalTensorComparison C₁ C₂ R hres
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda U P)))
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q))))),
      IsIso (derivedExternalTensorComparison C₁ C₂ R hres K₁ K₂) :=
  fun hgen => isIso_derivedExternalTensorComparison_of_generators_fst C₁ C₂ R hres K₁ K₂
    fun U P _ M₂ => isIso_derivedExternalTensorComparison_of_generators_snd C₁ C₂ R hres _ M₂
      fun V Q _ => hgen U V P Q

/-- **The comparison of Stacks 08QB is an isomorphism of bifunctors as soon as it is invertible at
a pair of generators.**  The morphism of bifunctors is
`Stacks.CategoryHomology.derivedExternalTensorComparisonNatTrans`, and a morphism of functors is
invertible as soon as each of its components is
(`CategoryTheory.NatIso.isIso_of_isIso_app`); the components are
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_of_generators`.

The generator case is the binder `_hgen`; it is
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparison_freeYoneda`, which gives
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparisonNatTrans`. -/
theorem isIso_derivedExternalTensorComparisonNatTrans_of_generators :
    ∀ (_hgen : ∀ (U : C₁) (V : C₂) (P Q : ModuleCat.{u} R) [Projective P] [Projective Q],
        IsIso (derivedExternalTensorComparison C₁ C₂ R hres
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₁ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda U P)))
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (C₂ᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
              (Presheaf.freeYoneda V Q))))),
      IsIso (derivedExternalTensorComparisonNatTrans C₁ C₂ R hres) := by
  intro hgen
  have : ∀ K, IsIso ((derivedExternalTensorComparisonNatTrans C₁ C₂ R hres).app K) := fun K =>
    isIso_derivedExternalTensorComparison_of_generators C₁ C₂ R hres K.1 K.2 hgen
  exact NatIso.isIso_of_isIso_app _

end Statement

end Stacks.CategoryHomology

end
