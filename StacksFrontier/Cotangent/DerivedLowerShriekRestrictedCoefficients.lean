module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitForgetBoundedAbove
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedChangeOfCoefficients
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek with coefficients, at a restricted module

Let `C` be a small category with the chaotic topology, let `B` be a ring, let `𝒪` be a presheaf
of rings on `C` and let `a : 𝒪 ⟶ B̲` be a map to the constant presheaf of rings. [Stacks, Tag
09CZ] builds from this the exact functor

`Lπ_! : D(𝒪) ⟶ D(B)`,

namely derived extension of scalars `- ⊗^𝐋_𝒪 B̲` followed by the derived colimit on diagrams of
`B`-modules. This file computes it at the `𝒪`-module underlying a `B̲`-module `𝒢`:

`Lπ_!(restrictScalars 𝒢) ≅ Lπ_!^{B̲}(𝒢)`,

where on the right `Lπ_!^{B̲}` is the total left derived functor of the colimit, which is what
[Stacks, Tag 08PS], [Stacks, Tag 08PT] and [Stacks, Tag 08QE] compute.

**This is not formal.** The underived counit `(restrictScalars 𝒢) ⊗_𝒪 B̲ ⟶ 𝒢` is *not* an
isomorphism — for a polynomial augmentation `α : P → B`, which is not surjective, a `B`-module
`M` has `M ⊗_P B ≠ M` — and the derived counit carries `Tor^P_{>0}` in every degree. The
comparison becomes invertible only after the derived colimit, which is the change of
coefficients of [Stacks, Tag 08QJ].

## Main definitions

* `Stacks.ChaoticSite.CoefficientInverted`: the hypothesis of [Stacks, Tag 08RX] on the
  coefficient map, that `L_nπ_!` invert it in every degree.
* `Stacks.ChaoticSite.derivedColimitWithCoefficientsRestrictScalarsIso`: the isomorphism above.

## Main results

* `Stacks.ChaoticSite.isIso_abelianDerivedColimit_map_derivedUnit`: [Stacks, Tag 08QJ] read as
  the invertibility of the derived unit.
* `Stacks.ChaoticSite.isIso_abelianDerivedColimit_map_restrictScalars_derivedCounit`: the
  invertibility of the derived **counit**, which is the direction the Atiyah triangle needs and
  which [Stacks, Tag 08QJ] does not state. The triangle identity of the derived adjunction makes
  `Lπ_!(restrictScalars ε)` a two-sided inverse of `Lπ_!(η)`.
* `Stacks.ChaoticSite.exists_Q_map_eq_of_isKProjective`: every morphism of the derived category
  out of a K-projective complex is `DerivedCategory.Q` of a morphism of complexes.

## Implementation notes

**Why a chain representative is needed.** The module-coefficient comparison
`Stacks.ChaoticSite.isIso_totalDerivedColimit_map_forget_iff` takes a morphism of *complexes*.
The derived counit is not one: its source `ℱ ⊗^𝐋_𝒪 B̲` is no single complex — its homology is
`Tor^P_n(ℱ(P), B)` in every degree — and a morphism of the derived category need not be `Q` of
anything. Both are repaired by resolving: `ext(P^•)` is K-projective, because `extendScalars` is
a left adjoint of the exact `restrictScalars` and so preserves projectives
(`CategoryTheory.Adjunction.map_projective`), and out of a K-projective complex every derived
morphism is `Q` of a chain map.

**Why this module is not `@[expose]`, and why the isomorphism is a `def`.** The proofs here
unfold `Stacks.ChaoticSite.derivedCoefficientExtension` and
`Stacks.CategoryHomology.totalDerivedLeftAdjoint`, whose bodies are not exposed by the modules
that define them; the `import all` directives above make those bodies visible. But an *exported*
declaration may not depend on unfolding a non-exposed definition — Lean rejects it with "this
requires that all definitions that need to be unfolded to prove this theorem must be exposed".
Hence the section is `public noncomputable section` **without** `@[expose]`, which keeps the
dependence local. A `theorem` cannot escape this, theorems being always exported, so the
comparison is stated as a `def` returning the isomorphism rather than as a `theorem` returning
`Nonempty` of it. Changing either decision reintroduces the error.

## References

* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B]
  {O : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ (Functor.const Cᵒᵖ).obj (RingCat.of B))
  (U : CosimplicialObject C)

/-- Abbreviation for the hypothesis of [Stacks, Tag 08RX] on the coefficient map. -/
abbrev CoefficientInverted : Prop :=
  ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
    (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})))

/-- **[Stacks, Tag 08QJ] read as the invertibility of the derived unit.** -/
theorem isIso_abelianDerivedColimit_map_derivedUnit (hU : IsPointResolution U)
    (ha : CoefficientInverted a) (F : PresheafOfModules.{u} O) :
    IsIso ((abelianDerivedColimitOfModules O).map
      ((derivedExtendScalarsAdjunction a).unit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj F)))) :=
  (isIso_derivedColimitTensorComparison_app_iff a _).1
    (isIso_derivedColimitTensorComparison_app_single U a hU ha F)

/-- **The derived counit of the change of coefficients is inverted by derived lower shriek**, at
a `B̲`-module placed in cohomological degree zero. The derived unit is inverted there by
[Stacks, Tag 08QJ], and the triangle identity of the derived adjunction turns that into the
invertibility of the counit. -/
theorem isIso_abelianDerivedColimit_map_restrictScalars_derivedCounit
    (hU : IsPointResolution U) (ha : CoefficientInverted a)
    (G : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :
    IsIso ((abelianDerivedColimitOfModules O).map
      ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory.map
        ((derivedExtendScalarsAdjunction a).counit.app (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
            (ComplexShape.up ℤ) 0).obj G))))) := by
  set Y := DerivedCategory.Q.obj
    ((HomologicalComplex.single
      (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
      (ComplexShape.up ℤ) 0).obj G)
  set R := (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory
  have hcomp := congrArg (abelianDerivedColimitOfModules O).map
    ((derivedExtendScalarsAdjunction a).right_triangle_components (Y := Y))
  rw [Functor.map_comp] at hcomp
  have : IsIso ((abelianDerivedColimitOfModules O).map
      ((derivedExtendScalarsAdjunction a).unit.app (R.obj Y))) := by
    have e : R.obj Y ≅ DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
          ((PresheafOfModules.restrictScalars.{u} a).obj G)) :=
      ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactors.app
          ((HomologicalComplex.single
            (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
            (ComplexShape.up ℤ) 0).obj G)) ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (PresheafOfModules.restrictScalars.{u} a) (ComplexShape.up ℤ) 0).app G)
    rw [isIso_map_app_iff_of_iso _ _ e]
    exact isIso_abelianDerivedColimit_map_derivedUnit a U hU ha _
  have : IsIso ((abelianDerivedColimitOfModules O).map
      ((derivedExtendScalarsAdjunction a).unit.app (R.obj Y)) ≫
    (abelianDerivedColimitOfModules O).map
      (R.map ((derivedExtendScalarsAdjunction a).counit.app Y))) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((abelianDerivedColimitOfModules O).map
      ((derivedExtendScalarsAdjunction a).unit.app (R.obj Y))) _

/-! ### Morphisms out of a K-projective complex -/

section KProjective

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **Every morphism of the derived category out of a K-projective complex is the image of a
morphism of complexes.** Morphisms out of a K-projective complex are the same in the homotopy
category and in the derived category, and the quotient to the homotopy category is full. -/
lemma exists_Q_map_eq_of_isKProjective (P L : CochainComplex A ℤ) [P.IsKProjective]
    (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :
    ∃ f : P ⟶ L, DerivedCategory.Q.map f = g := by
  obtain ⟨m, hm⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app P ≫ g ≫
      (DerivedCategory.quotientCompQhIso A).inv.app L)
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective m
  refine ⟨f, ?_⟩
  have h1 : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app L =
      (DerivedCategory.quotientCompQhIso A).hom.app P ≫ DerivedCategory.Q.map f :=
    (DerivedCategory.quotientCompQhIso A).hom.naturality f
  rw [hf, hm] at h1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h1
  exact ((Iso.cancel_iso_hom_left ((DerivedCategory.quotientCompQhIso A).app P) _ _).1 h1).symm

omit [HasDerivedCategory A] in
/-- An additive functor preserves the bound of a complex bounded above. -/
lemma isStrictlyLE_mapHomologicalComplex {A' : Type*} [Category* A'] [Abelian A']
    (F : A ⥤ A') [F.Additive] (P : CochainComplex A ℤ) (n : ℤ) [P.IsStrictlyLE n] :
    CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P : CochainComplex A' ℤ) n :=
  (CochainComplex.isStrictlyLE_iff
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P : CochainComplex A' ℤ) n).2
      fun i hi => F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P n i hi)

end KProjective


/-! ### Step 2: derived lower shriek with coefficients at a restricted module -/

/-- **The derived counit of the change of coefficients is inverted by derived lower shriek on
`B̲`-modules.** -/
theorem isIso_abelianDerivedColimitOfModules_derivedCounit
    (hU : IsPointResolution U) (ha : CoefficientInverted a)
    (G : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :
    IsIso ((abelianDerivedColimitOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of B))).map
      ((derivedExtendScalarsAdjunction a).counit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single
          (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
          (ComplexShape.up ℤ) 0).obj G)))) :=
  (NatIso.isIso_map_iff (restrictScalarsDerivedColimitIso a) _).1
    (isIso_abelianDerivedColimit_map_restrictScalars_derivedCounit a U hU ha G)

/-- The derived change of coefficients at a K-projective complex is the degreewise one. -/
def derivedExtendScalarsObjIsoOfIsKProjective (P : CochainComplex (PresheafOfModules.{u} O) ℤ)
    [P.IsKProjective] :
    (derivedExtendScalars a).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (extendScalars a)
  have := derivedExtendScalars_isLeftDerivedFunctor a
  Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective (extendScalars a)
    (derivedExtendScalars a) (derivedExtendScalarsCounit a) P

/-- Derived lower shriek with coefficients of Tag 09CZ, at a K-projective complex. -/
def derivedCoefficientExtensionObjIsoOfIsKProjective
    (P : CochainComplex (PresheafOfModules.{u} O) ℤ) [P.IsKProjective] :
    (derivedCoefficientExtension B O a).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((coefficientExtension B O a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  haveI := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (coefficientExtension B O a)
  haveI := Stacks.CategoryHomology.totalDerivedLeftAdjoint_isLeftDerivedFunctor
    (coefficientExtension B O a)
  Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective
    (F := coefficientExtension B O a)
    (LF := Stacks.CategoryHomology.totalDerivedLeftAdjoint (coefficientExtension B O a))
    (α := Stacks.CategoryHomology.totalDerivedLeftAdjointCounit (coefficientExtension B O a)) P


/-- **Step 2 of Tag 09DD: `Lπ_!(ℱ) = Lπ_!^{B̲}(𝒢)` for `ℱ` the `𝒪`-module underlying a
`B̲`-module `𝒢`.** On the left `Lπ_!` is the functor `D(𝒪) ⟶ D(B)` of [Stacks, Tag 09CZ], on the
right it is the total left derived functor of the colimit on diagrams of `B`-modules. -/
def derivedColimitWithCoefficientsRestrictScalarsIso
    (hU : IsPointResolution U) (ha : CoefficientInverted a)
    (G : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :
    (derivedColimitWithCoefficients B O a).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
          ((PresheafOfModules.restrictScalars.{u} a).obj G))) ≅
      (Stacks.CategoryHomology.totalDerivedColimit C (ModuleCat.{u} B)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0).obj ((constantModulePresheafEquivalence B).functor.obj G))) := by
  classical
  let P := (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
      ((PresheafOfModules.restrictScalars.{u} a).obj G)) inferInstance).choose
  haveI := P.projective
  haveI := P.boundedAbove
  haveI := P.quasiIso
  haveI : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex 0
  haveI : CochainComplex.IsStrictlyLE
      (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex :
        CochainComplex (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) ℤ) 0 :=
    isStrictlyLE_mapHomologicalComplex (extendScalars a) P.complex 0
  -- `Y`, and the identification of its restriction with the resolved complex
  have e : (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single
          (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
          (ComplexShape.up ℤ) 0).obj G)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single (PresheafOfModules.{u} O)
        (ComplexShape.up ℤ) 0).obj ((PresheafOfModules.restrictScalars.{u} a).obj G)) :=
    ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactors.app _) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (PresheafOfModules.restrictScalars.{u} a) (ComplexShape.up ℤ) 0).app G)
  haveI : IsIso (DerivedCategory.Q.map P.α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 P.quasiIso
  -- the canonical morphism out of the degreewise coefficient extension of the resolution
  set θ := (derivedExtendScalarsObjIsoOfIsKProjective a P.complex).inv ≫
    (derivedExtendScalars a).map (asIso (DerivedCategory.Q.map P.α) ≪≫ e.symm).hom ≫
      (derivedExtendScalarsAdjunction a).counit.app (DerivedCategory.Q.obj
        ((HomologicalComplex.single
          (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
          (ComplexShape.up ℤ) 0).obj G)) with hθ
  haveI := isIso_abelianDerivedColimitOfModules_derivedCounit a U hU ha G
  haveI hθiso : IsIso ((abelianDerivedColimitOfModules
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))).map θ) := by
    rw [hθ, Functor.map_comp, Functor.map_comp]
    infer_instance
  haveI hprojext : ∀ n, Projective ((((extendScalars a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P.complex).X n) :=
    fun n => (changeOfRingsAdjunction a).map_projective _ (P.projective n)
  haveI : CochainComplex.IsKProjective
      (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex :
        CochainComplex (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) ℤ) :=
    CochainComplex.isKProjective_of_projective _ 0
  let hex := exists_Q_map_eq_of_isKProjective
    (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex)
    ((HomologicalComplex.single
      (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
      (ComplexShape.up ℤ) 0).obj G) θ
  let f₀ := hex.choose
  have hf₀ : DerivedCategory.Q.map f₀ = θ := hex.choose_spec
  -- transport the invertibility to the abelian Moore side and then to module coefficients
  have hpre : IsIso (((DerivedCategory.Q ⋙
      (PresheafOfModules.toPresheaf.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))
        ).mapDerivedCategory) ⋙
      Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u}).map f₀) := by
    change IsIso ((abelianDerivedColimitOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of B))).map
      (DerivedCategory.Q.map f₀))
    rw [hf₀]
    exact hθiso
  have habel := (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (PresheafOfModules.toPresheaf.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B))
      ).mapDerivedCategoryFactors
    (Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u})) f₀).1 hpre
  haveI : CochainComplex.IsStrictlyLE
      ((((constantModulePresheafEquivalence B).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex)) :
        CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) 0 :=
    isStrictlyLE_mapHomologicalComplex (constantModulePresheafEquivalence B).functor _ 0
  haveI : CochainComplex.IsStrictlyLE
      ((((constantModulePresheafEquivalence B).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((HomologicalComplex.single
          (PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
          (ComplexShape.up ℤ) 0).obj G)) : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) 0 :=
    isStrictlyLE_mapHomologicalComplex (constantModulePresheafEquivalence B).functor _ 0
  haveI hmod := (isIso_totalDerivedColimit_map_forget_iff U hU
    (((constantModulePresheafEquivalence B).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map f₀)).2 habel
  -- assemble
  exact ((Stacks.CategoryHomology.totalDerivedColimit C (ModuleCat.{u} B)).mapIso
        ((derivedCoefficientExtension B O a).mapIso
          (asIso (DerivedCategory.Q.map P.α)).symm ≪≫
            derivedCoefficientExtensionObjIsoOfIsKProjective a P.complex)) ≪≫
      asIso ((Stacks.CategoryHomology.totalDerivedColimit C (ModuleCat.{u} B)).map
        (DerivedCategory.Q.map
          (((constantModulePresheafEquivalence B).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).map f₀))) ≪≫
      (Stacks.CategoryHomology.totalDerivedColimit C (ModuleCat.{u} B)).mapIso
        (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (constantModulePresheafEquivalence B).functor (ComplexShape.up ℤ) 0).app G))

end Stacks.ChaoticSite

end
