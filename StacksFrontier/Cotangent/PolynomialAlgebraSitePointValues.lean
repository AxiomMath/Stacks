module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentialsShriek
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The values of `Lπ_!` on `𝒪`, on `B̲` and on the differentials

Let `A → B` be a ring map and let `π`, `𝒪`, `B̲` be as in [Stacks, Tag 08PR]. [Stacks, Tag 08QK]
asserts that in `D(Ab)`

```
Lπ_!(𝒪) = Lπ_!(B̲) = B      and      L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A}).
```

**This file does not prove that tag**; it proves those four identifications at a different and
smaller site, and so carries no `@[stacks 08QK]`. The footnote to the source's section cuts
`C_{B/A}` down to the full subcategory of the augmentations whose set of variables has cardinality
at most a fixed bound, and both `Ab(-)` and `Lπ_!` change when one passes to a full subcategory,
so neither reading implies the other. The tag itself is stated at `CommAlgCat.polynomialSite` in
`StacksFrontier/Cotangent/PolynomialAlgebraSitePointValuesLargeSite.lean`, for all of it except the
last identification `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A})`; see the note on
`CommAlgCat.derivedLowerShriekDifferentialsIso` for what that one still needs.

**Which site, and which `Lπ_!`.** As in
`StacksFrontier/Cotangent/PolynomialAlgebraSiteCotangentComplex.lean` and
`StacksFrontier/Cotangent/PolynomialAlgebraSiteCoefficientChange.lean`, the site is the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the footnote-restricted site `C_{B/A}`, at the
cardinal `CommAlgCat.standardResolutionVarCardinal A B` bounding the standard resolution, and
`Lπ_!` is `Stacks.CategoryHomology.totalDerivedColimit`, the total left derived functor of the
colimit over the index category — which is the `π_!` of [Stacks, Tag 08PF] on a chaotic site.
This is the same functor the [Stacks, Tag 08Q9] and [Stacks, Tag 08QJ] registrations are
about, so the four identifications below are statements about the objects those lemmas compute,
not about fresh copies of them.

All four identifications are here, at that site: `Lπ_!(𝒪) = B`, `Lπ_!(B̲) = B`,
`L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` and `L_{B/A} = Lπ_!(Ω_{𝒪/A})`. The last is the only one that is
not formal: it is [Stacks, Tag 08QJ] at `ℱ = Ω_{𝒪/A}`, and the dévissage behind that tag inverts
the change-of-coefficients unit only at a *projective* presheaf of `𝒪`-modules, while `Ω_{𝒪/A}`
is merely objectwise free. The passage between the two is the source's step
`Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`, carried by
`Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentialsShriek.lean`.

## Main definitions

* `CommAlgCat.abelianDerivedLowerShriek` and `CommAlgCat.derivedLowerShriekSingle`: `Lπ_!` on
  `D(Ab(C_{B/A}))`, and its value at an abelian presheaf placed in cohomological degree zero.
* `CommAlgCat.baseInDerived`: `B`, as an object of `D(Ab)`.

## Main results

* `CommAlgCat.derivedLowerShriekConstantIso`: **`Lπ_!(B̲) = B`** in `D(Ab)`. The augmentation
  `A → B` is a terminal object of the site (`CommAlgCat.isTerminal_smallPolynomialBaseObj`), so
  `π^{-1} = const` has an exact right adjoint and
  `Stacks.ChaoticSite.derivedConstCompColimitIso` — [Stacks, Tag 08Q7] — applies.
* `CommAlgCat.derivedLowerShriekStructureConstantIso` and
  `CommAlgCat.derivedLowerShriekStructureIso`: **`Lπ_!(𝒪) = Lπ_!(B̲) = B`** in `D(Ab)`. The first
  is `CommAlgCat.isIso_totalDerivedColimit_smallPolynomialAugmentation` read as an isomorphism.
* `CommAlgCat.derivedLowerShriekCotangentIso`: **`L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`** in `D(Ab)`.
  The derived form of [Stacks, Tag 08Q9] at abelian coefficients,
  `Stacks.ChaoticSite.AbelianValued.mooreCochainIsoDerivedColimitApp`, computes `Lπ_!` of the
  sheaf by its extended Moore complex on the standard resolution, and
  `CommAlgCat.standardResolutionCotangentMooreComplexIso` identifies that Moore complex with the
  complex of [Stacks, Tag 08PN] — an isomorphism of complexes, which is what lets the degreewise
  statement of [Stacks, Tag 08PU] be upgraded to an isomorphism in `D(Ab)`.
* `CommAlgCat.isIso_shriek_resolutionUnitMap` and
  `CommAlgCat.quasiIso_extendRestrict_differentialsResolution`: the two halves of
  [Stacks, Tag 08QJ] at `Ω_{𝒪/A}`, for a chosen projective resolution `P^• ⟶ Ω_{𝒪/A}[0]` of
  [Stacks, Tag 0646] — `Lπ_!` inverts the change-of-coefficients unit on `P^•` by the dévissage
  of [Stacks, Tag 08RX], and `P^•` stays a resolution after the change of coefficients because
  the sections of `Ω_{𝒪/A}` are free, which is the step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`.
* `CommAlgCat.derivedLowerShriekDifferentialsExtendIso`:
  **`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`** in `D(Ab)`, the comparison of [Stacks, Tag 08QJ]
  with the derived tensor product replaced by the underived one.
* `CommAlgCat.derivedLowerShriekDifferentialsIso`: **`L_{B/A} = Lπ_!(Ω_{𝒪/A})`** in `D(Ab)`, the
  previous isomorphism composed with `CommAlgCat.extendScalarsDifferentialsIso` and the third
  identification of the tag.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08QK](https://stacks.math.columbia.edu/tag/08QK)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The small model of `C_{B/A}` at the cardinal bounding the standard resolution. -/
abbrev standardPolynomialSite : Type u :=
  smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)

/-- `Lπ_! : D(Ab(C_{B/A})) ⥤ D(Ab)`. -/
abbrev abelianDerivedLowerShriek :
    DerivedCategory ((standardPolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  totalDerivedColimit (standardPolynomialSite A B) AddCommGrpCat.{u}

/-- `Lπ_!(ℱ)` for an abelian presheaf `ℱ` placed in cohomological degree zero. -/
abbrev derivedLowerShriekSingle
    (F : (standardPolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    DerivedCategory AddCommGrpCat.{u} :=
  (abelianDerivedLowerShriek A B).obj (DerivedCategory.Q.obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- The abelian group underlying `B`. -/
abbrev abelianOfBase : AddCommGrpCat.{u} :=
  (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (ringOfBase A B)

/-- `B`, as an object of `D(Ab)`. -/
abbrev baseInDerived : DerivedCategory AddCommGrpCat.{u} :=
  DerivedCategory.Q.obj
    ((HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).obj (abelianOfBase A B))

/-- The abelian presheaf underlying `B̲` is the constant presheaf with value `B`. -/
def constantPresheafAbelianIso (κ : Cardinal.{u}) :
    smallPolynomialConstantPresheaf A B κ ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ≅
      (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (abelianOfBase A B) :=
  Functor.constComp _ _ _

/-- The constant diagram on `M[0]`, read in the derived category, is `(π^{-1}M)[0]`. -/
def derivedConstSingleIso (M : AddCommGrpCat.{u}) :
    (Functor.const (standardPolynomialSite A B)ᵒᵖ :
          AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).obj M)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((Functor.const (standardPolynomialSite A B)ᵒᵖ).obj M)) :=
  (Functor.const (standardPolynomialSite A B)ᵒᵖ :
      AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Functor.const (standardPolynomialSite A B)ᵒᵖ) (ComplexShape.up ℤ) 0).app M)

/-- **`Lπ_!(B̲) = B` in `D(Ab)`**, the second identification of [Stacks, Tag 08QK]. Here `B̲` is
the constant sheaf of rings with value `B` read on its underlying abelian sheaf, `π` is the point
morphism of the small model of the footnote-restricted site `C_{B/A}`, and `Lπ_!` is the total
left derived functor of the colimit over the index category.

The proof is the one the source's chain of identifications rests on in the end: the polynomial
algebra on no variables, augmented by `A → B`, is a terminal object of the site
(`CommAlgCat.isTerminal_smallPolynomialBaseObj`), so `π^{-1}` is the constant diagram and
[Stacks, Tag 08Q7] in the form `Stacks.ChaoticSite.derivedConstCompColimitIso` gives
`Lπ_! ∘ π^{-1} = id` with no further hypothesis.

### No `@[stacks 08QK]`

This is a special case of the tag's second identification, not the identification. Tag 08QK is
about `π`, `𝒪` and `B̲` as in [Stacks, Tag 08PR], whose site is `CommAlgCat.polynomialSite`; the
site here is the small model of the *footnote-restricted* site, the full subcategory of the
augmentations whose set of variables has cardinality at most
`CommAlgCat.standardResolutionVarCardinal A B`. Both `Ab(-)` and `Lπ_!` change when one passes to
a full subcategory, so neither statement implies the other. The tag's own statement is
`CommAlgCat.polynomialSiteDerivedLowerShriekConstantIso`. -/
def derivedLowerShriekConstantIso :
    derivedLowerShriekSingle A B
        (smallPolynomialConstantPresheaf A B (standardResolutionVarCardinal A B) ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}) ≅
      baseInDerived A B :=
  (abelianDerivedLowerShriek A B).mapIso (DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (constantPresheafAbelianIso A B (standardResolutionVarCardinal A B)))) ≪≫
    (abelianDerivedLowerShriek A B).mapIso
      (derivedConstSingleIso A B (abelianOfBase A B)).symm ≪≫
    (Stacks.ChaoticSite.derivedConstCompColimitIso (standardPolynomialSite A B)
      AddCommGrpCat.{u} (Or.inr inferInstance)).app (baseInDerived A B)

/-- **`Lπ_!(𝒪) = Lπ_!(B̲)` in `D(Ab)`**, the first identification of [Stacks, Tag 08QK], as an
isomorphism: it is the map induced by the augmentation `𝒪 ⟶ B̲`, which
`CommAlgCat.isIso_totalDerivedColimit_smallPolynomialAugmentation` shows to be invertible.

### No `@[stacks 08QK]`

A special case of the tag's first identification, read at the small model of the
footnote-restricted site rather than at the site `C_{B/A}` of [Stacks, Tag 08PR]; see the note on
`CommAlgCat.derivedLowerShriekConstantIso`. The tag's own statement is
`CommAlgCat.polynomialSiteDerivedLowerShriekStructureConstantIso`. -/
def derivedLowerShriekStructureConstantIso :
    derivedLowerShriekSingle A B
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B) ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}) ≅
      derivedLowerShriekSingle A B
        (smallPolynomialConstantPresheaf A B (standardResolutionVarCardinal A B) ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  haveI := isIso_totalDerivedColimit_smallPolynomialAugmentation A B
  asIso ((abelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B)))))

/-- **`Lπ_!(𝒪) = B` in `D(Ab)`**, the composite of the two identifications
`Lπ_!(𝒪) = Lπ_!(B̲)` and `Lπ_!(B̲) = B`.

### No `@[stacks 08QK]`

A special case, read at the small model of the footnote-restricted site rather than at the site
`C_{B/A}` of [Stacks, Tag 08PR]; see the note on `CommAlgCat.derivedLowerShriekConstantIso`. The
tag's own statement is `CommAlgCat.polynomialSiteDerivedLowerShriekStructureIso`. -/
def derivedLowerShriekStructureIso :
    derivedLowerShriekSingle A B
        (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B) ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}) ≅
      baseInDerived A B :=
  derivedLowerShriekStructureConstantIso A B ≪≫ derivedLowerShriekConstantIso A B

/-- **`L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` in `D(Ab)`**, the third identification of
[Stacks, Tag 08QK]. The left-hand side is the cotangent complex of [Stacks, Tag 08PN] with its
`B`-module structures forgotten, and the right-hand side is `Lπ_!` of the abelian sheaf
`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteCotangentComplex.lean`.

This is [Stacks, Tag 08PU] in `D(Ab)`. Beyond the degreewise form
`CommAlgCat.standardResolutionLeftDerivedCotangentComplexIso` it needs the *derived* form of
the computation of `Lπ_!` by a point resolution; that is available at abelian coefficients as
`Stacks.ChaoticSite.AbelianValued.mooreCochainIsoDerivedColimitApp`, and
`CommAlgCat.standardResolutionCotangentMooreComplexIso` is already an isomorphism of complexes,
so the two assemble with no further input.

### No `@[stacks 08QK]`

A special case of the tag's third identification, read at the small model of the
footnote-restricted site rather than at the site `C_{B/A}` of [Stacks, Tag 08PR]; see the note on
`CommAlgCat.derivedLowerShriekConstantIso`. The tag's own statement is
`CommAlgCat.polynomialSiteDerivedLowerShriekCotangentIso`. -/
def derivedLowerShriekCotangentIso :
    derivedLowerShriekSingle A B
        (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B)).obj ≅
      DerivedCategory.Q.obj
        (((forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) :=
  (Stacks.ChaoticSite.AbelianValued.mooreCochainIsoDerivedColimitApp
        (standardResolutionSmallCosimplicialObject A B)
        (isPointResolution_standardResolutionSmallCosimplicialObject A B) _).symm ≪≫
    DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{u}).mapIso
        (standardResolutionCotangentMooreComplexIso A B)) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.mapHomologicalComplexExtendIso
      (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u})
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ)))

/-! ### `L_{B/A} = Lπ_!(Ω_{𝒪/A})` -/

section Differentials

/-- `Lπ_!` of a complex of presheaves of `𝒪`-modules, read on abelian groups. -/
abbrev shriekComplex :
    CochainComplex (PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B))) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⋙ abelianDerivedLowerShriek A B

/-- `Ω_{𝒪/A}` placed in cohomological degree zero. -/
abbrev differentialsSingle :
    CochainComplex (PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B))) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))

/-- A projective resolution of `Ω_{𝒪/A}[0]`, as produced by [Stacks, Tag 0646]. -/
def differentialsResolution :
    ProjectiveResolutionLemma.ProjectiveResolutionComplex (differentialsSingle A B) 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ) (differentialsSingle A B) inferInstance).choose

/-- **Extension of scalars carries the chosen projective resolution of `Ω_{𝒪/A}` to a resolution
of `Ω_{𝒪/A} ⊗_𝒪 B̲`**, because the sections of `Ω_{𝒪/A}` are free. This is the step
`Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` of [Stacks, Tag 08PU]. -/
theorem quasiIso_extendScalars_differentialsResolution :
    QuasiIso (((Stacks.PullbackModel.extendScalars
        (smallPolynomialAugmentationComm A B (standardResolutionVarCardinal A B))
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map (differentialsResolution A B).α) :=
  Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections _
    (differentialsResolution A B).boundedAbove
    (differentialsResolution A B).projective
    (projective_smallPolynomialDifferentials_obj A B (standardResolutionVarCardinal A B))
    (differentialsResolution A B).α (differentialsResolution A B).quasiIso

/-- Abbreviation for the augmentation `𝒪 ⟶ B̲` at the cardinal of the standard resolution. -/
abbrev standardAugmentation :
    smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B) ⟶
      smallPolynomialConstantPresheaf A B (standardResolutionVarCardinal A B) :=
  smallPolynomialAugmentation A B (standardResolutionVarCardinal A B)

/-- The change of coefficients `- ⊗_𝒪 B̲` followed by restriction of scalars, which does not
change the underlying abelian presheaf. -/
abbrev extendRestrict :
    PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B)) ⥤
      PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B)) :=
  Stacks.ChaoticSite.extendScalars (standardAugmentation A B) ⋙
    PresheafOfModules.restrictScalars (standardAugmentation A B)

/-- The change-of-coefficients unit on the chosen projective resolution of `Ω_{𝒪/A}`, read on
the underlying abelian presheaves. -/
abbrev resolutionUnitMap :
    ((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (differentialsResolution A B).complex ⟶
      ((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (differentialsResolution A B).complex) :=
  ((PresheafOfModules.toPresheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex
      (Stacks.ChaoticSite.changeOfRingsAdjunction (standardAugmentation A B)).unit
        (ComplexShape.up ℤ)).app (differentialsResolution A B).complex)

/-- **The dévissage of [Stacks, Tag 08RX] at the chosen resolution**: `Lπ_!` inverts the
change-of-coefficients unit on a bounded above complex of projective presheaves of
`𝒪`-modules. -/
theorem isIso_shriek_resolutionUnitMap :
    IsIso ((abelianDerivedLowerShriek A B).map
      (DerivedCategory.Q.map (resolutionUnitMap A B))) := by
  have h₁ := Stacks.isStrictlyLE_mapHomologicalComplex
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B)))
    (differentialsResolution A B).complex 0 (differentialsResolution A B).boundedAbove
  have h₂ := Stacks.isStrictlyLE_mapHomologicalComplex
    (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B)))
    (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (differentialsResolution A B).complex) 0
    (Stacks.isStrictlyLE_mapHomologicalComplex (extendRestrict A B)
      (differentialsResolution A B).complex 0 (differentialsResolution A B).boundedAbove)
  exact Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B)
    (resolutionUnitMap A B)
    (fun p => by
      have := (differentialsResolution A B).projective p
      exact Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_of_projective
        (standardResolutionSmallCosimplicialObject A B) (standardAugmentation A B)
        (isPointResolution_standardResolutionSmallCosimplicialObject A B)
        (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B)
        ((differentialsResolution A B).complex.X p))

/-- The chosen resolution stays a resolution after the change of coefficients, read on the
underlying abelian presheaves. This is `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` transported from
`Stacks.PullbackModel.extendScalars` to the abstract left adjoint
`Stacks.ChaoticSite.extendScalars` along `Stacks.PullbackModel.extendScalarsIsoLeftAdjoint`. -/
theorem quasiIso_extendRestrict_differentialsResolution :
    QuasiIso (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (differentialsResolution A B).α)) := by
  have e := NatIso.mapHomologicalComplex (Stacks.PullbackModel.extendScalarsIsoLeftAdjoint
    (smallPolynomialAugmentationComm A B (standardResolutionVarCardinal A B)))
    (ComplexShape.up ℤ)
  have harr : Arrow.mk (((Stacks.PullbackModel.extendScalars
        (smallPolynomialAugmentationComm A B (standardResolutionVarCardinal A B))
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map (differentialsResolution A B).α) ≅
      Arrow.mk (((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map (differentialsResolution A B).α) :=
    Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality _).symm
  have hq : QuasiIso (((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map (differentialsResolution A B).α) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ harr).1
      (quasiIso_extendScalars_differentialsResolution A B)
  change QuasiIso (((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
      (standardResolutionVarCardinal A B))).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (differentialsResolution A B).α))
  infer_instance

/-- `Lπ_!` of an abelian presheaf in degree zero is functorial in the presheaf. -/
def derivedLowerShriekSingleMapIso
    {F G : (standardPolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}} (e : F ≅ G) :
    derivedLowerShriekSingle A B F ≅ derivedLowerShriekSingle A B G :=
  (abelianDerivedLowerShriek A B).mapIso (DerivedCategory.Q.mapIso
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso e))

/-- `Lπ_!` of `Ω_{𝒪/A}` placed in degree zero, computed on the complex. -/
def shriekDifferentialsSingleIso :
    (shriekComplex A B).obj (differentialsSingle A B) ≅
      derivedLowerShriekSingle A B
        ((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))).obj
            (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))) :=
  (abelianDerivedLowerShriek A B).mapIso (DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))) (ComplexShape.up ℤ) 0).app
          (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))))

/-- `Lπ_!` of `Ω_{𝒪/A} ⊗_𝒪 B̲` placed in degree zero, computed on the complex. -/
def shriekExtendDifferentialsSingleIso :
    (shriekComplex A B).obj
        (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (differentialsSingle A B)) ≅
      derivedLowerShriekSingle A B
        ((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
          (standardResolutionVarCardinal A B))).obj
            ((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)).obj
              (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B)))) :=
  (abelianDerivedLowerShriek A B).mapIso (DerivedCategory.Q.mapIso
    (((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
          (standardResolutionVarCardinal A B))).mapHomologicalComplex
            (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (Stacks.ChaoticSite.extendScalars (standardAugmentation A B))
            (ComplexShape.up ℤ) 0).app
              (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex
        (PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
          (standardResolutionVarCardinal A B))) (ComplexShape.up ℤ) 0).app
            ((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)).obj
              (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B)))))

/-- **`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` in `D(Ab)`**, the comparison of
[Stacks, Tag 08QJ] at `Ω_{𝒪/A}`, with the derived tensor product replaced by the underived one.

The chain is the source's: a projective resolution `P^• ⟶ Ω_{𝒪/A}[0]` of [Stacks, Tag 0646];
`Lπ_!` inverts the change-of-coefficients unit on `P^•` by the dévissage of
[Stacks, Tag 08RX] (`CommAlgCat.isIso_shriek_resolutionUnitMap`); and the resolution stays a
resolution after the change of coefficients because the sections of `Ω_{𝒪/A}` are free, which is
the step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`
(`CommAlgCat.quasiIso_extendRestrict_differentialsResolution`). -/
def derivedLowerShriekDifferentialsExtendIso :
    derivedLowerShriekSingle A B
        ((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))).obj
            (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))) ≅
      derivedLowerShriekSingle A B
        ((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
          (standardResolutionVarCardinal A B))).obj
            ((Stacks.ChaoticSite.extendScalars (standardAugmentation A B)).obj
              (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B)))) :=
  haveI h₁ : QuasiIso (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
      (standardResolutionVarCardinal A B))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (differentialsResolution A B).α) :=
    haveI := (differentialsResolution A B).quasiIso
    inferInstance
  haveI h₂ : IsIso ((shriekComplex A B).map (differentialsResolution A B).α) := by
    have : IsIso (DerivedCategory.Q.map
        (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (differentialsResolution A B).α)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h₁
    exact inferInstanceAs (IsIso ((abelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
      (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
        (standardResolutionVarCardinal A B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (differentialsResolution A B).α))))
  haveI h₃ : IsIso ((shriekComplex A B).map
      (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (differentialsResolution A B).α)) := by
    have : IsIso (DerivedCategory.Q.map
        (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
            (standardResolutionVarCardinal A B))).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
          (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (differentialsResolution A B).α))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (quasiIso_extendRestrict_differentialsResolution A B)
    exact inferInstanceAs (IsIso ((abelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
      (((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (differentialsResolution A B).α)))))
  haveI := isIso_shriek_resolutionUnitMap A B
  (shriekDifferentialsSingleIso A B).symm ≪≫
    (asIso ((shriekComplex A B).map (differentialsResolution A B).α)).symm ≪≫
    asIso ((abelianDerivedLowerShriek A B).map
      (DerivedCategory.Q.map (resolutionUnitMap A B))) ≪≫
    asIso ((shriekComplex A B).map
      (((extendRestrict A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (differentialsResolution A B).α)) ≪≫
    shriekExtendDifferentialsSingleIso A B

/-- **`L_{B/A} = Lπ_!(Ω_{𝒪/A})` in `D(Ab)`**, the fourth identification of [Stacks, Tag 08QK].
The cotangent complex of [Stacks, Tag 08PN], read in `D(Ab)`, is derived lower shriek of the
sheaf of relative differentials itself — no base change to `B̲`.

This is [Stacks, Tag 08QJ] at `ℱ = Ω_{𝒪/A}` followed by [Stacks, Tag 08PU]: the comparison
`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` is
`CommAlgCat.derivedLowerShriekDifferentialsExtendIso`, the identification of that base change
with `i^*Ω_{𝒪/A}` is `CommAlgCat.extendScalarsDifferentialsIso`, and
`CommAlgCat.derivedLowerShriekCotangentIso` is the third identification of the tag.

### No `@[stacks 08QK]`

A special case of the tag's fourth identification, read at the small model of the
footnote-restricted site rather than at the site `C_{B/A}` of [Stacks, Tag 08PR]; see the note on
`CommAlgCat.derivedLowerShriekConstantIso`.

The clause `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A})` is registered at `C_{B/A}` itself as
`CommAlgCat.polynomialSiteDerivedLowerShriekDifferentialsBaseChangeIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentialsBaseChangeLargeSite.lean`, and the
other three identifications of the tag are
`CommAlgCat.polynomialSiteDerivedLowerShriekStructureConstantIso`,
`CommAlgCat.polynomialSiteDerivedLowerShriekConstantIso` and
`CommAlgCat.polynomialSiteDerivedLowerShriekCotangentIso`.

What this declaration is a special case of, [Stacks, Tag 08QJ] at the unrestricted site, remains
unavailable: the dévissage of [Stacks, Tag 08RX] behind it is formalized only for a site that is a
`SmallCategory` with coefficients in `RingCat.{u}` --
`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single` and every link of its chain,
through `Stacks.ChaoticSite.changeOfRingsAdjunction`,
`Stacks.ChaoticSite.derivedColimitTensorComparison` and
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero`. The objects of `C_{B/A}` live
one universe above its morphisms, so none of those apply, and the transport that removed the same
restriction from [Stacks, Tag 08Q9] --
`Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso`, an equivalence for *abelian* coefficients
-- does not by itself carry a statement about `- ⊗^L_𝒪 B̲`. The registration at `C_{B/A}` goes
around Tag 08QJ instead, through the Δ-instance of Tag 08RX. -/
def derivedLowerShriekDifferentialsIso :
    derivedLowerShriekSingle A B
        ((PresheafOfModules.toPresheaf (smallPolynomialStructurePresheaf A B
          (standardResolutionVarCardinal A B))).obj
            (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))) ≅
      DerivedCategory.Q.obj
        (((forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) :=
  derivedLowerShriekDifferentialsExtendIso A B ≪≫
    derivedLowerShriekSingleMapIso A B
      ((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
          (standardResolutionVarCardinal A B))).mapIso
        ((Stacks.PullbackModel.extendScalarsIsoLeftAdjoint
          (smallPolynomialAugmentationComm A B
            (standardResolutionVarCardinal A B))).app
              (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))).symm) ≪≫
    derivedLowerShriekSingleMapIso A B
      (extendScalarsDifferentialsIso A B (standardResolutionVarCardinal A B)) ≪≫
    derivedLowerShriekCotangentIso A B

end Differentials

end CommAlgCat

end
