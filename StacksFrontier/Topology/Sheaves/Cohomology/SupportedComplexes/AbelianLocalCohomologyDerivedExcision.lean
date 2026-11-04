module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPostcomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived-category excision for the local cohomology of sheaves of abelian groups

Let `T` be a subset of a topological space `X`, let `U ⊆ X` be an open subset and let
`j : U → X` be its inclusion.  On the **unbounded** derived category of sheaves of abelian groups
a total right derived functor `RH_T` of the subsheaf of sections supported on `T` commutes with
restriction to `U`:

`RH_T(K)|_U ≅ RH_{j⁻¹T}(K|_U)`,

naturally in `K : D(Ab(X))`.  That is `derivedAbelianSupportedSectionsRestrictNatIso`, stated for
an *arbitrary* pair of total right derived functors with their units, in the style of
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`, so that it
composes with the statements of [Stacks, Tag 0G74] part (2) that quantify over theirs.

The implementation notes of
`Stacks.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyExcision` record exactly
this as missing: the library had the abelian excision
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` **classically only**,
as a comparison of the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, and had no abelian total
right derived functor of supported sections on a subset of a topological space at all.  Both
halves are supplied here.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSections`: **`RH_T` on abelian
  sheaves for an arbitrary subset `T` of a topological space**, the total right derived functor of
  the subsheaf of sections supported on `T`, with
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsUnit` its derivation unit
  and `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSections_isRightDerivedFunctor`
  the instance saying so.  This is the subset counterpart of
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed`, built by the
  same `CategoryTheory.Functor.totalRightDerived` recipe, and it instantiates everything below.
* `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsCompRestrictUnit` and
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianRestrictOpenCompSupportedSectionsUnit`: the
  units exhibiting the two composites as right derived functors of `H_T(-)|_U` and of
  `H_{j⁻¹T}((-)|_U)`.
* `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictHomotopyIso`: the
  degree-zero excision read on the homotopy category and then on the derived category, which is
  the single mathematical input of the comparison.
* `Stacks.Cohomology.SupportedComplexes.abelianExtendByZero` and
  `Stacks.Cohomology.SupportedComplexes.abelianExtendByZeroAdjunction`: `ExtensionByZero.jExt`
  and `ExtensionByZero.jExtAdjunction` at the spelling of the open subset that
  `abelianRestrictOpen` is ascribed, which is what lets the exact left adjoint be handed to the
  pre-composition criterion.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isRightDerivedFunctor_derivedAbelianSupportedSectionsComp`:
  `RH_T ⋙ (-)|_U` **is** a right derived functor of `H_T(-)|_U`, restriction to an open subset
  being exact.
* `Stacks.Cohomology.SupportedComplexes.isRightDerivedFunctor_restrictCompAbelianSupportedSections`
  : `(-)|_U ⋙ RH_{j⁻¹T}` **is** a right derived functor of `H_{j⁻¹T}((-)|_U)`, restriction having
  the exact left adjoint "extension by zero" and hence preserving K-injectivity
  ([Stacks, Tag 08BJ]).
* `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso`:
  **derived-category excision for abelian local cohomology**, `RH_T ⋙ (-)|_U ≅ (-)|_U ⋙
  RH_{j⁻¹T}`.  No closedness assumption on `T` is needed.
* `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso_fac` and
  `..._hom_app`: **the defining factorization**, in natural-transformation and in componentwise
  form — the unit of the first composite followed by the comparison is the degreewise excision
  followed by the unit of the second.  This is the `CategoryTheory.Functor.rightDerived_fac`
  specialisation a consumer computing the comparison after a derivation unit uses, and it is the
  one property that pins the comparison down.

## Implementation notes

**The route.**  Both composites are right derived functors of degreewise-isomorphic functors, so
Mathlib's `CategoryTheory.Functor.rightDerivedNatIso` supplies the comparison, exactly as in the
module analogue
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso`.  The two
presuppositions are discharged by the two generic statements of the project rather than rebuilt:

* post-composition, `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, which needs only
  that restriction to an open subset is exact
  (`Stacks.Cohomology.SupportedComplexes.sheafRestrict_preservesFiniteLimits` and
  `...sheafRestrict_preservesFiniteColimits`); it is a consequence of absoluteness of a right
  derived functor computed by K-injective resolutions;
* pre-composition, `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`,
  which is *not* formal: it asks that restriction carry K-injective complexes to K-injective ones,
  and that holds by [Stacks, Tag 08BJ] because `ExtensionByZero.jExtAdjunction` exhibits
  restriction as the right adjoint of extension by zero, which is exact ([Stacks, Tag 01AK]).

The K-injective-resolution hypotheses of both are
`Stacks.Cohomology.Localization.enoughKInjectives`, abelian sheaves on a space being Grothendieck
abelian.  The degreewise input is
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso`, which is where the
mathematics is; everything above it is the uniqueness of right derived functors.

**Why `hasRightDerivedFunctor_abelianSheaves` is not the source of the existence hypothesis.**
`Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.hasRightDerivedFunctor_abelianSheaves` is
stated for the abelian sheaves on the underlying space of a *ringed* space, and there is no ringed
space here, only `X : TopCat`.  `hasRightDerivedFunctor_abelianSheavesOnSpace` of this file is the
same statement at a bare topological space, with the same one-line proof: the small-site instance
makes `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` Grothendieck abelian, so
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck` applies.

**No `@[stacks ...]` attribute is attached to any declaration here.**  Excision for local
cohomology is not a numbered result of the source, exactly as in
`Stacks.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision`; the generic homological
algebra used is tagged where it is proved.

**What is still not identified.**  The comparison built here is not compared with the classical
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` through
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.  Both are induced by the one
degree-zero isomorphism `abelianSupportedSectionsRestrictNatIso`, and the three coherences that
would identify them are listed in the implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision`; the two units this file
exhibits are `Stacks.DerivedFunctor.postcomposeUnit` and `Stacks.DerivedFunctor.precomposeUnit`,
whose componentwise forms `...postcomposeUnit_app` and `...precomposeUnit_app` are the hypotheses
those coherences take, so the identification is within reach and is not carried out here.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 01AK](https://stacks.math.columbia.edu/tag/01AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}}

/-! ### Existence of the total right derived functor -/

/-- **Every functor out of the homotopy category of abelian sheaves on a topological space has a
total right derived functor.**  Abelian sheaves on a space are Grothendieck abelian — the site of
opens is small — so every cochain complex of them admits a quasi-isomorphism into a K-injective
one and `Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck` applies.

This is
`Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.hasRightDerivedFunctor_abelianSheaves`
at a bare topological space rather than at the underlying space of a ringed space. -/
theorem hasRightDerivedFunctor_abelianSheavesOnSpace {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck _ F

/-! ### `RH_T` on abelian sheaves -/

/-- **`RH_T` on abelian sheaves**, the total right derived functor of the subsheaf of sections
supported on the subset `T`, along the localization of the homotopy category at the
quasi-isomorphisms.

This is the subset counterpart of `derivedAbelianSupportedSectionsOnClosed`, constructed by the
same `CategoryTheory.Functor.totalRightDerived` recipe; no closedness of `T` is needed.  The
`HasRightDerivedFunctor` hypothesis of `totalRightDerived` is not an instance and is supplied from
`hasRightDerivedFunctor_abelianSheavesOnSpace`. -/
@[sga "4 V 6.3" "special case"]
def derivedAbelianSupportedSections (T : Set X) :
    DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  let := hasRightDerivedFunctor_abelianSheavesOnSpace
    ((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  Functor.totalRightDerived
    ((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))

/-- The derivation unit of `derivedAbelianSupportedSections`: the canonical comparison from the
subsheaf of sections of a complex of abelian sheaves supported on `T` to the value of the total
right derived functor on it, with the `HasRightDerivedFunctor` hypothesis supplied exactly as in
the functor itself. -/
def derivedAbelianSupportedSectionsUnit (T : Set X) :
    (abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianSupportedSections T :=
  let := hasRightDerivedFunctor_abelianSheavesOnSpace
    ((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  Functor.totalRightDerivedUnit
    ((abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))

/-- **The unit exhibits `derivedAbelianSupportedSections` as the right derived functor of the
subsheaf of supported sections.**  Both it and its unit are the `totalRightDerived` data of the
same functor, so the general instance applies after unfolding; the `HasRightDerivedFunctor`
hypothesis is a `Prop` and is supplied the same way in both. -/
instance derivedAbelianSupportedSections_isRightDerivedFunctor (T : Set X) :
    (derivedAbelianSupportedSections T).IsRightDerivedFunctor
      (derivedAbelianSupportedSectionsUnit T)
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedAbelianSupportedSections, derivedAbelianSupportedSectionsUnit]
  infer_instance

/-! ### Exactness and additivity of extension by zero -/

section Adjunction

variable (U : Opens X)

/-- **Extension by zero of abelian sheaves along the inclusion of an open subset**, with its
source spelled as abelian sheaves on the open subset viewed as a topological space.  This is
`ExtensionByZero.jExt`; only the spelling of the source category differs, and the spelling is
what matters, for exactly the reason recorded on `abelianRestrictOpen`: `↥U` and
`↑((Opens.toTopCat X).obj U)` are definitionally equal but are different keys, and the left
adjoint of `abelianRestrictOpen U` has to be presented at the latter for the instances below to
be the ones an application needs. -/
abbrev abelianExtendByZero :
    Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ExtensionByZero.jExt U

/-- **Extension by zero is left exact**, the first half of [Stacks, Tag 01AK], at the spelling
of `abelianExtendByZero`. -/
instance abelianExtendByZero_preservesFiniteLimits :
    PreservesFiniteLimits (abelianExtendByZero U) :=
  (ExtensionByZero.jExt_exactFunctor U).1

/-- **Extension by zero is right exact**, the second half of [Stacks, Tag 01AK]: it is a left
adjoint, by `ExtensionByZero.jExtAdjunction`, so it preserves all colimits. -/
instance abelianExtendByZero_preservesFiniteColimits :
    PreservesFiniteColimits (abelianExtendByZero U) :=
  (ExtensionByZero.jExt_exactFunctor U).2

/-- Extension by zero is additive, being exact and in particular preserving binary products. -/
instance abelianExtendByZero_additive : (abelianExtendByZero U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Extension by zero is left adjoint to restriction**, at the two ascribed spellings.  This is
`ExtensionByZero.jExtAdjunction`, retyped: both functors are the same, only the spelling of the
category of abelian sheaves on `U` differs, and the two spellings are definitionally equal. -/
def abelianExtendByZeroAdjunction : abelianExtendByZero U ⊣ abelianRestrictOpen U :=
  ExtensionByZero.jExtAdjunction U

/-- The supported-sections endofunctor followed by restriction to an open subset is additive.  It
is stated by hand because the generic instance for a composite is not reliably found at this
spelling of the intermediate category, exactly as for
`sheafRestrict_comp_abelianSupportedSections_additive` in the other order. -/
instance abelianSupportedSections_comp_sheafRestrict_additive (T : Set X) :
    (abelianSupportedSections T ⋙ abelianRestrictOpen U).Additive where
  map_add := by intros; rfl

end Adjunction

/-! ### The two units and the degreewise comparison -/

section Derived

variable (T : Set X) (U : Opens X)
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSections T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  (RHab' : DerivedCategory
      (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}) ⥤
    DerivedCategory
      (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}))
  (aHab' : (abelianSupportedSections (preimageSubset U T)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab')

/-- The unit exhibiting `RH_T ⋙ (-)|_U` as a right derived functor of `H_T(-)|_U`: the unit
`aHab` of `RH_T` pushed through the derived functor of restriction, after the identification of
the two sources.  This is `Stacks.DerivedFunctor.postcomposeUnit` at the data of this file, and
`Stacks.DerivedFunctor.postcomposeUnit_app` computes it at an object. -/
def derivedAbelianSupportedSectionsCompRestrictUnit :
    (abelianSupportedSections T ⋙ abelianRestrictOpen U).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RHab ⋙ (abelianRestrictOpen U).mapDerivedCategory :=
  Stacks.DerivedFunctor.postcomposeUnit (abelianSupportedSections T) (abelianRestrictOpen U)
    RHab aHab

/-- The unit exhibiting `(-)|_U ⋙ RH_{j⁻¹T}` as a right derived functor of `H_{j⁻¹T}((-)|_U)`:
the unit `aHab'` of `RH_{j⁻¹T}` at the restriction of a complex, between the two reassociations.
This is `Stacks.DerivedFunctor.precomposeUnit` at the data of this file, and
`Stacks.DerivedFunctor.precomposeUnit_app` computes it at an object. -/
def derivedAbelianRestrictOpenCompSupportedSectionsUnit :
    (abelianRestrictOpen U ⋙ abelianSupportedSections (preimageSubset U T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (abelianRestrictOpen U).mapDerivedCategory ⋙ RHab' :=
  Stacks.DerivedFunctor.precomposeUnit (abelianRestrictOpen U)
    (abelianSupportedSections (preimageSubset U T)) RHab' aHab'

/-- **The degree-zero excision, read on the homotopy category and then on the derived category.**
This is `abelianSupportedSectionsRestrictNatIso` applied degreewise: the comparison of the
homotopy-category functor of a composite with the composite of the homotopy-category functors,
inverted, then the degree-zero excision, then `DerivedCategory.Qh`.  It is the single mathematical
input of `derivedAbelianSupportedSectionsRestrictNatIso`. -/
def abelianSupportedSectionsRestrictHomotopyIso :
    (abelianSupportedSections T ⋙ abelianRestrictOpen U).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (abelianRestrictOpen U ⋙ abelianSupportedSections (preimageSubset U T)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (abelianSupportedSections T ⋙ abelianRestrictOpen U))
          (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso (abelianSupportedSectionsRestrictNatIso T U)
        (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- **`RH_T ⋙ (-)|_U` is a right derived functor of `H_T(-)|_U`.**  Restriction of abelian sheaves
to an open subset is exact, so this is absoluteness of a right derived functor computed by
K-injective resolutions, `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`; the existence
of those resolutions is `Stacks.Cohomology.Localization.enoughKInjectives`. -/
theorem isRightDerivedFunctor_derivedAbelianSupportedSectionsComp
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))] :
    (RHab ⋙ (abelianRestrictOpen U).mapDerivedCategory).IsRightDerivedFunctor
      (derivedAbelianSupportedSectionsCompRestrictUnit T U RHab aHab)
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose (abelianSupportedSections T)
    (abelianRestrictOpen U) RHab aHab Stacks.Cohomology.Localization.enoughKInjectives

/-- **`(-)|_U ⋙ RH_{j⁻¹T}` is a right derived functor of `H_{j⁻¹T}((-)|_U)`.**  Unlike the
post-composition statement this is not formal: it needs that restriction to an open subset carries
K-injective complexes to K-injective ones, which holds by [Stacks, Tag 08BJ] because
`ExtensionByZero.jExtAdjunction` exhibits restriction as the right adjoint of extension by zero,
and extension by zero is exact ([Stacks, Tag 01AK]). -/
theorem isRightDerivedFunctor_restrictCompAbelianSupportedSections
    [RHab'.IsRightDerivedFunctor aHab'
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))] :
    ((abelianRestrictOpen U).mapDerivedCategory ⋙ RHab').IsRightDerivedFunctor
      (derivedAbelianRestrictOpenCompSupportedSectionsUnit T U RHab' aHab')
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint
    (abelianRestrictOpen U) (abelianSupportedSections (preimageSubset U T)) RHab' aHab'
    (abelianExtendByZero U) (abelianExtendByZeroAdjunction U)
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives

/-- **Derived-category excision for abelian local cohomology.**  For a subset `T` of a
topological space `X` and an open subset `U ⊆ X` with inclusion `j : U → X`,

`RH_T(K)|_U ≅ RH_{j⁻¹T}(K|_U)`,

naturally in `K` in the unbounded derived category of abelian sheaves on `X`, for any total right
derived functors `RH_T` of `H_T` and `RH_{j⁻¹T}` of `H_{j⁻¹T}` with units `aHab` and `aHab'`.  No
closedness assumption on `T` is needed.

Both sides are right derived functors of the degreewise-isomorphic functors `H_T(-)|_U` and
`H_{j⁻¹T}((-)|_U)` — the two theorems above — so the uniqueness of right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`, supplies the comparison from the degree-zero excision
`abelianSupportedSectionsRestrictNatIso`.  What pins it down is
`derivedAbelianSupportedSectionsRestrictNatIso_fac`. -/
@[sga "4 V 6.4" "Clause 1), special case"]
def derivedAbelianSupportedSectionsRestrictNatIso
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [RHab'.IsRightDerivedFunctor aHab'
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))] :
    RHab ⋙ (abelianRestrictOpen U).mapDerivedCategory ≅
      (abelianRestrictOpen U).mapDerivedCategory ⋙ RHab' :=
  have := isRightDerivedFunctor_derivedAbelianSupportedSectionsComp T U RHab aHab
  have := isRightDerivedFunctor_restrictCompAbelianSupportedSections T U RHab' aHab'
  Functor.rightDerivedNatIso (RHab ⋙ (abelianRestrictOpen U).mapDerivedCategory)
    ((abelianRestrictOpen U).mapDerivedCategory ⋙ RHab')
    (derivedAbelianSupportedSectionsCompRestrictUnit T U RHab aHab)
    (derivedAbelianRestrictOpenCompSupportedSectionsUnit T U RHab' aHab')
    (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))
    (abelianSupportedSectionsRestrictHomotopyIso T U)

/-- **The defining factorization of the derived excision.**  The unit exhibiting `RH_T ⋙ (-)|_U`
as a right derived functor, followed by the comparison, is the degreewise excision followed by the
unit exhibiting `(-)|_U ⋙ RH_{j⁻¹T}` as one.  This is the `CategoryTheory.Functor.rightDerived_fac`
factorization at the data of this file, and it is the one property that determines
`derivedAbelianSupportedSectionsRestrictNatIso`. -/
theorem derivedAbelianSupportedSectionsRestrictNatIso_fac
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [RHab'.IsRightDerivedFunctor aHab'
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))] :
    derivedAbelianSupportedSectionsCompRestrictUnit T U RHab aHab ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedAbelianSupportedSectionsRestrictNatIso T U RHab aHab RHab' aHab').hom =
      (abelianSupportedSectionsRestrictHomotopyIso T U).hom ≫
        derivedAbelianRestrictOpenCompSupportedSectionsUnit T U RHab' aHab' :=
  have := isRightDerivedFunctor_derivedAbelianSupportedSectionsComp T U RHab aHab
  have := isRightDerivedFunctor_restrictCompAbelianSupportedSections T U RHab' aHab'
  Functor.rightDerivedNatTrans_fac (RHab ⋙ (abelianRestrictOpen U).mapDerivedCategory)
    ((abelianRestrictOpen U).mapDerivedCategory ⋙ RHab')
    (derivedAbelianSupportedSectionsCompRestrictUnit T U RHab aHab)
    (derivedAbelianRestrictOpenCompSupportedSectionsUnit T U RHab' aHab')
    (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ))
    (abelianSupportedSectionsRestrictHomotopyIso T U).hom

/-- **The defining factorization, at one object.**  The componentwise form of
`derivedAbelianSupportedSectionsRestrictNatIso_fac`, which is what a consumer computing the
comparison after a derivation unit at a single complex uses. -/
theorem derivedAbelianSupportedSectionsRestrictNatIso_hom_app
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [RHab'.IsRightDerivedFunctor aHab'
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (K : HomotopyCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    (derivedAbelianSupportedSectionsCompRestrictUnit T U RHab aHab).app K ≫
        (derivedAbelianSupportedSectionsRestrictNatIso T U RHab aHab RHab' aHab').hom.app
          (DerivedCategory.Qh.obj K) =
      (abelianSupportedSectionsRestrictHomotopyIso T U).hom.app K ≫
        (derivedAbelianRestrictOpenCompSupportedSectionsUnit T U RHab' aHab').app K :=
  NatTrans.congr_app (derivedAbelianSupportedSectionsRestrictNatIso_fac T U RHab aHab RHab' aHab') K

end Derived

end Stacks.Cohomology.SupportedComplexes

end
