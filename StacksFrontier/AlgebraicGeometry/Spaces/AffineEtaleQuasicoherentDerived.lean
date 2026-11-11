module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent derived categories on the affine étale charts of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 0H05
sets up four triangulated categories attached to it:

1. `D_QCoh(𝒪_F)`, on the small étale site;
2. `D_QCoh(F_{affine,étale}, 𝒪_F)`, on the affine étale charts with the étale topology;
3. `D_QCoh(F_{affine}, 𝒪_F)`, on the affine étale charts with the *chaotic* topology;
4. `QC(F_{affine}, 𝒪_F)`, the cartesian objects of Stacks 0GYU on the chaotic site;

and Stacks 0H06 asserts that all four are canonically exactly equivalent.  This file treats the
comparison of (3) with (4), and the comparison of (1) with (2).

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleChaoticRingedSite` is the ringed site of category (3) and
  (4): the affine étale charts of `F` carrying the chaotic topology, with the affine étale
  structure sheaf of Stacks 0H03.
* `AlgebraicGeometry.Space.affineEtaleRingRestriction` and
  `AlgebraicGeometry.Space.affineEtaleModuleRestriction` are the restriction to affine charts of
  the small étale sheaf of rings and of the sheaves of modules over it.
* `AlgebraicGeometry.Space.affineEtaleModuleRestrictionEquivalence` is the resulting equivalence
  of abelian categories of modules, and
  `AlgebraicGeometry.Space.affineEtaleDerivedRestrictionEquivalence` the equivalence of their
  unbounded derived categories.

## Main results

* `AlgebraicGeometry.Space.flat_affineEtaleChaoticRingedSite_O_map`: the restriction maps of the
  affine étale structure sheaf are flat, which is the hypothesis under which quasi-coherent
  cohomology and the cartesian condition agree.
* `AlgebraicGeometry.Space.isQC_iff_hasQuasicoherentCohomology_affineEtaleChaotic` and
  `AlgebraicGeometry.Space.isQC_eq_hasQuasicoherentCohomology_affineEtaleChaotic`:
  **categories (3) and (4) of Stacks 0H06 agree**, as an equivalence of membership conditions
  and as an equality of the two object properties on `D(𝒪_F)` of the chaotic affine étale site.
* `AlgebraicGeometry.Space.isEquivalence_affineEtaleRestriction_addCommGrpCat` and
  `AlgebraicGeometry.Space.isEquivalence_affineEtaleModuleRestriction`: restriction to affine
  charts is an equivalence on sheaves of abelian groups and on sheaves of modules.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModuleRestriction`: restriction to
  affine charts carries quasi-coherence.
* `AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleEquivalence`: **categories (1) and (2)
  of Stacks 0H06 agree**, over the one explicitly named input described below.

## What is carried as a hypothesis

The unconditional form of the comparison of (1) and (2), and the whole of Stacks 0H06, is in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleQuasicoherentDerivedChain.lean`
(`AlgebraicGeometry.Space.quasicoherentDerivedAffineEtaleChain`) and
`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleQuasicoherentDerivedChainTriangulated.lean`,
where the tag is registered; the declarations of this file are not registered under it.

The comparison of (1) and (2) carries a single hypothesis, `hrefl`: that a sheaf of
`𝒪_F`-modules on the small étale site whose restriction to the affine charts is quasi-coherent
is itself quasi-coherent.  That is the converse of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModuleRestriction`, which is proved
here, and together the two say that the equivalence of module categories matches the two
quasi-coherence conditions — clause (6) of Stacks 03DL read along the inclusion of the affine
charts, in the direction Stacks 03DM does not supply here.  It is a statement about single
modules, i.e. about objects of degree zero, whereas the conclusion is about complexes; it is
therefore strictly weaker than the conclusion, being the degree-zero part of it, and it is not
the conclusion in disguise.  Nothing else is assumed: the equivalence of module categories, its
exactness, the equivalence of the unbounded derived categories and the identification of
cohomology across it are all proved.

The comparison of (2) with (3) is *not* treated.  It is the comparison across the change from
the étale to the chaotic topology on the same category, i.e. the morphism of ringed sites `ε`
of Stacks 0EWK, and the input it needs is the second conclusion of Stacks 07A8 — the
equivalence `D_A(R_τ) = D_A(R_τ')` induced by `ε^*` and `Rε_*`.  Only the first conclusion of
07A8 exists in this library, as
`Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE`; the second needs Stacks 0D7W
and the total right derived functor of `ε_*` on the unbounded derived category, neither of
which is available.  No statement about (2) versus (3) is made here, not even a hypothetical
one.

## Implementation notes

The structure sheaf of the chaotic affine étale ringed site is the one of Stacks 0H03,
`AlgebraicGeometry.Space.affineEtaleStructureSheaf`, read as a sheaf for the chaotic topology —
every presheaf is, by `CategoryTheory.Presheaf.isSheaf_bot`.  Taking the same structure sheaf as
Stacks 0H04 is what lets `AlgebraicGeometry.Space.flat_affineEtaleStructurePresheaf_map` supply
the flatness hypothesis with no comparison of structure sheaves.

Restriction to affine charts is `AlgebraicGeometry.Space.affineEtaleRestriction` of Stacks 0H03,
which takes the algebraicity of `F` explicitly and installs the dense-subsite property of
Stacks 04JS internally; stating the results in terms of it rather than of
`CategoryTheory.Functor.sheafPushforwardContinuous` keeps the dense-subsite instance out of
every statement, while the two are definitionally equal so the proofs still consume the general
API of `Stacks.DenseSubsiteModules` directly.

The two comparisons here are stated over two different presentations of `𝒪_F`, and are not
chained.  The chaotic site of categories (3) and (4) carries the structure sheaf of Stacks 0H03,
`AlgebraicGeometry.Space.affineEtaleStructureSheaf`, whose rings of sections live in universe
`u + 1`, because that is the sheaf for which Stacks 0H04 supplies flatness of the restriction
maps; categories (1) and (2) are read over the structure sheaf of
`AlgebraicGeometry.Space.smallEtaleRingedSite` and its restriction, whose rings of sections live
in universe `u`.  The two are canonically isomorphic, by
`AlgebraicGeometry.Space.affineEtaleStructurePresheaf_eq`, but that identification is not made
here, so no statement below composes the (1)-(2) comparison with the (3)-(4) one.

The Comparison Lemma for sheaves of modules forces the sections of the modules into the
universe of the sections of the structure rings, which here is `u`, the universe of the schemes;
so these results are about `D_QCoh(𝒪_F)` at module universe `u`, which is the universe at which
`AlgebraicGeometry.Space.derivedQuasicoherent_tfae` and
`AlgebraicGeometry.Space.QuasicoherentSheaves` are also read.  The abelian input of that
Comparison Lemma asks `AddCommGrpCat.{u}` for limits over the comma categories of the inclusion;
those categories are essentially small at `u` because the affine étale site is, which is
`AlgebraicGeometry.Space.AffineEtale.instEssentiallySmall` below.

## References

* [Stacks Project, Tag 0H06](https://stacks.math.columbia.edu/tag/0H06)
* [Stacks Project, Tag 0H05](https://stacks.math.columbia.edu/tag/0H05)
* [Stacks Project, Tag 0H03](https://stacks.math.columbia.edu/tag/0H03)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.QuasiCoherentCohomology

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Categories (3) and (4): the chaotic affine étale ringed site -/

/-- The affine étale charts of `F` with the **chaotic** topology and the affine étale structure
sheaf of Stacks 0H03: the ringed site underlying categories (3) and (4) of Stacks 0H06.

Only the bottom topology appears, so being a sheaf is no condition at all
(`CategoryTheory.Presheaf.isSheaf_bot`) and the structure sheaf is the one of Stacks 0H03 with
its sheaf condition discarded. -/
noncomputable def affineEtaleChaoticRingedSite : RingedSite.{u + 1, u, u + 1} where
  C := AffineEtale B S hS F
  J := ⊥
  O := ⟨(affineEtaleStructureSheaf B S hS F hF).obj, Presheaf.isSheaf_bot _⟩

/-- The topology of the chaotic affine étale ringed site is the bottom one. -/
theorem affineEtaleChaoticRingedSite_J :
    (affineEtaleChaoticRingedSite B S hS F hF).J = ⊥ := rfl

/-- **The restriction maps of the affine étale structure sheaf are flat.**  A morphism of affine
étale charts is étale, hence flat, on the underlying affine schemes, so the induced map of rings
of global functions is flat; this is
`AlgebraicGeometry.Space.flat_affineEtaleStructurePresheaf_map` of Stacks 0H04, read on the
opposite category. -/
theorem flat_affineEtaleChaoticRingedSite_O_map
    {U V : (affineEtaleChaoticRingedSite B S hS F hF).Cᵒᵖ} (a : V ⟶ U) :
    RingHom.Flat ((affineEtaleChaoticRingedSite B S hS F hF).O.obj.map a).hom :=
  flat_affineEtaleStructurePresheaf_map B S hS F hF (U := U.unop) (V := V.unop) a.unop

/-- **Categories (3) and (4) of Stacks 0H06 agree.**  On the affine étale charts of an algebraic
space with the chaotic topology, an object of the derived category of `𝒪_F`-modules is a
cartesian object in the sense of Stacks 0GYU exactly when all of its cohomology sheaves are
quasi-coherent; that is, `QC(F_{affine}, 𝒪_F) = D_QCoh(F_{affine}, 𝒪_F)`.

This is Stacks 0GZR,
`Stacks.ModulesOnACategory.QuasiCoherentCohomology.isQC_iff_hasQuasicoherentCohomology`, whose
two hypotheses are supplied by `AlgebraicGeometry.Space.affineEtaleChaoticRingedSite_J` and
`AlgebraicGeometry.Space.flat_affineEtaleChaoticRingedSite_O_map`. -/
theorem isQC_iff_hasQuasicoherentCohomology_affineEtaleChaotic
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleChaoticRingedSite B S hS F hF).O).obj)
    (K : DMod.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleChaoticRingedSite B S hS F hF).O).obj) :
    IsQC.{w} bc K ↔
      hasQuasicoherentCohomology.{w} (affineEtaleChaoticRingedSite B S hS F hF) K :=
  isQC_iff_hasQuasicoherentCohomology.{w, u + 1, u, u + 1}
    (affineEtaleChaoticRingedSite B S hS F hF) rfl
    (flat_affineEtaleChaoticRingedSite_O_map B S hS F hF) bc K

/-- **Categories (3) and (4) of Stacks 0H06 are cut out of `D(𝒪_F)` by the same object
property.**  This is the previous result as an equality of object properties, which is the form
that exhibits the two full subcategories as the same subcategory of `D(𝒪_F)` rather than merely
as equivalent ones. -/
theorem isQC_eq_hasQuasicoherentCohomology_affineEtaleChaotic
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleChaoticRingedSite B S hS F hF).O).obj) :
    (fun K ↦ IsQC.{w} bc K :
        ObjectProperty (DMod.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (affineEtaleChaoticRingedSite B S hS F hF).O).obj)) =
      hasQuasicoherentCohomology.{w} (affineEtaleChaoticRingedSite B S hS F hF) := by
  funext K
  exact propext (isQC_iff_hasQuasicoherentCohomology_affineEtaleChaotic B S hS F hF bc K)

/-! ### Categories (1) and (2): restriction to the affine charts -/

/-- The affine étale site of `F` is essentially small at the universe of the schemes: it is a
full subcategory of the small étale site, which is essentially small there
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`). -/
instance AffineEtale.instEssentiallySmall : EssentiallySmall.{u} (AffineEtale B S hS F) :=
  essentiallySmall_of_fully_faithful (AffineEtale.inclusion B S hS F)

/-- Sheaves of abelian groups on the affine étale site admit sheafification, transported from a
small model of the site. -/
instance AffineEtale.instHasSheafifyAddCommGrpCat :
    HasSheafify (AffineEtale.topology B S hS F) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On the affine étale site the morphisms of abelian sheaves inverted by sheafification are
exactly the locally bijective ones. -/
instance AffineEtale.instWEqualsLocallyBijectiveAddCommGrpCat :
    (AffineEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  .ofEssentiallySmall.{u} _


/-- **Restriction to the affine charts is an equivalence on sheaves of abelian groups** at the
universe of the schemes.

This is the Comparison Lemma for `AddCommGrpCat.{u}` along the dense subsite inclusion of
Stacks 04JS.  Its size input — that `AddCommGrpCat.{u}` has limits over the comma categories of
the inclusion — holds because those comma categories are essentially small at `u`, the affine
étale site being so. -/
theorem isEquivalence_affineEtaleRestriction_addCommGrpCat :
    (affineEtaleRestriction B S hS F hF AddCommGrpCat.{u}).IsEquivalence := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hl : ∀ X : (SmallEtale B S hS F)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (AffineEtale.inclusion B S hS F).op)
        AddCommGrpCat.{u} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  dsimp [affineEtaleRestriction]
  infer_instance

/-- The sheaf of rings of the affine étale site: the restriction to affine charts of the sheaf
of rings underlying the small étale structure sheaf. -/
noncomputable abbrev affineEtaleRingRestriction :
    Sheaf (AffineEtale.topology B S hS F) RingCat.{u} :=
  (affineEtaleRestriction B S hS F hF RingCat.{u}).obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- **Restriction of sheaves of modules to the affine charts of `F`.**  This is the functor
`Mod(𝒪_F) ⥤ Mod(F_{affine,étale}, 𝒪_F)` comparing the modules of category (1) with those of
category (2). -/
noncomputable def affineEtaleModuleRestriction :
    SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ⥤
      SheafOfModules.{u} (affineEtaleRingRestriction B S hS F hF) := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  exact Stacks.DenseSubsiteModules.moduleRestriction
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) _

/-- **Restriction of sheaves of modules to the affine charts is an equivalence of abelian
categories**, `Mod(𝒪_F) ≌ Mod(F_{affine,étale}, 𝒪_F)`.

This is the Comparison Lemma for sheaves of modules,
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`, along the dense subsite inclusion of
Stacks 04JS, with the abelian input supplied by
`AlgebraicGeometry.Space.isEquivalence_affineEtaleRestriction_addCommGrpCat`.  Its underlying
functor is `AlgebraicGeometry.Space.affineEtaleModuleRestriction`, by definition. -/
noncomputable def affineEtaleModuleRestrictionEquivalence :
    SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ≌
      SheafOfModules.{u} (affineEtaleRingRestriction B S hS F hF) := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have he : ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous AddCommGrpCat.{u}
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).IsEquivalence :=
    isEquivalence_affineEtaleRestriction_addCommGrpCat B S hS F hF
  exact Stacks.DenseSubsiteModules.moduleRestrictionEquivalence.{u}
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- The functor of the equivalence is restriction of modules to the affine charts. -/
theorem affineEtaleModuleRestrictionEquivalence_functor :
    (affineEtaleModuleRestrictionEquivalence B S hS F hF).functor =
      affineEtaleModuleRestriction B S hS F hF := rfl

/-- **Restriction of sheaves of modules to the affine charts is an equivalence.** -/
theorem isEquivalence_affineEtaleModuleRestriction :
    (affineEtaleModuleRestriction B S hS F hF).IsEquivalence :=
  (affineEtaleModuleRestrictionEquivalence B S hS F hF).isEquivalence_functor

/-- **Restriction to the affine charts carries quasi-coherence.**  The restriction of a
quasi-coherent sheaf of `𝒪_F`-modules to the affine étale charts, over the restricted structure
sheaf, is quasi-coherent.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`, i.e. Stacks 03DM for clause
(6) of Stacks 03DL in the dense-subsite form, applied to the inclusion of Stacks 04JS: the
inclusion is continuous and cocontinuous, and its localizations are dense subsite inclusions by
`Stacks.Sites.overPost_isDenseSubsite`, so the structure map of the comparison is the identity
and no comparison of structure sheaves is involved. -/
theorem isQuasicoherentOnSite_affineEtaleModuleRestriction
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (hM : M.IsQuasicoherentOnSite) :
    ((affineEtaleModuleRestriction B S hS F hF).obj M).IsQuasicoherentOnSite := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hc : (AffineEtale.inclusion B S hS F).IsCocontinuous
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).1
  have hcont : (AffineEtale.inclusion B S hS F).IsContinuous
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) := inferInstance
  have hover : ∀ X : AffineEtale B S hS F,
      (Over.post (X := X) (AffineEtale.inclusion B S hS F)).IsContinuous
        ((AffineEtale.topology B S hS F).over X)
        ((SmallEtale.topology B S hS F).over
          ((AffineEtale.inclusion B S hS F).obj X)) := fun X ↦
    have : (Over.post (X := X) (AffineEtale.inclusion B S hS F)).IsDenseSubsite
        ((AffineEtale.topology B S hS F).over X)
        ((SmallEtale.topology B S hS F).over
          ((AffineEtale.inclusion B S hS F).obj X)) :=
      Stacks.Sites.overPost_isDenseSubsite (AffineEtale.inclusion B S hS F) X
    inferInstance
  exact @Stacks.SheafOfModules.isQuasicoherentOnSite_restriction.{u + 1, u, u, u}
    (SmallEtale B S hS F) (AffineEtale B S hS F) _ _
    (SmallEtale.topology B S hS F) (AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) hcont hc hover
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) M hM

/-! ### Categories (1) and (2): the derived comparison -/

/-- Restriction of sheaves of modules to the affine charts is additive: it is
`SheafOfModules.pushforward`, which is computed objectwise on sections. -/
instance additive_affineEtaleModuleRestriction :
    (affineEtaleModuleRestriction B S hS F hF).Additive := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (smallEtaleRingedSite B S hS F hF).J :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  exact { map_add := fun {_ _ _ _} ↦ rfl }

/-- Restriction of sheaves of modules to the affine charts preserves finite limits, being an
equivalence. -/
instance preservesFiniteLimits_affineEtaleModuleRestriction :
    PreservesFiniteLimits (affineEtaleModuleRestriction B S hS F hF) := by
  have := isEquivalence_affineEtaleModuleRestriction B S hS F hF
  infer_instance

/-- Restriction of sheaves of modules to the affine charts preserves finite colimits, being an
equivalence. -/
instance preservesFiniteColimits_affineEtaleModuleRestriction :
    PreservesFiniteColimits (affineEtaleModuleRestriction B S hS F hF) := by
  have := isEquivalence_affineEtaleModuleRestriction B S hS F hF
  infer_instance

/-- **Restriction to the affine charts induces an equivalence of the unbounded derived
categories** of `𝒪_F`-modules.

The equivalence of abelian categories
`AlgebraicGeometry.Space.affineEtaleModuleRestrictionEquivalence` is exact, both directions of an
equivalence preserving all limits and colimits, so
`Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` applies. -/
noncomputable def affineEtaleDerivedRestrictionEquivalence :
    DerivedCategory
        (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) ≌
      DerivedCategory (SheafOfModules.{u} (affineEtaleRingRestriction B S hS F hF)) :=
  have : (affineEtaleModuleRestrictionEquivalence B S hS F hF).functor.Additive :=
    additive_affineEtaleModuleRestriction B S hS F hF
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (affineEtaleModuleRestrictionEquivalence B S hS F hF)

/-- **Categories (1) and (2) of Stacks 0H06 agree**, over the single named input `hrefl`.

Restriction to the affine étale charts is an equivalence of the unbounded derived categories of
`𝒪_F`-modules (`AlgebraicGeometry.Space.affineEtaleDerivedRestrictionEquivalence`), and under it
a complex has quasi-coherent cohomology exactly when its restriction does; so it identifies
`D_QCoh(𝒪_F)` with `D_QCoh(F_{affine,étale}, 𝒪_F)`.

One direction of the identification of quasi-coherence is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleModuleRestriction`, proved above; the
other is the hypothesis `hrefl`, a statement about single modules and therefore the degree-zero
part of the conclusion rather than the conclusion itself.  The passage from modules to complexes
is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which identifies the cohomology
sheaves of the restricted complex with the restrictions of the cohomology sheaves. -/
theorem derivedCategoryB_isQuasicoherentOnSite_affineEtaleRestriction_iff
    (hrefl : ∀ M : SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)),
      ((affineEtaleModuleRestriction B S hS F hF).obj M).IsQuasicoherentOnSite →
        M.IsQuasicoherentOnSite)
    (K : DerivedCategory
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))) :
    DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite (affineEtaleRingRestriction B S hS F hF))
        ((affineEtaleDerivedRestrictionEquivalence B S hS F hF).functor.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) K := by
  have hadd : (affineEtaleModuleRestriction B S hS F hF).Additive :=
    additive_affineEtaleModuleRestriction B S hS F hF
  have hcomp := fun n : ℤ ↦
    (CategoryTheory.Functor.mapDerivedCategoryHomologyIso
      (affineEtaleModuleRestriction B S hS F hF) n).app K
  refine ⟨fun h n ↦ hrefl _ ?_, fun h n ↦ ?_⟩
  · exact ObjectProperty.prop_of_iso _ (hcomp n) (h n)
  · exact ObjectProperty.prop_of_iso _ (hcomp n).symm
      (isQuasicoherentOnSite_affineEtaleModuleRestriction B S hS F hF _ (h n))

/-- Category (2) of Stacks 0H06: `D_QCoh(F_{affine,étale}, 𝒪_F)`, the full subcategory of the
unbounded derived category of modules on the affine étale site all of whose cohomology sheaves
are quasi-coherent. -/
noncomputable abbrev affineEtaleQuasicoherentDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite
        (affineEtaleRingRestriction B S hS F hF))).FullSubcategory

/-- `D_QCoh(F_{affine,étale}, 𝒪_F)` is closed under isomorphisms in the derived category: a
cohomology sheaf of an object isomorphic to a given one is isomorphic to the corresponding
cohomology sheaf, and quasi-coherence is closed under isomorphisms. -/
theorem isClosedUnderIsomorphisms_derivedCategoryB_affineEtale :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite
          (affineEtaleRingRestriction B S hS F hF))).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e hX n ↦
    (inferInstance : (SheafOfModules.isQuasicoherentOnSite
        (affineEtaleRingRestriction B S hS F hF)).IsClosedUnderIsomorphisms).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hX n)⟩

/-- **Categories (1) and (2) of Stacks 0H06 are equivalent**, over the single named input
`hrefl`: restriction to the affine étale charts is an exact equivalence

`D_QCoh(𝒪_F) ⟶ D_QCoh(F_{affine,étale}, 𝒪_F)`.

It is the equivalence of unbounded derived categories
`AlgebraicGeometry.Space.affineEtaleDerivedRestrictionEquivalence`, which is triangulated, cut
down to the two full subcategories by
`AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_affineEtaleRestriction_iff`; so
the comparison is the canonical one, being the restriction of the derived restriction functor,
and not merely some equivalence.  See the module docstring for the status of `hrefl`. -/
noncomputable def quasicoherentDerivedAffineEtaleEquivalence
    (hrefl : ∀ M : SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)),
      ((affineEtaleModuleRestriction B S hS F hF).obj M).IsQuasicoherentOnSite →
        M.IsQuasicoherentOnSite) :
    QuasicoherentDerivedCategory.{u, u} B S hS F hF ≌
      affineEtaleQuasicoherentDerivedCategory B S hS F hF :=
  have := isClosedUnderIsomorphisms_derivedCategoryB_affineEtale B S hS F hF
  (affineEtaleDerivedRestrictionEquivalence B S hS F hF).congrFullSubcategory
    (funext fun K ↦ propext
      (derivedCategoryB_isQuasicoherentOnSite_affineEtaleRestriction_iff B S hS F hF hrefl K))

end AlgebraicGeometry.Space

end
