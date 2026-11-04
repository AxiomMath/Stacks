module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSheafTopology
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdequacy
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.UniversalQuasiIso
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasiCoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves

/-!
# The inputs of Tag 06ZR over an affine base, supplied

[Stacks, Tag 06ZR] is stated in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/DerivedLocalization.lean` as
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`, over
seven inputs, and in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedModuleAdequacy.lean` as
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv`,
with the two inputs of [Stacks, Tag 06VK] discharged and five left. This module supplies the
four structural ones, leaving only the source's opening sentence `huniv`:

* the abelian structure of `Adeq(𝒪)` on the chosen big fppf site over an affine base, which is
  [Stacks, Tag 06VQ] (1), `Stacks.Adequate.abelian_adequate`;
* the abelian structure of `QCoh(𝒪_U)`, which is [Stacks, Tag 01IC] and is
  `Stacks.DerivedQCoh.abelianQuasiCoherent`;
* the additivity of the inclusion of `QCoh(𝒪_U)`, which the inherited preadditive structure
  gives outright;
* the additivity of `u : QCoh(𝒪_U) ⥤ Adeq(𝒪)`, which is
  `Stacks.Adequate.BigSite.additive_associatedModuleAdeq`.

## Main definitions

* `Stacks.Adequate.BigSite.abelianAdequateAffine` — the abelian structure of `Adeq(𝒪)` over an
  affine base, [Stacks, Tag 06VQ] (1) with its hypothesis discharged. Every use of the abelian
  structure of `Adeq(𝒪)` below is routed through this one name.

## Main results

* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_huniv` —
  [Stacks, Tag 06ZR] over the single remaining input `huniv`.
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic`
  — the same over that input read on objects: a complex is universally acyclic exactly when its
  associated complex of adequate modules is acyclic.
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_Qh` —
  the general form of [Stacks, Tag 06ZR] read in Mathlib's model `DerivedCategory.Plus`.
* `Stacks.Adequate.BigSite.plus_subcategoryAcyclic_adequate_eq_inverseImage` — the `Adeq(𝒪)`
  half of that remaining input, with no hypothesis: a bounded below complex of adequate
  `𝒪`-modules is acyclic exactly when its complex of affine-section functors is. This moves the
  right-hand side of `hacyc` off the adequate modules and onto the sections over the affines of
  the site. What is still missing is the identification of those sections, for a complex in the
  image of `u`, with the pullbacks of the complex of quasi-coherent modules, and the passage
  from the affines of the site to all schemes over `Spec A`.

## Implementation notes

**Why a new module.** `DerivedLocalization.lean` removes
`CategoryTheory.Preadditive.fullSubcategory` from instance search inside its `Affine` section,
so that the preadditive structure there is the one underlying its *assumed* abelian structures;
and adding imports to that file has broken it before, because an import can change which
preadditive structure instance search finds. Nothing here edits it. The abelian structure
supplied below is the one built on the *inherited* preadditive structure
(`CategoryTheory.Preadditive.fullSubcategory` is `(abelianAdequateAffine B hS).toPreadditive` on
the nose, by `rfl`, and likewise for `Stacks.DerivedQCoh.abelianQuasiCoherent`), which is the
structure the triangulated results of `UniversalQuasiIso.lean` are stated with. So the two
sections' terms are elaborated against one and the same preadditive structure and the
instantiation is type-correct with no transport.

**The universe.** `Stacks.Adequate.abelian_adequate` is stated at `.{u, u}`, which is the universe
[Stacks, Tag 06ZR] is stated at here: `adequate.{u, u}`. The universe arguments are written out
because `max u ?m =?= u` is not solvable by unification.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Adequate

section Affine

variable {A : CommRingCat.{u}} (B : BigFppfSite.{u}) (hS : B.Contains (Spec A))

/-! ### The abelian structure of `Adeq(𝒪)` over an affine base -/

/-- **[Stacks, Tag 06VQ] (1) over an affine base, with no hypothesis.** The adequate
`𝒪`-modules on the chosen big fppf site over `U = Spec A` form an abelian category.

This is `Stacks.Adequate.abelian_adequate` at this site. The additive structure is the one a full
subcategory inherits from its ambient category, by
`Stacks.Adequate.BigSite.abelianAdequateAffine_toPreadditive`. -/
@[instance_reducible]
public noncomputable def BigSite.abelianAdequateAffine :
    Abelian (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory :=
  abelian_adequate.{u} (BigSite.ofBigFppfSite B (Spec A) hS)

/-- The preadditive structure underlying `Stacks.Adequate.BigSite.abelianAdequateAffine` is the
one the full subcategory of adequate modules inherits from all `𝒪`-modules on the site. So the
results stated with the inherited structure — the pretriangulated structure of
`K⁺(Adeq(𝒪))` among them — apply to it with no transport. -/
public theorem BigSite.abelianAdequateAffine_toPreadditive :
    (BigSite.abelianAdequateAffine B hS).toPreadditive =
      CategoryTheory.Preadditive.fullSubcategory
        (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)) :=
  rfl

/-! ### Tag 06ZR over the source's opening sentence alone -/

attribute [local instance] BigSite.abelianAdequateAffine

/-- **[Stacks, Tag 06ZR] over the source's opening sentence alone.** Over an affine scheme
`U = Spec A` the bounded below derived category `D⁺(Adeq(𝒪))` is the localization of
`K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms, granted only `huniv`: that `uφ` is a
quasi-isomorphism exactly when `φ` is a universal quasi-isomorphism.

This is `BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv` with its
four structural inputs supplied — the abelian structure of `Adeq(𝒪)` by
`Stacks.Adequate.BigSite.abelianAdequateAffine`, that of `QCoh(𝒪_U)` by
`Stacks.DerivedQCoh.abelianQuasiCoherent`, and the two additivity inputs by instance search, the
second being `Stacks.Adequate.BigSite.additive_associatedModuleAdeq`. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_huniv
    (huniv : universalQuasiIso (Spec A) =
      (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory).inverseImage
        (BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq.mapHomotopyCategoryPlus) :
    ((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u}
            (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv
    (BigSite.ofBigFppfSite B (Spec A) hS) huniv

/-- **[Stacks, Tag 06ZR] over the source's opening sentence read on objects.** The same
conclusion as
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_huniv`,
over the weaker-to-prove hypothesis that a bounded below complex of quasi-coherent
`𝒪_U`-modules is universally acyclic exactly when its associated complex of adequate modules is
acyclic. Morphisms are reduced to objects by
`Stacks.Adequate.universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq`, which is
unconditional.

This is the shape in which the remaining input of [Stacks, Tag 06ZR] should be attacked: both
sides are object properties, and the source reads the identification off [Stacks, Tags 06VI and
06VM], both of which the library now has — 06VI unconditionally as
`Stacks.Adequate.isAdequate_affineSectionFunctor`. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic
    (hacyc : universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory).inverseImage
        (BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq.mapHomotopyCategoryPlus) :
    ((BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u}
            (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_huniv B hS
    (universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq _ hacyc)

/-! ### Acyclicity of a complex of adequate modules, read on the affine sections -/

/-- **A bounded below complex of adequate `𝒪`-modules over an affine base is acyclic exactly
when its complex of affine-section functors is**, with no hypothesis.

The affine-section functor is exact and reflects isomorphisms on `Adeq(𝒪)` — this is
`Stacks.Adequate.preservesHomology_affineSections` and
`Stacks.Adequate.reflectsIsomorphisms_affineSections`, both read off the equivalence of
[Stacks, Tag 06ZJ] — so `Stacks.Adequate.plus_subcategoryAcyclic_eq_inverseImage` applies.

This is the `Adeq(𝒪)` half of the hypothesis `hacyc` of
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_acyclic`:
it moves the acyclicity condition on the right-hand side off the adequate modules and onto
module-valued functors on the `A`-algebras of the site, where it is a condition on the sections
over each affine of the site. What it does *not* yet do is identify those sections for a complex
in the image of `u` with the pullbacks of the complex of quasi-coherent modules, nor pass from
the affines of the site to all schemes over `Spec A`; both of those remain. -/
public theorem BigSite.plus_subcategoryAcyclic_adequate_eq_inverseImage :
    HomotopyCategory.Plus.subcategoryAcyclic
        (adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).FullSubcategory =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctorOn.{u}
            (AdequateFunctor.siteAlgebraInclusion A
              (schemeSizeBelow (BigSite.ofBigFppfSite B (Spec A) hS).cutoff)))).inverseImage
        ((adequate.{u, u} (BigSite.ofBigFppfSite B (Spec A) hS)).ι ⋙
          affineSectionsFunctor (BigSite.ofBigFppfSite B (Spec A) hS) A
            (𝟙 (Spec A))).mapHomotopyCategoryPlus :=
  let := preservesHomology_affineSections (BigSite.ofBigFppfSite B (Spec A) hS)
  let := reflectsIsomorphisms_affineSections (BigSite.ofBigFppfSite B (Spec A) hS)
  plus_subcategoryAcyclic_eq_inverseImage _

end Affine

/-! ### The bounded below derived category in Mathlib's model -/

section MathlibModel

-- Inside this section the preadditive structure of a full subcategory is the one underlying the
-- assumed abelian structure, not the one induced from the ambient category.
attribute [-instance] CategoryTheory.Preadditive.fullSubcategory

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- [Stacks, Tag 06ZR] for Mathlib's model `D⁺(Adeq(𝒪))` of the bounded below derived category:
over an affine scheme `U = Spec A` the functor `K⁺(QCoh(𝒪_U)) ⥤ D⁺(Adeq(𝒪))` induced by the
associated module functor is a localization at the universal quasi-isomorphisms.

This is `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`
read in `DerivedCategory.Plus` rather than in the constructed localization
`MorphismProperty.Q`, under exactly the same hypotheses; the underlying result is stated for an
arbitrary localization of `K⁺(Adeq(𝒪))` at the quasi-isomorphisms, and `DerivedCategory.Plus.Qh`
is one. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_Qh
    [Abelian (adequate.{u, u} B).FullSubcategory]
    [Abelian (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory]
    [(SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι.Additive]
    [B.associatedModuleAdeq.Additive]
    [HasDerivedCategory.{w}
      (adequate.{u, u} B).FullSubcategory]
    (hmono : ∀ F : (adequate.{u, u} B).FullSubcategory,
      ∃ (G : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory)
        (i : F ⟶ B.associatedModuleAdeq.obj G), Mono i)
    (huniv : universalQuasiIso (Spec A) =
      (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory).inverseImage
        B.associatedModuleAdeq.mapHomotopyCategoryPlus) :
    (B.associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).IsLocalization (universalQuasiIso (Spec A)) := by
  have := B.full_associatedModuleAdeq
  have := B.faithful_associatedModuleAdeq
  exact Functor.isLocalization_mapHomotopyCategoryPlus_comp'
    B.associatedModuleAdeq hmono _ (universalQuasiIso (Spec A)) huniv

end MathlibModel

end Stacks.Adequate

end
