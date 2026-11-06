module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroCounitTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived trace map of an étale morphism is the counit of `Lj_! ⊣ j^{-1}`

Let `j : U ⟶ X` be an étale morphism of schemes, presented as an object of the small étale site
of `X` inside a big étale site. Remark 0GL4 says that the trace map `Tr : j_! j^{-1}K ⟶ K` of
Example 0GKI is the counit of the adjunction between `j_!` and `j^{-1}`, for `K` an object of
the *derived* category. This file proves that.

`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` is the statement for a single abelian
sheaf. Both `j_!` and `j^{-1}` are exact, so each descends to the unbounded derived category,
the family of sheaf-level trace maps descends to a natural transformation
`j_! j^{-1} ⟶ id` there — this is Stacks 0GKH part (3) — and the sheaf-level adjunction of
Stacks 03S3 descends to an adjunction of the descended functors. The content of this file is
that the two descents agree: deriving the counit of an adjunction of exact functors produces the
counit of the derived adjunction.

## Main results

* `CategoryTheory.Adjunction.mapDerivedCategory_counit` — **the counit of a derived adjunction is
  the derived counit.** For an adjunction `F ⊣ G` of exact functors of abelian categories with
  derived categories, the counit of the induced adjunction
  `CategoryTheory.Adjunction.mapDerivedCategory` of the derived functors is
  `CategoryTheory.NatTrans.mapDerivedCategoryCompToId` of the counit. This is the coherence
  statement which makes "the derived form of the trace" and "the counit of the derived
  adjunction" the same morphism.
* `AlgebraicGeometry.derivedWeightedTraceFamily_eq_derivedCounit` — **Stacks 0GL4 on the
  unbounded derived category of abelian étale sheaves.** The derived form of the family of trace
  maps of Example 0GKI is the counit of the adjunction between the derived functors of `j_!` and
  `j^{-1}`, and `AlgebraicGeometry.derivedWeightedTraceFamily_app_eq_derivedCounit_app` is the
  same statement at a fixed object `K` of the derived category.
* `AlgebraicGeometry.hasWeightedTraceStalksMod_counit` — for a `Λ`-linear adjunction lifting the
  one of Stacks 03S3, the counit is a trace map for the canonical weighting of `j` in the sense
  of Stacks 0GKH part (3), and
  `AlgebraicGeometry.hasWeightedTraceStalksMod_counit_etale` is that statement for the
  `Λ`-linear adjunction of
  `AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction`.
* `AlgebraicGeometry.hasWeightedTraceStalksMod_iff_eq_counit` — **Stacks 0GL4 at
  `Λ`-coefficients, on a single sheaf of `Λ`-modules.** A morphism `j_! j^{-1}M ⟶ M` of sheaves
  of `Λ`-modules is the trace map of Stacks 0GKH part (3) for the canonical weighting of `j` if
  and only if it is the counit of the `Λ`-linear adjunction `j_! ⊣ j^{-1}`.
* `AlgebraicGeometry.derivedWeightedTrace_eq_derivedCounit` — the same for an arbitrary
  `Λ`-linear lift of the inverse image and of the adjunction of Stacks 03S3, and
  `AlgebraicGeometry.derivedWeightedTrace_pullbackMod_eq_derivedCounit` is that statement at the
  lift constructed in this library, both of them for a trace family left general.
* `AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit` — **Stacks 0GL4 on
  `D(X_étale, Λ)`.** The derived trace `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` of
  Stacks 0GKH part (3), for an étale `j` and its canonical weighting, is the counit of the
  adjunction between the derived functors of the `Λ`-linear `j_!` and `j^{-1}`, and
  `AlgebraicGeometry.derivedWeightedTraceMod_app_eq_derivedCounit_app` is the same statement at
  a fixed object `K`, where it reads `Tr_{j, w, K} : j_! j^{-1}K ⟶ K` is the counit at `K`.

## Implementation notes

**Why a coherence lemma is needed.** The derived trace is, by definition,
`CategoryTheory.NatTrans.mapDerivedCategoryCompToId` of the sheaf-level trace: the derived form
of the sheaf-level transformation, read through the identification of the derived functor of
`j^{-1} ⋙ j_!` with the composite of the derived functors and of the derived functor of `𝟭`
with `𝟭`. The counit of the derived adjunction is instead produced by
`CategoryTheory.Adjunction.localization`, which lifts the degreewise adjunction on cochain
complexes through the two localizations. Neither is defined through the other, so the identity
between them is proved rather than unfolded: both transformations are lifts through
`DerivedCategory.Q`, so `CategoryTheory.Localization.natTrans_ext` reduces the comparison to the
objects `Q.obj P`, where `CategoryTheory.Adjunction.localization_counit_app` computes one side
and `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app_Q` the other, and the two agree once
the three comparison isomorphisms involved are evaluated at `Q.obj P`. Those evaluations are
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso_inv_app_Q` and
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_comp_mapDerivedCategoryIdIso_hom` below;
the second goes through the homotopy category, because
`CategoryTheory.Functor.mapDerivedCategoryIdIso` is lifted through `DerivedCategory.Qh` rather
than through `DerivedCategory.Q`.

**Coefficient universes.** The abelian statements are at `AddCommGrpCat.{u + 1}`, which is where
the adjunction `AlgebraicGeometry.etaleFShriekAbPullbackAdjunction` of Stacks 03S3 is carried in
this library, and the `Λ`-linear ones at `ModuleSheaf.{u, u + 1, u}` with `Λ : Type u`, which is
where Stacks 0GKH part (3) is carried. No base change enters Remark 0GL4, so the universe is
forced only by those two inputs. The universe of the derived category itself is arbitrary.

**The instances for the exactness of `j_!` and `j^{-1}`**, abelian and `Λ`-linear, are declared
file-locally with their universes written out. The general statements
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_abPullback` and its companions quantify over
a coefficient universe `v` entering only through `max (u + 1) v`, and at `v = u + 1` that
constraint no longer determines `v`, so instance resolution reports it as stuck.

**The `Λ`-linear data.** As in Stacks 0GKH part (3), the `Λ`-linear inverse image is a functor on
sheaves of `Λ`-modules together with an isomorphism identifying it with the abelian `j^{-1}` on
underlying abelian sheaves, and the `Λ`-linear adjunction is an adjunction between the `Λ`-linear
functors whose counit is the abelian counit of Stacks 03S3 on underlying abelian sheaves. Both
are built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction`, for
an arbitrary coefficient ring: `AlgebraicGeometry.SmallEtale.pullbackMod` is the `Λ`-linear lift
of the abelian `j^{-1}`, and `AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction` is
the lift of the abelian adjunction, whose counit is the abelian counit by construction. The
identification of the two counits is not a formal consequence of the rest of the data —
adjunctions between a fixed pair of functors are not unique, and forgetting the module structure,
being faithful but not full, does not transport hom-set bijections — which is why it is read off
the construction of the adjunction rather than deduced from it.

The statements with the `Λ`-linear inverse image, the adjunction and the family of sheaf-level
trace maps left general are kept, since the derived comparison uses nothing of the particular
constructions: `AlgebraicGeometry.derivedWeightedTrace_eq_derivedCounit` leaves all three
general and `AlgebraicGeometry.derivedWeightedTrace_pullbackMod_eq_derivedCounit` leaves the
trace family general. `AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit`, the
statement of the remark, is their instance at the constructed data, where the comparison of the
two counits is a theorem rather than an input and the derived trace is
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` rather than a hypothesis of the
statement.

## References

* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w₁ w₂ u t

namespace Stacks.Cohomology.PerfectComplexTriangles

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

/-- **The comparison of the derived functor of a composite with the composite of the derived
functors, at the image of a cochain complex.** Each of the three derived functors involved is a
lift through the localization, and on the image of the localization the comparison is the chain
of their canonical factorizations. -/
public theorem mapDerivedCategoryCompIso_inv_app_Q (G : D ⥤ C) (F : C ⥤ D)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex D ℤ) :
    (mapDerivedCategoryCompIso G F).inv.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (G ⋙ F).mapDerivedCategoryFactors.inv.app P := by
  have hrefl : DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Iso.refl (G ⋙ F)) (ComplexShape.up ℤ)).hom.app P) =
      𝟙 (DerivedCategory.Q.obj (((G ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
    have h0 : (NatIso.mapHomologicalComplex (Iso.refl (G ⋙ F)) (ComplexShape.up ℤ)).hom.app P =
        𝟙 _ := by
      ext i
      simp
    rw [h0]
    exact CategoryTheory.Functor.map_id _ _
  simp only [mapDerivedCategoryCompIso, Localization.Lifting.iso,
    Functor.mapHomologicalComplexCompIso, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.associator_inv_app,
    Functor.associator_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [hrefl]
  exact congrArg (fun k => F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫ k)
    (Category.id_comp ((G ⋙ F).mapDerivedCategoryFactors.inv.app P))

end Stacks.Cohomology.PerfectComplexTriangles

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

/-- **The derived functor of `𝟭` is identified with `𝟭` by the canonical factorization.** The
isomorphism `CategoryTheory.Functor.mapDerivedCategoryIdIso` is lifted through the localization
of the homotopy category, so its value on the image of `DerivedCategory.Q` is reached by
naturality against the comparison `DerivedCategory.quotientCompQhIso` of the two localizations;
there the factorization of `𝟭` through the homotopy category cancels it. -/
public theorem Functor.mapDerivedCategoryFactors_inv_comp_mapDerivedCategoryIdIso_hom
    (P : CochainComplex C ℤ) :
    (𝟭 C).mapDerivedCategoryFactors.inv.app P ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) = 𝟙 _ := by
  have hnat := (Functor.mapDerivedCategoryIdIso C).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app P)
  have hQh := Functor.mapDerivedCategoryIdIso_hom_app_Qh
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)
  have hfh := (𝟭 C).mapDerivedCategoryFactorsh_hom_app P
  rw [hfh] at hQh
  simp only [Functor.comp_obj, Functor.id_map] at hnat
  rw [hQh] at hnat
  have key := (IsIso.eq_inv_comp _).2 hnat
  have hid : ((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app P ≫
        (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) = 𝟙 _ := by
    have hmhc : (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app
        (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P).as) = 𝟙 _ := by
      ext i
      simp
    simp only [comp_obj, id_obj, mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      mapHomotopyCategoryIdIso, Quotient.natIsoLift, Quotient.natTransLift, isoWhiskerRight_hom,
      whiskerRight_app, isoWhiskerRight_inv, hmhc, map_id]
    exact Category.comp_id _
  rw [key]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, hid]
  simp only [comp_obj, id_obj, map_id, Category.id_comp]
  exact (DerivedCategory.quotientCompQhIso C).inv_hom_id_app P

/-- **The counit of a derived adjunction is the derived counit.** For an adjunction `F ⊣ G` of
exact functors of abelian categories with derived categories, the counit of the adjunction
`CategoryTheory.Adjunction.mapDerivedCategory` between the derived functors is the derived form
of the counit `G ⋙ F ⟶ 𝟭`.

Both sides are natural transformations out of `D(G) ⋙ D(F)`, hence determined by their values on
the image of `DerivedCategory.Q`; there each is the degreewise counit conjugated by canonical
comparisons, and the comparisons match. -/
public theorem Adjunction.mapDerivedCategory_counit {F : C ⥤ D} {G : D ⥤ C}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    (Adjunction.mapDerivedCategory adj).counit =
      NatTrans.mapDerivedCategoryCompToId G F adj.counit := by
  refine (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) fun P => ?_).symm
  rw [NatTrans.mapDerivedCategoryCompToId_app_Q,
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso_inv_app_Q,
    Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryFactors_inv_comp_mapDerivedCategoryIdIso_hom]
  simp
  rfl

end CategoryTheory

namespace AlgebraicGeometry

open SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- The inverse image of abelian étale sheaves along the structure morphism of an object of the
small étale site preserves finite limits, at the coefficient universe at which Stacks 03S3 is
carried here. -/
local instance preservesFiniteLimits_etaleAbPullback :
    PreservesFiniteLimits (abPullback.{u, u + 1} B U.obj.hom) :=
  preservesFiniteLimits_abPullback.{u, u + 1} B U.obj.hom

/-- The inverse image of abelian étale sheaves along the structure morphism of an object of the
small étale site preserves finite colimits. -/
local instance preservesFiniteColimits_etaleAbPullback :
    PreservesFiniteColimits (abPullback.{u, u + 1} B U.obj.hom) :=
  preservesFiniteColimits_abPullback.{u, u + 1} B U.obj.hom

/-- The inverse image of abelian étale sheaves along the structure morphism of an object of the
small étale site is additive. -/
local instance additive_etaleAbPullback : (abPullback.{u, u + 1} B U.obj.hom).Additive :=
  additive_abPullback.{u, u + 1} B U.obj.hom

/-- The direct image with compact support along the structure morphism of an object of the small
étale site preserves finite limits, at the coefficient universe used here. -/
local instance preservesFiniteLimits_etaleFShriek :
    PreservesFiniteLimits (fShriekFunctor.{u, u + 1} B U.obj.hom) :=
  fShriekFunctor_preservesFiniteLimits.{u, u + 1} B U.obj.hom

/-- The direct image with compact support along the structure morphism of an object of the small
étale site preserves finite colimits. -/
local instance preservesFiniteColimits_etaleFShriek :
    PreservesFiniteColimits (fShriekFunctor.{u, u + 1} B U.obj.hom) :=
  fShriekFunctor_preservesFiniteColimits.{u, u + 1} B U.obj.hom

/-- The direct image with compact support along the structure morphism of an object of the small
étale site is additive. -/
local instance additive_etaleFShriek : (fShriekFunctor.{u, u + 1} B U.obj.hom).Additive :=
  fShriekFunctor_additive.{u, u + 1} B U.obj.hom

section Abelian

variable [HasDerivedCategory.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{t}
    (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})]

variable (τ : ∀ F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1},
    (fShriekFunctor.{u, u + 1} B U.obj.hom).obj
      ((abPullback.{u, u + 1} B U.obj.hom).obj F) ⟶ F)
  (hτ : ∀ F, HasWeightedTraceStalks.{u, u + 1} B U.obj.hom
    (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F (τ F))

/-- **Stacks 0GL4 on the unbounded derived category of abelian étale sheaves.** Let
`j : U ⟶ X` be étale and let `τ` be the family of trace maps of Example 0GKI, that is a morphism
`j_! j^{-1}ℱ ⟶ ℱ` for each abelian étale sheaf `ℱ` on `X` with the behaviour on geometric stalks
by which Lemma 0GKG characterises the trace for the canonical weighting of Stacks 0F3D. Both
`j_!` and `j^{-1}` are exact, so the family descends to a natural transformation
`j_! j^{-1} ⟶ id` of the unbounded derived category, and the adjunction of Stacks 03S3 descends
to an adjunction of the descended functors. Then the descended trace is the counit of the
descended adjunction.

The weighting hypothesis of Stacks 0GKG is not needed and the trace maps are not assumed to
exist: the counit itself is such a family, by
`AlgebraicGeometry.hasWeightedTraceStalks_counit`. -/
@[stacks 0GL4 "At derived coefficients, on the unbounded derived category of abelian étale \
sheaves: for an étale j the derived form of the family of trace maps of Example 0GKI -- each of \
them characterised on geometric stalks by Lemma 0GKG for the canonical weighting of 0F3D -- is \
the counit of the adjunction between the derived functors of j_! and j^{-1}, which is the \
derived form of the adjunction of Stacks 03S3. Both descents are constructed here: the trace by \
`CategoryTheory.NatTrans.mapDerivedCategoryCompToId` as in 0GKH part (3), the adjunction by \
`CategoryTheory.Adjunction.mapDerivedCategory`, and they are compared by the coherence lemma \
`CategoryTheory.Adjunction.mapDerivedCategory_counit`. The sheaf-level input is \
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit`. Coefficients in \
AddCommGrpCat.{u + 1}, the universe at which 03S3 is available here; the universe of the \
derived category is arbitrary."]
public theorem derivedWeightedTraceFamily_eq_derivedCounit :
    NatTrans.mapDerivedCategoryCompToId (abPullback.{u, u + 1} B U.obj.hom)
        (fShriekFunctor.{u, u + 1} B U.obj.hom)
        (weightedTraceFamilyNatTrans.{u, u + 1} B U.obj.hom
          (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ) =
      (Adjunction.mapDerivedCategory (etaleFShriekAbPullbackAdjunction B X hX U)).counit := by
  have heq : weightedTraceFamilyNatTrans.{u, u + 1} B U.obj.hom
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit :=
    NatTrans.ext (funext fun F => hasWeightedTraceStalks_unique.{u, u + 1} B U.obj.hom
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) F (hτ F)
      (hasWeightedTraceStalks_counit B X hX U F))
  rw [heq]
  exact (Adjunction.mapDerivedCategory_counit _).symm

/-- **Stacks 0GL4 at a fixed object of the derived category.** The component at `K` of the
derived trace is the component at `K` of the counit of the derived adjunction: the morphism
`Tr : j_! j^{-1}K ⟶ K` of Remark 0GL4 is the counit at `K`. -/
public theorem derivedWeightedTraceFamily_app_eq_derivedCounit_app
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})) :
    (NatTrans.mapDerivedCategoryCompToId (abPullback.{u, u + 1} B U.obj.hom)
          (fShriekFunctor.{u, u + 1} B U.obj.hom)
          (weightedTraceFamilyNatTrans.{u, u + 1} B U.obj.hom
            (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ)).app K =
      (Adjunction.mapDerivedCategory
        (etaleFShriekAbPullbackAdjunction B X hX U)).counit.app K :=
  NatTrans.congr_app (derivedWeightedTraceFamily_eq_derivedCounit B X hX U τ hτ) K

end Abelian

section Module

variable (Λ : Type u) [Ring Λ]

/-- Sheafification of presheaves of `Λ`-modules on the small étale site of the base, with the
base written as a scheme together with its containment rather than as an object of the big étale
site. In that spelling the general instance
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf` cannot be matched: its object argument
occurs only under the two projections, which instance resolution cannot invert. -/
local instance hasSheafify_moduleSheaf_base :
    HasSheafify (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, u + 1, u} B (B.obj X hX) Λ

/-- Sheaves of `Λ`-modules on the small étale site of the base form a Grothendieck abelian
category, in the spelling of the base used here. -/
local instance isGrothendieckAbelian_moduleSheaf_base :
    IsGrothendieckAbelian.{u + 1} (ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :=
  isGrothendieckAbelian_moduleSheaf.{u, u + 1, u} B (B.obj X hX) Λ

/-- The `Λ`-linear direct image with compact support along the structure morphism of an object of
the small étale site preserves finite limits, at the coefficient universes used here. -/
local instance preservesFiniteLimits_etaleFShriekMod :
    PreservesFiniteLimits (fShriekMod.{u, u + 1, u} B Λ U.obj.hom) :=
  fShriekMod_preservesFiniteLimits.{u, u + 1, u} B Λ U.obj.hom

/-- The `Λ`-linear direct image with compact support along the structure morphism of an object of
the small étale site preserves finite colimits. -/
local instance preservesFiniteColimits_etaleFShriekMod :
    PreservesFiniteColimits (fShriekMod.{u, u + 1, u} B Λ U.obj.hom) :=
  fShriekMod_preservesFiniteColimits.{u, u + 1, u} B Λ U.obj.hom

/-- The `Λ`-linear direct image with compact support along the structure morphism of an object of
the small étale site is additive. -/
local instance additive_etaleFShriekMod : (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).Additive :=
  fShriekMod_additive.{u, u + 1, u} B Λ U.obj.hom

/-- The `Λ`-linear inverse image along the structure morphism of an object of the small étale
site preserves finite limits, at the coefficient universes used here. -/
local instance preservesFiniteLimits_etalePullbackMod :
    PreservesFiniteLimits (pullbackMod.{u, u + 1, u} B Λ U.obj.hom) :=
  pullbackMod_preservesFiniteLimits.{u, u + 1, u} B Λ U.obj.hom

/-- The `Λ`-linear inverse image along the structure morphism of an object of the small étale
site preserves finite colimits. -/
local instance preservesFiniteColimits_etalePullbackMod :
    PreservesFiniteColimits (pullbackMod.{u, u + 1, u} B Λ U.obj.hom) :=
  pullbackMod_preservesFiniteColimits.{u, u + 1, u} B Λ U.obj.hom

/-- The `Λ`-linear inverse image along the structure morphism of an object of the small étale
site is additive. -/
local instance additive_etalePullbackMod :
    (pullbackMod.{u, u + 1, u} B Λ U.obj.hom).Additive :=
  pullbackMod_additive.{u, u + 1, u} B Λ U.obj.hom

variable (modPull : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ ⥤
    ModuleSheaf.{u, u + 1, u} B U.obj.left Λ)
  (hpull : modPull ⋙ forgetModuleSheaf.{u, u + 1, u} B U.obj.left Λ ≅
    forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ ⋙ abPullback.{u, u + 1} B U.obj.hom)
  (adjMod : fShriekMod.{u, u + 1, u} B Λ U.obj.hom ⊣ modPull)

/-- **The counit of a `Λ`-linear lift of the adjunction of Stacks 03S3 is a trace map.** If the
morphism of abelian sheaves underlying the counit of `adjMod` is, through the identification of
`AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso`, the counit of the adjunction
`j_! ⊣ j^{-1}` of abelian sheaves, then the counit has at each sheaf of `Λ`-modules the
behaviour on geometric stalks by which Lemma 0GKG characterises the trace map of Example 0GKI
for the canonical weighting of `j`. This is `AlgebraicGeometry.hasWeightedTraceStalks_counit`
read at `Λ`-coefficients, and it shows that the family of trace maps of Stacks 0GKH part (3) is
the family of counits. -/
public theorem hasWeightedTraceStalksMod_counit
    (hadj : ∀ M, forgetModTrace.{u, u + 1, u} B Λ U.obj.hom modPull hpull M
        (adjMod.counit.app M) =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit.app
        ((forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).obj M))
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :
    HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom modPull hpull
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M (adjMod.counit.app M) := by
  show HasWeightedTraceStalks.{u, u + 1} B U.obj.hom _ _ _
  rw [hadj M]
  exact hasWeightedTraceStalks_counit B X hX U _

/-- **The counit of the `Λ`-linear adjunction `j_! ⊣ j^{-1}` is a trace map.** For an étale `j`
and a ring `Λ`, the counit of
`AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction` has at each sheaf of
`Λ`-modules the behaviour on geometric stalks by which Lemma 0GKG characterises the trace map of
Stacks 0GKH part (3) for the canonical weighting of `j`. Together with
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` this says that the family of
trace maps at `Λ`-coefficients exists and is the family of counits. -/
@[sga "4 XVIII 3.1.8" "(iii)"]
public theorem hasWeightedTraceStalksMod_counit_etale
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :
    HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom
      (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
      (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M
      ((etaleFShriekModPullbackAdjunction B X hX U Λ).counit.app M) :=
  hasWeightedTraceStalksMod_counit B X hX U Λ _ _ _
    (forgetModTrace_etaleFShriekModPullbackAdjunction_counit B X hX U Λ) M

/-- **Stacks 0GL4 at `Λ`-coefficients, on a single sheaf of `Λ`-modules.** For an étale `j`, a
ring `Λ` and a sheaf of `Λ`-modules `M` on the small étale site of `X`, a morphism
`τ : j_! j^{-1}M ⟶ M` is the trace map of Stacks 0GKH part (3) for the canonical weighting of
`j` — that is, the morphism of abelian sheaves underlying it has the behaviour on geometric
stalks prescribed by Lemma 0GKG — if and only if it is the counit of the `Λ`-linear adjunction
`j_! ⊣ j^{-1}` at `M`. The backward direction produces the trace map, so the equivalence also
says that the trace map exists. -/
@[stacks 0GL4 "At Lambda-coefficients on a single sheaf of Lambda-modules, for an arbitrary \
ring Lambda: a morphism j_!j^{-1}M ⟶ M of sheaves of Lambda-modules is the trace map of 0GKH \
part (3) for the canonical weighting of 0F3D -- its underlying morphism of abelian sheaves \
having the behaviour on geometric stalks prescribed by 0GKG -- if and only if it is the counit \
of the Lambda-linear adjunction \
`AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction` at M. The backward direction \
is the existence of the trace map at Lambda-coefficients, the forward direction is the \
remark. The Lambda-linear form of \
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit`.",
  sga "4 IX 5.1" "more general",
  sga "4 XVII 6.2.11" "more general",
  sga "4 XVIII 3.1.8" "(iii), special case",
  sga "4½ Dualite 2.3" "special case"]
public theorem hasWeightedTraceStalksMod_iff_eq_counit
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ)
    (τ : (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).obj
      ((pullbackMod.{u, u + 1, u} B Λ U.obj.hom).obj M) ⟶ M) :
    HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom
        (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
        (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M τ ↔
      τ = (etaleFShriekModPullbackAdjunction B X hX U Λ).counit.app M := by
  refine ⟨fun h => hasWeightedTraceStalksMod_unique.{u, u + 1, u} B Λ U.obj.hom
      (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
      (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom) _ M h
      (hasWeightedTraceStalksMod_counit_etale B X hX U Λ M), fun h => ?_⟩
  rw [h]
  exact hasWeightedTraceStalksMod_counit_etale B X hX U Λ M

variable [modPull.Additive] [PreservesFiniteLimits modPull] [PreservesFiniteColimits modPull]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B U.obj.left Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ)]

/-- **Remark 0GL4 on `D(X_étale, Λ)`, for an arbitrary `Λ`-linear lift of the adjunction.** Let
`j : U ⟶ X` be étale, let `Λ` be a ring, and take for `j^{-1}` on sheaves of `Λ`-modules a
functor together with an isomorphism identifying it with the abelian `j^{-1}` of Stacks 03Q1 on
underlying abelian sheaves, as Stacks 0GKH part (3) does. Take moreover an adjunction between
the `Λ`-linear `j_!` and that `j^{-1}` whose counit has the counit of the adjunction
`j_! ⊣ j^{-1}` of Stacks 03S3 as its underlying morphism of abelian sheaves, so that it is a
lift of the adjunction of Stacks 03S3. Let `τ` be the family of trace maps of Stacks 0GKH part
(3) for the canonical weighting of `j`, that is a morphism `j_! j^{-1}M ⟶ M` for each sheaf of
`Λ`-modules whose underlying morphism of abelian sheaves has the behaviour on geometric stalks
by which Lemma 0GKG characterises the trace. Then the derived trace
`Tr_{j, w} : j_! j^{-1} ⟶ id` of `D(X_étale, Λ)` built from `τ` is the counit of the adjunction
between the derived functors of the `Λ`-linear `j_!` and `j^{-1}`; in particular, for each `K`
the trace map `Tr_{j, w, K} : j_! j^{-1}K ⟶ K` is the counit at `K`.

The family `τ` is not assumed to exist: the family of counits is such a family, by
`AlgebraicGeometry.hasWeightedTraceStalksMod_counit`, and by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` there is at most one such
morphism for each sheaf of `Λ`-modules, so `τ` is the family of trace maps.

`AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit` is this statement at the
`Λ`-linear inverse image and adjunction built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction`,
where the comparison of the two counits is a theorem. -/
@[sga "4 XVII 6.2.11" "more general",
  sga "4 XVIII 3.1.8" "(iii), special case",
  sga "4½ Dualite 2.3" "special case"]
public theorem derivedWeightedTrace_eq_derivedCounit
    (hadj : ∀ M, forgetModTrace.{u, u + 1, u} B Λ U.obj.hom modPull hpull M
        (adjMod.counit.app M) =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit.app
        ((forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).obj M))
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ,
      (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).obj (modPull.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom modPull hpull
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M (τ M)) :
    derivedWeightedTrace.{u, u + 1, t, u} B Λ U.obj.hom modPull hpull
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ =
      (Adjunction.mapDerivedCategory adjMod).counit := by
  have heq : weightedTraceModNatTrans.{u, u + 1, u} B Λ U.obj.hom modPull hpull
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ = adjMod.counit :=
    NatTrans.ext (funext fun M => hasWeightedTraceStalksMod_unique.{u, u + 1, u} B Λ
      U.obj.hom modPull hpull _ M (hτ M)
      (hasWeightedTraceStalksMod_counit B X hX U Λ modPull hpull adjMod hadj M))
  rw [derivedWeightedTrace, heq]
  exact (Adjunction.mapDerivedCategory_counit _).symm

/-- **Remark 0GL4 on `D(X_étale, Λ)`, at a fixed object**, for an arbitrary `Λ`-linear lift of
the adjunction. The trace map `Tr_{j, w, K} : j_! j^{-1}K ⟶ K` of Stacks 0GKH part (3) is the
counit at `K` of the adjunction between the derived functors of the `Λ`-linear `j_!` and
`j^{-1}`. -/
public theorem derivedWeightedTrace_app_eq_derivedCounit_app
    (hadj : ∀ M, forgetModTrace.{u, u + 1, u} B Λ U.obj.hom modPull hpull M
        (adjMod.counit.app M) =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit.app
        ((forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).obj M))
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ,
      (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).obj (modPull.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom modPull hpull
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M (τ M))
    (K : DerivedCategory (ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ)) :
    (derivedWeightedTrace.{u, u + 1, t, u} B Λ U.obj.hom modPull hpull
          (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ).app K =
      (Adjunction.mapDerivedCategory adjMod).counit.app K :=
  NatTrans.congr_app
    (derivedWeightedTrace_eq_derivedCounit.{u, t} B X hX U Λ modPull hpull adjMod hadj τ hτ) K

/-- **Remark 0GL4 on `D(X_étale, Λ)`, for a trace family left general**, at the `Λ`-linear
inverse image and adjunction constructed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleModulePullbackAdjunction`. Let
`j : U ⟶ X` be étale and let `Λ` be a ring. Let `τ` be a family of trace maps of Stacks 0GKH
part (3) for the canonical weighting of `j`, that is a morphism `j_! j^{-1}M ⟶ M` for each sheaf
of `Λ`-modules whose underlying morphism of abelian sheaves has the behaviour on geometric
stalks by which Lemma 0GKG characterises the trace. Then the derived trace
`Tr_{j, w} : j_! j^{-1} ⟶ id` of `D(X_étale, Λ)` built from `τ` is the counit of the adjunction
between the derived functors of the `Λ`-linear `j_!` and `j^{-1}`.

The `Λ`-linear inverse image is `AlgebraicGeometry.SmallEtale.pullbackMod` and the `Λ`-linear
adjunction `AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction`, both constructed
for an arbitrary coefficient ring, the latter as the lift of the adjunction of Stacks 03S3; its
counit is the abelian counit on underlying abelian sheaves by
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit`.

`AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit` is the registration of the remark:
it is this statement at the constructed trace family, where `τ` is no longer quantified over. -/
@[sga "4 XVII 6.2.11" "more general",
  sga "4 XVIII 3.1.8" "(iii), special case",
  sga "4½ Dualite 2.3" "special case"]
public theorem derivedWeightedTrace_pullbackMod_eq_derivedCounit
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ,
      (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).obj
        ((pullbackMod.{u, u + 1, u} B Λ U.obj.hom).obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom
      (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
      (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M (τ M)) :
    derivedWeightedTrace.{u, u + 1, t, u} B Λ U.obj.hom
        (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
        (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
        (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ =
      (Adjunction.mapDerivedCategory
        (etaleFShriekModPullbackAdjunction B X hX U Λ)).counit :=
  derivedWeightedTrace_eq_derivedCounit.{u, t} B X hX U Λ _ _ _
    (forgetModTrace_etaleFShriekModPullbackAdjunction_counit B X hX U Λ) τ hτ

/-- **Remark 0GL4 on `D(X_étale, Λ)` at a fixed object, for a trace family left general.** For
an étale `j`, a ring `Λ` and an object `K` of `D(X_étale, Λ)`, the trace map
`Tr_{j, w, K} : j_! j^{-1}K ⟶ K` built from a family `τ` of sheaf-level trace maps of
Stacks 0GKH part (3) is the counit at `K` of the adjunction between the derived functors of the
`Λ`-linear `j_!` and `j^{-1}`.
`AlgebraicGeometry.derivedWeightedTraceMod_app_eq_derivedCounit_app` is the registration of the
remark: it is this statement at the constructed trace family. -/
public theorem derivedWeightedTrace_pullbackMod_app_eq_derivedCounit_app
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ,
      (fShriekMod.{u, u + 1, u} B Λ U.obj.hom).obj
        ((pullbackMod.{u, u + 1, u} B Λ U.obj.hom).obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom
      (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
      (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
      (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) M (τ M))
    (K : DerivedCategory (ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ)) :
    (derivedWeightedTrace.{u, u + 1, t, u} B Λ U.obj.hom
          (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
          (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)
          (flatQuasiFiniteWeight (B.inclusion.map U.obj.hom)) τ hτ).app K =
      (Adjunction.mapDerivedCategory
        (etaleFShriekModPullbackAdjunction B X hX U Λ)).counit.app K :=
  NatTrans.congr_app
    (derivedWeightedTrace_pullbackMod_eq_derivedCounit.{u, t} B X hX U Λ τ hτ) K

/-- **Stacks 0GL4 on `D(X_étale, Λ)`.** Let `j : U ⟶ X` be étale and let `Λ` be a ring. The
derived trace `Tr_{j, w} : j_! j^{-1} ⟶ id` of `D(X_étale, Λ)` of Stacks 0GKH part (3), for the
canonical weighting `w` of `j` of Stacks 0F3D, is the counit of the adjunction between the
derived functors of the `Λ`-linear `j_!` and `j^{-1}`.

Every object in the statement is constructed. The trace is
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod`, the derived form of the sheaf-level
trace `AlgebraicGeometry.SmallEtale.weightedTraceMod`, which has at each sheaf of `Λ`-modules
the behaviour on geometric stalks by which Lemma 0GKG characterises the trace — that is
`AlgebraicGeometry.SmallEtale.weightedTraceMod_hasWeightedTraceStalksMod` — and is by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` the only such morphism, so it is
*the* trace map and `Tr_{j, w}` is *the* derived trace rather than one of a family of candidates.
The `Λ`-linear inverse image is `AlgebraicGeometry.SmallEtale.pullbackMod` and the `Λ`-linear
adjunction `AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction`, the lift of the
adjunction of Stacks 03S3, whose counit is the abelian counit on underlying abelian sheaves by
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit`;
the weighting is the canonical one, a weighting by
`AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`.

This is `AlgebraicGeometry.derivedWeightedTrace_pullbackMod_eq_derivedCounit`, which leaves the
trace family general, instantiated at that constructed trace. -/
@[stacks 0GL4 "At the derived coefficients of the remark, D(X_etale, Lambda) for an arbitrary \
ring Lambda: for an étale j the derived trace Tr_{j,w} of 0GKH part (3) -- \
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` for the canonical weighting of 0F3D -- \
is the counit of the adjunction between the derived functors of the Lambda-linear j_! and \
j^{-1}, so for each K in D(X_etale, Lambda) the morphism Tr_{j,w,K} : j_!j^{-1}K ⟶ K is the \
counit at K. Every object the statement names is constructed and nothing is quantified over: \
the derived trace is `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod`, the derived form \
of the sheaf-level `AlgebraicGeometry.SmallEtale.weightedTraceMod`, which is the trace of 0GKG \
by `AlgebraicGeometry.SmallEtale.weightedTraceMod_hasWeightedTraceStalksMod` and the unique \
such morphism by `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique`; the \
Lambda-linear inverse image is `AlgebraicGeometry.SmallEtale.pullbackMod`, the lift of the \
abelian j^{-1} of 03Q1; the Lambda-linear adjunction is \
`AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction`, the lift of the abelian \
adjunction of 03S3, whose counit is the abelian counit on underlying abelian sheaves by \
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit`; \
and the weighting is the canonical one of 0F3D, a weighting by \
`AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`. The identification of the derived trace \
with the derived counit comes from the abelian case \
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` through the coherence lemma \
`CategoryTheory.Adjunction.mapDerivedCategory_counit`, which says that the counit of a derived \
adjunction is the derived counit, and the sheaf-level trace is the counit by \
`AlgebraicGeometry.hasWeightedTraceStalksMod_counit_etale` with the uniqueness of 0GKG at \
Lambda-coefficients. Coefficient universes ModuleSheaf.{u, u+1, u} with Lambda : Type u, those \
of 0GKH part (3); the universe of the derived category is arbitrary.",
  sga "4 XVII 6.2.11" "more general",
  sga "4 XVIII 3.1.8" "(iii), special case",
  sga "4½ Dualite 2.3" "special case"]
public theorem derivedWeightedTraceMod_eq_derivedCounit :
    SmallEtale.derivedWeightedTraceMod.{u, u + 1, t, u} B Λ U.obj.hom
        (flatQuasiFiniteWeight_isWeighting (B.inclusion.map U.obj.hom)) =
      (Adjunction.mapDerivedCategory
        (etaleFShriekModPullbackAdjunction B X hX U Λ)).counit :=
  derivedWeightedTrace_pullbackMod_eq_derivedCounit.{u, t} B X hX U Λ
    (weightedTraceMod.{u, u + 1, u} B Λ U.obj.hom
      (flatQuasiFiniteWeight_isWeighting (B.inclusion.map U.obj.hom)))
    (weightedTraceMod_hasWeightedTraceStalksMod.{u, u + 1, u} B Λ U.obj.hom
      (flatQuasiFiniteWeight_isWeighting (B.inclusion.map U.obj.hom)))

/-- **Stacks 0GL4 on `D(X_étale, Λ)`, at a fixed object.** For an étale `j`, a ring `Λ` and an
object `K` of `D(X_étale, Λ)`, the trace map `Tr_{j, w, K} : j_! j^{-1}K ⟶ K` of Stacks 0GKH
part (3), for the canonical weighting `w` of `j`, is the counit at `K` of the adjunction between
the derived functors of the `Λ`-linear `j_!` and `j^{-1}`. This is the form in which the remark
reads, and it is the component at `K` of
`AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit`. -/
@[stacks 0GL4 "At a fixed object K of D(X_etale, Lambda) for an arbitrary ring Lambda, which is \
how the remark reads: for an étale j the trace map Tr_{j,w,K} : j_!j^{-1}K ⟶ K of 0GKH part (3) \
-- the component at K of `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` for the \
canonical weighting of 0F3D -- is the counit at K of the adjunction between the derived \
functors of the Lambda-linear j_! and j^{-1}. The trace, the two functors and the adjunction \
are all constructed and nothing is quantified over; this is the component form of \
`AlgebraicGeometry.derivedWeightedTraceMod_eq_derivedCounit`.",
  sga "4 XVIII 3.1.8" "(iii), special case"]
public theorem derivedWeightedTraceMod_app_eq_derivedCounit_app
    (K : DerivedCategory (ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ)) :
    (SmallEtale.derivedWeightedTraceMod.{u, u + 1, t, u} B Λ U.obj.hom
          (flatQuasiFiniteWeight_isWeighting (B.inclusion.map U.obj.hom))).app K =
      (Adjunction.mapDerivedCategory
        (etaleFShriekModPullbackAdjunction B X hX U Λ)).counit.app K :=
  NatTrans.congr_app (derivedWeightedTraceMod_eq_derivedCounit.{u, t} B X hX U Λ) K

end Module

end AlgebraicGeometry

end
