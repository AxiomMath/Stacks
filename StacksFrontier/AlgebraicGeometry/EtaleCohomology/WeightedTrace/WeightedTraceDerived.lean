module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceNatTrans
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The weighted trace with coefficients in a ring, on unbounded derived categories

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `w` be an
integer-valued function on `X` and let `Λ` be a ring. Part (3) of Stacks 0GKH says that the
trace maps `Tr_{f, w}` of Stacks 0GKG, which live on abelian sheaves, give for every object `K`
of `D(Y_étale, Λ)` a morphism `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`, functorial in `K` and compatible
with arbitrary base change. This file carries out that passage.

The route is the one the source takes. A trace map at `Λ`-coefficients is a morphism of sheaves
of `Λ`-modules whose underlying morphism of abelian sheaves has the behaviour on geometric
stalks by which Stacks 0GKG characterises the trace; that behaviour forces every naturality
square to commute, so a family of such morphisms is a natural transformation
`f_! f^{-1} ⟶ id` of functors on sheaves of `Λ`-modules; and `f_!` and `f^{-1}` are exact, so
that natural transformation descends to unbounded derived categories, where it is the derived
trace. Being a natural transformation *is* functoriality in `K`, and the base-change
compatibility at `Λ`-coefficients descends the same way.

## Main definitions

* `AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso` — the identification, natural in the
  sheaf of `Λ`-modules `M`, of the abelian sheaf underlying `f_! f^{-1}M` with `f_! f^{-1}` of
  the abelian sheaf underlying `M`, assembled from the two comparisons which say that the
  `Λ`-linear `f_!` and `f^{-1}` lift the abelian ones.
* `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalksMod` — **the characterising property of
  the trace map at `Λ`-coefficients.** A morphism `τ : f_! f^{-1}M ⟶ M` of sheaves of
  `Λ`-modules has weighted trace stalks if the morphism of abelian sheaves obtained from it by
  forgetting the module structure and transporting along
  `AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso` has the behaviour on geometric
  stalks of `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks`.
* `AlgebraicGeometry.SmallEtale.weightedTraceModNatTrans` — a family of such morphisms, one for
  each sheaf of `Λ`-modules on the small étale site of `Y`, is a natural transformation
  `f^{-1} ⋙ f_! ⟶ id`.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTrace` — **the derived trace of Stacks 0GKH part
  (3)**: the natural transformation
  `f^{-1} ⋙ f_! ⟶ id` of `D(Y_étale, Λ)` obtained from the sheaf-level one. Its component at an
  object `K` is `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`.
* `AlgebraicGeometry.SmallEtale.traceBaseChangeComparison` — for a cartesian square, the
  comparison `f^{-1} ⋙ f_! ⋙ g^{-1} ≅ g^{-1} ⋙ f'^{-1} ⋙ f'_!` assembled from the base-change
  isomorphism of Stacks 0F5J and the comparison of the two iterated inverse images, at
  `Λ`-coefficients.

## Main results

* `CategoryTheory.NatTrans.mapDerivedCategory_whiskerRight` and
  `CategoryTheory.NatTrans.mapDerivedCategory_whiskerLeft` — **deriving a natural transformation
  commutes with whiskering by an exact functor**, through the comparison
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` of the derived functor of a
  composite with the composite of the derived functors. These are general facts about exact
  functors between abelian categories; they are what turns the derived form of a whiskered
  sheaf-level transformation into a whiskering of the derived transformation.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_abPullback`,
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_abPullback` and
  `AlgebraicGeometry.SmallEtale.additive_abPullback` — the inverse image of abelian sheaves on
  small étale sites is exact, which is Stacks 03Q1 at the coefficient universe used here.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` — **uniqueness at
  `Λ`-coefficients.** Two morphisms `f_! f^{-1}M ⟶ M` with the characterising behaviour on
  geometric stalks are equal.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_naturality` — **part (1) of Stacks
  0GKH at `Λ`-coefficients.** The naturality square of two such morphisms commutes.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_naturality` — **functoriality in `K`**: the
  derived trace is a natural transformation, so for `ψ : K ⟶ K'` the square commutes.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_eq` and
  `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_app_Q` — **the derived trace restricts to
  the sheaf-level trace.** The first exhibits it as the derived form of the sheaf-level trace
  read through the identification of the derived functor of `f^{-1} ⋙ f_!` with the composite of
  the derived functors and of the derived functor of the identity with the identity; the second
  computes its component at a complex of sheaves as the localization of the degreewise trace.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_of_iso` — **the weighted trace behaviour
  on geometric stalks transports along an isomorphism of the sheaf on the base.** This is what
  lets the trace at `Λ`-coefficients for the base change, which lives on the abelian sheaf
  underlying `g^{-1}` of a sheaf of `Λ`-modules, be fed to part (2) of Stacks 0GKH, whose
  statement is about the abelian `g^{-1}` of the underlying abelian sheaf.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_baseChange` — **part (2) of Stacks
  0GKH at `Λ`-coefficients**, deduced from part (2) at abelian coefficients
  (`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange`): the square formed by the
  two `Λ`-linear comparisons attached to a cartesian square and the two trace maps commutes.
* `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_baseChange` and
  `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_baseChange_whisker` — **compatibility with
  arbitrary base change in the derived category.**
* `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_spec_of_lifts` — all of the above in one,
  with the base-change square at `Λ`-coefficients proved rather than assumed: part (3) of Stacks
  0GKH run on a given `Λ`-linear inverse image, a given pair of comparisons for the square and a
  given family of trace maps. `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_spec` is the
  same conjunction at arbitrary coefficient universes, with that square as an input. The tag is
  registered on `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec` of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction`,
  where all of those are constructed.

## Implementation notes

**How the trace maps enter.** As in parts (1) and (2), the trace maps enter through the
behaviour on geometric stalks by which Stacks 0GKG characterises them: a morphism with that
behaviour exists and is unique by
`AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks`, and by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` there is at most one such
morphism for each sheaf of `Λ`-modules.

**The `Λ`-linear inverse image is data.** The `Λ`-linear direct image with compact support is the
concrete `AlgebraicGeometry.SmallEtale.fShriekMod`, which is a lift of the abelian `f_!` by
`AlgebraicGeometry.SmallEtale.fShriekModForgetIso`. The `Λ`-linear inverse image is taken as data
instead: `AlgebraicGeometry.SmallEtale.modPullback` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor` is available only for a commutative
coefficient ring, while Stacks 0GKH part (3) asks for an arbitrary ring. So a functor on sheaves
of `Λ`-modules together with an isomorphism identifying it with `f^{-1}` on underlying abelian
sheaves is taken as input, as
`AlgebraicGeometry.SmallEtale.moduleFShriekDerivedFunctor` does for `f_!`. Its exactness is not
assumed on top of that: `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_of_forgetModPullIso`
and its two companions derive the three exactness properties from the identification alone,
through the exactness of the abelian `f^{-1}`, which is proved here as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_abPullback`. They are carried as instance
hypotheses in the sections that need them only so that the derived functors appearing in the
statements elaborate.

**The shape of the base-change statement.** The derived trace
`AlgebraicGeometry.SmallEtale.derivedWeightedTrace` is, by definition and by
`AlgebraicGeometry.SmallEtale.derivedWeightedTrace_eq`, the derived form
`NatTrans.mapDerivedCategory` of the sheaf-level trace read through two fixed comparison
isomorphisms which do not involve the cartesian square. The base-change statement is therefore
formulated for that derived form: `derivedWeightedTrace_baseChange` says that the derived forms
of the two sides of the sheaf-level base-change square agree, and
`derivedWeightedTrace_baseChange_whisker` rewrites both of them, using the whiskering lemmas
above, as the two whiskerings of the derived traces by the derived `g^{-1}`, composed with the
canonical comparisons of the derived functor of a composite with the composite of the derived
functors. The second is the base-change square in the derived category.

**How the sheaf-level base-change square is obtained.** The two comparisons attached to the
cartesian square — the base-change isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J and the
comparison `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images — are available
at abelian coefficients as `AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso` and
`AlgebraicGeometry.SmallEtale.inverseImageSquareIso`, and at `Λ`-coefficients they enter as
lifts of those, each with the identification of its underlying morphism of abelian sheaves with
its abelian counterpart, in the same sense in which `hpullF` makes the `Λ`-linear inverse image
a lift of the abelian one. From those identifications
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_baseChange` proves the `Λ`-coefficient
square from part (2) at abelian coefficients: forgetting the module structure is faithful, so it
is enough to check the square on underlying abelian sheaves, where it is part (2) applied to the
transported traces. The transport is
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_of_iso`, needed because the trace at
`Λ`-coefficients for the base change lives on `g^{-1}` of a sheaf of `Λ`-modules and part (2)
speaks about the abelian `g^{-1}` of the underlying abelian sheaf.

**Coefficient universes.** The `Λ`-coefficient statements of this file hold at arbitrary
coefficient universes as long as the base-change square at `Λ`-coefficients is taken as an
input, which is `AlgebraicGeometry.SmallEtale.derivedWeightedTrace_spec`. Deducing that square
from part (2) requires the abelian side to be at the coefficient universe at which Stacks 0F5J
is carried, namely `AddCommGrpCat.{u + 1}`; since
`AlgebraicGeometry.SmallEtale.forgetModuleSheaf` lands in `AddCommGrpCat.{max (u + 1) v r}`,
the sheaves of `Λ`-modules are taken at `ModuleSheaf.{u, u + 1, u}` with `Λ : Type u` there.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- **Deriving a natural transformation commutes with whiskering on the right by an exact
functor.** Both sides are read through the comparison of the derived functor of a composite with
the composite of the derived functors; on the image of the localization the two composites are
the same chain of factorizations, and the one step that is not formal is the naturality of the
factorization of `H`. -/
public theorem NatTrans.mapDerivedCategory_whiskerRight
    (F G : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (η : F ⟶ G)
    (H : C₂ ⥤ C₃) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F H).inv ≫
        NatTrans.mapDerivedCategory (Functor.whiskerRight η H) =
      Functor.whiskerRight (NatTrans.mapDerivedCategory η) H.mapDerivedCategory ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G H).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  have key : (NatTrans.mapHomologicalComplex (Functor.whiskerRight η H)
        (ComplexShape.up ℤ)).app P =
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P) := rfl
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    NatTrans.mapDerivedCategory_app_Q, NatTrans.mapDerivedCategory_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_comp, key]
  rw [← CategoryTheory.Functor.map_comp_assoc H.mapDerivedCategory
      (G.mapDerivedCategoryFactors.inv.app P) (G.mapDerivedCategoryFactors.hom.app P),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    H.mapDerivedCategoryFactors_hom_naturality_assoc]

/-- **Deriving a natural transformation commutes with whiskering on the left by an exact
functor.** The companion of `CategoryTheory.NatTrans.mapDerivedCategory_whiskerRight`. The
derived transformation is met at an object outside the image of the localization, namely the
image of a complex under the derived functor of `H`; the factorization of `H` is a morphism from
there into the image of the localization, and
`CategoryTheory.NatTrans.mapDerivedCategory_app_comp` moves the transformation across it. -/
public theorem NatTrans.mapDerivedCategory_whiskerLeft
    (H : C₁ ⥤ C₂) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (F G : C₂ ⥤ C₃) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (η : F ⟶ G) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso H F).inv ≫
        NatTrans.mapDerivedCategory (Functor.whiskerLeft H η) =
      Functor.whiskerLeft H.mapDerivedCategory (NatTrans.mapDerivedCategory η) ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso H G).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  have key : (NatTrans.mapHomologicalComplex (Functor.whiskerLeft H η)
        (ComplexShape.up ℤ)).app P =
      (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := rfl
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    NatTrans.mapDerivedCategory_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, key]
  rw [NatTrans.mapDerivedCategory_app_comp_assoc
    (Z := H.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) η
    (H.mapDerivedCategoryFactors.hom.app P)]
  simp only [Iso.inv_hom_id_app_assoc]

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

universe u v t r

/-! ### Exactness of the inverse image of abelian étale sheaves -/

section AbPullback

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (q : T ⟶ S)

/-- **Stacks 03Q1 for abelian coefficients.** The inverse image of abelian sheaves on small
étale sites preserves finite limits. It is the sheafification of the left Kan extension along
the opposite of base change; base change is representably flat, so the costructured-arrow
categories computing that extension pointwise are filtered, the forgetful functor from abelian
groups preserves filtered colimits of that size, and a filtered colimit of abelian groups is
therefore left exact.

This is Stacks 03Q1 at the coefficient universe used here and carries no attribute: the tag's
carrier in this library is
`AlgebraicGeometry.smallEtaleSheafPullback_preservesFiniteLimits` for sheaves of sets, and the
statement below is that one transported to abelian coefficients rather than an independent
result. -/
@[sga "5 VI 2.1" "left exactness of f*"]
public theorem preservesFiniteLimits_abPullback :
    PreservesFiniteLimits (abPullback.{u, v} B q) := by
  have hlan : PreservesFiniteLimits ((smallEtaleBaseChange B q).op.lan :
      ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) := by
    refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun Z => ?_
    have : IsFiltered (CostructuredArrow (smallEtaleBaseChange B q).op Z) :=
      IsFiltered.of_equivalence
        (structuredArrowOpEquivalence (smallEtaleBaseChange B q) (Opposite.unop Z))
    have : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    infer_instance
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The inverse image of abelian sheaves on small étale sites preserves finite colimits, being
a left adjoint. -/
public theorem preservesFiniteColimits_abPullback :
    PreservesFiniteColimits (abPullback.{u, v} B q) :=
  let : (abPullback.{u, v} B q).IsLeftAdjoint :=
    ((smallEtaleBaseChange B q).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).isLeftAdjoint
  inferInstance

/-- The inverse image of abelian sheaves on small étale sites is additive, preserving binary
products by left exactness. -/
public theorem additive_abPullback : (abPullback.{u, v} B q).Additive :=
  have := preservesFiniteLimits_abPullback.{u, v} B q
  Functor.additive_of_preserves_binary_products _

end AbPullback

/-! ### Exactness of a `Λ`-linear lift of the inverse image -/

section ModPullback

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  (modPull : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ)
  (hpull : modPull ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
    forgetModuleSheaf.{u, v, r} B Y Λ ⋙ abPullback.{u, max v r} B f)

include hpull

/-- A `Λ`-linear lift of the inverse image preserves finite limits: the abelian `f^{-1}` is left
exact by Stacks 03Q1, forgetting the module structure is left exact, and it reflects
isomorphisms hence finite limits. -/
public theorem preservesFiniteLimits_of_forgetModPullIso : PreservesFiniteLimits modPull := by
  have := preservesFiniteLimits_forgetModuleSheaf.{u, v, r} B X Λ
  have := preservesFiniteLimits_forgetModuleSheaf.{u, v, r} B Y Λ
  have := preservesFiniteLimits_abPullback.{u, max v r} B f
  have : ReflectsFiniteLimits (forgetModuleSheaf.{u, v, r} B X Λ) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  have : PreservesFiniteLimits (forgetModuleSheaf.{u, v, r} B Y Λ ⋙
    abPullback.{u, max v r} B f) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (modPull ⋙ forgetModuleSheaf.{u, v, r} B X Λ) :=
    preservesFiniteLimits_of_natIso hpull.symm
  exact preservesFiniteLimits_of_reflects_of_preserves modPull
    (forgetModuleSheaf.{u, v, r} B X Λ)

/-- A `Λ`-linear lift of the inverse image is additive, preserving binary products by left
exactness. -/
public theorem additive_of_forgetModPullIso : modPull.Additive :=
  have := preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f modPull hpull
  Functor.additive_of_preserves_binary_products _

/-- A `Λ`-linear lift of the inverse image preserves finite colimits: the abelian `f^{-1}` is a
left adjoint, forgetting the module structure commutes with sheafification hence preserves all
colimits, and it reflects isomorphisms hence finite colimits. -/
public theorem preservesFiniteColimits_of_forgetModPullIso :
    PreservesFiniteColimits modPull := by
  have hX := preservesColimitsOfSize_forgetModuleSheaf.{u, v, r} B X Λ
  have hY := preservesColimitsOfSize_forgetModuleSheaf.{u, v, r} B Y Λ
  have : PreservesFiniteColimits (forgetModuleSheaf.{u, v, r} B X Λ) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteColimits (forgetModuleSheaf.{u, v, r} B Y Λ) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have := preservesFiniteColimits_abPullback.{u, max v r} B f
  have : ReflectsFiniteColimits (forgetModuleSheaf.{u, v, r} B X Λ) := inferInstance
  have : PreservesFiniteColimits (forgetModuleSheaf.{u, v, r} B Y Λ ⋙
    abPullback.{u, max v r} B f) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits (modPull ⋙ forgetModuleSheaf.{u, v, r} B X Λ) :=
    preservesFiniteColimits_of_natIso hpull.symm
  exact preservesFiniteColimits_of_reflects_of_preserves modPull
    (forgetModuleSheaf.{u, v, r} B X Λ)

end ModPullback

/-! ### Exactness of the `Λ`-linear direct image with compact support -/

section FShriekMod

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The `Λ`-linear direct image with compact support has a right adjoint: it preserves all
colimits, forgetting the module structure both preserving and reflecting them and `f_!`
preserving them by Stacks 0F5F, and the special adjoint functor theorem applies to étale sheaves
of `Λ`-modules. -/
public instance fShriekMod_isLeftAdjoint : (fShriekMod.{u, v, r} B Λ f).IsLeftAdjoint :=
  isLeftAdjoint_of_forgetModuleSheafIso.{u, v, r} B Λ f _ (fShriekModForgetIso.{u, v, r} B Λ f)

/-- The `Λ`-linear direct image with compact support preserves finite colimits, being a left
adjoint. With `AlgebraicGeometry.SmallEtale.fShriekMod_preservesFiniteLimits` this makes it
exact, which is what lets it be read on unbounded derived categories. -/
public instance fShriekMod_preservesFiniteColimits :
    PreservesFiniteColimits (fShriekMod.{u, v, r} B Λ f) :=
  ⟨fun _ _ _ => inferInstance⟩

end FShriekMod

/-! ### The weighted trace at `Λ`-coefficients -/

section ModuleTrace

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (modPull : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ)
  (hpull : modPull ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
    forgetModuleSheaf.{u, v, r} B Y Λ ⋙ abPullback.{u, max v r} B f)

/-- **The abelian sheaf underlying `f_! f^{-1}M` is `f_! f^{-1}` of the abelian sheaf underlying
`M`**, naturally in the sheaf of `Λ`-modules `M`. It is the comparison identifying the
`Λ`-linear inverse image with the abelian one, pushed forward by `f_!`, followed by the
comparison `AlgebraicGeometry.SmallEtale.fShriekModForgetIso` identifying the `Λ`-linear direct
image with compact support with the abelian one. -/
public def forgetFShriekModPullNatIso :
    forgetModuleSheaf.{u, v, r} B Y Λ ⋙
        abPullback.{u, max v r} B f ⋙ fShriekFunctor.{u, max v r} B f ≅
      modPull ⋙ fShriekMod.{u, v, r} B Λ f ⋙ forgetModuleSheaf.{u, v, r} B Y Λ :=
  Functor.isoWhiskerRight hpull.symm (fShriekFunctor.{u, max v r} B f) ≪≫
    Functor.isoWhiskerLeft modPull (fShriekModForgetIso.{u, v, r} B Λ f).symm

/-- **The morphism of abelian sheaves underlying a candidate trace map at `Λ`-coefficients.**
Forgetting the module structure of `τ : f_! f^{-1}M ⟶ M` and transporting the source along
`AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso` gives a morphism
`f_! f^{-1}M' ⟶ M'`, where `M'` is the abelian sheaf underlying `M`. -/
public def forgetModTrace (M : ModuleSheaf.{u, v, r} B Y Λ)
    (τ : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M) :
    (fShriekFunctor.{u, max v r} B f).obj
        ((abPullback.{u, max v r} B f).obj ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M)) ⟶
      (forgetModuleSheaf.{u, v, r} B Y Λ).obj M :=
  (forgetFShriekModPullNatIso.{u, v, r} B Λ f modPull hpull).hom.app M ≫
    (forgetModuleSheaf.{u, v, r} B Y Λ).map τ

/-- **The underlying abelian morphism recovers the trace map.** Composing
`AlgebraicGeometry.SmallEtale.forgetModTrace` with the inverses of the two comparisons it was
transported along returns the morphism of abelian sheaves underlying `τ` itself. -/
public theorem forgetModTrace_conjugate (M : ModuleSheaf.{u, v, r} B Y Λ)
    (τ : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M) :
    (fShriekModForgetIso.{u, v, r} B Λ f).hom.app (modPull.obj M) ≫
        (fShriekFunctor.{u, max v r} B f).map (hpull.hom.app M) ≫
        forgetModTrace.{u, v, r} B Λ f modPull hpull M τ =
      (forgetModuleSheaf.{u, v, r} B Y Λ).map τ := by
  change (fShriekModForgetIso.{u, v, r} B Λ f).hom.app (modPull.obj M) ≫
      (fShriekFunctor.{u, max v r} B f).map (hpull.hom.app M) ≫
      ((fShriekFunctor.{u, max v r} B f).map (hpull.inv.app M) ≫
        (fShriekModForgetIso.{u, v, r} B Λ f).inv.app (modPull.obj M) ≫
        (forgetModuleSheaf.{u, v, r} B Y Λ).map τ) = _
  rw [← CategoryTheory.Functor.map_comp_assoc (fShriekFunctor.{u, max v r} B f)
      (hpull.hom.app M) (hpull.inv.app M),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

/-- **The characterising property of the trace map of Stacks 0GKG at `Λ`-coefficients.** A
morphism `τ : f_! f^{-1}M ⟶ M` of sheaves of `Λ`-modules has weighted trace stalks if the
morphism of abelian sheaves underlying it, read through the identification
`AlgebraicGeometry.SmallEtale.forgetFShriekModPullNatIso`, has at every geometric point of `Y`
the weighted sum over the geometric fibre as its effect on stalks. -/
public def HasWeightedTraceStalksMod (w : X.obj → ℤ) (M : ModuleSheaf.{u, v, r} B Y Λ)
    (τ : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M) : Prop :=
  HasWeightedTraceStalks.{u, max v r} B f w ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M)
    (forgetModTrace.{u, v, r} B Λ f modPull hpull M τ)

/-- **Uniqueness of the weighted trace at `Λ`-coefficients.** Two morphisms `f_! f^{-1}M ⟶ M` of
sheaves of `Λ`-modules whose underlying morphisms of abelian sheaves have the weighted behaviour
on geometric stalks are equal: the underlying morphisms agree by the uniqueness half of Stacks
0GKG, and forgetting the module structure of an étale sheaf is faithful. -/
@[sga "4 IX 5.1" "more general"]
public theorem hasWeightedTraceStalksMod_unique (w : X.obj → ℤ)
    (M : ModuleSheaf.{u, v, r} B Y Λ)
    {τ τ' : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M}
    (h : HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M τ)
    (h' : HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M τ') :
    τ = τ' := by
  refine (forgetModuleSheaf.{u, v, r} B Y Λ).map_injective ?_
  refine (Iso.cancel_iso_hom_left
    ((forgetFShriekModPullNatIso.{u, v, r} B Λ f modPull hpull).app M) _ _).1 ?_
  exact hasWeightedTraceStalks_unique.{u, max v r} B f w
    ((forgetModuleSheaf.{u, v, r} B Y Λ).obj M) h h'

/-- **Part (1) of Stacks 0GKH at `Λ`-coefficients: the trace map is functorial in the sheaf of
`Λ`-modules.** If `τM` and `τN` have the weighted behaviour on geometric stalks then for every
`φ : M ⟶ N` the naturality square commutes. The underlying square of abelian sheaves commutes by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_naturality`, the identification of the
underlying sheaf of `f_! f^{-1}M` is natural in `M`, and forgetting the module structure is
faithful. -/
@[sga "4 XVII 6.2.3" "more general", sga "4 XVII 6.2.5" "more general"]
public theorem hasWeightedTraceStalksMod_naturality (w : X.obj → ℤ)
    {M N : ModuleSheaf.{u, v, r} B Y Λ} (φ : M ⟶ N)
    {τM : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M}
    {τN : (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj N) ⟶ N}
    (hM : HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M τM)
    (hN : HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w N τN) :
    (fShriekMod.{u, v, r} B Λ f).map (modPull.map φ) ≫ τN = τM ≫ φ := by
  refine (forgetModuleSheaf.{u, v, r} B Y Λ).map_injective ?_
  have hnat := hasWeightedTraceStalks_naturality.{u, max v r} B f w
    ((forgetModuleSheaf.{u, v, r} B Y Λ).map φ) hM hN
  have hsq := (forgetFShriekModPullNatIso.{u, v, r} B Λ f modPull hpull).hom.naturality φ
  dsimp only [Functor.comp_map] at hsq
  refine (Iso.cancel_iso_hom_left
    ((forgetFShriekModPullNatIso.{u, v, r} B Λ f modPull hpull).app M) _ _).1 ?_
  dsimp only [Iso.app_hom]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← hsq]
  simpa only [forgetModTrace, Category.assoc] using hnat

/-- **A family of weighted trace maps at `Λ`-coefficients is a natural transformation.** Given,
for each sheaf of `Λ`-modules `M` on the small étale site of `Y`, a morphism
`τ M : f_! f^{-1}M ⟶ M` with the behaviour on geometric stalks which characterises the trace map
of Stacks 0GKG, the family is a natural transformation `f^{-1} ⋙ f_! ⟶ id`. Naturality is part
(1) of Stacks 0GKH at `Λ`-coefficients. -/
public def weightedTraceModNatTrans (w : X.obj → ℤ)
    (τ : ∀ M : ModuleSheaf.{u, v, r} B Y Λ,
      (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M (τ M)) :
    modPull ⋙ fShriekMod.{u, v, r} B Λ f ⟶ 𝟭 (ModuleSheaf.{u, v, r} B Y Λ) where
  app M := τ M
  naturality _ _ φ :=
    hasWeightedTraceStalksMod_naturality.{u, v, r} B Λ f modPull hpull w φ (hτ _) (hτ _)

/-- The component of the natural transformation at a sheaf of `Λ`-modules is the given trace
map. -/
@[simp]
public theorem weightedTraceModNatTrans_app (w : X.obj → ℤ)
    (τ : ∀ M : ModuleSheaf.{u, v, r} B Y Λ,
      (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M (τ M))
    (M : ModuleSheaf.{u, v, r} B Y Λ) :
    (weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ hτ).app M = τ M :=
  rfl

/-- Two families of weighted trace maps at `Λ`-coefficients define the same natural
transformation, the characterisation on geometric stalks determining at most one morphism for
each sheaf. -/
public theorem weightedTraceModNatTrans_unique (w : X.obj → ℤ)
    (τ τ' : ∀ M : ModuleSheaf.{u, v, r} B Y Λ,
      (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M (τ M))
    (hτ' : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M (τ' M)) :
    weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ hτ =
      weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ' hτ' :=
  NatTrans.ext (funext fun M =>
    hasWeightedTraceStalksMod_unique.{u, v, r} B Λ f modPull hpull w M (hτ M) (hτ' M))

end ModuleTrace

/-! ### The derived trace -/

section Derived

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (modPull : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ)
  (hpull : modPull ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
    forgetModuleSheaf.{u, v, r} B Y Λ ⋙ abPullback.{u, max v r} B f)
  [modPull.Additive] [PreservesFiniteLimits modPull] [PreservesFiniteColimits modPull]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y Λ)]
  (w : X.obj → ℤ)
  (τ : ∀ M : ModuleSheaf.{u, v, r} B Y Λ,
    (fShriekMod.{u, v, r} B Λ f).obj (modPull.obj M) ⟶ M)
  (hτ : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPull hpull w M (τ M))

/-- **The derived weighted trace: Stacks 0GKH, part (3).** The `Λ`-linear inverse image and the
`Λ`-linear direct image with compact support are exact, so each induces a functor on unbounded
derived categories of sheaves of `Λ`-modules, and the sheaf-level trace
`AlgebraicGeometry.SmallEtale.weightedTraceModNatTrans` induces a natural transformation
`f^{-1} ⋙ f_! ⟶ id` between them. Its component at an object `K` of `D(Y_étale, Λ)` is the trace
map `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`. -/
public def derivedWeightedTrace :
    modPull.mapDerivedCategory ⋙ (fShriekMod.{u, v, r} B Λ f).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ)) :=
  NatTrans.mapDerivedCategoryCompToId modPull (fShriekMod.{u, v, r} B Λ f)
    (weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ hτ)

/-- **Functoriality of the derived trace in the object of `D(Y_étale, Λ)`**, which is part of
Stacks 0GKH part (3): for `ψ : K ⟶ K'` the square formed by the two trace maps, `f_! f^{-1}ψ`
and `ψ` commutes. -/
public theorem derivedWeightedTrace_naturality
    {K K' : DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ)} (ψ : K ⟶ K') :
    (modPull.mapDerivedCategory ⋙ (fShriekMod.{u, v, r} B Λ f).mapDerivedCategory).map ψ ≫
        (derivedWeightedTrace.{u, v, t, r} B Λ f modPull hpull w τ hτ).app K' =
      (derivedWeightedTrace.{u, v, t, r} B Λ f modPull hpull w τ hτ).app K ≫ ψ :=
  (derivedWeightedTrace.{u, v, t, r} B Λ f modPull hpull w τ hτ).naturality ψ

/-- **The derived trace is the sheaf-level trace, derived.** It is
`CategoryTheory.NatTrans.mapDerivedCategory` of the natural transformation whose component at a
sheaf of `Λ`-modules is the trace map there, read through the identification of the derived
functor of `f^{-1} ⋙ f_!` with the composite of the derived functors and the identification of
the derived functor of the identity with the identity. -/
public theorem derivedWeightedTrace_eq :
    derivedWeightedTrace.{u, v, t, r} B Λ f modPull hpull w τ hτ =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
          modPull (fShriekMod.{u, v, r} B Λ f)).inv ≫
        NatTrans.mapDerivedCategory
          (weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ hτ) ≫
        (Functor.mapDerivedCategoryIdIso _).hom :=
  rfl

/-- **The derived trace at a complex of sheaves is the localization of the degreewise trace.**
This is the restriction of the derived trace to the sheaf level: the transformation is a lift
through the localization, so its values at the objects `Q.obj P` determine it, and there it is
the degreewise sheaf-level trace conjugated by the canonical factorizations. -/
public theorem derivedWeightedTrace_app_Q
    (P : CochainComplex (ModuleSheaf.{u, v, r} B Y Λ) ℤ) :
    (derivedWeightedTrace.{u, v, t, r} B Λ f modPull hpull w τ hτ).app
          (DerivedCategory.Q.obj P) =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
            modPull (fShriekMod.{u, v, r} B Λ f)).inv.app (DerivedCategory.Q.obj P) ≫
        ((modPull ⋙ fShriekMod.{u, v, r} B Λ f).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (weightedTraceModNatTrans.{u, v, r} B Λ f modPull hpull w τ hτ)
                (ComplexShape.up ℤ)).app P) ≫
            (𝟭 (ModuleSheaf.{u, v, r} B Y Λ)).mapDerivedCategoryFactors.inv.app P) ≫
          (Functor.mapDerivedCategoryIdIso _).hom.app (DerivedCategory.Q.obj P) :=
  NatTrans.mapDerivedCategoryCompToId_app_Q modPull (fShriekMod.{u, v, r} B Λ f) _ P

end Derived

/-! ### Base change in the derived category -/

section BaseChange

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y X' Y' : B.Scheme}
  (f' : X' ⟶ Y') (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  (modPullF : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ)
  (modPullF' : ModuleSheaf.{u, v, r} B Y' Λ ⥤ ModuleSheaf.{u, v, r} B X' Λ)
  (modPullG : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B Y' Λ)
  (modPullP : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B X' Λ)
  [modPullF.Additive] [PreservesFiniteLimits modPullF] [PreservesFiniteColimits modPullF]
  [modPullF'.Additive] [PreservesFiniteLimits modPullF'] [PreservesFiniteColimits modPullF']
  [modPullG.Additive] [PreservesFiniteLimits modPullG] [PreservesFiniteColimits modPullG]
  [modPullP.Additive] [PreservesFiniteLimits modPullP] [PreservesFiniteColimits modPullP]
  (bcMod : fShriekMod.{u, v, r} B Λ f ⋙ modPullG ≅
    modPullP ⋙ fShriekMod.{u, v, r} B Λ f')
  (epsMod : modPullF ⋙ modPullP ≅ modPullG ⋙ modPullF')

/-- **The comparison attached to a cartesian square at `Λ`-coefficients.** The base-change
isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J and the comparison
`p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images combine to an isomorphism of
functors `f^{-1} ⋙ f_! ⋙ g^{-1} ≅ g^{-1} ⋙ f'^{-1} ⋙ f'_!`; it is the comparison under which
part (2) of Stacks 0GKH matches the two trace maps. -/
public def traceBaseChangeComparison :
    modPullF ⋙ fShriekMod.{u, v, r} B Λ f ⋙ modPullG ≅
      modPullG ⋙ modPullF' ⋙ fShriekMod.{u, v, r} B Λ f' :=
  Functor.isoWhiskerLeft modPullF bcMod ≪≫
    Functor.isoWhiskerRight epsMod (fShriekMod.{u, v, r} B Λ f')

variable [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X' Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y' Λ)]
  (trF : modPullF ⋙ fShriekMod.{u, v, r} B Λ f ⟶ 𝟭 (ModuleSheaf.{u, v, r} B Y Λ))
  (trF' : modPullF' ⋙ fShriekMod.{u, v, r} B Λ f' ⟶ 𝟭 (ModuleSheaf.{u, v, r} B Y' Λ))

omit [modPullP.Additive] [PreservesFiniteLimits modPullP] [PreservesFiniteColimits modPullP]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X' Λ)] in
/-- **Base change of the derived trace, in the form the sheaf-level square derives to.** If the
square formed by the two comparisons of a cartesian square and the two trace maps commutes at
the level of sheaves of `Λ`-modules, then its derived form commutes. -/
public theorem derivedWeightedTrace_baseChange
    (hbc : (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
          bcMod epsMod).hom ≫ Functor.whiskerLeft modPullG trF' =
      Functor.whiskerRight trF modPullG) :
    NatTrans.mapDerivedCategory
          (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
            bcMod epsMod).hom ≫
        NatTrans.mapDerivedCategory (Functor.whiskerLeft modPullG trF') =
      NatTrans.mapDerivedCategory (Functor.whiskerRight trF modPullG) := by
  rw [← NatTrans.mapDerivedCategory_comp, hbc]

omit [modPullP.Additive] [PreservesFiniteLimits modPullP] [PreservesFiniteColimits modPullP]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X' Λ)] in
/-- **Compatibility of the derived trace with arbitrary base change.** The base-change square of
part (2) of Stacks 0GKH, derived: the derived comparison of the cartesian square, followed by
the derived trace for `(f', w ∘ p)` whiskered by the derived `g^{-1}`, is the derived trace for
`(f, w)` whiskered by the derived `g^{-1}`. Both whiskerings are read through the canonical
identification of the derived functor of a composite with the composite of the derived functors,
which is where
`CategoryTheory.NatTrans.mapDerivedCategory_whiskerLeft` and
`CategoryTheory.NatTrans.mapDerivedCategory_whiskerRight` enter. -/
public theorem derivedWeightedTrace_baseChange_whisker
    (hbc : (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
          bcMod epsMod).hom ≫ Functor.whiskerLeft modPullG trF' =
      Functor.whiskerRight trF modPullG) :
    NatTrans.mapDerivedCategory
          (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
            bcMod epsMod).hom ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
          (modPullF' ⋙ fShriekMod.{u, v, r} B Λ f')).hom ≫
        Functor.whiskerLeft modPullG.mapDerivedCategory
          (NatTrans.mapDerivedCategory trF') ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
          (𝟭 (ModuleSheaf.{u, v, r} B Y' Λ))).inv =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (modPullF ⋙ fShriekMod.{u, v, r} B Λ f) modPullG).hom ≫
        Functor.whiskerRight (NatTrans.mapDerivedCategory trF)
          modPullG.mapDerivedCategory ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (𝟭 (ModuleSheaf.{u, v, r} B Y Λ)) modPullG).inv := by
  have hL := NatTrans.mapDerivedCategory_whiskerLeft modPullG
    (modPullF' ⋙ fShriekMod.{u, v, r} B Λ f') (𝟭 (ModuleSheaf.{u, v, r} B Y' Λ)) trF'
  have hR := NatTrans.mapDerivedCategory_whiskerRight
    (modPullF ⋙ fShriekMod.{u, v, r} B Λ f) (𝟭 (ModuleSheaf.{u, v, r} B Y Λ)) trF modPullG
  rw [Iso.inv_comp_eq] at hL hR
  rw [← hL, ← hR]
  exact derivedWeightedTrace_baseChange.{u, v, t, r} B Λ f' f modPullF modPullF' modPullG
    modPullP bcMod epsMod trF trF' hbc

end BaseChange

/-! ### Stacks 0GKH, part (3) -/

section Tagged

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  (sq : IsPullback p f' f g)
  (modPullF : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ)
  (hpullF : modPullF ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
    forgetModuleSheaf.{u, v, r} B Y Λ ⋙ abPullback.{u, max v r} B f)
  (modPullF' : ModuleSheaf.{u, v, r} B Y' Λ ⥤ ModuleSheaf.{u, v, r} B X' Λ)
  (hpullF' : modPullF' ⋙ forgetModuleSheaf.{u, v, r} B X' Λ ≅
    forgetModuleSheaf.{u, v, r} B Y' Λ ⋙ abPullback.{u, max v r} B f')
  (modPullG : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B Y' Λ)
  (modPullP : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B X' Λ)
  [modPullG.Additive] [PreservesFiniteLimits modPullG] [PreservesFiniteColimits modPullG]
  [modPullP.Additive] [PreservesFiniteLimits modPullP] [PreservesFiniteColimits modPullP]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X' Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B Y' Λ)]
  (bcMod : fShriekMod.{u, v, r} B Λ f ⋙ modPullG ≅
    modPullP ⋙ fShriekMod.{u, v, r} B Λ f')
  (epsMod : modPullF ⋙ modPullP ≅ modPullG ⋙ modPullF')
  (w : X.obj → ℤ)
  (τ : ∀ M : ModuleSheaf.{u, v, r} B Y Λ,
    (fShriekMod.{u, v, r} B Λ f).obj (modPullF.obj M) ⟶ M)
  (hτ : ∀ M, HasWeightedTraceStalksMod.{u, v, r} B Λ f modPullF hpullF w M (τ M))
  (τ' : ∀ N : ModuleSheaf.{u, v, r} B Y' Λ,
    (fShriekMod.{u, v, r} B Λ f').obj (modPullF'.obj N) ⟶ N)
  (hτ' : ∀ N, HasWeightedTraceStalksMod.{u, v, r} B Λ f' modPullF' hpullF'
    (w ∘ B.inclusion.map p) N (τ' N))

omit [modPullP.Additive] [PreservesFiniteLimits modPullP] [PreservesFiniteColimits modPullP]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, v, r} B X' Λ)] in
include sq in
/-- **Stacks 0GKH, part (3) at arbitrary coefficient universes.** Let `f : X ⟶ Y` be locally
quasi-finite, let `w` be an integer-valued function on `X`, let `Λ` be a ring, and let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square. Suppose given, for each sheaf of `Λ`-modules `M` on the small étale site
of `Y`, a morphism `τ M : f_! f^{-1}M ⟶ M` whose underlying morphism of abelian sheaves has the
behaviour on geometric stalks by which Stacks 0GKG characterises the trace of `(f, w)`, and
likewise a family `τ'` for `(f', w ∘ p)`; and suppose the square formed by the two comparisons
attached to the cartesian square and those two families commutes, which is part (2) of Stacks
0GKH at `Λ`-coefficients. Then:

* `f^{-1}` and `f_!` are exact on sheaves of `Λ`-modules, so each induces a functor on unbounded
  derived categories, and the family `τ` induces a natural transformation
  `Tr_{f, w} : f_! f^{-1} ⟶ id` of `D(Y_étale, Λ)`, whose component at `K` is
  `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`;
* that transformation is **functorial in `K`**: every naturality square commutes;
* it **restricts to the sheaf-level trace**: it is the derived form of the natural
  transformation whose component at a sheaf of `Λ`-modules `M` is `τ M`, read through the
  canonical identification of the derived functor of `f^{-1} ⋙ f_!` with the composite of the
  derived functors and of the derived functor of the identity with the identity; and the
  component of that sheaf-level transformation at `M` is `τ M`;
* it is **compatible with arbitrary base change**: the derived form of the base-change square
  commutes, with the two derived traces appearing whiskered by the derived `g^{-1}`;
* and the weight attached to the base change is the right one: `w ∘ p` is a weighting of `f'`
  whenever `w` is a weighting of `f`, which is Stacks 0F3B.

The trace maps enter through the behaviour on geometric stalks by which Stacks 0GKG
characterises them; by `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` there is
at most one morphism per sheaf of `Λ`-modules with that behaviour, so the families `τ` and `τ'`
are the trace maps. The weighting hypothesis of the source is not needed: the statement holds for
an arbitrary integer-valued `w`, the pulled-back function `w ∘ p` being a weighting of `f'`
whenever `w` is a weighting of `f` by Stacks 0F3B.

This is the form at arbitrary coefficient universes, where the base-change square at
`Λ`-coefficients is an input; see `AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec`
for the form in which the `Λ`-linear inverse images, the comparisons and the trace maps are
constructed. -/
public theorem derivedWeightedTrace_spec
    (hbc : (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
          bcMod epsMod).hom ≫
        Functor.whiskerLeft modPullG
          (weightedTraceModNatTrans.{u, v, r} B Λ f' modPullF' hpullF'
            (w ∘ B.inclusion.map p) τ' hτ') =
      Functor.whiskerRight
        (weightedTraceModNatTrans.{u, v, r} B Λ f modPullF hpullF w τ hτ) modPullG) :
    letI := additive_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
    letI := additive_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
    (∀ (K K' : DerivedCategory (ModuleSheaf.{u, v, r} B Y Λ)) (ψ : K ⟶ K'),
        (modPullF.mapDerivedCategory ⋙
            (fShriekMod.{u, v, r} B Λ f).mapDerivedCategory).map ψ ≫
            (derivedWeightedTrace.{u, v, t, r} B Λ f modPullF hpullF w τ hτ).app K' =
          (derivedWeightedTrace.{u, v, t, r} B Λ f modPullF hpullF w τ hτ).app K ≫ ψ) ∧
      (derivedWeightedTrace.{u, v, t, r} B Λ f modPullF hpullF w τ hτ =
          (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
              modPullF (fShriekMod.{u, v, r} B Λ f)).inv ≫
            NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, v, r} B Λ f modPullF hpullF w τ hτ) ≫
            (Functor.mapDerivedCategoryIdIso _).hom) ∧
      (∀ M : ModuleSheaf.{u, v, r} B Y Λ,
          (weightedTraceModNatTrans.{u, v, r} B Λ f modPullF hpullF w τ hτ).app M = τ M) ∧
      (NatTrans.mapDerivedCategory
            (traceBaseChangeComparison.{u, v, r} B Λ f' f modPullF modPullF' modPullG modPullP
              bcMod epsMod).hom ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
            (modPullF' ⋙ fShriekMod.{u, v, r} B Λ f')).hom ≫
          Functor.whiskerLeft modPullG.mapDerivedCategory
            (NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, v, r} B Λ f' modPullF' hpullF'
                (w ∘ B.inclusion.map p) τ' hτ')) ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
            (𝟭 (ModuleSheaf.{u, v, r} B Y' Λ))).inv =
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (modPullF ⋙ fShriekMod.{u, v, r} B Λ f) modPullG).hom ≫
          Functor.whiskerRight
            (NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, v, r} B Λ f modPullF hpullF w τ hτ))
            modPullG.mapDerivedCategory ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (𝟭 (ModuleSheaf.{u, v, r} B Y Λ)) modPullG).inv) ∧
      (AlgebraicGeometry.IsWeighting (B.inclusion.map f) w →
        AlgebraicGeometry.IsWeighting (B.inclusion.map f') (w ∘ B.inclusion.map p)) := by
  let := additive_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
  let := preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
  let := preservesFiniteColimits_of_forgetModPullIso.{u, v, r} B Λ f modPullF hpullF
  let := additive_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
  let := preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
  let := preservesFiniteColimits_of_forgetModPullIso.{u, v, r} B Λ f' modPullF' hpullF'
  refine ⟨fun _ _ ψ =>
      derivedWeightedTrace_naturality.{u, v, t, r} B Λ f modPullF hpullF w τ hτ ψ,
    derivedWeightedTrace_eq.{u, v, t, r} B Λ f modPullF hpullF w τ hτ,
    fun M => weightedTraceModNatTrans_app.{u, v, r} B Λ f modPullF hpullF w τ hτ M, ?_,
    fun hw => AlgebraicGeometry.IsWeighting.comp_of_isPullback hw (sq.map B.inclusion)⟩
  exact derivedWeightedTrace_baseChange_whisker.{u, v, t, r} B Λ f' f modPullF modPullF'
    modPullG modPullP bcMod epsMod _ _ hbc

end Tagged

section Transport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Mutually inverse morphisms of abelian sheaves on `X` induce mutually inverse maps on the
direct sum of the stalks over a geometric fibre of `f`. -/
public theorem fiberStalksMap_comp_eq_id (s : GeometricPoint Y.obj)
    {G₁ G₂ : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (a : G₁ ⟶ G₂) (b : G₂ ⟶ G₁) (hab : a ≫ b = 𝟙 G₁) :
    AddCommGrpCat.ofHom (fiberStalksMap.{u, u + 1} B f s a) ≫
        AddCommGrpCat.ofHom (fiberStalksMap.{u, u + 1} B f s b) = 𝟙 _ := by
  refine fiberStalks_hom_ext.{u, u + 1} B f s fun x z => ?_
  have h1 := fiberStalksMap_fiberStalkOf.{u, u + 1} B f s a x z
  have h2 := fiberStalksMap_fiberStalkOf.{u, u + 1} B f s b x
    ((colim.map (Functor.whiskerLeft (Functor.Elements.π
      (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op a.hom)) z)
  have h3 := etaleStalk_map_comp_eq_id B X.obj X.property
    (x.toGeometricPoint B f s) a b hab z
  change (fiberStalksMap.{u, u + 1} B f s b)
      ((fiberStalksMap.{u, u + 1} B f s a)
        (fiberStalkOf.{u, u + 1} B f s G₁ x z)) =
    fiberStalkOf.{u, u + 1} B f s G₁ x z
  rw [h1, h2]
  exact congrArg (fun m => (ConcreteCategory.hom (fiberStalkOf.{u, u + 1} B f s G₁ x)) m) h3

/-- **The weighted trace behaviour on geometric stalks is transported along an isomorphism of
the sheaf on the base.** If `τ : f_! f^{-1}G₁ ⟶ G₁` has the behaviour on geometric stalks which
characterises the trace of Stacks 0GKG and `α : G₁ ≅ G₂`, then the morphism
`f_! f^{-1}G₂ ⟶ G₂` obtained by conjugating `τ` with `α` has it too. On the summand of the
stalk decomposition of Stacks 0F5F indexed by a point `x` of a geometric fibre both sides are
the weight of `x` times a germ, the two germs being matched by the naturality of the
identification of Stacks 03Q1 above `x`. -/
public theorem hasWeightedTraceStalks_of_iso (w : X.obj → ℤ)
    {G₁ G₂ : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}}
    (α : G₁ ≅ G₂)
    {τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj G₁) ⟶ G₁}
    (h : HasWeightedTraceStalks.{u, u + 1} B f w G₁ τ) :
    HasWeightedTraceStalks.{u, u + 1} B f w G₂
      ((fShriekFunctor.{u, u + 1} B f).map ((abPullback.{u, u + 1} B f).map α.inv) ≫
        τ ≫ α.hom) := by
  refine hasWeightedTraceStalks_of_fiberStalkOf.{u, u + 1} B f w G₂ _ fun s x z => ?_
  -- split the stalk map of the composite into its three factors
  have hsplit := congrArg
    (fun m => (ConcreteCategory.hom m)
      ((fShriekStalkIso.{u, u + 1} B f s ((abPullback.{u, u + 1} B f).obj G₂)).inv
        (fiberStalkOf.{u, u + 1} B f s ((abPullback.{u, u + 1} B f).obj G₂) x z)))
    ((etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{u + 1}).map_comp
      (((fShriekFunctor.{u, u + 1} B f).map ((abPullback.{u, u + 1} B f).map α.inv)).hom)
      ((τ ≫ α.hom).hom))
  refine hsplit.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  -- the first factor moves the summand across the inverse image of `α`
  have hfirst := fShriekStalkIso_inv_natural_apply.{u} B f s
    ((abPullback.{u, u + 1} B f).map α.inv)
    (fiberStalkOf.{u, u + 1} B f s ((abPullback.{u, u + 1} B f).obj G₂) x z)
  have hsummand := fiberStalksMap_fiberStalkOf.{u, u + 1} B f s
    ((abPullback.{u, u + 1} B f).map α.inv) x z
  refine (congrArg (fun m => ((etaleStalkPresheafFunctor B Y.obj Y.property s
      AddCommGrpCat.{u + 1}).map ((τ ≫ α.hom).hom)) m)
    (hfirst.trans (congrArg (fun m => (fShriekStalkIso.{u, u + 1} B f s
      ((abPullback.{u, u + 1} B f).obj G₁)).inv m) hsummand))).trans ?_
  -- split the remaining two factors and use the hypothesis on the summand
  have hrest := congrArg
    (fun m => (ConcreteCategory.hom m)
      ((fShriekStalkIso.{u, u + 1} B f s ((abPullback.{u, u + 1} B f).obj G₁)).inv
        (fiberStalkOf.{u, u + 1} B f s ((abPullback.{u, u + 1} B f).obj G₁) x
          ((colim.map (Functor.whiskerLeft (Functor.Elements.π
            (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op
            ((abPullback.{u, u + 1} B f).map α.inv).hom)) z))))
    ((etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{u + 1}).map_comp
      τ.hom α.hom.hom)
  refine hrest.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  have hτ := hasWeightedTraceStalks_fiberStalkOf.{u, u + 1} B f w G₁ h s x
    ((colim.map (Functor.whiskerLeft (Functor.Elements.π
      (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op
      ((abPullback.{u, u + 1} B f).map α.inv).hom)) z)
  refine (congrArg (fun m => (ConcreteCategory.hom
      ((etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{u + 1}).map
        α.hom.hom)) m) hτ).trans ?_
  refine (map_zsmul _ _ _).trans ?_
  refine congrArg (fun m => w (x.1 default) • m) ?_
  have hnat := ConcreteCategory.congr_hom
    (fiberPointPullbackStalkIso_natural.{u, u + 1} B f s α.hom x)
    ((colim.map (Functor.whiskerLeft (Functor.Elements.π
      (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s))).op
      ((abPullback.{u, u + 1} B f).map α.inv).hom)) z)
  have hcancel := etaleStalk_map_comp_eq_id B X.obj X.property
    (x.toGeometricPoint B f s) ((abPullback.{u, u + 1} B f).map α.inv)
    ((abPullback.{u, u + 1} B f).map α.hom)
    (by rw [← CategoryTheory.Functor.map_comp, α.inv_hom_id,
      CategoryTheory.Functor.map_id]) z
  refine ((ConcreteCategory.comp_apply _ _ _).symm.trans
    (hnat.trans (ConcreteCategory.comp_apply _ _ _))).symm.trans ?_
  exact congrArg (fun m => (ConcreteCategory.hom
    (fiberPointPullbackStalkIso.{u, u + 1} B f s G₂ x).hom) m) hcancel

end Transport

/-! ### The base-change square at `Λ`-coefficients -/

section ModBaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
  (sq : IsPullback p f' f g)
  (modPullF : ModuleSheaf.{u, u + 1, u} B Y Λ ⥤ ModuleSheaf.{u, u + 1, u} B X Λ)
  (hpullF : modPullF ⋙ forgetModuleSheaf.{u, u + 1, u} B X Λ ≅
    forgetModuleSheaf.{u, u + 1, u} B Y Λ ⋙ abPullback.{u, u + 1} B f)
  (modPullF' : ModuleSheaf.{u, u + 1, u} B Y' Λ ⥤ ModuleSheaf.{u, u + 1, u} B X' Λ)
  (hpullF' : modPullF' ⋙ forgetModuleSheaf.{u, u + 1, u} B X' Λ ≅
    forgetModuleSheaf.{u, u + 1, u} B Y' Λ ⋙ abPullback.{u, u + 1} B f')
  (modPullG : ModuleSheaf.{u, u + 1, u} B Y Λ ⥤ ModuleSheaf.{u, u + 1, u} B Y' Λ)
  (hpullG : modPullG ⋙ forgetModuleSheaf.{u, u + 1, u} B Y' Λ ≅
    forgetModuleSheaf.{u, u + 1, u} B Y Λ ⋙ abPullback.{u, u + 1} B g)
  (modPullP : ModuleSheaf.{u, u + 1, u} B X Λ ⥤ ModuleSheaf.{u, u + 1, u} B X' Λ)
  (hpullP : modPullP ⋙ forgetModuleSheaf.{u, u + 1, u} B X' Λ ≅
    forgetModuleSheaf.{u, u + 1, u} B X Λ ⋙ abPullback.{u, u + 1} B p)
  (bcMod : fShriekMod.{u, u + 1, u} B Λ f ⋙ modPullG ≅
    modPullP ⋙ fShriekMod.{u, u + 1, u} B Λ f')
  (epsMod : modPullF ⋙ modPullP ≅ modPullG ⋙ modPullF')

/-- **Part (2) of Stacks 0GKH at `Λ`-coefficients.** For a cartesian square, the square formed
by the two comparisons attached to it at `Λ`-coefficients — the base-change isomorphism
`g^{-1}f_!N ≅ f'_!p^{-1}N` of Stacks 0F5J and the comparison `p^{-1}f^{-1}M ≅ f'^{-1}g^{-1}M` of
the two iterated inverse images, each a lift of its abelian counterpart — and the two families of
trace maps commutes. Forgetting the module structure is faithful, so it is enough to check the
square on underlying abelian sheaves, where the two identifications carry it to part (2) at
abelian coefficients, `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange`, applied
to the transported traces; the transport is
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_of_iso`, needed because the trace at
`Λ`-coefficients for the base change lives on `g^{-1}` of a sheaf of `Λ`-modules while part (2)
speaks of the abelian `g^{-1}` of the underlying abelian sheaf. -/
public theorem hasWeightedTraceStalksMod_baseChange
    (hbcForget : ∀ n : ModuleSheaf.{u, u + 1, u} B X Λ,
      (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map (bcMod.hom.app n) ≫
          (fShriekModForgetIso.{u, u + 1, u} B Λ f').hom.app (modPullP.obj n) ≫
          (fShriekFunctor.{u, u + 1} B f').map (hpullP.hom.app n) =
        hpullG.hom.app ((fShriekMod.{u, u + 1, u} B Λ f).obj n) ≫
          (abPullback.{u, u + 1} B g).map
            ((fShriekModForgetIso.{u, u + 1, u} B Λ f).hom.app n) ≫
          (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
            ((forgetModuleSheaf.{u, u + 1, u} B X Λ).obj n))
    (hepsForget : ∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
      (forgetModuleSheaf.{u, u + 1, u} B X' Λ).map (epsMod.hom.app M) ≫
          hpullF'.hom.app (modPullG.obj M) ≫
          (abPullback.{u, u + 1} B f').map (hpullG.hom.app M) =
        hpullP.hom.app (modPullF.obj M) ≫
          (abPullback.{u, u + 1} B p).map (hpullF.hom.app M) ≫
          (inverseImageSquareIso.{u} B p f' f g sq).hom.app
            ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M))
    (w : X.obj → ℤ)
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
      (fShriekMod.{u, u + 1, u} B Λ f).obj (modPullF.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f modPullF hpullF w M (τ M))
    (τ' : ∀ N : ModuleSheaf.{u, u + 1, u} B Y' Λ,
      (fShriekMod.{u, u + 1, u} B Λ f').obj (modPullF'.obj N) ⟶ N)
    (hτ' : ∀ N, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f' modPullF' hpullF'
      (w ∘ B.inclusion.map p) N (τ' N)) :
    (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f modPullF modPullF' modPullG modPullP
          bcMod epsMod).hom ≫
        Functor.whiskerLeft modPullG
          (weightedTraceModNatTrans.{u, u + 1, u} B Λ f' modPullF' hpullF'
            (w ∘ B.inclusion.map p) τ' hτ') =
      Functor.whiskerRight
        (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ) modPullG := by
  refine NatTrans.ext (funext fun M => ?_)
  refine (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map_injective ?_
  refine (Iso.cancel_iso_hom_right _ _ (hpullG.app M)).1 ?_
  have hσ := hasWeightedTraceStalks_of_iso.{u} B f' (w ∘ B.inclusion.map p)
    (hpullG.app M) (hτ' (modPullG.obj M))
  have hpart2 := (hasWeightedTraceStalks_baseChange.{u} B p f' f g sq w
    ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M) (hτ M)).2 _ hσ
  dsimp only [Iso.app_hom, Iso.app_inv] at hpart2
  have hT := forgetModTrace_conjugate.{u, u + 1, u} B Λ f modPullF hpullF M (τ M)
  have hT' := forgetModTrace_conjugate.{u, u + 1, u} B Λ f' modPullF' hpullF'
    (modPullG.obj M) (τ' (modPullG.obj M))
  have hTG : forgetModTrace.{u, u + 1, u} B Λ f' modPullF' hpullF' (modPullG.obj M)
          (τ' (modPullG.obj M)) ≫ hpullG.hom.app M =
      (fShriekFunctor.{u, u + 1} B f').map
          ((abPullback.{u, u + 1} B f').map (hpullG.hom.app M)) ≫
        (fShriekFunctor.{u, u + 1} B f').map
          ((abPullback.{u, u + 1} B f').map (hpullG.inv.app M)) ≫
        forgetModTrace.{u, u + 1, u} B Λ f' modPullF' hpullF' (modPullG.obj M)
          (τ' (modPullG.obj M)) ≫ hpullG.hom.app M := by
    rw [← CategoryTheory.Functor.map_comp_assoc (fShriekFunctor.{u, u + 1} B f')
        ((abPullback.{u, u + 1} B f').map (hpullG.hom.app M))
        ((abPullback.{u, u + 1} B f').map (hpullG.inv.app M)),
      ← CategoryTheory.Functor.map_comp (abPullback.{u, u + 1} B f')
        (hpullG.hom.app M) (hpullG.inv.app M),
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hGnat := hpullG.hom.naturality (τ M)
  have hlF'nat := (fShriekModForgetIso.{u, u + 1, u} B Λ f').hom.naturality (epsMod.hom.app M)
  have hbcNnat := (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.naturality (hpullF.hom.app M)
  dsimp only [Functor.comp_map] at hGnat hlF'nat hbcNnat
  have hepsS := congrArg (fun m => (fShriekFunctor.{u, u + 1} B f').map m) (hepsForget M)
  simp only [CategoryTheory.Functor.map_comp] at hepsS
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    traceBaseChangeComparison, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, weightedTraceModNatTrans_app, Iso.app_hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hT', hGnat, ← hT]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hTG]
  rw [reassoc_of% hlF'nat, reassoc_of% hepsS,
    reassoc_of% (hbcForget (modPullF.obj M)), ← reassoc_of% hbcNnat, hpart2]

/-- Sheafification of presheaves of `Λ`-modules on the small étale site at the coefficient
universe `u + 1`, for a ring in `Type u`. This is
`AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf` with its universes written out: once the
coefficient universe has collapsed to `u + 1` the general instance's `max (u + 1) v r` no longer
determines `v` and `r`, and instance resolution reports the universe constraint as stuck, so the
specialization is recorded separately. -/
public instance hasSheafify_moduleSheaf_ofTypeU (B : BigEtaleSite.{u}) (S : B.Scheme)
    (Λ : Type u) [Ring Λ] :
    HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, u + 1, u} B S Λ

variable [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y' Λ)]

omit [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)] in
include sq in
/-- **Stacks 0GKH, part (3): the weighted trace with coefficients in a ring, on unbounded
derived categories.** Let `f : X ⟶ Y` be locally quasi-finite, let `w` be an integer-valued
function on `X`, let `Λ` be a ring, and let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square. Take for each of the four morphisms a `Λ`-linear inverse image, that is a
functor on sheaves of `Λ`-modules together with an isomorphism identifying it with the abelian
`f^{-1}` of Stacks 03Q1 on underlying abelian sheaves, and take the two comparisons attached to
the square — the base-change isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J and the
comparison `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images — again as lifts
of the abelian ones, each with the identification of its underlying morphism of abelian sheaves
with its abelian counterpart. Suppose given, for each sheaf of `Λ`-modules `M` on the small
étale site of `Y`, a morphism `τ M : f_! f^{-1}M ⟶ M` whose underlying morphism of abelian
sheaves has the behaviour on geometric stalks by which Stacks 0GKG characterises the trace of
`(f, w)`, and likewise a family `τ'` for `(f', w ∘ p)`. Then:

* `f^{-1}` and `f_!` are exact on sheaves of `Λ`-modules — their exactness is read off the
  identifications above — so each induces a functor on unbounded derived categories, and the
  family `τ` induces a natural transformation `Tr_{f, w} : f_! f^{-1} ⟶ id` of `D(Y_étale, Λ)`,
  whose component at `K` is `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`;
* that transformation is **functorial in `K`**: every naturality square commutes;
* it **restricts to the sheaf-level trace**: it is the derived form of the natural
  transformation whose component at a sheaf of `Λ`-modules `M` is `τ M`, read through the
  canonical identification of the derived functor of `f^{-1} ⋙ f_!` with the composite of the
  derived functors and of the derived functor of the identity with the identity;
* it is **compatible with arbitrary base change**: the base-change square at `Λ`-coefficients
  holds, by `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_baseChange`, and its derived
  form commutes, with the two derived traces appearing whiskered by the derived `g^{-1}`;
* and the weight attached to the base change is the right one: `w ∘ p` is a weighting of `f'`
  whenever `w` is a weighting of `f`, which is Stacks 0F3B.

The trace maps enter through the behaviour on geometric stalks by which Stacks 0GKG
characterises them; by `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalksMod_unique` there is
at most one morphism per sheaf of `Λ`-modules with that behaviour, so the families `τ` and `τ'`
are the trace maps. The weighting hypothesis of the source is not needed: the statement holds for
an arbitrary integer-valued `w`.

The coefficient universes are the ones at which the base-change isomorphism of Stacks 0F5J is
available: the abelian étale sheaves have coefficients in `AddCommGrpCat.{u + 1}`, so the sheaves
of `Λ`-modules are taken at `ModuleSheaf.{u, u + 1, u}` with `Λ : Type u`. The general-universe
form of the first three clauses, with the base-change square at `Λ`-coefficients as an input, is
`AlgebraicGeometry.SmallEtale.derivedWeightedTrace_spec`.

This statement carries no attribute: it is the engine, run on whichever `Λ`-linear inverse
images, comparisons and trace maps one has in hand. The registered form of the tag is
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction`,
which is this conjunction run on the `Λ`-linear inverse image
`AlgebraicGeometry.SmallEtale.pullbackMod`, the two comparisons
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` and
`AlgebraicGeometry.SmallEtale.inverseImageSquareMod`, and the trace maps
`AlgebraicGeometry.SmallEtale.weightedTraceMod`, all four constructed there, with the two
compatibilities below proved for them. -/
public theorem derivedWeightedTrace_spec_of_lifts
    (hbcForget : ∀ n : ModuleSheaf.{u, u + 1, u} B X Λ,
      (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map (bcMod.hom.app n) ≫
          (fShriekModForgetIso.{u, u + 1, u} B Λ f').hom.app (modPullP.obj n) ≫
          (fShriekFunctor.{u, u + 1} B f').map (hpullP.hom.app n) =
        hpullG.hom.app ((fShriekMod.{u, u + 1, u} B Λ f).obj n) ≫
          (abPullback.{u, u + 1} B g).map
            ((fShriekModForgetIso.{u, u + 1, u} B Λ f).hom.app n) ≫
          (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
            ((forgetModuleSheaf.{u, u + 1, u} B X Λ).obj n))
    (hepsForget : ∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
      (forgetModuleSheaf.{u, u + 1, u} B X' Λ).map (epsMod.hom.app M) ≫
          hpullF'.hom.app (modPullG.obj M) ≫
          (abPullback.{u, u + 1} B f').map (hpullG.hom.app M) =
        hpullP.hom.app (modPullF.obj M) ≫
          (abPullback.{u, u + 1} B p).map (hpullF.hom.app M) ≫
          (inverseImageSquareIso.{u} B p f' f g sq).hom.app
            ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M))
    (w : X.obj → ℤ)
    (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
      (fShriekMod.{u, u + 1, u} B Λ f).obj (modPullF.obj M) ⟶ M)
    (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f modPullF hpullF w M (τ M))
    (τ' : ∀ N : ModuleSheaf.{u, u + 1, u} B Y' Λ,
      (fShriekMod.{u, u + 1, u} B Λ f').obj (modPullF'.obj N) ⟶ N)
    (hτ' : ∀ N, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f' modPullF' hpullF'
      (w ∘ B.inclusion.map p) N (τ' N)) :
    letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
    letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
    letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
    letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
    letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
    letI := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
    (∀ (K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) (ψ : K ⟶ K'),
        (modPullF.mapDerivedCategory ⋙
            (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
            (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ).app K' =
          (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ).app K ≫ ψ) ∧
      (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ =
          (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
              modPullF (fShriekMod.{u, u + 1, u} B Λ f)).inv ≫
            NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ) ≫
            (Functor.mapDerivedCategoryIdIso _).hom) ∧
      (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
          (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ).app M = τ M) ∧
      (NatTrans.mapDerivedCategory
            (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f modPullF modPullF' modPullG
              modPullP bcMod epsMod).hom ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
            (modPullF' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
          Functor.whiskerLeft modPullG.mapDerivedCategory
            (NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, u + 1, u} B Λ f' modPullF' hpullF'
                (w ∘ B.inclusion.map p) τ' hτ')) ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
            (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (modPullF ⋙ fShriekMod.{u, u + 1, u} B Λ f) modPullG).hom ≫
          Functor.whiskerRight
            (NatTrans.mapDerivedCategory
              (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ))
            modPullG.mapDerivedCategory ≫
          (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ)) modPullG).inv) ∧
      (AlgebraicGeometry.IsWeighting (B.inclusion.map f) w →
        AlgebraicGeometry.IsWeighting (B.inclusion.map f') (w ∘ B.inclusion.map p)) := by
  let := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
  let := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
  let := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
  let := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
  let := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
  let := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
  let := additive_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
  let := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
  let := preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
  exact derivedWeightedTrace_spec.{u, u + 1, t, u} B Λ p f' f g sq modPullF hpullF modPullF'
    hpullF' modPullG modPullP bcMod epsMod w τ hτ τ' hτ'
    (hasWeightedTraceStalksMod_baseChange.{u} B Λ p f' f g sq modPullF hpullF modPullF' hpullF'
      modPullG hpullG modPullP hpullP bcMod epsMod hbcForget hepsForget w τ hτ τ' hτ')

end ModBaseChange

end AlgebraicGeometry.SmallEtale

end

