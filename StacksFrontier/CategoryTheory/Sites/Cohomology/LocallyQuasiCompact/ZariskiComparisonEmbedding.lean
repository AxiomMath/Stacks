module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Topology.Compactness.LocallyCompact
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.StacksAttribute

/-!
# The Zariski comparison morphism is an embedding of topoi

Let `X` be an object of the locally quasi-compact Zariski site `LC_Zar`, and let
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)` be the comparison morphism of topoi given by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonAdjunction`, induced by the
open-subset functor
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice`. Part of Stacks 0DCU is the
assertion that the unit of the comparison adjunction on abelian sheaves is an isomorphism, i.e.
that the inverse image `π_X^{-1}` is fully faithful: the Zariski topos of the space `X` sits
inside the topos of the localized big site.

Both come from properties of the functor `opensToSlice` itself, proved here:

* it is **full** — a map `U → V` in the slice over `X` between two open immersions forces
  `U ⊆ V`, and then the inclusion is the unique such map, because the structure morphism of `V`
  is a monomorphism;
* it is **cocontinuous** — if a sieve on `U → X` in the slice covers it in the Zariski topology
  of the big site, then its arrows are open immersions which jointly cover `U`, so their images
  form an open covering of `U` in the small site `X_Zar`, and each member of that covering
  factors through an arrow of the sieve.

Fullness and faithfulness of `opensToSlice`, together with continuity and cocontinuity, make
`π_X^{-1} = g_!` fully faithful by Stacks 00XU
(`CategoryTheory.Functor.full_and_faithful_sheafPullback`), and a left adjoint is fully
faithful exactly when the unit of its adjunction is an isomorphism.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_full`: `opensToSlice` is
  full.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_isCocontinuous`:
  `opensToSlice` is cocontinuous.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonAdjunction_unit_isIso`:
  the unit of the comparison adjunction on abelian sheaves is an isomorphism.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImage_fullyFaithful` and
  `comparisonAdjunction_unit_isIso`: the same on sheaves of sets, for coefficients in any
  universe containing the universe of the spaces.

## Implementation notes

Invertibility is stated for the unit natural transformation rather than object by object, which
retains the canonicality and the naturality in the sheaf that the source asserts.

Cocontinuity needs the Zariski precoverage to have isomorphisms, to be stable under composition
and to be stable under base change. All three are inherited from the open-embedding precoverage
of `TopCat`, which is why the proof first arranges that the inclusion of the bounded
subcategory into `TopCat` preserves fibre products: that is the content of the `CountableCategory`
and `IsClosedUnderLimitsOfShape` steps, which transport the cospan shape through
`ULiftHom (ULift WalkingCospan)` so that the bounded subcategory's closure under *countable*
limits applies to it.

Stacks 0DCU numbers seven clauses, the last of which the source splits into (7a) and (7b), and
each is in the library and carries the tag where it is stated: the cohomology comparison
`zariskiCohomologyComparisonIso` (1), the exactness of the direct image
`abelianComparisonDirectImage_exact` (2), the invertibility of the unit
`abelianComparisonAdjunction_unit_isIso` (3), its derived counterpart
`abelianDerivedComparisonAdjunction_unit_isIso` (4), the commutative square
`zariskiComparisonSquareIso` (5), the relative cohomology comparison
`relativeZariskiCohomologyIso` (6), and the compatibility of the comparison with pushforward
along a *proper* morphism, `properDirectImageComparisonIsoOfProperMap` (7a) and
`properDerivedImageComparison_isIso` (7b). The clause stated in this file is (3).

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The inclusion of the bounded subcategory of the quasi-compact site into `TopCat` preserves
fibre products: the cospan shape is transported through `ULiftHom (ULift WalkingCospan)`, where
the closure of the bounded subcategory under *countable* limits applies to it. -/
theorem preservesLimitsOfShape_walkingCospan_inclusionToTop
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    PreservesLimitsOfShape WalkingCospan
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop) := by
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let _ : CreatesLimitsOfShape (ULiftHom (ULift.{u} WalkingCospan))
      (locallyQuasiCompactHausdorffToTop.{u}) :=
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv WalkingCospan)
      (locallyQuasiCompactHausdorffToTop.{u})
  let _ : HasLimitsOfShape (ULiftHom (ULift.{u} WalkingCospan)) TopCat := inferInstance
  let _ : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun Y : LocallyQuasiCompactHausdorff.{u} => lcSize Y < S.qcSite.cutoff)
      (ULiftHom (ULift.{u} WalkingCospan)) :=
    S.qcSite.boundedSubcategory.closedUnderCountableLimits (ULiftHom (ULift.{u} WalkingCospan))
  let _ : HasLimitsOfShape (ULiftHom (ULift.{u} WalkingCospan))
      LocallyQuasiCompactHausdorff.{u} :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (locallyQuasiCompactHausdorffToTop.{u})
  let _ : CreatesLimitsOfShape (ULiftHom (ULift.{u} WalkingCospan)) E := inferInstance
  let _ : CreatesLimitsOfShape WalkingCospan E :=
    createsLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv WalkingCospan).symm E
  infer_instance

/-- The Zariski precoverage is stable under composition, being pulled back from the
open-embedding precoverage of `TopCat`. -/
theorem zariskiPrecoverage_isStableUnderComposition
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    S.zariskiPrecoverage.IsStableUnderComposition := by
  show (TopCat.precoverage.comap
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)).IsStableUnderComposition
  infer_instance

/-- The Zariski precoverage contains the isomorphisms, being pulled back from the open-embedding
precoverage of `TopCat`. -/
theorem zariskiPrecoverage_hasIsos
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    S.zariskiPrecoverage.HasIsos := by
  show (TopCat.precoverage.comap
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)).HasIsos
  infer_instance

/-- The Zariski precoverage is stable under base change: fibre products exist in the bounded
subcategory and are computed in `TopCat`, where the open-embedding precoverage is stable under
base change. -/
theorem zariskiPrecoverage_isStableUnderBaseChange
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    S.zariskiPrecoverage.IsStableUnderBaseChange := by
  let _ := preservesLimitsOfShape_walkingCospan_inclusionToTop S
  show (TopCat.precoverage.comap
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)).IsStableUnderBaseChange
  infer_instance

/-- The open-subset functor `Opens X ⥤ LC_Zar/X` is full: a morphism over `X` between the open
immersions of two opens `U` and `V` forces `U ≤ V`, and it then agrees with the inclusion,
because the structure morphism of `V` is injective. -/
theorem opensToSlice_full
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) : (S.opensToSlice X).1.Full := by
  constructor
  intro U V f
  have hUV : U ≤ V := fun x hx => by
    obtain ⟨y, hy⟩ := ((S.opensToSlice X).2 U).2.ge hx
    exact ((S.opensToSlice X).2 V).2.le
      ⟨f.left y, (ConcreteCategory.congr_hom (Over.w f) y).trans hy⟩
  refine ⟨homOfLE hUV, ?_⟩
  have : Mono ((S.opensToSlice X).1.obj V).hom :=
    ConcreteCategory.mono_of_injective _ ((S.opensToSlice X).2 V).1.injective
  exact Over.OverMorphism.ext ((cancel_mono ((S.opensToSlice X).1.obj V).hom).1
    ((Over.w ((S.opensToSlice X).1.map (homOfLE hUV) : _ ⟶ _)).trans (Over.w f).symm))

/-- An open immersion `f : Z₀ ⟶ U` over `X` whose image is the open `V ≤ U` factors the
inclusion of `V` into `U`: the structure morphism of `V` lifts through `f`, because the lift is
continuous for the subspace topology that `f` induces on its image. -/
theorem exists_comp_eq_opensToSlice_map_left
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    {U V : Opens X.obj} (hVU : V ≤ U) {Z₀ : S.category}
    (f : Z₀ ⟶ ((S.opensToSlice X).1.obj U).left)
    (hf : IsOpenEmbedding ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f))
    (hV : Set.range (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f ≫
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
        ((S.opensToSlice X).1.obj U).hom) : _ → X.obj) = V.carrier) :
    ∃ g : ((S.opensToSlice X).1.obj V).left ⟶ Z₀,
      g ≫ f = ((S.opensToSlice X).1.map (homOfLE hVU)).left := by
  let G := (S.opensToSlice X).1
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let p : E.obj (G.obj U).left ⟶ TopCat.of X.obj := E.map (G.obj U).hom
  let q : E.obj Z₀ ⟶ TopCat.of X.obj := E.map f ≫ p
  let r : E.obj ((G.obj V).left) ⟶ TopCat.of X.obj := E.map (G.obj V).hom
  have hq : Topology.IsOpenEmbedding q := ((S.opensToSlice X).2 U).1.comp hf
  have hRange : Set.range (q : E.obj Z₀ → X.obj) = Set.range (r : _ → X.obj) :=
    hV.trans ((S.opensToSlice X).2 V).2.symm
  choose φ hφ using fun z : E.obj ((G.obj V).left) => hRange.ge (Set.mem_range_self z)
  have hφ_cont : Continuous φ := hq.isInducing.continuous_iff.mpr <| by
    rw [show (q : E.obj Z₀ → X.obj) ∘ φ = r from funext hφ]
    exact (ConcreteCategory.hom r).continuous
  let e : E.obj ((G.obj V).left) ⟶ E.obj Z₀ := TopCat.ofHom ⟨φ, hφ_cont⟩
  have hVOverE : E.map (G.map (homOfLE hVU)).left ≫ p = E.map (G.obj V).hom := by
    rw [← Functor.map_comp, Over.w]
  have : Mono p :=
    ConcreteCategory.mono_of_injective _ (((S.opensToSlice X).2 U).1).injective
  refine ⟨E.preimage e,
    E.map_injective ((cancel_mono p).1 (ConcreteCategory.hom_ext _ _ fun z => ?_))⟩
  show (E.map (E.preimage e) ≫ E.map f ≫ p) z = (E.map (G.map (homOfLE hVU)).left ≫ p) z
  rw [Functor.map_preimage E e]
  exact (hφ z).trans (ConcreteCategory.congr_hom hVOverE.symm z)

/-- The image of an open immersion `f : Z₀ ⟶ U` over `X` is an open `V ≤ U` through which the
inclusion of `V` into `U` factors, and it contains every point of `X` hit by `f`. -/
theorem exists_opens_le_and_comp_eq_of_isOpenEmbedding
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (U : Opens X.obj) {Z₀ : S.category}
    (f : Z₀ ⟶ ((S.opensToSlice X).1.obj U).left)
    (hf : IsOpenEmbedding ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f))
    {x : X.obj} (z : (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Z₀)
    (hz : ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f ≫
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
        ((S.opensToSlice X).1.obj U).hom) z = x) :
    ∃ (V : Opens X.obj) (hVU : V ≤ U), x ∈ V ∧
      ∃ g : ((S.opensToSlice X).1.obj V).left ⟶ Z₀,
        g ≫ f = ((S.opensToSlice X).1.map (homOfLE hVU)).left := by
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let q : E.obj Z₀ ⟶ TopCat.of X.obj := E.map f ≫ E.map ((S.opensToSlice X).1.obj U).hom
  let V : Opens X.obj :=
    ⟨Set.range (q : E.obj Z₀ → X.obj), (((S.opensToSlice X).2 U).1.comp hf).isOpen_range⟩
  have hVU : V ≤ U := by
    rintro _ ⟨z', rfl⟩
    exact ((S.opensToSlice X).2 U).2.le ⟨E.map f z', rfl⟩
  exact ⟨V, hVU, ⟨z, hz⟩, exists_comp_eq_opensToSlice_map_left S X hVU f hf rfl⟩

/-- The open-subset functor is cocontinuous: a Zariski covering sieve of the open immersion
`U → X` in the localized big site consists of open immersions which jointly cover `U`, and the
opens they cut out form a covering of `U` in the small Zariski site of `X` each of whose members
factors through the sieve. -/
theorem opensToSlice_isCocontinuous
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    (S.opensToSlice X).1.IsCocontinuous (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X) := by
  let G := (S.opensToSlice X).1
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let _ := zariskiPrecoverage_isStableUnderComposition S
  let _ := zariskiPrecoverage_hasIsos S
  let _ := zariskiPrecoverage_isStableUnderBaseChange S
  let _ : G.Full := opensToSlice_full S X
  let _ : G.Faithful := inferInstance
  constructor
  intro U R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨T, hT, hTR⟩ : ∃ T ∈ S.zariskiPrecoverage (G.obj U).left,
      T ≤ (Sieve.overEquiv (G.obj U) R).arrows :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := S.zariskiPrecoverage)).mp hR
  have htop : T.map E ∈ TopCat.precoverage ((E.obj (G.obj U).left)) := by
    simpa [LocallyQuasiCompactZariskiSituation.zariskiPrecoverage, E] using hT
  obtain ⟨hjoint, hopen⟩ : T.map E ∈
      Types.jointlySurjectivePrecoverage.comap (forget TopCat) (E.obj (G.obj U).left) ∧
      T.map E ∈ TopCat.isOpenEmbedding.precoverage (E.obj (G.obj U).left) := htop
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hjoint
  intro x hx
  let p : E.obj (G.obj U).left ⟶ TopCat.of X.obj := E.map (G.obj U).hom
  obtain ⟨y, hy⟩ := ((S.opensToSlice X).2 U).2.ge hx
  obtain ⟨Z, g, hg, z, hz⟩ := hjoint y
  cases hg with
  | @of Z₀ f hf =>
    have hgf : IsOpenEmbedding (E.map f) := hopen (Presieve.map.of hf)
    obtain ⟨V, hVU, hxV, g', hmap⟩ := exists_opens_le_and_comp_eq_of_isOpenEmbedding S X U f hgf
      z ((congrArg p hz).trans hy)
    let α : Over.mk (f ≫ (G.obj U).hom) ⟶ G.obj U := Over.homMk f
    have hα : R α := (Sieve.overEquiv_iff R f).mp (hTR Z₀ f hf)
    let k : G.obj V ⟶ Over.mk (f ≫ (G.obj U).hom) := Over.homMk g' (by
      show g' ≫ f ≫ (G.obj U).hom = (G.obj V).hom
      rw [← Category.assoc, hmap]
      exact Over.w (G.map (homOfLE hVU)))
    have hk : k ≫ α = G.map (homOfLE hVU) := Over.OverMorphism.ext hmap
    refine ⟨V, homOfLE hVU, ?_, hxV⟩
    show R (G.map (homOfLE hVU))
    simpa only [hk] using R.downward_closed hα k

/-- The left adjoint of the comparison direct image is full and faithful, given the right Kan
extensions along `opensToSlice` and a right adjoint to the direct image. -/
private theorem comparisonDirectImage_leftAdjoint_full_and_faithful
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (A : Type t) [Category.{v} A]
    [∀ F : (Opens X.obj)ᵒᵖ ⥤ A, (S.opensToSlice X).1.op.HasPointwiseRightKanExtension F]
    [(S.comparisonDirectImage X A).IsRightAdjoint] :
    (S.comparisonDirectImage X A).leftAdjoint.Full ∧
      (S.comparisonDirectImage X A).leftAdjoint.Faithful := by
  let _ := S.opensToSlice_isContinuous X
  let _ := opensToSlice_isCocontinuous S X
  let _ := opensToSlice_full S X
  let _ : (S.opensToSlice X).1.Faithful := inferInstance
  let _ : ((S.opensToSlice X).1.sheafPushforwardContinuous A (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X)).IsRightAdjoint := ‹(S.comparisonDirectImage X A).IsRightAdjoint›
  exact Functor.full_and_faithful_sheafPullback (S.opensToSlice X).1 A _ _

/-- **Stacks 0DCU, the unit clause.** The unit of the Zariski comparison adjunction on abelian
sheaves is an isomorphism: the inverse image `π_X^{-1}` is fully faithful, because
`opensToSlice` is continuous, cocontinuous, full and faithful. -/
@[stacks 0DCU "unit_isomorphism"]
theorem abelianComparisonAdjunction_unit_isIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit := by
  let _ : ∀ F : (Opens X.obj)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (S.opensToSlice X).1.op.HasPointwiseRightKanExtension F := fun F => inferInstance
  let _ : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).IsRightAdjoint :=
    S.abelianComparisonDirectImage_isRightAdjoint.{u, w, max (u + 1) v} X
  have hff := comparisonDirectImage_leftAdjoint_full_and_faithful S X
    AddCommGrpCat.{max (u + 1) v}
  let _ : (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).Full := hff.1
  let _ : (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).Faithful := hff.2
  exact Adjunction.unit_isIso_of_L_fully_faithful
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)

/-- The comparison inverse image on sheaves of sets is full and faithful, for coefficients in any
universe containing the universe of the spaces: `opensToSlice` is continuous, cocontinuous, full
and faithful, and the right Kan extensions along it exist because the shapes computing them are
small in the universe of the spaces. -/
theorem comparisonInverseImage_fullyFaithful
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    (comparisonInverseImage.{u, w, t} S X).Full ∧
      (comparisonInverseImage.{u, w, t} S X).Faithful := by
  let A := Type (max u t)
  let _ : HasSheafify (S.zariskiTopology.over X) A := hasSheafify_zariskiTopology_over.{u, w, t} S X
  let _ : ∀ Z : (Over X)ᵒᵖ, Small.{max u t} (StructuredArrow Z (S.opensToSlice X).1.op) :=
    fun _ => small_lift.{u, t, u} _
  let _ : ∀ Z : (Over X)ᵒᵖ, HasLimitsOfShape (StructuredArrow Z (S.opensToSlice X).1.op) A :=
    fun _ => inferInstance
  let _ : ∀ F : (Opens X.obj)ᵒᵖ ⥤ A, (S.opensToSlice X).1.op.HasPointwiseRightKanExtension F :=
    fun _ _ => inferInstance
  let _ : (S.comparisonDirectImage X A).IsRightAdjoint :=
    comparisonDirectImage_isRightAdjoint.{u, w, t} S X
  exact comparisonDirectImage_leftAdjoint_full_and_faithful S X A

/-- **Stacks 0DCU, the unit clause, on sheaves of sets.** The unit of the Zariski comparison
adjunction on sheaves of sets is an isomorphism, because `comparisonInverseImage` is fully
faithful. The coefficients are types in any universe containing the universe of the spaces; the
case `t = u` is the one in which sheaves of sets on the underlying topological spaces live. -/
theorem comparisonAdjunction_unit_isIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    IsIso (comparisonAdjunction.{u, w, t} S X).unit := by
  obtain ⟨hfull, hfaithful⟩ := comparisonInverseImage_fullyFaithful.{u, w, t} S X
  exact Adjunction.unit_isIso_of_L_fully_faithful (comparisonAdjunction.{u, w, t} S X)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
