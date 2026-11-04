module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness
import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# Restriction to the small étale site of an algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, and fix an equivalence over the site between `𝒳` and the category of elements of the sheaf
of points of `F`. An étale chart `φ : U ⟶ F` is an element of that sheaf over `U`, so the
equivalence turns it into an object of `𝒳` over `U`; this is a functor `F_étale ⥤ 𝒳` which is
continuous and cocontinuous for the étale topology on `𝒳`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.costructuredArrowToElements`: the scheme charts of a
  presheaf of sets are its category of elements.
* `AlgebraicGeometry.Space.restrictionFunctor`: the functor `F_étale ⥤ 𝒳` induced by a chosen
  equivalence.
* `AlgebraicGeometry.Space.schemeChartFunctor`: its extension to all scheme charts of `F`.
* `AlgebraicGeometry.Space.restrictionToposHom` and
  `AlgebraicGeometry.Space.restrictionRingedToposHom`: the morphism of topoi, and of ringed topoi,
  `i_F : Sh(F_étale) ⟶ Sh(𝒳_étale)`.
* `AlgebraicGeometry.Space.restrictionSheafFunctor`: the restriction `ℱ ↦ ℱ|_{F_étale}`.
* `AlgebraicGeometry.Space.lowerShriek`: the inverse image `π_F^{-1} = i_{F,!}`, and
  `AlgebraicGeometry.Space.lowerShriekAdjunction`: `i_{F,!} ⊣ i_F^{-1}`.

## Main results

* `AlgebraicGeometry.Space.restrictionFunctor_comp`: the functor sends an étale chart to an
  object over the underlying scheme of that chart.
* `AlgebraicGeometry.Space.restrictionFunctor_isContinuous` and
  `AlgebraicGeometry.Space.restrictionFunctor_isCocontinuous`: it is continuous and
  cocontinuous for the étale topology on `𝒳`.
* `AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` and
  `AlgebraicGeometry.Space.hasPointwiseRightKanExtension_restrictionFunctor_op`: a category
  fibred in groupoids representable by `F` is essentially small at the universe of the schemes,
  and the right Kan extension along `F_étale ⥤ 𝒳` is computed pointwise at every sheaf of sets.
* `AlgebraicGeometry.Space.restrictionFunctor_coversTop` and
  `AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton`: the objects coming
  from étale charts, and already a single one of them, cover the final object of the inherited
  étale site of `𝒳`.
* `AlgebraicGeometry.Space.lowerShriek_preservesFiniteLimits` and
  `AlgebraicGeometry.Space.lowerShriek_preservesFiniteColimits`: `i_{F,!}` is exact on sheaves
  of sets, so `AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites` holds.
* `AlgebraicGeometry.Space.lowerShriekAdjunction_unit_isIso`: `π_F ∘ i_F = id`.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace CategoryTheory.PresheafOfCategories

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (G : Cᵒᵖ ⥤ Type v₁)

/-- A scheme chart `φ : yoneda.obj U ⟶ G` of a presheaf of sets, read as an element of `G` over
`U`: the two categories have the same objects and the same morphisms, the factorizations. -/
def costructuredArrowToElements :
    CostructuredArrow yoneda G ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj where
  obj X := ⟨X.left, Discrete.mk (yonedaEquiv X.hom)⟩
  map {X Y} f := ⟨f.left, Discrete.eqToHom (by
    calc yonedaEquiv X.hom = yonedaEquiv (yoneda.map f.left ≫ Y.hom) :=
          congrArg yonedaEquiv f.w.symm
      _ = G.map f.left.op (yonedaEquiv Y.hom) := (yonedaEquiv_naturality Y.hom f.left).symm)⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- The base of the element attached to a scheme chart `X` is `X.left`. -/
@[simp] theorem costructuredArrowToElements_obj_base (X : CostructuredArrow yoneda G) :
    ((costructuredArrowToElements G).obj X).base = X.left := rfl

/-- The element of `G` attached to a scheme chart `X` is `yonedaEquiv X.hom`. -/
@[simp] theorem costructuredArrowToElements_obj_fiber_as (X : CostructuredArrow yoneda G) :
    ((costructuredArrowToElements G).obj X).fiber.as = yonedaEquiv X.hom := rfl

/-- The comparison of the scheme charts of `G` with its category of elements is strictly over
the base category. -/
theorem costructuredArrowToElements_comp :
    costructuredArrowToElements G ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      CostructuredArrow.proj yoneda G := rfl

/-- The comparison of the scheme charts of `G` with its category of elements is full. -/
instance costructuredArrowToElements_full : (costructuredArrowToElements G).Full where
  map_surjective {X Y} f := by
    refine ⟨CostructuredArrow.homMk f.base (yonedaEquiv.injective ?_), ?_⟩
    · exact (yonedaEquiv_naturality Y.hom f.base).symm.trans
        (Discrete.eq_of_hom f.fiber).symm
    · exact elements_hom_ext _ _ rfl

/-- The comparison of the scheme charts of `G` with its category of elements is faithful. -/
instance costructuredArrowToElements_faithful : (costructuredArrowToElements G).Faithful where
  map_injective h := CostructuredArrow.hom_ext _ _ (congrArg (fun t => t.base) h)

/-- The comparison of the scheme charts of `G` with its category of elements is essentially
surjective. -/
instance costructuredArrowToElements_essSurj : (costructuredArrowToElements G).EssSurj where
  mem_essImage X :=
    ⟨CostructuredArrow.mk (yonedaEquiv.symm X.fiber.as),
      ⟨elementsIsoOfBaseIso (Iso.refl X.base) (by simp; rfl)⟩⟩

/-- The scheme charts of `G` are equivalent to its category of elements. -/
instance costructuredArrowToElements_isEquivalence :
    (costructuredArrowToElements G).IsEquivalence where

end CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The functor `F_étale ⥤ 𝒳` attached to an equivalence over the site between a category
fibred in groupoids `𝒳` and the category of elements of the sheaf of points of `F`: an étale
chart of `F` is an element of that sheaf, hence an object of `𝒳`. -/
noncomputable def restrictionFunctor
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    SmallEtale B S hS F ⥤ 𝒳 :=
  SmallEtale.inclusion B S hS F ⋙
    PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor

/-- The object of `𝒳` attached to an étale chart of `F` lies over the underlying scheme of that
chart. -/
theorem restrictionFunctor_comp
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    restrictionFunctor B S hS F p e ⋙ p = SmallEtale.toOver B S hS F := by
  rw [restrictionFunctor, Functor.assoc, Functor.assoc, e.inv.w,
    PresheafOfCategories.costructuredArrowToElements_comp]

/-- The functor `F_étale ⥤ 𝒳` is full. -/
instance restrictionFunctor_full
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (restrictionFunctor B S hS F p e).Full :=
  letI : e.inv.functor.Full := inferInstanceAs e.toEquivalence.inverse.Full
  inferInstanceAs (SmallEtale.inclusion B S hS F ⋙
    PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor).Full

/-- The functor `F_étale ⥤ 𝒳` is faithful. -/
instance restrictionFunctor_faithful
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (restrictionFunctor B S hS F p e).Faithful :=
  letI : e.inv.functor.Faithful := inferInstanceAs e.toEquivalence.inverse.Faithful
  inferInstanceAs (SmallEtale.inclusion B S hS F ⋙
    PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor).Faithful

/-- The functor `F_étale ⥤ 𝒳` preserves pullbacks. -/
instance restrictionFunctor_preservesPullbacks
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    PreservesLimitsOfShape WalkingCospan (restrictionFunctor B S hS F p e) :=
  letI : e.inv.functor.IsEquivalence := inferInstanceAs e.toEquivalence.inverse.IsEquivalence
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (SmallEtale.inclusion B S hS F ⋙
      PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor))

/-! ### Continuity -/

private theorem presieve_map_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (H : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (G ⋙ H) = (R.map G).map H := by
  funext Y f
  exact propext ⟨fun ⟨h⟩ => ⟨⟨h⟩⟩, fun ⟨⟨h⟩⟩ => ⟨h⟩⟩

/-- The family of objects of the big fppf category of `S` underlying a covering family of étale
charts of `F` is a covering family for the étale topology localized at `S`. -/
private theorem map_toOver_mem_baseOverTopology {X : SmallEtale B S hS F} (R : Presieve X)
    (hR : R ∈ SmallEtale.precoverage B S hS F X) :
    R.map (SmallEtale.toOver B S hS F) ∈
      (BigFppfOver.baseOverTopology B S hS .etale).toPrecoverage
        ((SmallEtale.toOver B S hS F).obj X) := by
  obtain ⟨E, rfl, hE⟩ := hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff]
  show (Sieve.generate (E.presieve₀.map (SmallEtale.toOver B S hS F))).functorPushforward
    (Over.forget (B.obj hS)) ∈ _
  rw [← Sieve.generate_map_eq_functorPushforward, ← presieve_map_comp]
  exact Precoverage.Saturate.of _ _
    ⟨E.map (SmallEtale.toSchemes B S hS F), by simp only [PreZeroHypercover.presieve₀_map], hE⟩

/-- **Stacks 073M.** The functor `F_étale ⥤ 𝒳` is continuous for the étale topology on `𝒳`: it
preserves fibre products and carries a covering family of étale charts to a covering family of
the inherited étale topology, the images of its members being strongly cartesian. -/
@[stacks 073M "continuity of the functor from the small étale site of the space"]
theorem restrictionFunctor_isContinuous (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (restrictionFunctor B S hS F p e).IsContinuous
      (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale) := by
  have hcp : CoverPreserving (SmallEtale.precoverage B S hS F).toGrothendieck
      (BigFppfOver.associatedTopology B S hS p .etale) (restrictionFunctor B S hS F p e) := by
    refine coverPreserving_of_generators _ (SmallEtale.precoverage B S hS F) _ ?_
    intro X R hR
    rw [← Sieve.generate_map_eq_functorPushforward]
    refine Precoverage.Saturate.of _ _ ⟨fun _ f _ => hp.isStronglyCartesian f, ?_⟩
    rw [← presieve_map_comp]
    exact (congrArg (fun Q : SmallEtale B S hS F ⥤ BigFppfOver B S hS =>
      R.map Q ∈ (BigFppfOver.baseOverTopology B S hS .etale).toPrecoverage (Q.obj X))
      (restrictionFunctor_comp B S hS F p e)).mpr
        (map_toOver_mem_baseOverTopology B S hS F R hR)
  let _ : Functor.PreservesOneHypercovers.{u + 1} (restrictionFunctor B S hS F p e)
      (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale) :=
    Functor.PreservesOneHypercovers.of_coverPreserving hcp
  infer_instance

/-! ### Cocontinuity -/

/-- A covering sieve for the big étale topology carried by `B` is refined by a chosen étale
covering family. -/
private theorem etale_exists_covering_refining_sieve {Y : B.Schemes} {R : Sieve Y}
    (hR : R ∈ B.etaleTopology Y) :
    ∃ E : PreZeroHypercover.{u + 1} Y, B.etaleCovering ⟨_, E⟩ ∧ E.presieve₀ ≤ R := by
  change R ∈ B.etalePrecoverage.toGrothendieck Y at hR
  induction hR with
  | of Y P hP =>
      obtain ⟨E, rfl, hE⟩ := hP
      exact ⟨E, hE, Sieve.le_generate _⟩
  | top Y =>
      exact ⟨PreZeroHypercover.singleton (𝟙 Y),
        (AlgebraicGeometry.etaleCovering_isSite B).1 (𝟙 Y), by intro Z f hf; trivial⟩
  | pullback Y R hR Z f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ :=
        (AlgebraicGeometry.etaleCovering_isSite B).2.2 ⟨Y, E⟩ hE Z f
      refine ⟨⟨E.I₀, P, p₂⟩, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive Y R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      choose H hH hHle using fun i : E.I₀ => ihRQ (hle _ _ ⟨i⟩)
      refine ⟨E.bind H, (AlgebraicGeometry.etaleCovering_isSite B).2.1 ⟨Y, E⟩ hE
        (fun i => ⟨E.X i, H i⟩) hH (fun _ => rfl), ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, k⟩
      exact hHle i _ _ ⟨k⟩

/-- An étale morphism of the big fppf category of `S` into the scheme underlying an étale chart
of `F` is itself an étale chart of `F`. -/
private def etaleCoverChart (U : SmallEtale B S hS F)
    {V : B.Schemes} (f : V ⟶ U.obj.left.left) (hf : Etale (B.inclusion.map f)) :
    SmallEtale B S hS F :=
  let v : BigFppfOver B S hS := Over.mk (f ≫ U.obj.left.hom)
  let a : v ⟶ U.obj.left := Over.homMk f
  ⟨CostructuredArrow.mk (yoneda.map a ≫ U.obj.hom),
    etale_comp_of_scheme B S hS a U.obj.hom hf U.property⟩

/-- The morphism of étale charts underlying `AlgebraicGeometry.Space.etaleCoverChart`. -/
private def etaleCoverChartMap (U : SmallEtale B S hS F)
    {V : B.Schemes} (f : V ⟶ U.obj.left.left) (hf : Etale (B.inclusion.map f)) :
    etaleCoverChart B S hS F U f hf ⟶ U :=
  ⟨CostructuredArrow.homMk (Over.homMk f)⟩

private theorem sieve_over_mem_of_map_mem {C : Type*} [Category C] {U : C}
    {X Y : Over U} (R : Sieve X) (f : Y ⟶ X)
    (hf : (R.functorPushforward (Over.forget U)) f.left) : R f := by
  obtain ⟨Z, g, a, hg, ha⟩ := hf
  change f.left = a ≫ g.left at ha
  have hw : a ≫ Z.hom = Y.hom := by
    rw [← g.w, ← Category.assoc, ← ha]
    exact f.w
  have hb : (Over.homMk a hw : Y ⟶ Z) ≫ g = f := Over.OverMorphism.ext ha.symm
  rw [← hb]
  exact R.downward_closed hg _

/-- **Stacks 073M.** The canonical functor from the small étale site of `F` to the big fppf
category of `S` is cocontinuous for the étale topology: an étale covering of the scheme
underlying a chart is refined by a covering family of charts. -/
theorem toOver_isCocontinuous :
    (SmallEtale.toOver B S hS F).IsCocontinuous
      (SmallEtale.topology B S hS F) (BigFppfOver.baseOverTopology B S hS .etale) := by
  constructor
  intro U R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := etale_exists_covering_refining_sieve B hR
  have he (i : E.I₀) : Etale (B.inclusion.map (E.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).1 hE.2).2 i
  let H : PreZeroHypercover.{u + 1} U :=
    ⟨E.I₀, fun i => etaleCoverChart B S hS F U (E.f i) (he i),
      fun i => etaleCoverChartMap B S hS F U (E.f i) (he i)⟩
  have hH : SmallEtale.IsCovering B S hS F ⟨U, H⟩ := hE
  refine (SmallEtale.topology B S hS F).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck ⟨H, rfl, hH⟩)
  rw [Presieve.ofArrows_le_iff]
  exact fun i => sieve_over_mem_of_map_mem R _ (hER (E.X i) (E.f i) (Presieve.ofArrows.mk i))

private theorem sieve_mem_of_map_mem {C D : Type*} [Category C] [Category D]
    (q : C ⥤ D) {X Y : C} (R : Sieve X)
    (hcart : ∀ ⦃Z : C⦄ (f : Z ⟶ X), R f → q.IsStronglyCartesian (q.map f) f)
    (f : Y ⟶ X) (hf : (R.functorPushforward q) (q.map f)) : R f := by
  obtain ⟨Z, g, a, hg, ha⟩ := hf
  let _ := hcart g hg
  obtain ⟨b, ⟨_, hb⟩, _⟩ := Functor.IsStronglyCartesian.universal_property
    q (q.map g) g a (q.map f) ha f
  rw [← hb]
  exact R.downward_closed hg b

/-- **Stacks 073M.** The functor `F_étale ⥤ 𝒳` is cocontinuous for the étale topology on `𝒳`: a
covering sieve of the image of a chart pulls back to a covering sieve of that chart, because its
image under the structure functor already does and the members of a covering sieve of the
inherited topology are strongly cartesian. -/
@[stacks 073M "cocontinuity of the functor from the small étale site of the space"]
theorem restrictionFunctor_isCocontinuous (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (restrictionFunctor B S hS F p e).IsCocontinuous
      (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale) := by
  let _ := hp.isFibered
  let _ := toOver_isCocontinuous B S hS F
  let _ := Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered p
    (BigFppfOver.baseOverTopology B S hS .etale)
  set G := restrictionFunctor B S hS F p e with hG
  set q := SmallEtale.toOver B S hS F with hq
  let cmp : G ⋙ p ≅ q := eqToIso (restrictionFunctor_comp B S hS F p e)
  constructor
  intro U R hR
  have hpush := (CoverPreserving.of_isContinuous p
    (p.inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale))
    (BigFppfOver.baseOverTopology B S hS .etale)).cover_preserve hR
  have hc := q.cover_lift (SmallEtale.topology B S hS F)
    (BigFppfOver.baseOverTopology B S hS .etale)
    ((BigFppfOver.baseOverTopology B S hS .etale).pullback_stable (cmp.inv.app U) hpush)
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hc
  intro V f hf
  refine sieve_mem_of_map_mem p R (fun _ f _ => hp.isStronglyCartesian f) (G.map f) ?_
  have hh := (R.functorPushforward p).downward_closed hf (cmp.hom.app V)
  have hn : cmp.hom.app V ≫ q.map f ≫ cmp.inv.app U = (G ⋙ p).map f := by
    rw [cmp.inv.naturality, ← Category.assoc, cmp.hom_inv_id_app, Category.id_comp]
  change (R.functorPushforward p) (cmp.hom.app V ≫ q.map f ≫ cmp.inv.app U) at hh
  rwa [hn] at hh

/-! ### Smallness of the representing category -/

/-- The scheme charts of `F`, read as objects of `𝒳`: the functor `F_étale ⥤ 𝒳` of the source
extends to all scheme charts, not only the étale ones. -/
noncomputable def schemeChartFunctor
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    CostructuredArrow yoneda F ⥤ 𝒳 :=
  PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor

/-- The functor of the source is the restriction of `schemeChartFunctor` to the étale charts. -/
theorem restrictionFunctor_eq_inclusion_comp_schemeChartFunctor
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    restrictionFunctor B S hS F p e =
      SmallEtale.inclusion B S hS F ⋙ schemeChartFunctor B S hS F p e :=
  rfl

/-- A scheme chart of `F` is sent to an object of `𝒳` over its underlying scheme. -/
theorem schemeChartFunctor_comp
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    schemeChartFunctor B S hS F p e ⋙ p = CostructuredArrow.proj yoneda F := by
  rw [schemeChartFunctor, Functor.assoc, e.inv.w,
    PresheafOfCategories.costructuredArrowToElements_comp]

/-- The scheme charts of `F` are equivalent to `𝒳`. -/
instance schemeChartFunctor_isEquivalence
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (schemeChartFunctor B S hS F p e).IsEquivalence :=
  letI : e.inv.functor.IsEquivalence := inferInstanceAs e.toEquivalence.inverse.IsEquivalence
  inferInstanceAs (PresheafOfCategories.costructuredArrowToElements F ⋙
    e.inv.functor).IsEquivalence

/-- A category fibred in groupoids representable by `F` is essentially small at the universe of
the schemes: a chosen equivalence identifies it with the scheme charts of `F`, and those are
essentially small because the big fppf category is. -/
theorem essentiallySmall_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    EssentiallySmall.{u} 𝒳 :=
  EssentiallySmall.mk' ((e.toEquivalence.trans
    (PresheafOfCategories.costructuredArrowToElements F).asEquivalence.symm).trans
      (equivSmallModel.{u} (CostructuredArrow yoneda F)))

/-- A category fibred in groupoids representable by `F` is locally small at the universe of the
schemes. -/
theorem locallySmall_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    LocallySmall.{u} 𝒳 :=
  let : e.hom.functor.Faithful := inferInstanceAs e.toEquivalence.functor.Faithful
  locallySmall_of_faithful.{u} e.hom.functor

/-- The direct image of `i_F` exists: the right Kan extension along the functor `F_étale ⥤ 𝒳`
is computed pointwise at every sheaf of sets.

The comma categories indexing it are essentially small at the universe of the schemes, because
the small étale site is and `𝒳` is locally small; so the limits computing the extension are
limits of sets in that universe. -/
theorem hasPointwiseRightKanExtension_restrictionFunctor_op
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (G : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :
    (restrictionFunctor B S hS F p e).op.HasPointwiseRightKanExtension G := by
  have : LocallySmall.{u} 𝒳 := locallySmall_of_equivalenceOver B S hS F p e
  intro Y
  exact (hasLimitsOfShape_of_essentiallySmall.{u}
    (StructuredArrow Y (restrictionFunctor B S hS F p e).op) (Type u)).has_limit _

section DirectImage

universe v' w'

/-- The direct image along a 1-morphism between two categories representable by algebraic
spaces exists: for `f : 𝒳 ⥤ 𝒴` with `𝒳` representable by `F` and `𝒴` by `G`, the right Kan
extension along `f.op` of every presheaf of sets in the universe of the schemes is computed
pointwise.

The comma categories indexing it are essentially small at the universe of the schemes, because
`𝒳` is essentially small and `𝒴` locally small there, both by their chosen equivalences with
the scheme charts of `F` and of `G`. So the direct image `f_*` of Stacks 06W6 between the
associated étale topoi needs no size hypothesis in the situation of Stacks 073N. -/
theorem hasPointwiseRightKanExtension_op_of_equivalenceOver
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {𝒴 : Type v'} [Category.{w'} 𝒴]
    (q : 𝒴 ⥤ BigFppfOver B S hS)
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⥤ 𝒴) (P : 𝒳ᵒᵖ ⥤ Type u) :
    f.op.HasPointwiseRightKanExtension P := by
  have : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p eF
  have : LocallySmall.{u} 𝒴 := locallySmall_of_equivalenceOver B S hS G q eG
  intro Y
  exact (hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Y f.op) (Type u)).has_limit _

end DirectImage

/-! ### The morphism of ringed topoi `i_F` and the restriction of sheaves -/

section RingedTopoi

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Stacks 073M.** The morphism of topoi `i_F : Sh(F_étale) ⟶ Sh(𝒳_étale)` induced by the
continuous and cocontinuous functor `F_étale ⥤ 𝒳`: its inverse image is restriction along that
functor and its direct image is the right Kan extension along it. -/
@[stacks 073M "the morphism of topoi i_F"]
noncomputable def restrictionToposHom (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS F) (Type u))
      (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :=
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  letI := restrictionFunctor_isCocontinuous B S hS F p hp e
  letI := hasPointwiseRightKanExtension_restrictionFunctor_op B S hS F p e
  Functor.morphismOfTopoiOfCocontinuous (restrictionFunctor B S hS F p e)
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)

/-- **Stacks 073M, equation 075K.** The inverse image of `i_F` is restriction along the functor
`F_étale ⥤ 𝒳`. This is the source's `π_{F,*} = i_F^{-1}`: both send a sheaf `ℱ` to
`U ↦ ℱ(u(U))`.

It is also the left-hand identification `ℱ|_{F_étale} = i_F^{-1}ℱ` of equation 075K, the
right-hand side of this statement being the term that
`AlgebraicGeometry.Space.restrictionSheafFunctor` names `ℱ|_{F_étale}`. The right-hand
identification `ℱ|_{F_étale} = π_{F, *}ℱ` is
`AlgebraicGeometry.Space.projectionRingedToposHom_pushforward`. -/
@[stacks 075K "the identification `ℱ|_{F_étale} = i_F^{-1}ℱ`", stacks 073M "the inverse image \
of i_F is restriction along the functor"]
theorem restrictionToposHom_inverseImage (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    (restrictionToposHom B S hS F p hp e).inverseImage =
      (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale) :=
  rfl

/-- **Stacks 073M, equation 075K.** The restriction `ℱ|_{F_étale} = i_F^{-1}ℱ` of a sheaf on the
inherited étale site of `𝒳` to the small étale site of the algebraic space `F`. -/
@[stacks 075K]
noncomputable abbrev restrictionSheafFunctor (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS F) (Type u) :=
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)

/-- **Stacks 073M, equation 075K.** The sections of a restriction are the sections of the
original sheaf on the image of the chart: `ℱ|_{F_étale}(U) = ℱ(u(U))`. -/
@[simp, stacks 075K "sections of a restriction"]
theorem restrictionSheafFunctor_obj_obj (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (U : SmallEtale B S hS F) :
    ((restrictionSheafFunctor B S hS F p hp e).obj 𝓕).obj.obj (Opposite.op U) =
      𝓕.obj.obj (Opposite.op ((restrictionFunctor B S hS F p e).obj U)) :=
  rfl

/-- **Stacks 073M.** Restriction along the functor `F_étale ⥤ 𝒳` carries the structure sheaf of
`𝒳` to the structure sheaf of the small étale site of `F`, on the nose: both send a chart to the
ring of global functions on its underlying scheme. -/
@[stacks 073M "the restricted structure sheaf of the category is that of the space"]
theorem inverseImage_structureSheaf_eq (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    ((restrictionFunctor B S hS F p e).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale)).obj
        (FibredSite.structureSheaf B S hS p hp .etale) = structureSheaf B S hS F hF := by
  let _ := restrictionFunctor_isContinuous B S hS F p hp e
  apply ObjectProperty.FullSubcategory.ext
  show (restrictionFunctor B S hS F p e ⋙ p).op ⋙
      (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ =
    (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ
  rw [restrictionFunctor_comp]
  rfl

/-- **Stacks 073M.** The morphism of ringed topoi
`i_F : (Sh(F_étale), 𝒪_F) ⟶ (Sh(𝒳_étale), 𝒪_𝒳)`: the morphism of topoi `i_F` together with the
identification of the restricted structure sheaf of `𝒳` with the structure sheaf of `F`. -/
@[stacks 073M "the morphism of ringed topoi i_F"]
noncomputable def restrictionRingedToposHom (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) :
    RingedToposHom (smallEtaleRingedTopos B S hS ⟨F, hF⟩)
      (FibredSite.associatedRingedTopos B S hS p hp .etale) := by
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  letI := restrictionFunctor_isCocontinuous B S hS F p hp e
  letI := hasPointwiseRightKanExtension_restrictionFunctor_op B S hS F p e
  let f : MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS F) (Type u))
      (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u)) :=
    { pushforward := (restrictionFunctor B S hS F p e).sheafPushforwardCocontinuous (Type u)
        (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
      inverseImage := (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
      adj := (restrictionFunctor B S hS F p e).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
      preservesFiniteLimits := inferInstance }
  refine { toToposHom := f, fSharp := ?_ }
  refine (commRingImageAdjunction f).homEquiv _ _ ?_
  exact (restrictionCommRingIso (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale)
      (restrictionFunctor B S hS F p e)
      (FibredSite.structureSheaf B S hS p hp .etale)).hom ≫
    eqToHom (inverseImage_structureSheaf_eq B S hS F p hp e hF)

/-- **Stacks 073M.** The inverse image of the morphism of ringed topoi `i_F` is restriction
along the functor `F_étale ⥤ 𝒳`. -/
@[simp]
theorem restrictionRingedToposHom_inverseImage (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hF : IsAlgebraicSpace B S hS F) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    (restrictionRingedToposHom B S hS F p hp e hF).toToposHom.inverseImage =
      (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale) :=
  rfl

end RingedTopoi

/-! ### Products of charts -/

/-- The fibre product of two étale charts of `F` is already their product among all scheme
charts: the representing base change has the required universal property against an arbitrary
chart, not merely against an étale one. -/
private noncomputable def chartProdIsLimit (X Y : SmallEtale B S hS F) :
    Limits.IsLimit (Limits.BinaryFan.mk (SmallEtale.prodFst B S hS F X Y).hom
      (SmallEtale.prodSnd B S hS F X Y).hom) := by
  refine Limits.BinaryFan.isLimitMk (fun s => CostructuredArrow.homMk
    (X.property.rep.lift' (s.fst : s.pt ⟶ X.obj).left (s.snd : s.pt ⟶ Y.obj).left
      ((CostructuredArrow.w (s.fst : s.pt ⟶ X.obj)).trans
        (CostructuredArrow.w (s.snd : s.pt ⟶ Y.obj)).symm)) ?_) ?_ ?_ ?_
  · change yoneda.map _ ≫ yoneda.map (X.property.rep.snd Y.obj.hom) ≫ Y.obj.hom = _
    rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd]
    exact CostructuredArrow.w (s.snd : s.pt ⟶ Y.obj)
  · intro s
    exact CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.lift'_fst _ _ _ _)
  · intro s
    exact CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.lift'_snd _ _ _ _)
  · intro s m h₁ h₂
    have e₁ : m.left ≫ X.property.rep.fst' Y.obj.hom = (s.fst : s.pt ⟶ X.obj).left :=
      congrArg (fun f : s.pt ⟶ X.obj => f.left) h₁
    have e₂ : m.left ≫ X.property.rep.snd Y.obj.hom = (s.snd : s.pt ⟶ Y.obj).left :=
      congrArg (fun f : s.pt ⟶ Y.obj => f.left) h₂
    refine CostructuredArrow.hom_ext _ _ (Functor.relativelyRepresentable.hom_ext' _ ?_ ?_)
    · exact e₁.trans (Functor.relativelyRepresentable.lift'_fst _ _ _ _).symm
    · exact e₂.trans (Functor.relativelyRepresentable.lift'_snd _ _ _ _).symm

/-- The inclusion of the étale charts into all scheme charts of `F` preserves binary products,
both being the fibre product over `F`. -/
noncomputable instance smallEtaleInclusion_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (SmallEtale.inclusion B S hS F) := by
  have h (X Y : SmallEtale B S hS F) :
      PreservesLimit (Limits.pair X Y) (SmallEtale.inclusion B S hS F) :=
    Limits.preservesLimit_of_preserves_limit_cone (SmallEtale.prodIsLimit B S hS F X Y)
      ((Limits.isLimitMapConeBinaryFanEquiv _ _ _).symm (chartProdIsLimit B S hS F X Y))
  exact ⟨fun {K} => Limits.preservesLimit_of_iso_diagram _ (Limits.diagramIsoPair K).symm⟩

/-- The functor `F_étale ⥤ 𝒳` preserves binary products, which in the small étale site of `F`
are the fibre products over `F`. -/
noncomputable instance
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    PreservesLimitsOfShape (Discrete WalkingPair) (restrictionFunctor B S hS F p e) :=
  letI : e.inv.functor.IsEquivalence := inferInstanceAs e.toEquivalence.inverse.IsEquivalence
  inferInstanceAs (PreservesLimitsOfShape (Discrete WalkingPair)
    (SmallEtale.inclusion B S hS F ⋙
      PresheafOfCategories.costructuredArrowToElements F ⋙ e.inv.functor))

/-! ### The charts cover the final object -/

/-- A single surjective étale morphism of the big fppf category of `S` generates an étale
covering sieve of its target. -/
private theorem singleton_etale_mem {V W : B.Schemes} (f : V ⟶ W)
    [Etale (B.inclusion.map f)] [Surjective (B.inclusion.map f)] :
    Sieve.generate (Presieve.singleton f) ∈ B.etaleTopology W := by
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨PreZeroHypercover.singleton f, (PreZeroHypercover.presieve₀_singleton f).symm, ?_⟩
  constructor
  · constructor
    · show (PreZeroHypercover.singleton f).presieve₀.map B.inclusion ∈
        Scheme.fppfPrecoverage _
      rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
      exact Scheme.Hom.singleton_mem_fppfPrecoverage _
    · exact ((B.isSite).1 (𝟙 W)).2
  · show ((PreZeroHypercover.singleton f).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_singleton,
      Presieve.map_singleton]
    exact (Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨Surjective.surj, inferInstance⟩

/-- A morphism of `𝒳` whose image generates an étale covering sieve generates a covering sieve
of the inherited étale topology, its members being strongly cartesian. -/
private theorem singleton_inherited_etale_mem (hp : p.IsFiberedInGroupoids) {V W : 𝒳} (f : V ⟶ W)
    (hf : Sieve.generate (Presieve.singleton (p.map f)) ∈
      (BigFppfOver.baseOverTopology B S hS .etale) (p.obj W)) :
    Sieve.generate (Presieve.singleton f) ∈
      BigFppfOver.associatedTopology B S hS p .etale W := by
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨fun _ g _ => hp.isStronglyCartesian g, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_singleton]
  exact hf

/-- **Stacks 073M, by a single chart.** One object of `𝒳` already covers the final object of the
inherited étale site of `𝒳`: the object coming from an étale chart `A` of `F` built on a scheme
atlas of the algebraic space.

The surjective étale chart `φ : U ⟶ F` of the algebraic space does not depend on the object being
covered, so neither does the chart `A = (U ⟶ F)` it produces: for an object of `𝒳`, which is up
to isomorphism a scheme chart `V ⟶ F`, the base change `V ×_F U ⟶ V` of `φ` is a surjective
étale morphism, hence a one-element covering of that object, and it factors through `A` by its
other projection `V ×_F U ⟶ U`. So the single-object family `fun _ : Unit => A` suffices. -/
theorem exists_restrictionFunctor_coversTop_singleton (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    ∃ A : SmallEtale B S hS F,
      (BigFppfOver.associatedTopology B S hS p .etale).CoversTop
        (fun _ : Unit => (restrictionFunctor B S hS F p e).obj A) := by
  obtain ⟨U, a, ha, he⟩ := hF.exists_atlas
  set A : SmallEtale B S hS F := ⟨CostructuredArrow.mk a, he⟩
  refine ⟨A, ?_⟩
  set H := schemeChartFunctor B S hS F p e
  set K := BigFppfOver.associatedTopology B S hS p .etale
  have hc (V : CostructuredArrow yoneda F) :
      Sieve.ofObjects (fun _ : Unit => (restrictionFunctor B S hS F p e).obj A) (H.obj V) ∈
        K (H.obj V) := by
    let r := he.rep
    let W := CostructuredArrow.mk (yoneda.map (r.snd V.hom) ≫ V.hom)
    let b : W ⟶ V := CostructuredArrow.homMk (r.snd V.hom)
    let c : W ⟶ A.obj := CostructuredArrow.homMk (r.fst' V.hom) (by
      simpa only [W, A, CostructuredArrow.mk, Functor.relativelyRepresentable.map_fst'] using
        r.w V.hom)
    apply K.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_)
      (singleton_inherited_etale_mem B S hS p hp (H.map b) ?_)
    · rintro _ _ ⟨⟩
      exact ⟨(), ⟨H.map c⟩⟩
    · have hb : Sieve.generate (Presieve.singleton b.left) ∈
          (BigFppfOver.baseOverTopology B S hS .etale) V.left := by
        rw [GrothendieckTopology.mem_over_iff]
        show (Sieve.generate (Presieve.singleton b.left)).functorPushforward
          (Over.forget (B.obj hS)) ∈ _
        rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
        let : Etale (B.inclusion.map b.left.left) := he.property_snd V.hom
        let : Surjective (B.inclusion.map b.left.left) :=
          ha.property V.hom (r.fst V.hom) (r.snd V.hom) (r.isPullback V.hom)
        exact singleton_etale_mem B b.left.left
      exact (congrArg (fun Q : CostructuredArrow yoneda F ⥤ BigFppfOver B S hS =>
        Sieve.generate (Presieve.singleton (Q.map b)) ∈
          (BigFppfOver.baseOverTopology B S hS .etale) (Q.obj V))
        (schemeChartFunctor_comp B S hS F p e)).mpr hb
  exact fun X => K.superset_covering (fun _ _ hf => hf)
    (K.pullback_stable (H.objObjPreimageIso X).inv (hc (H.objPreimage X)))

/-- **Stacks 073M.** The objects of `𝒳` coming from étale charts of `F` cover the final object
of the inherited étale site of `𝒳`.

This is where the surjective étale chart `φ : U ⟶ F` of the algebraic space enters: an object of
`𝒳` is, up to isomorphism, a scheme chart `V ⟶ F`, and the base change `V ×_F U ⟶ V` of `φ` is a
surjective étale morphism from an étale chart, hence a one-element covering of that object. -/
theorem restrictionFunctor_coversTop (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    (BigFppfOver.associatedTopology B S hS p .etale).CoversTop
      (restrictionFunctor B S hS F p e).obj := by
  obtain ⟨A, hA⟩ := exists_restrictionFunctor_coversTop_singleton B S hS F p hF hp e
  intro X
  refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering ?_ (hA X)
  rintro T g ⟨_, ⟨b⟩⟩
  exact ⟨A, ⟨b⟩⟩

/-! ### The morphism of sites `π_F` -/

section LowerShriek

/-- The left Kan extension along the functor `F_étale ⥤ 𝒳` is computed pointwise on presheaves
of sets, the comma categories indexing it being essentially small at the universe of the
schemes. -/
theorem hasLeftKanExtension_restrictionFunctor_op
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    [EssentiallySmall.{u} 𝒳] (Q : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :
    (restrictionFunctor B S hS F p e).op.HasLeftKanExtension Q := by
  let (Y : 𝒳ᵒᵖ) : HasColimitsOfShape
      (CostructuredArrow (restrictionFunctor B S hS F p e).op Y) (Type u) :=
    hasColimitsOfShape_of_essentiallySmall.{u} _ _
  let : (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension Q :=
    fun Y => by infer_instance
  infer_instance

/-- **Stacks 073M.** The inverse image `π_F^{-1} = i_{F,!}` of the source: lower shriek along the
functor `F_étale ⥤ 𝒳`, the sheafification of the left Kan extension of a sheaf of sets on the
small étale site of `F`. It is the left adjoint of restriction `i_F^{-1}`. -/
@[stacks 073M "the inverse image i_F! of the morphism of sites"]
noncomputable def lowerShriek (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Sheaf (SmallEtale.topology B S hS F) (Type u) ⥤
      Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  letI : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  letI := hasLeftKanExtension_restrictionFunctor_op B S hS F p e
  (restrictionFunctor B S hS F p e).sheafPullback (Type u)
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)

/-- **Stacks 073M.** `π_{F,*} = i_F^{-1}` is right adjoint to `π_F^{-1} = i_{F,!}`.

This is the source's "Moreover `π_{F,*} = i_F^{-1}`": the direct image of `π_F` is restriction
along the functor `F_étale ⥤ 𝒳`, which is exactly the inverse image of `i_F` recorded by
`AlgebraicGeometry.Space.restrictionToposHom_inverseImage`. -/
@[stacks 073M "the direct image of the morphism of sites is the inverse image of i_F"]
noncomputable def lowerShriekAdjunction (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    lowerShriek B S hS F p hp e ⊣
      (restrictionFunctor B S hS F p e).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS F)
        (BigFppfOver.associatedTopology B S hS p .etale) := by
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  letI : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  letI := hasLeftKanExtension_restrictionFunctor_op B S hS F p e
  exact (restrictionFunctor B S hS F p e).sheafAdjunctionContinuous (Type u) _ _

/-- **Stacks 073M.** `i_{F,!}` is left exact on sheaves of sets.

This is the claim the source proves in order to define `π_F`: the small étale site of `F` has
binary products and fibre products, which the functor `F_étale ⥤ 𝒳` preserves, so the left Kan
extension is a pointwise filtered colimit and commutes with fibre products; and the images of the
étale charts cover the final object, which gives `i_{F,!}* = *`. -/
@[stacks 073M "left exactness of i_F! on sheaves of sets"]
theorem lowerShriek_preservesFiniteLimits (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    PreservesFiniteLimits (lowerShriek B S hS F p hp e) := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective (Type u) :=
    .ofEssentiallySmall.{_, _, _, _, u} _
  let := hasLeftKanExtension_restrictionFunctor_op B S hS F p e
  exact Stacks.Sites.LowerShriek.sheafPullback_preservesFiniteLimits_of_coversTop
    (restrictionFunctor B S hS F p e) _ _
    (restrictionFunctor_coversTop B S hS F p hF hp e)

/-- **Stacks 073M.** `i_{F,!}` is right exact on sheaves of sets, being a left adjoint. -/
@[stacks 073M "right exactness of i_F! on sheaves of sets"]
theorem lowerShriek_preservesFiniteColimits (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    PreservesFiniteColimits (lowerShriek B S hS F p hp e) := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let := (lowerShriekAdjunction B S hS F p hp e).isLeftAdjoint
  infer_instance

/-- **Stacks 073M.** The functor `F_étale ⥤ 𝒳` defines a morphism of sites
`π_F : 𝒳_étale ⟶ F_étale`: restriction along it has a left exact left adjoint, namely
`i_{F,!}`. -/
@[stacks 073M "the functor from the small etale site defines a morphism of sites"]
theorem restrictionFunctor_isMorphismOfSites (hF : IsAlgebraicSpace B S hS F)
    (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsMorphismOfSites.{u} (restrictionFunctor B S hS F p e)
      (SmallEtale.topology B S hS F)
      (BigFppfOver.associatedTopology B S hS p .etale) := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  exact { hasExactLeftAdjoint := ⟨lowerShriek B S hS F p hp e,
    ⟨lowerShriekAdjunction B S hS F p hp e⟩,
    lowerShriek_preservesFiniteLimits B S hS F p hF hp e⟩ }

/-- **Stacks 073M.** `π_F ∘ i_F = id`.

The inverse image of the composite is `i_F^{-1} ∘ π_F^{-1} = i_F^{-1} ∘ i_{F,!}`, so the
composite is the identity exactly when the unit `ℱ ⟶ i_F^{-1} i_{F,!} ℱ` of `i_{F,!} ⊣ i_F^{-1}`
is an isomorphism. That holds because the functor `F_étale ⥤ 𝒳` is continuous, cocontinuous and
fully faithful, which presents the small étale topos of `F` as a subtopos of that of `𝒳`. -/
@[stacks 073M "the unit of i_F! ⊣ i_F^{-1} is an isomorphism, so π_F ∘ i_F = id"]
theorem lowerShriekAdjunction_unit_isIso (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := restrictionFunctor_isContinuous B S hS F p hp e
    IsIso (lowerShriekAdjunction B S hS F p hp e).unit := by
  let _ := restrictionFunctor_isContinuous B S hS F p hp e
  let _ := restrictionFunctor_isCocontinuous B S hS F p hp e
  let _ := hasPointwiseRightKanExtension_restrictionFunctor_op B S hS F p e
  exact Functor.isIso_unit_of_sheafPushforwardContinuous
    (restrictionFunctor B S hS F p e) (Type u) _ _
    (lowerShriekAdjunction B S hS F p hp e)

end LowerShriek

end AlgebraicGeometry.Space

end
