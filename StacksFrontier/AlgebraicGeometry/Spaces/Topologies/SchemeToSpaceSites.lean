module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs
import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient

/-!
# The big scheme sites inside the big algebraic-space sites

Let `S` be a scheme and let `τ` be one of the étale, fppf and ph topologies. The canonical
inclusion of the big `τ` site of schemes over `S` into the big `τ` site of algebraic spaces
over `S` is a special cocontinuous functor in the sense of Stacks 03CG, and therefore
identifies the two topoi of sheaves.

## Main definitions

* `AlgebraicGeometry.etaleSchemeToSpace` is the inclusion for a big étale site of algebraic
  spaces whose chosen étale and fppf scheme cutoffs agree.
* `AlgebraicGeometry.etaleSchemeToSpaceSheafEquiv`,
  `AlgebraicGeometry.fppfSchemeToSpaceSheafEquiv` and
  `AlgebraicGeometry.phSchemeToSpaceSheafEquiv` are the resulting equivalences of topoi.

## Main results

* `AlgebraicGeometry.etaleSchemeToSpace_isSpecialCocontinuous`,
  `AlgebraicGeometry.fppfSchemeToSpace_isSpecialCocontinuous` and
  `AlgebraicGeometry.phSchemeToSpace_isSpecialCocontinuous`: **Stacks 0DFV** for the three
  topologies.

## Implementation notes

The three topologies are treated separately rather than uniformly in `τ`, because the three
big sites of algebraic spaces are three unrelated structures: their covering families are
given by three different predicates on families of morphisms of algebraic spaces, each with
its own proof that the site axioms hold, and the inclusion functor itself is a different
functor in each case. A common statement would have to quantify over a notion of big site of
algebraic spaces together with its inclusion from schemes, which this development does not
have, so it would be a weaker statement about a hypothetical structure rather than the same
theorem.

Algebraic spaces over `S` are presheaves on an auxiliary big fppf site of schemes, so a big
étale or ph site of algebraic spaces carries that auxiliary site alongside its own chosen
scheme site; the two are required to have the same cutoff, which identifies their underlying
categories of bounded schemes. The étale case records the agreement of the cutoffs as an
explicit hypothesis, since the big étale site of algebraic spaces stores the two cutoffs
separately.

Special cocontinuity is `IsSpecialCocontinuous`, that is cocontinuity together with
`CategoryTheory.Functor.IsDenseSubsite`, and the equivalence of topoi is the dense-subsite
sheaf equivalence attached to the latter. It is stated for sheaves of `Type (u + 1)`-valued
sets, the value category for which the limits computing the comparison exist on both sides.

For the ph topology the family of schemes underlying a chosen ph covering is *not* shown to
be a ph covering of algebraic spaces: that would require the base change of a ph covering of
schemes along a morphism from an affine scheme, which rests on Chow's lemma (Stacks 0202) and
is unavailable here. Cover preservation is obtained instead by refining twice, over the
affine opens of the base; see `ph_isCoverPreserving`.

## References

* [Stacks Project, Tag 0DFV](https://stacks.math.columbia.edu/tag/0DFV)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- An étale covering of algebraic spaces over `S` whose members are representable comes
from an étale covering of the representing schemes. -/
private theorem represented_etale_cover_mem_precoverage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (E : PreZeroHypercover.{v} V)
    (hE : AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun i => yoneda.obj (E.X i)) (fun i => yoneda.map (E.f i))) :
    (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let PF := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G
  have : CategoryTheory.Limits.HasPullbacks C := inferInstance
  have : CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan G := inferInstance
  have : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u).Faithful := inferInstance
  have : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u).Full := inferInstance
  have : PF.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro X Y Y' T f g f' g' hpb hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (hpb.map G) hf
  show (E.map G).presieve₀ ∈ Scheme.etalePrecoverage (G.obj V)
  apply (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (E.map G)).2
  constructor
  · intro x
    obtain ⟨i, y, hy⟩ :=
      AlgebraicGeometry.Space.exists_preimage_of_jointlySurjective_yoneda B S hS E.X V E.f
        hE.jointly_surjective x
    exact ⟨i, y, hy⟩
  · intro i
    have he' : PF.presheaf (𝟙 (yoneda.obj (E.X i)) ≫ yoneda.map (E.f i)) := by
      simpa using hE.etale i (E.X i) (𝟙 (yoneda.obj (E.X i)))
        (AlgebraicGeometry.Space.presheaf_etale_id B S hS (E.X i))
    show Etale (G.map (E.f i))
    exact (MorphismProperty.relative_map_iff (P := PF) (F := yoneda)
      (f := E.f i)).mp he'

/-- An fppf covering of algebraic spaces over `S` whose members are representable comes
from an fppf covering of the representing schemes. -/
private theorem represented_fppf_cover_mem_precoverage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (E : PreZeroHypercover.{v} V)
    (hE : AlgebraicGeometry.Space.IsFppfCovering B S hS
      (fun i => yoneda.obj (E.X i)) (fun i => yoneda.map (E.f i))) :
    (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) :=
  AlgebraicGeometry.Space.yoneda_fppfCovering_mem_fppfPrecoverage B S hS E.X V E.f hE

/-- Every algebraic space over `S` is covered by a single scheme of the big fppf site: a
surjective étale scheme atlas, read as a one-member étale covering. -/
private theorem exists_etale_atlas_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.AlgebraicSpaces B S hS) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ X.1),
      AlgebraicGeometry.Space.IsEtaleCovering B S hS
        (fun _ : Unit => yoneda.obj U) (fun _ => f) := by
  obtain ⟨U, f, hsurj, hetale⟩ := X.property.exists_atlas
  exact ⟨U, f, AlgebraicGeometry.Space.isEtaleCovering_atlas B S hS X.property hsurj hetale⟩

/-- Every algebraic space over `S` is covered by a single scheme of the big fppf site, with the
index type of the one-member étale covering lifted to `Type (u + 2)`. -/
private theorem exists_etale_atlas_cover_ulift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.AlgebraicSpaces B S hS) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ X.1),
      AlgebraicGeometry.Space.IsEtaleCovering B S hS
        (fun _ : ULift.{u + 2} Unit => yoneda.obj U) (fun _ => f) := by
  obtain ⟨U, f, htarget, hsource, hetale, hsurj⟩ := exists_etale_atlas_cover B S hS X
  exact ⟨U, f, htarget, fun _ => hsource (), fun _ => hetale (),
    by simpa only [Set.iUnion_const] using hsurj⟩

/-- A functor is cocontinuous for the topology generated by a precoverage as soon as the
pullback along the image of any morphism of a sieve generated by a covering family of that
precoverage is a covering sieve of the source. -/
private theorem isCocontinuous_of_generator_refinements
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (P : Precoverage D)
    (hgen : ∀ {X : D} (R : Presieve X), R ∈ P X →
      ∀ {Y : C} (f : F.obj Y ⟶ X),
        ((Sieve.generate R).pullback f).functorPullback F ∈ J Y) :
    F.IsCocontinuous J P.toGrothendieck := by
  constructor
  intro Y R hR
  rw [P.mem_toGrothendieck_iff] at hR
  have haux : ∀ {X : D} {S : Sieve X}, P.Saturate X S →
      ∀ {Z : C} (f : F.obj Z ⟶ X), (S.pullback f).functorPullback F ∈ J Z := by
    intro X S hS
    induction hS with
    | of X R hR =>
        intro Z f
        exact hgen R hR f
    | top X =>
        intro Z f
        exact J.top_mem Z
    | pullback X S hS Y' g ih =>
        intro Z f
        simpa [Sieve.pullback_comp] using ih (f := f ≫ g)
    | transitive X S R hS hSR ihS ihSR =>
        intro Z f
        apply J.transitive (ihS f)
        intro W g hg
        have hSg : S (F.map g ≫ f) := hg
        have hloc := ihSR hSg (𝟙 (F.obj W))
        have heq : Sieve.functorPullback F
            (Sieve.pullback (F.map g) (Sieve.pullback f R)) =
            Sieve.pullback g (Sieve.functorPullback F (Sieve.pullback f R)) := by
          ext V h
          simp [Sieve.functorPullback, Sieve.pullback_apply]
        have hloc' : Sieve.functorPullback F
            (Sieve.pullback (F.map g) (Sieve.pullback f R)) ∈ J W := by
          simpa [Sieve.pullback_id, Sieve.pullback_comp] using hloc
        rwa [heq] at hloc'
  simpa using haux hR (f := 𝟙 (F.obj Y))

/-- If a covering sieve of `X` is generated by a family of morphisms each of which factors
through the image of `F`, then the sieve of morphisms covered by images of `F` covers `X`. -/
private theorem coverDense_of_site_covering_refined_by_image
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (K : GrothendieckTopology D) {X : D}
    (E : PreZeroHypercover X) (hE : Sieve.generate E.presieve₀ ∈ K X)
    (himage : ∀ i, Presieve.coverByImage F X (E.f i)) :
    Sieve.coverByImage F X ∈ K X := by
  refine K.superset_covering ?_ hE
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact himage

/-- A covering sieve for the topology generated by the chosen covering families of a site is
refined by one of those families. -/
private theorem exists_siteCover_refining_sieve
    {C : Type*} [Category C] (Cov : Covering C → Prop) (hsite : IsSite Cov)
    (P : Precoverage C)
    (hrepr : ∀ {X : C} {R : Presieve X}, R ∈ P X →
      ∃ E : PreZeroHypercover X, R = E.presieve₀ ∧ Cov ⟨X, E⟩)
    {X : C} {R : Sieve X} (hR : R ∈ P.toGrothendieck X) :
    ∃ E : PreZeroHypercover X, Cov ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X P hP =>
      obtain ⟨E, hEq, hE⟩ := hrepr hP
      refine ⟨E, hE, ?_⟩
      rw [hEq]
      exact Sieve.le_generate _
  | top X =>
      exact ⟨PreZeroHypercover.singleton (𝟙 X), hsite.1 (𝟙 X), by simp⟩
  | pullback X R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := hsite.2.2 ⟨X, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive X R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose G hG hGle using hlocal
      let EG := E.bind G
      have hEG : Cov ⟨X, EG⟩ := by
        simpa [PreZeroHypercover.pushforward] using
          (hsite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, G i⟩) hG (fun _ ↦ rfl))
      refine ⟨EG, hEG, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      show Q ((G i).f j ≫ E.f i)
      exact hGle i _ _ ⟨j⟩

open CategoryTheory.Limits

/-- A chosen fppf covering of the underlying scheme of an object of the big fppf site of `S`
becomes an fppf covering of algebraic spaces over `S` under the Yoneda embedding. -/
private theorem localYonedaFppfCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (E : PreZeroHypercover T.left)
    (hE : B.IsCovering ⟨T.left, E⟩) :
    AlgebraicGeometry.Space.IsFppfCovering B S hS
      (fun i => yoneda.obj (Over.mk (E.f i ≫ T.hom)))
      (fun i => yoneda.map (Over.homMk (E.f i))) := by
  let V : E.I₀ → AlgebraicGeometry.BigFppfOver B S hS := fun i => Over.mk (E.f i ≫ T.hom)
  let g : ∀ i, V i ⟶ T := fun i => Over.homMk (E.f i)
  have hsite : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) := by
    simpa [AlgebraicGeometry.BigFppfSite.IsCovering, AlgebraicGeometry.IsFppfCovering,
      Scheme.fppfPrecoverage, PreZeroHypercover.presieve₀_map] using
      B.isFppfCovering_of_isCovering hE
  obtain ⟨hjoint, hprop⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hsite
  refine ⟨AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T,
    (fun i => AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (V i)),
    ?_, ?_, ?_⟩
  · intro i
    exact AlgebraicGeometry.Space.isFlat_yoneda_map B S hS (g i) (by
      show Flat ((E.f i).hom)
      exact (hprop i).1)
  · intro i
    exact AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map B S hS (g i) (by
      show LocallyOfFinitePresentation ((E.f i).hom)
      exact (hprop i).2)
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨i, y, hy⟩ :=
      AlgebraicGeometry.Space.exists_pointsMap_yonedaMap_eq_of_jointly_surjective B S hS g
        (fun z => by
          obtain ⟨i, y, hy⟩ := hjoint z
          exact ⟨i, y, hy⟩) x
    exact ⟨i, y, hy⟩

/-- A family satisfying the covering predicate generates a covering sieve of the topology of a
precoverage whose coverings are the chosen representatives of that predicate. -/
private theorem generate_mem_toGrothendieck_of_representative
    {C : Type u} [Category.{v} C] (Pred Cov : Covering.{u, v, w} C → Prop) (P : Precoverage C)
    (hP : ∀ {X : C} (E : PreZeroHypercover.{w} X), Cov ⟨X, E⟩ → E.presieve₀ ∈ P X)
    (hrep : ∀ E, Pred E → ∃ E', Cov E' ∧ Covering.CombEquiv E E')
    {X : C} (E : PreZeroHypercover.{w} X) (hE : Pred ⟨X, E⟩) :
    Sieve.generate E.presieve₀ ∈ P.toGrothendieck X := by
  obtain ⟨E', hE', hX, hcomb⟩ := hrep ⟨X, E⟩ hE
  cases hX
  apply Precoverage.generate_mem_toGrothendieck
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb]
  exact hP E'.2 hE'

/-- An fppf covering family of algebraic spaces generates a covering sieve of a big fppf
site of algebraic spaces. -/
private theorem fppf_covering_generates_site_cover
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S)
    {X : T.Spaces} (E : PreZeroHypercover.{u + 2} X)
    (hE : AlgebraicGeometry.Space.IsFppfCovering T.schemeSite S T.scheme_mem
      (fun i => (E.X i).1) (fun i => (E.f i).hom)) :
    Sieve.generate E.presieve₀ ∈ T.topology X := by
  exact generate_mem_toGrothendieck_of_representative _ _ T.precoverage
    (fun E' h => T.mem_precoverage_iff.2 ⟨E', rfl, h⟩) T.covering_representative E hE

/-- The Yoneda inclusion of the big fppf site of schemes into the algebraic spaces over `S`
sends covering sieves to covering sieves. -/
private theorem fppf_yonedaSpace_isCoverPreserving {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigFppfSpaceSite S) :
    CoverPreserving
      (AlgebraicGeometry.BigFppfOver.topology T.schemeSite S T.scheme_mem)
      T.topology
      (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem) := by
  classical
  let B := T.schemeSite
  let F := AlgebraicGeometry.schemeSpaceFunctor B S T.scheme_mem
  refine ⟨?_⟩
  intro Y R hR
  let X : B.Schemes := (AlgebraicGeometry.BigFppfOver.forget B S T.scheme_mem).obj Y
  have hRbase : (Sieve.overEquiv Y) R ∈ B.topology X := by
    change R ∈ (B.topology.over (B.obj T.scheme_mem)) Y at hR
    rwa [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := exists_covering_refining_sieve B hRbase
  let Eover : PreZeroHypercover Y :=
    { I₀ := E.I₀
      X := fun i => Over.mk (E.f i ≫ Y.hom)
      f := fun i => Over.homMk (E.f i) (by simp) }
  have hEover :=
    localYonedaFppfCovering B S T.scheme_mem Y E hE
  let Espace : PreZeroHypercover.{u + 2} (F.obj Y) :=
    { I₀ := ULift.{u + 2} E.I₀
      X := fun ij => F.obj (Eover.X ij.down)
      f := fun ij => F.map (Eover.f ij.down) }
  have hEspace : AlgebraicGeometry.Space.IsFppfCovering B S T.scheme_mem
      (fun i => (Espace.X i).1) (fun i => (Espace.f i).hom) := by
    refine ⟨hEover.target_isAlgebraicSpace, fun i => hEover.source_isAlgebraicSpace i.down,
      fun i => hEover.flat i.down, fun i => hEover.locallyOfFinitePresentation i.down, ?_⟩
    · apply Set.eq_univ_iff_forall.mpr
      intro p
      have hp : p ∈ ⋃ i : E.I₀,
          Set.range (AlgebraicGeometry.Space.pointsMap B S T.scheme_mem
            (yoneda.obj (Eover.X i)) (yoneda.map (Eover.f i))) := by
        rw [hEover.jointly_surjective]
        exact Set.mem_univ p
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨q, hq⟩ := Set.mem_range.mp hi
      refine Set.mem_iUnion.mpr ⟨ULift.up i, Set.mem_range.mpr ⟨q, ?_⟩⟩
      simpa [Espace, F, AlgebraicGeometry.schemeSpaceFunctor,
        AlgebraicGeometry.schemeSpace_obj, AlgebraicGeometry.schemeSpaceMap_hom] using hq
  have hERover : Eover.presieve₀ ≤ R := by
    rw [Presieve.ofArrows_le_iff]
    exact fun i => (Sieve.overEquiv_iff R (E.f i)).mp (hER _ _ (E.presieve₀_f i))
  have hle : Sieve.generate Espace.presieve₀ ≤ R.functorPushforward F := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    show R.functorPushforward F (F.map (Eover.f i.down))
    exact ⟨Eover.X i.down, Eover.f i.down, 𝟙 _, hERover _ _ (Eover.presieve₀_f i.down), by simp⟩
  exact T.topology.superset_covering hle (fppf_covering_generates_site_cover T Espace hEspace)

/-- The Yoneda inclusion of the big fppf site of schemes into the algebraic spaces over `S`
is cover dense. -/
private theorem fppf_yonedaSpace_isCoverDense {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigFppfSpaceSite S) :
    (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem).IsCoverDense
      T.topology := by
  let F := AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem
  constructor
  intro X
  obtain ⟨U, f, hAtlas⟩ := exists_etale_atlas_cover_ulift T.schemeSite S T.scheme_mem X
  let E₀ : PreZeroHypercover.{u + 2} X :=
    { I₀ := ULift.{u + 2} Unit
      X := fun _ => F.obj U
      f := fun _ => ObjectProperty.homMk f }
  have hFppf : AlgebraicGeometry.Space.IsFppfCovering T.schemeSite S T.scheme_mem
      (fun i => (E₀.X i).1) (fun i => (E₀.f i).hom) :=
    AlgebraicGeometry.Space.isFppfCovering_of_isEtaleCovering T.schemeSite S T.scheme_mem hAtlas
  exact coverDense_of_site_covering_refined_by_image F T.topology E₀
    (fppf_covering_generates_site_cover T E₀ hFppf)
    fun _ => Presieve.in_coverByImage F (ObjectProperty.homMk f : F.obj U ⟶ X)

/-- The Yoneda inclusion of the big fppf site of schemes into the algebraic spaces over `S`
is cocontinuous. -/
private theorem fppf_yonedaSpace_isCocontinuous {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigFppfSpaceSite S) :
    (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem).IsCocontinuous
      (AlgebraicGeometry.BigFppfOver.topology T.schemeSite S T.scheme_mem) T.topology := by
  let B := T.schemeSite
  let F := AlgebraicGeometry.schemeSpaceFunctor B S T.scheme_mem
  let J := AlgebraicGeometry.BigFppfOver.topology B S T.scheme_mem
  apply isCocontinuous_of_generator_refinements F J T.precoverage
  intro X R hR Y f
  obtain ⟨E, hR, hE⟩ := T.mem_precoverage_iff.mp hR
  subst R
  obtain ⟨P, p₁, p₂, hpb, hP⟩ := T.isSite.2.2 ⟨X, E⟩ hE (F.obj Y) f
  have hP' : AlgebraicGeometry.Space.IsFppfCovering B S T.scheme_mem
      (fun i => (P i).1) (fun i => (p₂ i).hom) := by
    exact hP.1
  classical
  choose U atlas hAtlas using fun i => exists_etale_atlas_cover B S T.scheme_mem (P i)
  have hAtlasFppf : ∀ i,
      AlgebraicGeometry.Space.IsFppfCovering B S T.scheme_mem
        (fun _ : Unit => yoneda.obj (U i)) (fun _ => atlas i) := fun i =>
    AlgebraicGeometry.Space.isFppfCovering_of_isEtaleCovering B S T.scheme_mem (hAtlas i)
  have hcomp := AlgebraicGeometry.Space.isFppfCovering_comp
    B S T.scheme_mem E.I₀ (fun _ : E.I₀ => Unit) (fun i => (P i).1)
    (fun i _ => yoneda.obj (U i)) (fun i => (p₂ i).hom)
    (fun i _ => atlas i) hP' hAtlasFppf
  let Erep : PreZeroHypercover.{u + 2} Y :=
    { I₀ := Σ i, Unit
      X := fun ij => U ij.1
      f := fun ij => yoneda.preimage (atlas ij.1 ≫ (p₂ ij.1).hom) }
  have hErep : AlgebraicGeometry.Space.IsFppfCovering B S T.scheme_mem
      (fun i => yoneda.obj (Erep.X i)) (fun i => yoneda.map (Erep.f i)) := by
    have key : ∀ ij, yoneda.map (Erep.f ij) = atlas ij.1 ≫ (p₂ ij.1).hom :=
      fun _ => yoneda.map_preimage _
    simp only [key]
    exact hcomp
  have hmem := represented_fppf_cover_mem_precoverage B S T.scheme_mem Erep hErep
  let Ebase := Erep.map (Over.forget (B.obj T.scheme_mem))
  have hmem' : (Ebase.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y.left) := by
    simpa [Ebase, AlgebraicGeometry.BigFppfOver.toScheme, PreZeroHypercover.map] using hmem
  obtain ⟨V, hV, hVref⟩ :=
    AlgebraicGeometry.exists_isCovering_refining_fppfCovering
      B Y.left (Ebase.map B.inclusion) hmem'
  let Esource : PreZeroHypercover.{u + 1} Y :=
    { I₀ := V.I₀
      X := fun i => Over.mk (V.f i ≫ Y.hom)
      f := fun i => Over.homMk (V.f i) (by simp) }
  have hsite : Sieve.generate Esource.presieve₀ ∈ J Y := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    have hVpre : V.presieve₀ ∈ B.precoverage Y.left := by
      exact ⟨V, rfl, hV⟩
    have hVgen : Sieve.generate V.presieve₀ ∈ B.topology Y.left :=
      Precoverage.generate_mem_toGrothendieck hVpre
    have hle : V.presieve₀ ≤
        Presieve.functorPushforward (Over.forget (B.obj T.scheme_mem))
          Esource.presieve₀ := by
      rw [Presieve.ofArrows_le_iff]
      intro i
      exact ⟨Esource.X i, Esource.f i, 𝟙 _, Esource.presieve₀_f i, by
        simp [Esource]
      ⟩
    apply B.topology.superset_covering (Sieve.generate_mono hle)
    exact hVgen
  have hVnonempty := hVref
  obtain ⟨H⟩ := hVnonempty
  let Hslice : Esource.Hom Erep :=
    { s₀ := H.s₀
      h₀ := fun (i : (V.map B.inclusion).I₀) =>
        Over.homMk (ObjectProperty.homMk (H.h₀ i)) (by
        change V.I₀ at i
        dsimp [Esource]
        apply B.inclusion.map_injective
        have hw := H.w₀ i
        change H.h₀ i ≫ B.inclusion.map (Ebase.f (H.s₀ i)) =
          B.inclusion.map (V.f i) at hw
        have hw' : H.h₀ i ≫ B.inclusion.map (Erep.f (H.s₀ i)).left =
            B.inclusion.map (V.f i) := by
          simpa [Ebase, PreZeroHypercover.map] using hw
        have hOver := congrArg B.inclusion.map (Over.w (Erep.f (H.s₀ i)))
        have hfirst : H.h₀ i ≫ B.inclusion.map (Erep.X (H.s₀ i)).hom =
            H.h₀ i ≫ B.inclusion.map
              ((Erep.f (H.s₀ i)).left ≫ Y.hom) :=
          congrArg (fun q => H.h₀ i ≫ q) hOver.symm
        have hsecond : H.h₀ i ≫
            B.inclusion.map ((Erep.f (H.s₀ i)).left ≫ Y.hom) =
              B.inclusion.map (V.f i) ≫ B.inclusion.map Y.hom := by
          have hmapcomp := B.inclusion.map_comp (Erep.f (H.s₀ i)).left Y.hom
          calc
            H.h₀ i ≫ B.inclusion.map ((Erep.f (H.s₀ i)).left ≫ Y.hom) =
                H.h₀ i ≫ (B.inclusion.map (Erep.f (H.s₀ i)).left ≫
                  B.inclusion.map Y.hom) :=
                    congrArg (fun q => H.h₀ i ≫ q) hmapcomp
            _ = (H.h₀ i ≫ B.inclusion.map (Erep.f (H.s₀ i)).left) ≫
                B.inclusion.map Y.hom :=
                  (Category.assoc (H.h₀ i)
                    (B.inclusion.map (Erep.f (H.s₀ i)).left)
                    (B.inclusion.map Y.hom)).symm
            _ = _ := congrArg (fun q => q ≫ B.inclusion.map Y.hom) hw'
        have hthird : B.inclusion.map (V.f i) ≫ B.inclusion.map Y.hom =
            B.inclusion.map (V.f i ≫ Y.hom) := by
          exact (B.inclusion.map_comp (V.f i) Y.hom).symm
        exact hfirst.trans (hsecond.trans hthird))
      w₀ := fun (i : (V.map B.inclusion).I₀) => by
        change V.I₀ at i
        dsimp [Esource]
        apply Over.OverMorphism.ext
        apply B.inclusion.map_injective
        simpa [Esource, Ebase, PreZeroHypercover.map] using H.w₀ i }
  have hle : Sieve.generate Esource.presieve₀ ≤
      ((Sieve.generate E.presieve₀).pullback f).functorPullback F := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    show Sieve.generate E.presieve₀ (F.map (Esource.f i) ≫ f)
    let j := Hslice.s₀ i
    have htriangle := Hslice.w₀ i
    have hmap : F.map (Hslice.h₀ i) ≫ F.map (Erep.f j) = F.map (Esource.f i) := by
      rw [← Functor.map_comp, htriangle]
    let atlasMap (i : E.I₀) : F.obj (U i) ⟶ P i := ObjectProperty.homMk (atlas i)
    have hrep : F.map (Erep.f j) = atlasMap j.1 ≫ p₂ j.1 := by
      apply ObjectProperty.hom_ext
      cases j.2
      show yoneda.map (yoneda.preimage (atlas j.1 ≫ (p₂ j.1).hom)) = _
      exact yoneda.map_preimage _
    have hsq := (hpb j.1).w.symm
    have hinner :
        atlasMap j.1 ≫ p₂ j.1 ≫ f =
          atlasMap j.1 ≫ p₁ j.1 ≫ (E.f j.1) := by
      apply ObjectProperty.hom_ext
      exact congrArg (fun q => atlas j.1 ≫ q.hom) hsq
    have hfac : F.map (Esource.f i) ≫ f =
        F.map (Hslice.h₀ i) ≫ atlasMap j.1 ≫ p₁ j.1 ≫ (E.f j.1) := by
      calc
        F.map (Esource.f i) ≫ f =
            (F.map (Hslice.h₀ i) ≫ F.map (Erep.f j)) ≫ f := by rw [hmap]
        _ = F.map (Hslice.h₀ i) ≫ (F.map (Erep.f j) ≫ f) := by
          simp [Category.assoc]
        _ = F.map (Hslice.h₀ i) ≫
              (atlasMap j.1 ≫ p₂ j.1 ≫ f) := by
                rw [hrep]
                simp [Category.assoc]
        _ = F.map (Hslice.h₀ i) ≫
              (atlasMap j.1 ≫ p₁ j.1 ≫ (E.f j.1)) := by rw [hinner]
        _ = _ := by simp
    rw [hfac]
    exact (Sieve.generate E.presieve₀).downward_closed
      (Sieve.le_generate E.presieve₀ _ _ (E.presieve₀_f j.1))
      (F.map (Hslice.h₀ i) ≫ atlasMap j.1 ≫ p₁ j.1)
  exact J.superset_covering hle hsite

/-- The identity-on-schemes functor between the matching underlying categories
of a big étale space site. -/
@[implicit_reducible]
public def etaleSchemesToFppf {S : Scheme.{u}} (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    T.schemeSite.Scheme ⥤ T.fppfSite.Schemes where
  obj X := ⟨X.1, by rw [← h]; exact X.2⟩
  map f := ObjectProperty.homMk f.hom
  map_id X := by ext; rfl
  map_comp f g := by ext; rfl

/-- The canonical inclusion of schemes into algebraic spaces on compatible
big étale sites. -/
@[implicit_reducible]
public def etaleSchemeToSpace {S : Scheme.{u}} (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) : T.Schemes ⥤ T.Spaces :=
  Over.post (etaleSchemesToFppf T h) ⋙
    AlgebraicGeometry.schemeSpaceFunctor T.fppfSite S T.fppf_mem

/-- The passage from the auxiliary big fppf site of a big étale site of algebraic spaces to
its chosen big étale site of schemes, available because the two cutoffs agree. -/
private def etaleOverFromFppf {S : Scheme.{u}} (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem ⥤ T.Schemes where
  obj X := Over.mk (ObjectProperty.homMk X.hom.hom :
    (⟨X.left.obj, by rw [h]; exact X.left.property⟩ : T.schemeSite.Scheme) ⟶ _)
  map f := Over.homMk (ObjectProperty.homMk f.left.hom) (by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.hom) f.w)

/-- An étale covering family of algebraic spaces generates a covering sieve of a big étale
site of algebraic spaces. -/
private theorem etale_covering_generates_site_cover
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    {X : T.Spaces} (E : PreZeroHypercover.{u + 2} X)
    (hE : AlgebraicGeometry.Space.IsEtaleCovering T.fppfSite S T.fppf_mem
      (fun i => (E.X i).1) (fun i => (E.f i).hom)) :
    Sieve.generate E.presieve₀ ∈ T.topology X := by
  exact generate_mem_toGrothendieck_of_representative _ _ T.precoverage
    (fun E' h => ⟨E', rfl, h⟩) T.covering_representative E hE

/-- A family in the big étale site of schemes over `S` whose underlying family of schemes is
an étale covering generates a covering sieve. -/
private theorem etale_scheme_cover_mem
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicGeometry.BigEtaleOver B S hS} (E : PreZeroHypercover.{v} Y)
    (hE : (E.map (AlgebraicGeometry.BigEtaleOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage Y.left.obj) :
    Sieve.generate E.presieve₀ ∈ AlgebraicGeometry.BigEtaleOver.topology B S hS Y := by
  let Ebase := E.map (Over.forget (B.obj S hS))
  have hbase : AlgebraicGeometry.IsEtaleCovering ⟨Y.left, Ebase.shrink⟩ := by
    show (Ebase.shrink.map B.inclusion).presieve₀ ∈ _
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_shrink,
      ← PreZeroHypercover.presieve₀_map]
    exact hE
  obtain ⟨⟨Z, V⟩, hV, hY, hc⟩ := B.exists_covering_rep ⟨Y.left, Ebase.shrink⟩ hbase
  cases hY
  let Esite : PreZeroHypercover.{u + 1} Y := {
    I₀ := V.I₀
    X := fun i => Over.mk (V.f i ≫ Y.hom)
    f := fun i => Over.homMk (V.f i) }
  have hsite : Sieve.generate Esite.presieve₀ ∈
      AlgebraicGeometry.BigEtaleOver.topology B S hS Y := by
    apply Precoverage.generate_mem_toGrothendieck
    exact ⟨Esite, rfl, hV⟩
  have heq : Ebase.presieve₀ = V.presieve₀ := by
    rw [← PreZeroHypercover.presieve₀_shrink Ebase]
    exact PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hc
  have hs : Sieve.generate Esite.presieve₀ = Sieve.generate E.presieve₀ := by
    apply (Sieve.overEquiv Y).injective
    rw [Sieve.overEquiv_generate, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward,
      ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve, Sieve.generate_sieve, ← PreZeroHypercover.presieve₀_map,
      ← PreZeroHypercover.presieve₀_map]
    show Sieve.generate V.presieve₀ = Sieve.generate Ebase.presieve₀
    rw [heq]
  rwa [hs] at hsite

/-- The inclusion of schemes into algebraic spaces is cocontinuous for the big étale
topologies. -/
private theorem etale_isCocontinuous {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    (etaleSchemeToSpace T h).IsCocontinuous
      (AlgebraicGeometry.BigEtaleOver.topology T.schemeSite S T.scheme_mem) T.topology := by
  let B := T.fppfSite
  let F := etaleSchemeToSpace T h
  let G : T.Schemes ⥤ AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem :=
    Over.post (etaleSchemesToFppf T h)
  let H := etaleOverFromFppf T h
  let J := AlgebraicGeometry.BigEtaleOver.topology T.schemeSite S T.scheme_mem
  apply isCocontinuous_of_generator_refinements F J T.precoverage
  intro X R hR Y f
  obtain ⟨E, rfl, hE⟩ := hR
  obtain ⟨P, p₁, p₂, hpb, hP⟩ := T.isSite.2.2 ⟨X, E⟩ hE (F.obj Y) f
  classical
  choose U a ha using fun i => exists_etale_atlas_cover B S T.fppf_mem (P i)
  have hc := AlgebraicGeometry.Space.isEtaleCovering_comp
    B S T.fppf_mem (fun _ : E.I₀ => Unit) (fun i => (P i).obj)
    (fun i => (p₂ i).hom) (fun i _ => yoneda.obj (U i)) (fun i _ => a i) hP.1 ha
  let Q : PreZeroHypercover.{u + 2} (G.obj Y) := {
    I₀ := Σ _ : E.I₀, Unit
    X := fun i => U i.1
    f := fun i => yoneda.preimage (a i.1 ≫ (p₂ i.1).hom) }
  have hQ : AlgebraicGeometry.Space.IsEtaleCovering B S T.fppf_mem
      (fun i => yoneda.obj (Q.X i)) (fun i => yoneda.map (Q.f i)) := by
    have key : ∀ ij, yoneda.map (Q.f ij) = a ij.1 ≫ (p₂ ij.1).hom :=
      fun _ => yoneda.map_preimage _
    simp only [key]
    exact hc
  have hmem := represented_etale_cover_mem_precoverage B S T.fppf_mem Q hQ
  have hsite : Sieve.generate (Q.map H).presieve₀ ∈ J Y :=
    etale_scheme_cover_mem T.schemeSite S T.scheme_mem (Q.map H) hmem
  apply J.superset_covering _ hsite
  refine (Sieve.generate_le_iff _ _).2 ?_
  refine Presieve.ofArrows_le_iff.2 ?_
  intro i
  show Sieve.generate E.presieve₀ (F.map (H.map (Q.f i)) ≫ f)
  have heq : F.map (H.map (Q.f i)) ≫ f =
      ObjectProperty.homMk (a i.1) ≫ p₁ i.1 ≫ E.f i.1 := by
    apply ObjectProperty.hom_ext
    show yoneda.map (yoneda.preimage (a i.1 ≫ (p₂ i.1).hom)) ≫ f.hom = _
    rw [yoneda.map_preimage]
    have hh := congrArg (fun q => a i.1 ≫ q.hom) (hpb i.1).w.symm
    change a i.1 ≫ ((p₂ i.1).hom ≫ f.hom) =
      a i.1 ≫ ((p₁ i.1).hom ≫ (E.f i.1).hom) at hh
    show (a i.1 ≫ (p₂ i.1).hom) ≫ f.hom =
      a i.1 ≫ (p₁ i.1).hom ≫ (E.f i.1).hom
    simpa only [Category.assoc] using hh
  rw [heq]
  exact (Sieve.generate E.presieve₀).downward_closed
    (Sieve.le_generate _ _ _ (E.presieve₀_f i.1))
    ((ObjectProperty.homMk (a i.1) : F.obj (H.obj (U i.1)) ⟶ P i.1) ≫ p₁ i.1)

/-- A family of morphisms of the big fppf site of `S` whose underlying morphisms of schemes
are étale and jointly surjective becomes an étale covering of algebraic spaces under Yoneda. -/
private theorem yoneda_etale_isEtaleCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicGeometry.BigFppfOver B S hS} (D : PreZeroHypercover.{v} Z)
    (hetale : ∀ j, AlgebraicGeometry.Etale
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (D.f j)))
    (hsurj : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z,
      ∃ j, ∃ y, (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (D.f j) y = x) :
    AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun j => yoneda.obj (D.X j)) (fun j => yoneda.map (D.f j)) := by
  refine ⟨AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Z,
    fun j => AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (D.X j), fun j => ?_, ?_⟩
  · exact AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS
      ((AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff B S hS (D.f j)).2 (hetale j))
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨j, y, hy⟩ :=
      AlgebraicGeometry.Space.exists_pointsMap_yonedaMap_eq_of_jointly_surjective
        B S hS D.f hsurj x
    exact ⟨j, y, hy⟩

/-- A family in the big fppf site of `S` whose underlying family of schemes is an étale
covering becomes an étale covering of algebraic spaces under Yoneda. -/
private theorem yoneda_etale_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicGeometry.BigFppfOver B S hS} (E : PreZeroHypercover.{v} Y)
    (hE : (E.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage Y.left.obj) :
    AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun i => yoneda.obj (E.X i)) (fun i => yoneda.map (E.f i)) := by
  obtain ⟨hjoint, hprop⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hE
  exact yoneda_etale_isEtaleCovering B S hS E hprop fun x => by
    obtain ⟨i, y, hy⟩ := hjoint x
    exact ⟨i, y, hy⟩

/-- The inclusion of schemes into algebraic spaces is cover dense for the big étale
topology of algebraic spaces. -/
private theorem etale_isCoverDense {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    (etaleSchemeToSpace T h).IsCoverDense T.topology := by
  let F := etaleSchemeToSpace T h
  constructor
  intro X
  obtain ⟨U, a, hE⟩ := exists_etale_atlas_cover_ulift T.fppfSite S T.fppf_mem X
  let U' := (etaleOverFromFppf T h).obj U
  let E : PreZeroHypercover.{u + 2} X := {
    I₀ := ULift.{u + 2} Unit
    X := fun _ => F.obj U'
    f := fun _ => ObjectProperty.homMk a }
  apply coverDense_of_site_covering_refined_by_image F T.topology E
    (etale_covering_generates_site_cover T E hE)
  exact fun _ => Presieve.in_coverByImage F (ObjectProperty.homMk a : F.obj U' ⟶ X)

/-- The inclusion of schemes into algebraic spaces of a big étale site is full. -/
private theorem etale_full {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) : (etaleSchemeToSpace T h).Full := by
  constructor
  intro X Y f
  refine ⟨(etaleOverFromFppf T h).map (yoneda.preimage f.hom), ?_⟩
  apply ObjectProperty.hom_ext
  exact yoneda.map_preimage _

/-- The inclusion of schemes into algebraic spaces of a big étale site is faithful. -/
private theorem etale_faithful {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) : (etaleSchemeToSpace T h).Faithful := by
  constructor
  intro X Y f g heq
  have hh := yoneda.map_injective (congrArg (fun f => f.hom) heq)
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact congrArg (fun f => f.left.hom) hh

/-- A fully faithful cover-dense functor is cover preserving for the topology generated by a
precoverage as soon as the image of every covering family of that precoverage generates a
covering sieve. -/
private theorem coverPreserving_of_dense_generators
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (P : Precoverage C) (K : GrothendieckTopology D)
    [F.Full] [F.Faithful] [F.IsCoverDense K]
    (hgen : ∀ {X : C} {R : Presieve X}, R ∈ P X →
      (Sieve.generate R).functorPushforward F ∈ K (F.obj X)) :
    CoverPreserving P.toGrothendieck K F := by
  have hle : P.toGrothendieck ≤ F.restrictedTopology K := by
    rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Functor.mem_restrictedTopology_iff]
    exact hgen hR
  exact ⟨fun hR => (Functor.mem_restrictedTopology_iff).mp (hle _ hR)⟩

/-- The inclusion of schemes into algebraic spaces sends covering sieves to covering sieves
for the big étale topologies. -/
private theorem etale_isCoverPreserving {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    CoverPreserving (AlgebraicGeometry.BigEtaleOver.topology T.schemeSite S T.scheme_mem)
      T.topology (etaleSchemeToSpace T h) := by
  let F := etaleSchemeToSpace T h
  let G : T.Schemes ⥤ AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem :=
    Over.post (etaleSchemesToFppf T h)
  have : F.Full := etale_full T h
  have : F.Faithful := etale_faithful T h
  have : F.IsCoverDense T.topology := etale_isCoverDense T h
  apply coverPreserving_of_dense_generators F
    (AlgebraicGeometry.BigEtaleOver.precoverage T.schemeSite S T.scheme_mem) T.topology
  intro Y R hR
  obtain ⟨E, rfl, hE⟩ := hR
  let Q : PreZeroHypercover.{u + 2} (G.obj Y) :=
    (E.map G).reindex Equiv.ulift.{u + 2}
  let Qspace := Q.map (AlgebraicGeometry.schemeSpaceFunctor T.fppfSite S T.fppf_mem)
  have hQ : (Q.map (AlgebraicGeometry.BigFppfOver.toScheme T.fppfSite S T.fppf_mem)).presieve₀ ∈
      Scheme.etalePrecoverage Y.left.obj := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_reindex,
      ← PreZeroHypercover.presieve₀_map]
    exact hE.1
  have hgen := etale_covering_generates_site_cover T Qspace
    (yoneda_etale_cover T.fppfSite S T.fppf_mem Q hQ)
  apply T.topology.superset_covering _ hgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  refine ⟨E.X i.down, E.f i.down, 𝟙 _, Sieve.le_generate _ _ _ (E.presieve₀_f i.down), ?_⟩
  show _ = 𝟙 _ ≫ F.map (E.f i.down)
  rw [Category.id_comp]
  rfl

/-- A sieve is covering as soon as its pullbacks along the members of a covering family are. -/
private theorem mem_of_pullback_mem_of_generate_mem
    {C : Type*} [Category C] (J : GrothendieckTopology C) {X : C} (A : PreZeroHypercover X)
    (R : Sieve X) (hA : Sieve.generate A.presieve₀ ∈ J X)
    (h : ∀ i, R.pullback (A.f i) ∈ J (A.X i)) : R ∈ J X := by
  apply J.transitive hA
  rintro Z g ⟨W, b, a, ⟨i⟩, rfl⟩
  simpa only [Sieve.pullback_comp] using J.pullback_stable b (h i)

/-- The passage from the auxiliary big fppf site of a big ph site of algebraic spaces to its
chosen big ph site of schemes, available because the two cutoffs agree. -/
private def phOverFromFppf {S : Scheme.{u}} (T : AlgebraicGeometry.BigPHSpaceSite S) :
    AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem ⥤ T.Schemes where
  obj X := Over.mk (ObjectProperty.homMk X.hom.hom :
    (⟨X.left.obj, by rw [T.cutoff_eq]; exact X.left.property⟩ : T.schemeSite.Schemes) ⟶ _)
  map f := Over.homMk (ObjectProperty.homMk f.left.hom) (by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.hom) f.w)

/-- A family in the big ph site of schemes over `S` whose underlying family of schemes is a
ph covering generates a covering sieve. -/
private theorem ph_scheme_cover_mem
    (B : AlgebraicGeometry.BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicGeometry.BigPHOver B S hS} (E : PreZeroHypercover.{v} Y)
    (hE : AlgebraicGeometry.IsPHCovering
      (E.map (AlgebraicGeometry.BigPHOver.toScheme B S hS)).X
      (E.map (AlgebraicGeometry.BigPHOver.toScheme B S hS)).f) :
    Sieve.generate E.presieve₀ ∈ AlgebraicGeometry.BigPHOver.topology B S hS Y := by
  let G := AlgebraicGeometry.BigPHOver.toScheme B S hS
  obtain ⟨V, hV, ⟨H⟩⟩ := AlgebraicGeometry.exists_isCovering_refinement B Y.left (E.map G) hE
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  have hVgen : Sieve.generate V.presieve₀ ∈ B.topology Y.left :=
    Precoverage.generate_mem_toGrothendieck (show V.presieve₀ ∈ B.precoverage _ from
      ⟨V, rfl, hV⟩)
  apply B.topology.superset_covering _ hVgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  let j := H.s₀ i
  let a : V.X i ⟶ (E.X j).left := ObjectProperty.homMk (H.h₀ i)
  have hw : a ≫ (E.f j).left = V.f i := by
    apply ObjectProperty.hom_ext
    exact H.w₀ i
  rw [← hw]
  apply Sieve.downward_closed
  apply Sieve.le_generate
  exact ⟨E.X j, E.f j, 𝟙 _, E.presieve₀_f j, by simp⟩

/-- The inclusion of schemes into algebraic spaces is cocontinuous for the big ph
topologies. -/
private theorem ph_isCocontinuous {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) :
    T.schemeToSpace.IsCocontinuous
      (AlgebraicGeometry.BigPHOver.topology T.schemeSite S T.scheme_mem) T.topology := by
  let B := T.schemeSite
  let F := T.schemeToSpace
  let G : T.Schemes ⥤ AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem :=
    Over.post T.schemesToFppf
  let H := phOverFromFppf T
  let J := AlgebraicGeometry.BigPHOver.topology B S T.scheme_mem
  apply isCocontinuous_of_generator_refinements F J T.precoverage
  intro X R hR Y f
  obtain ⟨E, rfl, hE⟩ := hR
  let U := Y.left.obj.affineCover
  have hsmall (i : U.I₀) : B.Contains (U.X i) :=
    Scheme.size_lt_of_mono_locallyOfFinitePresentation (U.f i) Y.left.property
  let A : PreZeroHypercover Y := {
    I₀ := U.I₀
    X := fun i => Over.mk ((ObjectProperty.homMk (U.f i) : B.obj _ (hsmall i) ⟶ Y.left) ≫ Y.hom)
    f := fun i => Over.homMk (ObjectProperty.homMk (U.f i)) }
  have hA : Sieve.generate A.presieve₀ ∈ J Y :=
    ph_scheme_cover_mem B S T.scheme_mem A (AlgebraicGeometry.IsPHCovering.of_openCover U)
  let Q := ((Sieve.generate E.presieve₀).pullback f).functorPullback F
  have hlocal (i : A.I₀) : Q.pullback (A.f i) ∈ J (A.X i) := by
    let V := G.obj (A.X i)
    have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V) := by
      show IsAffine (U.X i)
      infer_instance
    obtain ⟨C, hC, ⟨r⟩⟩ := hE.1.affine_refinement V (F.map (A.f i) ≫ f).hom
    have hCJ : Sieve.generate (C.map H).presieve₀ ∈ J (A.X i) :=
      ph_scheme_cover_mem B S T.scheme_mem (C.map H)
        (standardPHCovering_isPHCovering
          (E := C.map (AlgebraicGeometry.BigFppfOver.toScheme T.fppfSite S T.fppf_mem)) hC)
    apply J.superset_covering _ hCJ
    refine (Sieve.generate_le_iff _ _).2 ?_
    refine Presieve.ofArrows_le_iff.2 ?_
    intro j
    show Sieve.generate E.presieve₀ (F.map (H.map (C.f j) ≫ A.f i) ≫ f)
    let a : F.obj (H.obj (C.X j)) ⟶ E.X (r.s₀ j) := ObjectProperty.homMk (r.h₀ j)
    have hw : a ≫ E.f (r.s₀ j) = F.map (H.map (C.f j)) ≫ (F.map (A.f i) ≫ f) := by
      apply ObjectProperty.hom_ext
      exact r.w₀ j
    have hgoal : F.map (H.map (C.f j) ≫ A.f i) ≫ f =
        F.map (H.map (C.f j)) ≫ (F.map (A.f i) ≫ f) :=
      (congrArg (fun q ↦ q ≫ f) (F.map_comp (H.map (C.f j)) (A.f i))).trans
        (Category.assoc _ _ _)
    rw [hgoal, ← hw]
    exact (Sieve.generate E.presieve₀).downward_closed
      (Sieve.le_generate _ _ _ (E.presieve₀_f (r.s₀ j))) a
  exact mem_of_pullback_mem_of_generate_mem J A Q hA hlocal

/-- A ph covering family of algebraic spaces generates a covering sieve of a big ph site of
algebraic spaces. -/
private theorem ph_covering_generates_site_cover
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigPHSpaceSite S)
    {X : T.Spaces} (E : PreZeroHypercover.{u + 2} X)
    (hE : AlgebraicGeometry.Space.IsPHCovering T.fppfSite S T.fppf_mem
      (fun i => (E.X i).1) (fun i => (E.f i).hom)) :
    Sieve.generate E.presieve₀ ∈ T.topology X := by
  exact generate_mem_toGrothendieck_of_representative _ _ T.precoverage
    (fun E' h => ⟨E', rfl, h⟩) T.covering_representative E hE

/-- The inclusion of schemes into algebraic spaces is cover dense for the big ph topology of
algebraic spaces. -/
private theorem ph_isCoverDense {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) : T.schemeToSpace.IsCoverDense T.topology := by
  let F := T.schemeToSpace
  constructor
  intro X
  obtain ⟨U, a, hE⟩ := exists_etale_atlas_cover_ulift T.fppfSite S T.fppf_mem X
  let U' := (phOverFromFppf T).obj U
  let E : PreZeroHypercover.{u + 2} X := {
    I₀ := ULift.{u + 2} Unit
    X := fun _ => F.obj U'
    f := fun _ => ObjectProperty.homMk a }
  apply coverDense_of_site_covering_refined_by_image F T.topology E
    (ph_covering_generates_site_cover T E
      (AlgebraicGeometry.Space.isPHCovering_of_isEtaleCovering T.fppfSite S T.fppf_mem hE))
  exact fun _ => Presieve.in_coverByImage F (ObjectProperty.homMk a : F.obj U' ⟶ X)

/-- The inclusion of schemes into algebraic spaces of a big ph site is full. -/
private theorem ph_full {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) : T.schemeToSpace.Full := by
  constructor
  intro X Y f
  refine ⟨(phOverFromFppf T).map (yoneda.preimage f.hom), ?_⟩
  apply ObjectProperty.hom_ext
  exact yoneda.map_preimage _

/-- The inclusion of schemes into algebraic spaces of a big ph site is faithful. -/
private theorem ph_faithful {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) : T.schemeToSpace.Faithful := by
  constructor
  intro X Y f g heq
  have hh := yoneda.map_injective (congrArg (fun f => f.hom) heq)
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact congrArg (fun f => f.left.hom) hh

/-- A ph covering of schemes remains one after lifting its index type to a larger
universe. -/
private theorem scheme_ph_cover_ulift {X : Scheme.{u}} (E : PreZeroHypercover.{v} X)
    (hE : AlgebraicGeometry.IsPHCovering E.X E.f) :
    AlgebraicGeometry.IsPHCovering (E.reindex Equiv.ulift.{u + 2}).X
      (E.reindex Equiv.ulift.{u + 2}).f := by
  refine ⟨fun i => hE.1 i.down, ?_⟩
  intro U hU
  obtain ⟨A, hA, ⟨H⟩⟩ := hE.2 U hU
  exact ⟨A, hA, ⟨⟨fun i => ULift.up (H.s₀ i), H.h₀, H.w₀⟩⟩⟩

/-- A covering sieve of a big ph site of schemes is refined by a chosen covering family. -/
private theorem exists_phSiteCover_refining_sieve
    (B : AlgebraicGeometry.BigPHSite.{u}) {X : B.Schemes} {R : Sieve X}
    (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [AlgebraicGeometry.BigPHSite.topology] at hR
  exact exists_siteCover_refining_sieve B.IsCovering B.coverings_isSite B.precoverage
    id hR

/-- A ph covering of algebraic spaces over `S` remains one after lifting its index type to a
larger universe. -/
private theorem space_isPHCovering_ulift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Xᵢ : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, Xᵢ i ⟶ X}
    (h : AlgebraicGeometry.Space.IsPHCovering B S hS Xᵢ f) :
    AlgebraicGeometry.Space.IsPHCovering B S hS
      (fun i : ULift.{w} I => Xᵢ i.down) (fun i => f i.down) := by
  refine ⟨h.target_isAlgebraicSpace, fun i => h.source_isAlgebraicSpace i.down,
    fun i => h.locallyOfFiniteType i.down, ?_⟩
  intro U hU a
  obtain ⟨A, hA, ⟨H⟩⟩ := h.affine_refinement U a
  exact ⟨A, hA, ⟨⟨fun j => ULift.up (H.s₀ j), H.h₀, H.w₀⟩⟩⟩

/-- A family of morphisms of the big fppf site of `S` over an object with affine underlying
scheme whose underlying family of schemes is a standard ph covering becomes a ph covering of
algebraic spaces under Yoneda: base change along a scheme-valued point of the target is again
a standard ph covering, both schemes in sight being affine. -/
private theorem yoneda_standardPHCovering_isPHCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicGeometry.BigFppfOver B S hS}
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z)]
    (D : PreZeroHypercover.{u} Z)
    (hD : AlgebraicGeometry.StandardPHCovering
      (D.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).f) :
    AlgebraicGeometry.Space.IsPHCovering B S hS
      (fun j => yoneda.obj (D.X j)) (fun j => yoneda.map (D.f j)) := by
  let toSch := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  refine ⟨AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Z,
    fun j => AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (D.X j), fun j => ?_, ?_⟩
  · exact AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map B S hS
      AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (D.f j)
      (hD.locallyOfFiniteType j)
  intro V hV a
  have hVaff : IsAffine (toSch.obj V) := hV
  let g : V ⟶ Z := yoneda.preimage a
  have hga : yoneda.map g = a := yoneda.map_preimage _
  have hpb : AlgebraicGeometry.StandardPHCovering
      (fun j => pullback.snd ((D.map toSch).f j) (toSch.map g)) := hD.pullback (toSch.map g)
  have hlft (j : D.I₀) : LocallyOfFiniteType (pullback.snd ((D.map toSch).f j) (toSch.map g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback ((D.map toSch).f j) (toSch.map g))
      (hD.locallyOfFiniteType j)
  have hsmall (j : D.I₀) : B.Contains (pullback ((D.map toSch).f j) (toSch.map g)) := by
    have : IsAffine ((D.map toSch).X j) := hD.isAffine j
    have := hlft j
    exact (Scheme.size_le_of_locallyOfFiniteType
      (pullback.snd ((D.map toSch).f j) (toSch.map g))).trans_lt V.left.property
  let A : PreZeroHypercover.{u} V :=
    { I₀ := D.I₀
      X := fun j => Over.mk ((ObjectProperty.homMk
        (pullback.snd ((D.map toSch).f j) (toSch.map g)) :
          B.obj (hsmall j) ⟶ V.left) ≫ V.hom)
      f := fun j => Over.homMk
        (ObjectProperty.homMk (pullback.snd ((D.map toSch).f j) (toSch.map g))) }
  refine ⟨A, hpb, ⟨?_⟩⟩
  have hlift (j : D.I₀) : ∃ k : A.X j ⟶ D.X j,
      toSch.map k = pullback.fst ((D.map toSch).f j) (toSch.map g) := by
    refine ⟨Over.homMk (ObjectProperty.homMk
      (pullback.fst ((D.map toSch).f j) (toSch.map g))) ?_, rfl⟩
    apply ObjectProperty.hom_ext
    have hfac : toSch.map (D.f j) ≫ (Z).hom.hom = (D.X j).hom.hom :=
      congrArg (fun q => q.hom) (D.f j).w
    have hfacg : toSch.map g ≫ (Z).hom.hom = V.hom.hom :=
      congrArg (fun q => q.hom) g.w
    show pullback.fst ((D.map toSch).f j) (toSch.map g) ≫ (D.X j).hom.hom =
      pullback.snd ((D.map toSch).f j) (toSch.map g) ≫ V.hom.hom
    rw [← hfac, ← hfacg]
    exact pullback.condition_assoc _
  choose k hk using hlift
  refine ⟨fun j => j, fun j => yoneda.map (k j), fun j => ?_⟩
  have hsite (j : D.I₀) : k j ≫ D.f j = A.f j ≫ g := by
    apply Functor.map_injective toSch
    rw [Functor.map_comp, Functor.map_comp, hk]
    exact pullback.condition
  show yoneda.map (k j) ≫ yoneda.map (D.f j) = yoneda.map (A.f j) ≫ a
  rw [← hga, ← yoneda.map_comp, ← yoneda.map_comp, hsite j]

/-- The inclusion of schemes into algebraic spaces sends covering sieves to covering sieves
for the big ph topologies.

The underlying family of schemes of a chosen ph covering need not be a ph covering of
algebraic spaces, since that would require base change of ph coverings along a morphism from
an affine scheme, hence Chow's lemma. Covering sieves are instead reached in two steps: the
affine opens of the base form an étale, hence ph, covering, and over each of them the chosen
family is refined by a standard ph covering, whose base changes along morphisms of affines
are again standard. -/
private theorem ph_isCoverPreserving {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) :
    CoverPreserving (AlgebraicGeometry.BigPHOver.topology T.schemeSite S T.scheme_mem)
      T.topology T.schemeToSpace := by
  classical
  let B := T.schemeSite
  let F := T.schemeToSpace
  let G : T.Schemes ⥤ AlgebraicGeometry.BigFppfOver T.fppfSite S T.fppf_mem :=
    Over.post T.schemesToFppf
  let Fs := AlgebraicGeometry.schemeSpaceFunctor T.fppfSite S T.fppf_mem
  let toSch := AlgebraicGeometry.BigFppfOver.toScheme T.fppfSite S T.fppf_mem
  constructor
  intro Y R hR
  have hbase : (Sieve.overEquiv Y) R ∈ B.topology Y.left := by
    rwa [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := exists_phSiteCover_refining_sieve B hbase
  let Eover : PreZeroHypercover Y :=
    { I₀ := E.I₀
      X := fun i => Over.mk (E.f i ≫ Y.hom)
      f := fun i => Over.homMk (E.f i) }
  have hEoverR (i : E.I₀) : R (Eover.f i) :=
    (Sieve.overEquiv_iff R (E.f i)).mp (hER _ _ (E.presieve₀_f i))
  -- the affine opens of the underlying scheme of `Y`, as objects of the site over `Y`
  have hsmallA (W : (Y.left.obj).affineOpens) : B.Contains W.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion W.1.ι Y.left.property
  let A : PreZeroHypercover.{u} Y :=
    { I₀ := (Y.left.obj).affineOpens
      X := fun W => Over.mk ((ObjectProperty.homMk W.1.ι :
        B.obj _ (hsmallA W) ⟶ Y.left) ≫ Y.hom)
      f := fun W => Over.homMk (ObjectProperty.homMk W.1.ι) }
  let AG : PreZeroHypercover.{u + 2} (G.obj Y) := (A.map G).reindex Equiv.ulift.{u + 2}
  -- the affine opens form an étale, hence ph, covering of the represented algebraic space
  have hAph : AlgebraicGeometry.Space.IsPHCovering T.fppfSite S T.fppf_mem
      (fun i => yoneda.obj (AG.X i)) (fun i => yoneda.map (AG.f i)) := by
    refine AlgebraicGeometry.Space.isPHCovering_of_isEtaleCovering T.fppfSite S T.fppf_mem
      (yoneda_etale_isEtaleCovering T.fppfSite S T.fppf_mem AG (fun i => ?_) (fun x => ?_))
    · show AlgebraicGeometry.Etale (i.down.1.ι)
      infer_instance
    · obtain ⟨W, hWaff, hxW, -⟩ :=
        AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
          (X := Y.left.obj) (x := x) (U := ⊤) trivial
      obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι W).ge hxW
      exact ⟨ULift.up ⟨W, hWaff⟩, y, hy⟩
  have hA : Sieve.generate (AG.map Fs).presieve₀ ∈ T.topology (F.obj Y) :=
    ph_covering_generates_site_cover T (AG.map Fs) hAph
  -- over an affine open of `Y` the chosen ph covering is refined by a standard ph covering,
  -- whose Yoneda image is a ph covering of algebraic spaces
  have hlocal (i : AG.I₀) :
      (Sieve.functorPushforward F R).pullback ((AG.map Fs).f i) ∈
        T.topology ((AG.map Fs).X i) := by
    set W := i.down with hW
    have hWaff : IsAffine W.1.toScheme := W.2
    obtain ⟨𝒰, h𝒰, ⟨H⟩⟩ := hE.1.2 W.1 W.2
    have hlft (j : 𝒰.I₀) : LocallyOfFiniteType (𝒰.f j ≫ W.1.ι) := by
      have := h𝒰.locallyOfFiniteType j
      infer_instance
    have hsmallC (j : 𝒰.I₀) : B.Contains (𝒰.X j) := by
      have : IsAffine (𝒰.X j) := h𝒰.isAffine j
      have := hlft j
      exact (Scheme.size_le_of_locallyOfFiniteType (𝒰.f j ≫ W.1.ι)).trans_lt Y.left.property
    let C : PreZeroHypercover.{u} (A.X W) :=
      { I₀ := 𝒰.I₀
        X := fun j => Over.mk ((ObjectProperty.homMk (𝒰.f j) :
          B.obj _ (hsmallC j) ⟶ (A.X W).left) ≫ (A.X W).hom)
        f := fun j => Over.homMk (ObjectProperty.homMk (𝒰.f j)) }
    have hGaff : IsAffine (toSch.obj (G.obj (A.X W))) := hWaff
    have hCstd : AlgebraicGeometry.StandardPHCovering ((C.map G).map toSch).f := h𝒰
    have hCph : AlgebraicGeometry.Space.IsPHCovering T.fppfSite S T.fppf_mem
        (fun j : ULift.{u + 2} 𝒰.I₀ => yoneda.obj ((C.map G).X j.down))
        (fun j => yoneda.map ((C.map G).f j.down)) :=
      space_isPHCovering_ulift T.fppfSite S T.fppf_mem
        (yoneda_standardPHCovering_isPHCovering T.fppfSite S T.fppf_mem (C.map G) hCstd)
    let CG : PreZeroHypercover.{u + 2} (G.obj (A.X W)) :=
      (C.map G).reindex Equiv.ulift.{u + 2}
    have hCJ : Sieve.generate (CG.map Fs).presieve₀ ∈ T.topology ((AG.map Fs).X i) :=
      ph_covering_generates_site_cover T (CG.map Fs) hCph
    refine T.topology.superset_covering ?_ hCJ
    refine (Sieve.generate_le_iff _ _).2 ?_
    refine Presieve.ofArrows_le_iff.2 ?_
    intro j
    -- the refinement morphism, read in the site
    have hmSch : (H.h₀ j.down ≫ pullback.fst (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι) ≫
        B.inclusion.map (E.f (H.s₀ j.down)) = 𝒰.f j.down ≫ W.1.ι := by
      have hw : H.h₀ j.down ≫ pullback.snd (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι =
          𝒰.f j.down := H.w₀ j.down
      calc (H.h₀ j.down ≫ pullback.fst (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι) ≫
            B.inclusion.map (E.f (H.s₀ j.down))
          = H.h₀ j.down ≫ pullback.fst (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι ≫
              B.inclusion.map (E.f (H.s₀ j.down)) := Category.assoc _ _ _
        _ = H.h₀ j.down ≫ pullback.snd (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι ≫
              W.1.ι := congrArg (fun q => H.h₀ j.down ≫ q) pullback.condition
        _ = (H.h₀ j.down ≫ pullback.snd (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι) ≫
              W.1.ι := (Category.assoc _ _ _).symm
        _ = 𝒰.f j.down ≫ W.1.ι := congrArg (fun q => q ≫ W.1.ι) hw
    let mBase : B.obj _ (hsmallC j.down) ⟶ (Eover.X (H.s₀ j.down)).left :=
      B.inclusion.preimage
        (H.h₀ j.down ≫ pullback.fst (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι)
    have hmBase : mBase.hom =
        H.h₀ j.down ≫ pullback.fst (B.inclusion.map (E.f (H.s₀ j.down))) W.1.ι :=
      B.inclusion.map_preimage _
    let m : C.X j.down ⟶ Eover.X (H.s₀ j.down) := Over.homMk mBase (by
      apply ObjectProperty.hom_ext
      show mBase.hom ≫ (E.f (H.s₀ j.down)).hom ≫ Y.hom.hom =
        𝒰.f j.down ≫ W.1.ι ≫ Y.hom.hom
      rw [hmBase, ← Category.assoc]
      exact congrArg (fun q => q ≫ Y.hom.hom) hmSch
      )
    have hmsite : m ≫ Eover.f (H.s₀ j.down) = C.f j.down ≫ A.f W := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      show mBase.hom ≫ (E.f (H.s₀ j.down)).hom = 𝒰.f j.down ≫ W.1.ι
      rw [hmBase]
      exact hmSch
    refine ⟨Eover.X (H.s₀ j.down), Eover.f (H.s₀ j.down), F.map m, hEoverR _, ?_⟩
    show F.map (C.f j.down) ≫ F.map (A.f W) = F.map m ≫ F.map (Eover.f (H.s₀ j.down))
    rw [← Functor.map_comp, ← Functor.map_comp, hmsite]
  exact mem_of_pullback_mem_of_generate_mem T.topology (AG.map Fs) _ hA hlocal

/-- A cocontinuous, cover-dense, fully faithful and cover-preserving functor between sites is
a special cocontinuous functor in the sense of Stacks 03CG. -/
private theorem specialCocontinuous_of_full_coverDense
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsCocontinuous J K] [F.IsCoverDense K] [F.Full] [F.Faithful]
    (h : CoverPreserving J K F) : IsSpecialCocontinuous J K F :=
  ⟨inferInstance, Functor.isDenseSubsite_of_isCocontinuous F J K h
    (fun _ _ f g heq => by obtain rfl := F.map_injective heq; simp)
    (fun _ _ f => by
      obtain ⟨g, rfl⟩ := F.map_surjective f
      rw [Functor.imageSieve_map]
      exact J.top_mem _)⟩

/-- **Stacks 0DFV, étale case.** The inclusion of schemes into algebraic
spaces is special cocontinuous for the big étale sites. -/
@[stacks 0DFV "étale case"]
public theorem etaleSchemeToSpace_isSpecialCocontinuous
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    IsSpecialCocontinuous
      (AlgebraicGeometry.BigEtaleOver.topology T.schemeSite S T.scheme_mem)
      T.topology (etaleSchemeToSpace T h) := by
  have := etale_isCocontinuous T h
  have := etale_isCoverDense T h
  have := etale_full T h
  have := etale_faithful T h
  exact specialCocontinuous_of_full_coverDense _ _ _
    (etale_isCoverPreserving T h)

/-- **Stacks 0DFV, fppf case.** The Yoneda inclusion of schemes into
algebraic spaces is special cocontinuous for the big fppf sites. -/
@[stacks 0DFV "fppf case"]
public theorem fppfSchemeToSpace_isSpecialCocontinuous
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) :
    IsSpecialCocontinuous
      (AlgebraicGeometry.BigFppfOver.topology T.schemeSite S T.scheme_mem)
      T.topology
      (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem) := by
  let F := AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem
  have := fppf_yonedaSpace_isCocontinuous T
  have := fppf_yonedaSpace_isCoverDense T
  have : F.Full := by
    constructor
    intro X Y f
    refine ⟨yoneda.preimage f.hom, ?_⟩
    apply ObjectProperty.hom_ext
    exact yoneda.map_preimage _
  have : F.Faithful := by
    constructor
    intro X Y f g h
    apply yoneda.map_injective
    simpa [F, AlgebraicGeometry.schemeSpaceFunctor,
      AlgebraicGeometry.schemeSpace_obj, AlgebraicGeometry.schemeSpaceMap_hom] using
      congrArg (fun q => q.hom) h
  exact specialCocontinuous_of_full_coverDense F _ T.topology
    (fppf_yonedaSpace_isCoverPreserving T)

/-- **Stacks 0DFV, ph case.** The inclusion of schemes into algebraic
spaces is special cocontinuous for the big ph sites. -/
@[stacks 0DFV "ph case"]
public theorem phSchemeToSpace_isSpecialCocontinuous
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigPHSpaceSite S) :
    IsSpecialCocontinuous
      (AlgebraicGeometry.BigPHOver.topology T.schemeSite S T.scheme_mem)
      T.topology T.schemeToSpace := by
  have := ph_isCocontinuous T
  have := ph_isCoverDense T
  have := ph_full T
  have := ph_faithful T
  exact specialCocontinuous_of_full_coverDense _ _ _ (ph_isCoverPreserving T)

/-- **Stacks 0DFV, étale case: the identification of topoi.** The inclusion of schemes into
algebraic spaces induces an equivalence between the big étale topos of the scheme site and the
big étale topos of the algebraic-space site. -/
@[stacks 0DFV "étale case, equivalence of topoi"]
public noncomputable def etaleSchemeToSpaceSheafEquiv {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigEtaleSpaceSite S)
    (h : T.schemeSite.cutoff = T.fppfSite.cutoff) :
    Sheaf (AlgebraicGeometry.BigEtaleOver.topology T.schemeSite S T.scheme_mem)
        (Type (u + 1)) ≌
      Sheaf T.topology (Type (u + 1)) :=
  haveI := (etaleSchemeToSpace_isSpecialCocontinuous T h).2
  Functor.IsDenseSubsite.sheafEquiv _ _ (etaleSchemeToSpace T h) _

/-- **Stacks 0DFV, fppf case: the identification of topoi.** The Yoneda inclusion of schemes
into algebraic spaces induces an equivalence between the big fppf topos of the scheme site and
the big fppf topos of the algebraic-space site. -/
@[stacks 0DFV "fppf case, equivalence of topoi"]
public noncomputable def fppfSchemeToSpaceSheafEquiv {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigFppfSpaceSite S) :
    Sheaf (AlgebraicGeometry.BigFppfOver.topology T.schemeSite S T.scheme_mem)
        (Type (u + 1)) ≌
      Sheaf T.topology (Type (u + 1)) :=
  haveI := (fppfSchemeToSpace_isSpecialCocontinuous T).2
  Functor.IsDenseSubsite.sheafEquiv _ _
    (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem) _

/-- **Stacks 0DFV, ph case: the identification of topoi.** The inclusion of schemes into
algebraic spaces induces an equivalence between the big ph topos of the scheme site and the
big ph topos of the algebraic-space site. -/
@[stacks 0DFV "ph case, equivalence of topoi"]
public noncomputable def phSchemeToSpaceSheafEquiv {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigPHSpaceSite S) :
    Sheaf (AlgebraicGeometry.BigPHOver.topology T.schemeSite S T.scheme_mem)
        (Type (u + 1)) ≌
      Sheaf T.topology (Type (u + 1)) :=
  haveI := (phSchemeToSpace_isSpecialCocontinuous T).2
  Functor.IsDenseSubsite.sheafEquiv _ _ T.schemeToSpace _

end AlgebraicGeometry

end
