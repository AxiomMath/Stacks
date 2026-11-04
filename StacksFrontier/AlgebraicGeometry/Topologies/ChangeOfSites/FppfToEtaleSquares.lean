module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Change of topology from fppf to étale, and the resulting push-pull squares

The underlying category of a chosen big fppf site carries a second topology, the one generated
by its bounded étale coverings. Restriction along the identity functor of a slice is then a
morphism of topoi from the big fppf topos to the big étale topos, and composing with the
projection to the small étale topos gives a morphism to the latter. Both comparisons commute
with the morphisms induced by a morphism of the site: the two resulting squares of direct
images commute up to canonical natural isomorphism.

## Main definitions

* `AlgebraicGeometry.associatedBigEtaleSite` — the same category of schemes as a chosen big
  fppf site, with its bounded étale coverings.
* `AlgebraicGeometry.fppfToBigEtaleMorphism` and
  `AlgebraicGeometry.fppfToSmallEtaleMorphism` — the change-of-topology morphism and its
  composite with the big-to-small projection.
* `AlgebraicGeometry.smallEtaleMorphism` — the morphism of small étale topoi induced by base
  change in the associated étale site.

## Main results

* `AlgebraicGeometry.bigEtaleOverTopology_le_fppfOverTopology` — étale coverings of a slice are
  fppf coverings, which is what makes restriction continuous, and
  `AlgebraicGeometry.fppfToBigEtale_pushforwardIso` identifies the direct image of the
  change-of-topology morphism with that restriction.
* `AlgebraicGeometry.bigFppfBigEtale_pushforwardCommIso` and
  `AlgebraicGeometry.bigFppfSmallEtale_pushforwardCommIso` — the two commuting squares.

## Implementation notes

The associated étale site has the same cutoff, covering bound and covering ordinal as the
given fppf site, and no prescribed initial coverings. Commutativity of a square of geometric
morphisms is expressed by a natural isomorphism of the direct-image functors. The comparison
to the small site is defined as the stated composite, so its factorization through the big
étale topos holds definitionally and the second square reduces to the first together with the
commuting square for small étale base change.

## References

* [Stacks Project, Tag 0DDM](https://stacks.math.columbia.edu/tag/0DDM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- An fppf covering which is étale is the same thing as a bounded étale covering. -/
public theorem etaleBounded_eq_fppfEtaleBounded
    (B : BigFppfSite.{u}) (E : Covering B.Schemes) :
    (B.IsCovering E ∧ IsEtaleCovering E) ↔
      CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound E := by
  refine ⟨fun ⟨⟨_, hbound⟩, hetale⟩ => ⟨hetale, hbound⟩, fun ⟨hetale, hbound⟩ => ?_⟩
  refine ⟨⟨?_, hbound⟩, hetale⟩
  show E.2.presieve₀ ∈
    Scheme.fppfPrecoverage.comap (schemeBelowInclusion B.cutoff) E.1
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  change (E.2.map (schemeBelowInclusion B.cutoff)).presieve₀ ∈
    Scheme.etalePrecoverage ((schemeBelowInclusion B.cutoff).obj E.1) at hetale
  exact Scheme.etalePrecoverage_le_fppfPrecoverage _ hetale

/-- The étale site on the underlying category of a chosen big fppf site. -/
public abbrev associatedBigEtaleSite
    (B : BigFppfSite.{u}) : BigEtaleSite.{u} := by
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1} B.Schemes) := ∅
  have hpred : (fun E : Covering B.Schemes => B.IsCovering E ∧ IsEtaleCovering E) =
      CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound :=
    funext fun E ↦ propext (etaleBounded_eq_fppfEtaleBounded B E)
  have hsite : IsSite (CovBounded (IsEtaleCovering (κ := B.cutoff)) B.coveringBound) := by
    rw [← hpred]
    exact etaleCovering_isSite B
  have hrep : ∀ E : Covering B.Schemes,
      IsEtaleCovering E →
        ∃ E' : Covering B.Schemes,
          CovBounded (IsEtaleCovering (κ := B.cutoff))
            B.coveringBound E' ∧ Covering.CombEquiv E E' := by
    intro E hE
    obtain ⟨E', hE', hEq⟩ := etaleCovering_has_representative B E hE
    exact ⟨E', (etaleBounded_eq_fppfEtaleBounded B E').mp hE', hEq⟩
  letI : Small.{u + 1} Cov₀ := inferInstance
  letI : Small.{u} (∅ : Set Scheme.{u}) := inferInstance
  exact {
    S₀ := ∅
    small_S₀ := inferInstance
    cutoff := B.cutoff
    aleph0_lt_cutoff := B.aleph0_lt_cutoff
    cutoff_isStrongPrelimit := B.cutoff_isStrongPrelimit
    aleph0_lt_cutoff_cof := B.aleph0_lt_cutoff_cof
    mem_cutoff_of_mem := by simp
    initialCoverings := Cov₀
    small_initialCoverings := inferInstance
    initial_objects_mem := by simp [Cov₀]
    initialCoverings_etale := by simp [Cov₀]
    coveringBound := B.coveringBound
    coveringOrdinal := B.coveringOrdinal
    coveringOrdinal_isSuccLimit := B.coveringOrdinal_isSuccLimit
    initialCoverings_bounded := by simp [Cov₀]
    coverings_isSite := hsite
    exists_covering_rep := hrep
  }

/-- Every covering for the associated étale topology is an fppf covering. -/
public theorem associatedEtaleTopology_le_fppfTopology
    (B : BigFppfSite.{u}) :
    (associatedBigEtaleSite B).topology ≤ B.topology :=
  Precoverage.toGrothendieck_mono fun X _ ⟨E, hR, hE⟩ ↦
    ⟨E, hR, ((etaleBounded_eq_fppfEtaleBounded B ⟨X, E⟩).mpr hE).1⟩

/-- The big-site comparison from fppf to étale is induced by the identity
functor on the common slice category. -/
@[stacks 0DDM "étale coverings are fppf on the slice"]
public theorem bigEtaleOverTopology_le_fppfOverTopology
    (B : BigFppfSite.{u}) (X : B.Schemes) :
      BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2 ≤
      B.topology.over X := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro Y R hR
  obtain ⟨E, hR, hE⟩ :=
    (BigEtaleOver.mem_precoverage_iff _ _ _).mp hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff, hR, GrothendieckTopology.mem_over_iff]
  let p := Over.forget ((associatedBigEtaleSite B).obj X.1 X.2)
  let E' : Covering (associatedBigEtaleSite B).Scheme :=
    ⟨Y.left, E.map p⟩
  have hE' : (associatedBigEtaleSite B).IsCovering E' := hE
  have hmem : (E.presieve₀.map (Over.forget X)) ∈
      (associatedBigEtaleSite B).precoverage Y.left := by
    refine ⟨E.map p, ?_, hE'⟩
    rw [← PreZeroHypercover.presieve₀_map]
  have heq : Sieve.overEquiv Y (Sieve.generate E.presieve₀) =
      Sieve.generate (E.presieve₀.map p) := by
    show Sieve.functorPushforward p (Sieve.generate E.presieve₀) = _
    exact Sieve.generate_map_eq_functorPushforward p |>.symm
  rw [heq]
  exact associatedEtaleTopology_le_fppfTopology B Y.left
    (Precoverage.generate_mem_toGrothendieck hmem)

/-- Restriction along the identity on the common slice takes fppf sheaves to
étale sheaves. -/
public instance changeOfTopology_isContinuous
    (B : BigFppfSite.{u}) (X : B.Schemes) :
    (𝟭 (Over X)).IsContinuous
      (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)
      (B.topology.over X) :=
  let J := BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2
  let h := bigEtaleOverTopology_le_fppfOverTopology B X
  { op_comp_isSheaf_of_types := fun G => by
      change Presieve.IsSheaf J G.obj
      exact (isSheaf_iff_isSheaf_of_type _ _).1 (G.property.of_le h) }

/-- The morphism of topoi from fppf sheaves to big étale sheaves on the slice over `X`: its
pushforward and inverse image are those of the identity functor of the slice category, continuous
because every étale covering is an fppf covering. -/
@[stacks 0DDM "change-of-topology morphism"]
public def fppfToBigEtaleMorphism
    (B : BigFppfSite.{u}) (X : B.Schemes) :
    MorphismOfTopoi
      (Sheaf (B.topology.over X) (Type (u + 1)))
      (Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B)
        X.1 X.2) (Type (u + 1))) := by
  let J := BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2
  let K := B.topology.over X
  letI : (𝟭 (Over X)).IsContinuous J K := changeOfTopology_isContinuous B X
  haveI : PreservesFiniteLimits
      (((𝟭 (Over X)).op.lan :
        ((Over X)ᵒᵖ ⥤ Type (u + 1)) ⥤ ((Over X)ᵒᵖ ⥤ Type (u + 1)))) := by
    have e : (𝟭 (Over X)).op.lan ≅ 𝟭 ((Over X)ᵒᵖ ⥤ Type (u + 1)) := by
      simpa only [Functor.whiskeringLeft_obj_id] using
        Adjunction.leftAdjointUniq
          ((𝟭 (Over X)).op.lanAdjunction (Type (u + 1))) Adjunction.id
    exact preservesFiniteLimits_of_natIso e.symm
  exact
    { pushforward := (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1)) J K
      inverseImage := (𝟭 (Over X)).sheafPullback (Type (u + 1)) J K
      adj := (𝟭 (Over X)).sheafAdjunctionContinuous (Type (u + 1)) J K
      preservesFiniteLimits :=
        Functor.sheafPullbackConstruction.preservesFiniteLimits
          (𝟭 (Over X)) (Type (u + 1)) J K }

/-- The direct image of the change-of-topology morphism is restriction of
fppf sheaves along the identity functor on the common slice category. -/
@[stacks 0DDM "direct image of change of topology"]
public def fppfToBigEtale_pushforwardIso
    (B : BigFppfSite.{u}) (X : B.Schemes) :
    (fppfToBigEtaleMorphism B X).pushforward ≅
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2)
        (B.topology.over X) := by
  dsimp [fppfToBigEtaleMorphism]
  exact Iso.refl _

/-- The comparison from the big fppf topos to the small étale topos. -/
@[stacks 0DDM "factorization through the big étale topos"]
public def fppfToSmallEtaleMorphism
    (B : BigFppfSite.{u}) (X : B.Schemes) :
    MorphismOfTopoi
      (Sheaf (B.topology.over X) (Type (u + 1)))
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B)
        X.1 X.2) (Type (u + 1))) :=
  (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B)
    X.1 X.2).comp (fppfToBigEtaleMorphism B X)

/-- The morphism of small étale topoi induced by base change. -/
public def smallEtaleMorphism
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) :
    MorphismOfTopoi
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B)
        X.1 X.2) (Type (u + 1)))
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B)
        Y.1 Y.2) (Type (u + 1))) :=
  let E := associatedBigEtaleSite B
  let g := smallEtaleBaseChange E f
  let h := smallEtaleBaseChange_isMorphismOfSites E f
  letI := h.toIsContinuous
  let L := Classical.choose h.hasExactLeftAdjoint
  let hL := Classical.choose_spec h.hasExactLeftAdjoint
  { pushforward := g.sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology E Y.1 Y.2)
      (SmallEtale.topology E X.1 X.2)
    inverseImage := L
    adj := Classical.choice hL.1
    preservesFiniteLimits := hL.2 }

/-- The square of big fppf and big étale topoi commutes. -/
@[stacks 0DDM "the big fppf–big étale square"]
public def bigFppfBigEtale_pushforwardCommIso
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) :
    ((bigEtaleMorphism (associatedBigEtaleSite B) X Y f).comp
      (fppfToBigEtaleMorphism B X)).pushforward ≅
      ((fppfToBigEtaleMorphism B Y).comp
        (bigFppfMorphism B X Y f)).pushforward := by
  let E := associatedBigEtaleSite B
  let JeX := BigEtaleOver.topology E X.1 X.2
  let JeY := BigEtaleOver.topology E Y.1 Y.2
  let JfX := B.topology.over X
  let JfY := B.topology.over Y
  let eX : Over X ⥤ Over X := 𝟭 _
  let eY : Over Y ⥤ Over Y := 𝟭 _
  let bp : Over Y ⥤ Over X := Over.pullback f
  letI : eX.IsContinuous JeX JfX := changeOfTopology_isContinuous B X
  letI : eY.IsContinuous JeY JfY := changeOfTopology_isContinuous B Y
  letI : bp.IsContinuous JeY JeX := bigEtalePullback_isContinuous E X Y f
  letI : bp.IsContinuous JfY JfX := by
    dsimp [bp, JfX, JfY]
    infer_instance
  haveI : (bp ⋙ eX).IsContinuous JeY JfX :=
    Functor.isContinuous_comp bp eX JeY JeX JfX
  haveI : (eY ⋙ bp).IsContinuous JeY JfX :=
    Functor.isContinuous_comp eY bp JeY JfY JfX
  let eXpush := eX.sheafPushforwardContinuous (Type (u + 1)) JeX JfX
  let eYpush := eY.sheafPushforwardContinuous (Type (u + 1)) JeY JfY
  let hEtale :=
    bigEtaleMorphismPushforwardIso E X Y f
  let hFppf :
      (Over.map f).sheafPushforwardCocontinuous
          (Type (u + 1)) JfX JfY ≅
        (Over.pullback f).sheafPushforwardContinuous
          (Type (u + 1)) JfY JfX :=
    (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))
  let hEpsX := fppfToBigEtale_pushforwardIso B X
  let hEpsY := fppfToBigEtale_pushforwardIso B Y
  let hCompL := Functor.sheafPushforwardContinuousComp bp eX
    (Type (u + 1)) JeY JeX JfX
  let hCompR := Functor.sheafPushforwardContinuousComp eY bp
    (Type (u + 1)) JeY JfY JfX
  let hSite : bp ⋙ eX ≅ eY ⋙ bp := Iso.refl _
  let hSitePush := Functor.sheafPushforwardContinuousIso hSite
    (Type (u + 1)) JeY JfX
  exact
    Functor.isoWhiskerRight hEpsX
      (bigEtaleMorphism E X Y f).pushforward ≪≫
    Functor.isoWhiskerLeft eXpush hEtale ≪≫ hCompL ≪≫ hSitePush ≪≫
    hCompR.symm ≪≫
    (Functor.isoWhiskerRight hFppf eYpush).symm ≪≫
    Functor.isoWhiskerLeft
      (bigFppfMorphism B X Y f).pushforward hEpsY.symm

/-- The square of big fppf and small étale topoi commutes. -/
@[stacks 0DDM "the big fppf–small étale square"]
public def bigFppfSmallEtale_pushforwardCommIso
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y) :
    ((smallEtaleMorphism B f).comp
        (fppfToSmallEtaleMorphism B X)).pushforward ≅
      ((fppfToSmallEtaleMorphism B Y).comp
        (bigFppfMorphism B X Y f)).pushforward := by
  let εX := fppfToBigEtaleMorphism B X
  let εY := fppfToBigEtaleMorphism B Y
  let πX := bigEtaleToSmallEtaleMorphism
    (associatedBigEtaleSite B) X.1 X.2
  let πY := bigEtaleToSmallEtaleMorphism
    (associatedBigEtaleSite B) Y.1 Y.2
  let s := smallEtaleMorphism B f
  let b := bigFppfMorphism B X Y f
  let hSmall := bigSmallEtalePushforwardCommIso
    (associatedBigEtaleSite B) X Y f
  let hBig := bigFppfBigEtale_pushforwardCommIso B f
  change ((εX.pushforward ⋙ πX.pushforward) ⋙ s.pushforward) ≅
    (b.pushforward ⋙ (εY.pushforward ⋙ πY.pushforward))
  exact
    Functor.associator εX.pushforward πX.pushforward s.pushforward ≪≫
    Functor.isoWhiskerLeft εX.pushforward hSmall ≪≫
    (Functor.associator εX.pushforward
      (bigEtaleMorphism (associatedBigEtaleSite B) X Y f).pushforward
      πY.pushforward).symm ≪≫
    Functor.isoWhiskerRight hBig πY.pushforward ≪≫
    Functor.associator b.pushforward εY.pushforward πY.pushforward

end AlgebraicGeometry
