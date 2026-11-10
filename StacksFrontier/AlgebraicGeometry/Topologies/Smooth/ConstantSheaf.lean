module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteCoverings

/-!
# Constant sheaves on the big smooth site of a scheme

Let `B` be a big smooth site containing a scheme `S` and let `G` be an abstract group. On the
big smooth site of `S`, both the sheafification of the constant presheaf with value `G` for the
smooth topology and its sheafification for the Zariski topology restricted from schemes have
the locally constant `G`-valued maps as their sections; in particular the two sheafifications
agree. The constant sheaf of groups is in both cases the group-valued functor of points of the
constant group scheme `G_S`.

## Main results

* `AlgebraicGeometry.bigSmoothOver_openCoverData` and `bigSmoothOver_zariski_openCoverData`
  realise an arbitrary open cover of the scheme underlying a site object by a covering family,
  for the smooth and for the restricted Zariski topology respectively.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_bigSmooth` and
  `zariskiConstantSheafIsoLocallyConstantMaps_bigSmooth` identify the two constant sheaves, and
  the two `_unit` lemmas fix those identifications on constant sections.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigSmooth` and
  `zariskiGroupSheafRepresented_bigSmooth` are the representations of the constant group
  sheaves by `G_S`.

## Implementation notes

For the smooth topology an arbitrary open cover has to be replaced by a tautologically
equivalent covering family of the site, which is the content of Stacks 03WZ. For the restricted
Zariski topology the open subschemes of a site object are themselves small enough to lie in the
site, so the open cover is realised there directly.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- Every open cover of the scheme underlying an object of the big smooth site of `S` is
refined by a covering family of that site. -/
public theorem bigSmoothOver_openCoverData (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    ∀ {T : BigSmoothOver B S hS}
      (U : (BigSmoothOver.toScheme B S hS).obj T →
        ((BigSmoothOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigSmoothOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigSmoothOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ BigSmoothOver.topology B S hS T ∧
          ∀ i y, (BigSmoothOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let X := (BigSmoothOver.toScheme B S hS).obj T
  let O : X.OpenCover := X.openCoverOfIsOpenCover U hU
  obtain ⟨V, hV, hEq⟩ := exists_covering_tautologicallyEquivalent_openCover B T.left O
  obtain ⟨β, hβ⟩ := hEq.2
  choose e he using hβ
  let W : V.I₀ → BigSmoothOver B S hS := fun i => Over.mk (V.f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (V.f i) (by simp [W])
  have hpre : V.presieve₀ ∈ B.precoverage T.left := ⟨V, hV, rfl⟩
  have hcover : Sieve.ofArrows W a ∈ BigSmoothOver.topology B S hS T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.generate V.presieve₀ ∈ B.precoverage.toGrothendieck T.left
    exact B.precoverage.generate_mem_toGrothendieck hpre
  refine ⟨V.I₀, W, a, β, hcover, fun i y => ?_⟩
  have heval : (BigSmoothOver.toScheme B S hS).map (a i) y = O.f (β i) ((e i).hom y) :=
    (congrArg (fun f => f y) (he i)).symm
  rw [heval]
  exact ((e i).hom y).property

/-- Every open cover of the scheme underlying an object of the big smooth site of `S` is
refined by a family which covers for the Zariski topology restricted from schemes. -/
public theorem bigSmoothOver_zariski_openCoverData (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    ∀ {T : BigSmoothOver B S hS}
      (U : (BigSmoothOver.toScheme B S hS).obj T →
        ((BigSmoothOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigSmoothOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigSmoothOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈
          (BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology T ∧
          ∀ i y, (BigSmoothOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := BigSmoothOver.toScheme B S hS
  let X := F.obj T
  let U' : ULift.{u + 1, u} X → X.Opens := fun i => U i.down
  have hU' : TopologicalSpace.IsOpenCover U' := by
    rw [TopologicalSpace.IsOpenCover] at hU ⊢
    simpa [U'] using hU
  let O : X.OpenCover.{u + 1} := X.openCoverOfIsOpenCover U' hU'
  let V : O.I₀ → B.category := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.left.2⟩
  let f : ∀ i, V i ⟶ T.left := fun i => ⟨O.f i⟩
  let W : O.I₀ → BigSmoothOver B S hS := fun i => Over.mk (f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (f i) (by simp [W])
  have hpush : (Sieve.ofArrows W a).functorPushforward F = Sieve.ofArrows O.X O.f := by
    rw [Sieve.functorPushforward_ofArrows]
    congr 1
  refine ⟨O.I₀, W, a, ULift.down, ?_, ?_⟩
  · apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [hpush]
    exact O.mem_grothendieckTopology
  · intro i y
    change y.1 ∈ U' i
    simpa [U'] using y.2

/-- Locally constant `G`-valued maps form a sheaf on the big smooth site of `S`. -/
public theorem locallyConstantMaps_isSheaf_bigSmooth (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (BigSmoothOver.topology B S hS)
      ((BigSmoothOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_bigSmooth_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the big smooth site of `S` for the
Zariski topology restricted from schemes. -/
public theorem locallyConstantMaps_isSheaf_bigSmoothZariski (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      ((BigSmoothOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let F := BigSmoothOver.toScheme B S hS
  let : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  exact locallyConstantMaps_isSheaf_restrictedZariski F inferInstance G

/-- Constant sheaves on the chosen big smooth site have locally constant sections. -/
@[stacks 03P5 "big smooth site"]
public def constantSheafIsoLocallyConstantMaps_bigSmooth (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Small.{u} G]
    [Group G] :
    ((constantSheaf (BigSmoothOver.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((BigSmoothOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn.{u, v} (BigSmoothOver.toScheme B S hS) G
    (BigSmoothOver.topology B S hS) (bigSmoothOver_openCoverData B S hS)
    (openCoverData_bottom (BigSmoothOver.toScheme B S hS) (BigSmoothOver.topology B S hS)
      (bigSmoothOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSmooth B S hS G)

/-- The Zariski sheafification on a chosen big smooth site has locally constant sections. -/
@[stacks 03P5 "Zariski sheafification on the big smooth site"]
public def zariskiConstantSheafIsoLocallyConstantMaps_bigSmooth (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Small.{u} G]
    [Group G] :
    ((constantSheaf
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((BigSmoothOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn.{u, v} (BigSmoothOver.toScheme B S hS) G
    ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigSmoothOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigSmoothOver.toScheme B S hS)
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigSmoothOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSmoothZariski B S hS G)

/-- The specified-topology identification on the big smooth site preserves constant
sections. -/
@[stacks 03P5 "tau unit on the big smooth site"]
public theorem constantSheafIsoLocallyConstantMaps_bigSmooth_unit (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Small.{u} G]
    [Group G] :
    ConstantSheafIso.UnitCompatible (BigSmoothOver.toScheme B S hS)
      (BigSmoothOver.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_bigSmooth B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit.{u, v} (BigSmoothOver.toScheme B S hS) G
    (BigSmoothOver.topology B S hS) (bigSmoothOver_openCoverData B S hS)
    (openCoverData_bottom (BigSmoothOver.toScheme B S hS) (BigSmoothOver.topology B S hS)
      (bigSmoothOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSmooth B S hS G)

/-- The Zariski-topology identification on the big smooth site preserves constant sections. -/
@[stacks 03P5 "Zariski unit on the big smooth site"]
public theorem zariskiConstantSheafIsoLocallyConstantMaps_bigSmooth_unit
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigSmoothOver.toScheme B S hS)
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G
      (zariskiConstantSheafIsoLocallyConstantMaps_bigSmooth B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit.{u, v} (BigSmoothOver.toScheme B S hS) G
    ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigSmoothOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigSmoothOver.toScheme B S hS)
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigSmoothOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSmoothZariski B S hS G)

/-- Representation of the constant group sheaf on the chosen big smooth site. -/
@[stacks 03P5 "group-valued representation on the big smooth site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_bigSmooth
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S
      (Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _))
      (BigSmoothOver.topology B S hS) G := by
  let H := Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _)
  let J := BigSmoothOver.topology B S hS
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_bigSmooth_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
      (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigSmoothOver_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

/-- The Zariski constant group sheaf on the chosen big smooth site is represented by `G_S`. -/
@[stacks 03P5 "Zariski group sheaf on the big smooth site"]
public def zariskiGroupSheafRepresented_bigSmooth (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S
      (Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _))
      ((BigSmoothOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G := by
  let H := Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _)
  let F := BigSmoothOver.toScheme B S hS
  let J := F.restrictedTopology Scheme.zariskiTopology
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      (locallyConstantMaps_isSheaf_bigSmoothZariski B S hS G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigSmoothOver_zariski_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

end AlgebraicGeometry

end
