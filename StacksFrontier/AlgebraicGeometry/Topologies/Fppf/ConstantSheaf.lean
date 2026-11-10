module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# Constant sheaves on the big fppf site of a scheme

Let `B` be a big fppf site containing a scheme `S` and let `G` be an abstract group. On the big
fppf site of `S`, both the sheafification of the constant presheaf with value `G` for the fppf
topology and its sheafification for the Zariski topology restricted from schemes have the
locally constant `G`-valued maps as their sections; in particular the two sheafifications
agree. The constant sheaf of groups is in both cases the group-valued functor of points of the
constant group scheme `G_S`.

## Main results

* `AlgebraicGeometry.bigFppfOver_openCoverData` and `bigFppfOver_zariski_openCoverData`
  realise an arbitrary open cover of the scheme underlying a site object by a covering family,
  for the fppf and for the restricted Zariski topology respectively.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_bigFppf` and
  `zariskiConstantSheafIsoLocallyConstantMaps_bigFppf` identify the two constant sheaves, and
  the two `_unit` lemmas fix those identifications on constant sections.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigFppf` and
  `zariskiGroupSheafRepresented_bigFppf` are the representations of the constant group sheaves
  by `G_S`.

## Implementation notes

For the fppf topology an arbitrary open cover has to be replaced by a tautologically equivalent
covering family of the site, which is the content of Stacks 03WX. For the restricted Zariski
topology the open subschemes of a site object are themselves small enough to lie in the site,
so the open cover is realised there directly.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The open cover of `X` indexed by `ULift X` with `i`-th member `U i.down`. -/
private def uliftOpenCover (X : Scheme.{u}) (U : X → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U) : X.OpenCover.{u + 1} :=
  X.openCoverOfIsOpenCover (fun i : ULift.{u + 1, u} X => U i.down) <| by
    rw [TopologicalSpace.IsOpenCover] at hU ⊢
    simpa using hU

/-- Every open cover of the scheme underlying an object of the big fppf site of `S` is refined
by a covering family of that site. -/
public theorem bigFppfOver_openCoverData (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigFppfOver B S hS}
      (U : (BigFppfOver.toScheme B S hS).obj T →
        ((BigFppfOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigFppfOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigFppfOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ BigFppfOver.topology B S hS T ∧
          ∀ i y, (BigFppfOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let X := B.inclusion.obj T.left
  change TopologicalSpace.IsOpenCover (X := X) U at hU
  let O := uliftOpenCover X U hU
  obtain ⟨V, hV, hEq⟩ :=
    exists_isCovering_tautologicallyEquivalent_openCover B T.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  let W : V.I₀ → BigFppfOver B S hS := fun i => Over.mk (V.f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (V.f i) (by simp [W])
  refine ⟨V.I₀, W, a, fun i => (β i).down, ?_, fun i y => ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.generate V.presieve₀ ∈ B.precoverage.toGrothendieck T.left
    exact B.precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩
  · have heval : (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) :=
      (congrArg (fun f => f y) (he i)).symm
    change B.inclusion.map (V.f i) y ∈ _
    rw [heval]
    change ((e i).hom y).val ∈ U (β i).down
    simpa using ((e i).hom y).property

/-- Every open cover of the scheme underlying an object of the big fppf site of `S` is refined
by a family which covers for the Zariski topology restricted from schemes. -/
public theorem bigFppfOver_zariski_openCoverData (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigFppfOver B S hS}
      (U : (BigFppfOver.toScheme B S hS).obj T →
        ((BigFppfOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigFppfOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigFppfOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈
          (BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology T ∧
          ∀ i y, (BigFppfOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := BigFppfOver.toScheme B S hS
  let X := F.obj T
  let O := uliftOpenCover X U hU
  let V : O.I₀ → B.Schemes := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.left.2⟩
  let f : ∀ i, V i ⟶ T.left := fun i => ⟨O.f i⟩
  let W : O.I₀ → BigFppfOver B S hS := fun i => Over.mk (f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (f i) (by simp [W])
  have hpush : (Sieve.ofArrows W a).functorPushforward F = Sieve.ofArrows O.X O.f := by
    rw [Sieve.functorPushforward_ofArrows]
    congr 1
  refine ⟨O.I₀, W, a, fun i => i.down, ?_, ?_⟩
  · apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [hpush]
    exact O.mem_grothendieckTopology
  · intro i y
    change y.1 ∈ U i.down
    simpa using y.2

/-- Locally constant `G`-valued maps form a sheaf on the big fppf site of `S`. -/
public theorem locallyConstantMaps_isSheaf_bigFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((BigFppfOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_bigFppf_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the big fppf site of `S` for the Zariski
topology restricted from schemes. -/
public theorem locallyConstantMaps_isSheaf_bigFppfZariski (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      ((BigFppfOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let F := BigFppfOver.toScheme B S hS
  let : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  exact locallyConstantMaps_isSheaf_restrictedZariski F inferInstance G

/-- Constant sheaves on the chosen big fppf site have locally constant sections. -/
@[stacks 03P5 "big fppf site"]
public def constantSheafIsoLocallyConstantMaps_bigFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (BigFppfOver.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((BigFppfOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn.{u, v} (BigFppfOver.toScheme B S hS) G
    (BigFppfOver.topology B S hS) (bigFppfOver_openCoverData B S hS)
    (openCoverData_bottom (BigFppfOver.toScheme B S hS) (BigFppfOver.topology B S hS)
      (bigFppfOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigFppf B S hS G)

/-- The Zariski sheafification on a chosen big fppf site has locally constant sections. -/
@[stacks 03P5 "Zariski sheafification on the big fppf site"]
public def zariskiConstantSheafIsoLocallyConstantMaps_bigFppf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((BigFppfOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn.{u, v} (BigFppfOver.toScheme B S hS) G
    ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigFppfOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigFppfOver.toScheme B S hS)
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigFppfOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigFppfZariski B S hS G)

/-- The specified-topology identification on the big fppf site preserves constant sections. -/
@[stacks 03P5 "tau unit on the big fppf site"]
public theorem constantSheafIsoLocallyConstantMaps_bigFppf_unit (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigFppfOver.toScheme B S hS)
      (BigFppfOver.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_bigFppf B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit.{u, v} (BigFppfOver.toScheme B S hS) G
    (BigFppfOver.topology B S hS) (bigFppfOver_openCoverData B S hS)
    (openCoverData_bottom (BigFppfOver.toScheme B S hS) (BigFppfOver.topology B S hS)
      (bigFppfOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigFppf B S hS G)

/-- The Zariski-topology identification on the big fppf site preserves constant sections. -/
@[stacks 03P5 "Zariski unit on the big fppf site"]
public theorem zariskiConstantSheafIsoLocallyConstantMaps_bigFppf_unit (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigFppfOver.toScheme B S hS)
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G
      (zariskiConstantSheafIsoLocallyConstantMaps_bigFppf B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit.{u, v} (BigFppfOver.toScheme B S hS) G
    ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigFppfOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigFppfOver.toScheme B S hS)
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigFppfOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigFppfZariski B S hS G)

/-- On the chosen big fppf site, the constant group sheaf itself is the restriction of the
group-valued functor of points of the constant group scheme. -/
@[stacks 03P5 "group-valued representation on the big fppf site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_bigFppf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj hS) B.inclusion)
      (BigFppfOver.topology B S hS) G := by
  let H := Over.post (X := B.obj hS) B.inclusion
  let J := BigFppfOver.topology B S hS
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_bigFppf_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
      (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigFppfOver_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

/-- The Zariski constant group sheaf on the chosen big fppf site is represented by `G_S`. -/
@[stacks 03P5 "Zariski group sheaf on the big fppf site"]
public def zariskiGroupSheafRepresented_bigFppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj hS) B.inclusion)
      ((BigFppfOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G := by
  let H := Over.post (X := B.obj hS) B.inclusion
  let F := BigFppfOver.toScheme B S hS
  let J := F.restrictedTopology Scheme.zariskiTopology
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      (locallyConstantMaps_isSheaf_bigFppfZariski B S hS G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigFppfOver_zariski_openCoverData B S hS
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen
    (openCoverData_bottom (H ⋙ Over.forget S) J hOpen) hSet

end AlgebraicGeometry

end
