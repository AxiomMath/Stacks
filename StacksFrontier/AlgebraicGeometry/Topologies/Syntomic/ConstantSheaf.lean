module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Support.SyntomicSiteRepresentatives
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.Coverings

/-!
# Constant sheaves on the big syntomic site of a scheme

Let `B` be a big syntomic site containing a scheme `S` and let `G` be an abstract group. On the
big syntomic site of `S`, both the sheafification of the constant presheaf with value `G` for
the syntomic topology and its sheafification for the Zariski topology restricted from schemes
have the locally constant `G`-valued maps as their sections; in particular the two
sheafifications agree. The constant sheaf of groups is in both cases the group-valued functor
of points of the constant group scheme `G_S`.

## Main results

* `AlgebraicGeometry.BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_openCover` —
  a Zariski covering of an object of a big syntomic site is tautologically equivalent to one of
  the site's own covering families.
* `AlgebraicGeometry.bigSyntomicOver_openCoverData` and
  `bigSyntomicOver_zariski_openCoverData` realise an arbitrary open cover of the scheme
  underlying a site object by a covering family, for the syntomic and for the restricted
  Zariski topology respectively.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps_bigSyntomic` and
  `zariskiConstantSheafIsoLocallyConstantMaps_bigSyntomic` identify the two constant sheaves,
  and the two `_unit` lemmas fix those identifications on constant sections.
* `AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigSyntomic` and
  `zariskiGroupSheafRepresented_bigSyntomic` are the representations of the constant group
  sheaves by `G_S`.

## Implementation notes

For the syntomic topology an arbitrary open cover has to be replaced by a tautologically
equivalent covering family of the site. An open cover is a syntomic covering and its members
are open subschemes, hence small enough to lie in the site, so this is an instance of the
general realisation result for syntomic coverings with representable sources. For the
restricted Zariski topology the open subschemes are realised in the site directly.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
* [Stacks Project, Tag 03X2](https://stacks.math.columbia.edu/tag/03X2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A Zariski covering of an object of a big syntomic site is tautologically equivalent to one
of the site's own covering families. -/
@[stacks 03X2 "part (3)"]
public theorem BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_openCover
    (B : BigSyntomicSite.{u}) (T : B.category) (𝒰 : Scheme.OpenCover.{w} T.1) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰.toPreZeroHypercover
          (V.map B.inclusion) :=
  B.exists_isCovering_tautologicallyEquivalent_of_sources_iso T 𝒰.toPreZeroHypercover
    (isSyntomicCovering_of_mem_zariskiPrecoverage 𝒰.mem₀)
    (fun i => ⟨⟨𝒰.X i, Scheme.size_lt_of_isOpenImmersion (𝒰.f i) T.2⟩, ⟨Iso.refl _⟩⟩)

/-- An open cover of a scheme by the members of an open cover of its space, with each member
mapping into the chosen open. -/
private theorem exists_openCover_forall_mem (X : Scheme.{u}) (U : X → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ (O : X.OpenCover.{u + 1}) (r : O.I₀ → X), ∀ i (y : O.X i), O.f i y ∈ U (r i) := by
  let U' : ULift.{u + 1, u} X → X.Opens := fun i => U i.down
  have hU' : TopologicalSpace.IsOpenCover U' := by
    rw [TopologicalSpace.IsOpenCover] at hU ⊢
    simpa [U'] using hU
  exact ⟨X.openCoverOfIsOpenCover U' hU', fun i => i.down, fun i y => y.2⟩

/-- Every open cover of the scheme underlying an object of the big syntomic site of `S` is
refined by a covering family of that site. -/
public theorem bigSyntomicOver_openCoverData (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {T : BigSyntomicOver B S hS}
      (U : (BigSyntomicOver.toScheme B S hS).obj T →
        ((BigSyntomicOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigSyntomicOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigSyntomicOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈ BigSyntomicOver.topology B S hS T ∧
          ∀ i y, (BigSyntomicOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let X := B.inclusion.obj T.left
  change TopologicalSpace.IsOpenCover (X := X) U at hU
  obtain ⟨O, r, hO⟩ := exists_openCover_forall_mem X U hU
  obtain ⟨V, hV, hEq⟩ :=
    BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_openCover B T.left O
  rcases hEq.2 with ⟨β, hβ⟩
  choose e he using hβ
  let W : V.I₀ → BigSyntomicOver B S hS := fun i => Over.mk (V.f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (V.f i) (by simp [W])
  have hcover : Sieve.ofArrows W a ∈ BigSyntomicOver.topology B S hS T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact B.precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩
  refine ⟨V.I₀, W, a, fun i => r (β i), hcover, fun i y => ?_⟩
  have heval : (B.inclusion.map (V.f i)) y = O.f (β i) ((e i).hom y) :=
    (congrArg (fun f => f y) (he i)).symm
  have hmap : (BigSyntomicOver.toScheme B S hS).map (a i) y =
      (B.inclusion.map (V.f i)) y := rfl
  rw [hmap, heval]
  exact hO _ _

/-- Every open cover of the scheme underlying an object of the big syntomic site of `S` is
refined by a family which covers for the Zariski topology restricted from schemes. -/
public theorem bigSyntomicOver_zariski_openCoverData (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    ∀ {T : BigSyntomicOver B S hS}
      (U : (BigSyntomicOver.toScheme B S hS).obj T →
        ((BigSyntomicOver.toScheme B S hS).obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → BigSyntomicOver B S hS) (a : ∀ i, W i ⟶ T)
        (r : I → (BigSyntomicOver.toScheme B S hS).obj T),
        Sieve.ofArrows W a ∈
          (BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology T ∧
          ∀ i y, (BigSyntomicOver.toScheme B S hS).map (a i) y ∈ U (r i) := by
  intro T U hU
  let F := BigSyntomicOver.toScheme B S hS
  let X := F.obj T
  obtain ⟨O, r, hO⟩ := exists_openCover_forall_mem X U hU
  let V : O.I₀ → B.category := fun i =>
    ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.left.2⟩
  let f : ∀ i, V i ⟶ T.left := fun i => ⟨O.f i⟩
  let W : O.I₀ → BigSyntomicOver B S hS := fun i => Over.mk (f i ≫ T.hom)
  let a : ∀ i, W i ⟶ T := fun i => Over.homMk (f i) (by simp [W])
  have hpush : (Sieve.ofArrows W a).functorPushforward F = Sieve.ofArrows O.X O.f := by
    rw [Sieve.functorPushforward_ofArrows]
    congr 1
  refine ⟨O.I₀, W, a, r, ?_, fun i y => hO i y⟩
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [hpush]
  exact O.mem_grothendieckTopology

/-- Locally constant `G`-valued maps form a sheaf on the big syntomic site of `S`. -/
public theorem locallyConstantMaps_isSheaf_bigSyntomic (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (BigSyntomicOver.topology B S hS)
      ((BigSyntomicOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
    (locallyConstantMapsOver_isSheaf_fpqc S G)

/-- Locally constant `G`-valued maps form a sheaf on the big syntomic site of `S` for the
Zariski topology restricted from schemes. -/
public theorem locallyConstantMaps_isSheaf_bigSyntomicZariski (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      ((BigSyntomicOver.toScheme B S hS).op ⋙
        locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let F := BigSyntomicOver.toScheme B S hS
  let : (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape Limits.WalkingCospan :=
    schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  exact locallyConstantMaps_isSheaf_restrictedZariski F inferInstance G

/-- Constant sheaves on the chosen big syntomic site have locally constant sections. -/
@[stacks 03P5 "big syntomic site"]
public def constantSheafIsoLocallyConstantMaps_bigSyntomic (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf (BigSyntomicOver.topology B S hS) (Type (max (u + 1) v))).obj G).obj ≅
    ((BigSyntomicOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (BigSyntomicOver.toScheme B S hS) G
    (BigSyntomicOver.topology B S hS) (bigSyntomicOver_openCoverData B S hS)
    (openCoverData_bottom (BigSyntomicOver.toScheme B S hS)
      (BigSyntomicOver.topology B S hS) (bigSyntomicOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSyntomic B S hS G)

/-- The Zariski sheafification on a chosen big syntomic site has locally constant sections. -/
@[stacks 03P5 "Zariski sheafification on the big syntomic site"]
public def zariskiConstantSheafIsoLocallyConstantMaps_bigSyntomic (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ((constantSheaf
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (Type (max (u + 1) v))).obj G).obj ≅
    ((BigSyntomicOver.toScheme B S hS).op ⋙
      locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
  constantSheafIsoLocallyConstantMapsOn (BigSyntomicOver.toScheme B S hS) G
    ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigSyntomicOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigSyntomicOver.toScheme B S hS)
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigSyntomicOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSyntomicZariski B S hS G)

/-- The specified-topology identification on the big syntomic site preserves constant
sections. -/
@[stacks 03P5 "tau unit on the big syntomic site"]
public theorem constantSheafIsoLocallyConstantMaps_bigSyntomic_unit (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigSyntomicOver.toScheme B S hS)
      (BigSyntomicOver.topology B S hS) G
      (constantSheafIsoLocallyConstantMaps_bigSyntomic B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (BigSyntomicOver.toScheme B S hS) G
    (BigSyntomicOver.topology B S hS) (bigSyntomicOver_openCoverData B S hS)
    (openCoverData_bottom (BigSyntomicOver.toScheme B S hS)
      (BigSyntomicOver.topology B S hS) (bigSyntomicOver_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSyntomic B S hS G)

/-- The Zariski-topology identification on the big syntomic site preserves constant
sections. -/
@[stacks 03P5 "Zariski unit on the big syntomic site"]
public theorem zariskiConstantSheafIsoLocallyConstantMaps_bigSyntomic_unit
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    ConstantSheafIso.UnitCompatible (BigSyntomicOver.toScheme B S hS)
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G
      (zariskiConstantSheafIsoLocallyConstantMaps_bigSyntomic B S hS G) :=
  constantSheafIsoLocallyConstantMapsOn_unit (BigSyntomicOver.toScheme B S hS) G
    ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
    (bigSyntomicOver_zariski_openCoverData B S hS)
    (openCoverData_bottom (BigSyntomicOver.toScheme B S hS)
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology)
      (bigSyntomicOver_zariski_openCoverData B S hS))
    (locallyConstantMaps_isSheaf_bigSyntomicZariski B S hS G)

/-- Representation of the constant group sheaf on the chosen big syntomic site. -/
@[stacks 03P5 "group-valued representation on the big syntomic site"]
public def constantGroupSheafRepresentedByConstantGroupScheme_bigSyntomic
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj S hS) B.inclusion)
      (BigSyntomicOver.topology B S hS) G := by
  let H := Over.post (X := B.obj S hS) B.inclusion
  let J := BigSyntomicOver.topology B S hS
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS (locallyConstantMapsOver G S ⋙ forget GrpCat)
      (locallyConstantMapsOver_isSheaf_fpqc S G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigSyntomicOver_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T :=
    fun hT => openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

/-- The Zariski constant group sheaf on the chosen big syntomic site is represented by
`G_S`. -/
@[stacks 03P5 "Zariski group sheaf on the big syntomic site"]
public def zariskiGroupSheafRepresented_bigSyntomic (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] :
    GroupSheafRepresentation S (Over.post (X := B.obj S hS) B.inclusion)
      ((BigSyntomicOver.toScheme B S hS).restrictedTopology Scheme.zariskiTopology) G := by
  let H := Over.post (X := B.obj S hS) B.inclusion
  let F := BigSyntomicOver.toScheme B S hS
  let J := F.restrictedTopology Scheme.zariskiTopology
  have hSet : Presheaf.IsSheaf J (H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (relativeLocallyConstantMapsIsoOnScheme S H G)).mpr
      (locallyConstantMaps_isSheaf_bigSyntomicZariski B S hS G)
  let : HasSheafify J GrpCat.{max (u + 1) v} := hasSheafify_grpCat J
  let : J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := wEqualsLocallyBijective_grpCat J
  have hOpen := @bigSyntomicOver_zariski_openCoverData B S hS
  have hEmpty : ∀ {T}, IsEmpty ((H ⋙ Over.forget S).obj T) → (⊥ : Sieve T) ∈ J T :=
    fun hT => openCoverData_bottom (H ⋙ Over.forget S) J hOpen hT
  exact groupSheafRepresentationOfLocallyConstantMaps.{u, v} S H J G hOpen hEmpty hSet

end AlgebraicGeometry

end
